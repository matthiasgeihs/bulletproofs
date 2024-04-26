#![allow(non_snake_case)]

extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use std::convert::TryInto;
use std::error::Error;
use std::iter::FromIterator;

use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::{thread_rng, RngCore, SeedableRng};
use rand_chacha::ChaChaRng;
use sha3::{Digest, Sha3_256};

const LATTICE_DIM: usize = 512;
const ROW_COUNT: usize = 32;
const LOG2Q: usize = 12;
const LOG2P: usize = 8;
const MAX_INT_SIZE: usize = 2 * LOG2Q + LOG2P.ilog2() as usize + LOG2P.is_power_of_two() as usize;

/// Hash input `x` onto a matrix of size `l x dim`.
pub fn lakey_hash<D: Digest, R: RngCore + SeedableRng<Seed = [u8; 32]>>(
    x: &[u8],
) -> Result<Vec<Vec<Scalar>>, Box<dyn Error>> {
    // Derive PRG seed from `x`.
    let hash = D::digest(x);
    let mut rng = R::from_seed(hash.as_slice().try_into()?);

    // Generate matrix from PRG.
    let l = ROW_COUNT;
    let q = 1 << LOG2Q;
    if q > u64::MAX {
        panic!("q is too large");
    }

    let rows = (0..l)
        .map(|_| {
            (0..LATTICE_DIM)
                .map(|_| (rng.next_u64() % q).into())
                .collect::<Vec<_>>()
        })
        .collect();
    Ok(rows)
}

fn mat_mul_var(A: &Vec<Vec<Scalar>>, K: &[Variable]) -> Vec<LinearCombination> {
    A.iter()
        .map(|ai| {
            if ai.len() != K.len() {
                panic!("Matrix and vector dimensions do not match");
            }
            let it = ai
                .iter()
                .zip(K.iter())
                .map(|(aij, kj)| (kj.clone(), aij.clone()));
            LinearCombination::from_iter(it)
        })
        .collect::<Vec<_>>()
}

fn mat_mul_scalar(A: &Vec<Vec<Scalar>>, k: &[Scalar]) -> Vec<Scalar> {
    A.iter()
        .map(|ai| {
            if ai.len() != k.len() {
                panic!("Matrix and vector dimensions do not match");
            }
            ai.iter().zip(k.iter()).map(|(aij, kj)| aij * kj).sum()
        })
        .collect::<Vec<_>>()
}

fn u64_from_scalar(x: &Scalar) -> u64 {
    x.as_bytes()
        .iter()
        .enumerate()
        .map(|(i, &xi)| {
            if i >= u64::BITS as usize / 8 && xi != 0 {
                panic!("Scalar is too large to fit in u64");
            }
            u64::from(xi) * (1 << i)
        })
        .sum()
}

fn bin(x: &Vec<Scalar>) -> Vec<Vec<Scalar>> {
    x.iter()
        .map(|xi| {
            let xi_u64 = u64_from_scalar(xi);
            (0..MAX_INT_SIZE)
                .map(|i| ((xi_u64 >> i) & 1).into())
                .collect()
        })
        .collect()
}

fn bin_equality_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    mut x: LinearCombination,
    x_bits: Option<Vec<Scalar>>,
) -> Vec<Variable> {
    let mut exp_2 = Scalar::ONE;
    let mut bit_vars = vec![];
    for i in 0..MAX_INT_SIZE {
        // Create low-level variables and add them to constraints
        let (a, b, o) = cs
            .allocate_multiplier(x_bits.as_ref().map(|q| {
                let bit = q[i];
                (Scalar::from(1u64) - bit, bit)
            }))
            .unwrap();

        // Enforce a * b = 0, so one of (a,b) is zero
        cs.constrain(o.into());

        // Enforce that a = 1 - b, so they both are 1 or 0.
        cs.constrain(a + (b - 1u64));

        // Add `-b_i*2^i` to the linear combination
        // in order to form the following constraint by the end of the loop:
        // x = Sum(b_i * 2^i, i = 0..n-1)
        x = x - b * exp_2;

        bit_vars.push(b);

        exp_2 = exp_2 + exp_2;
    }

    // Enforce that x = Sum(b_i * 2^i, i = 0..n-1)
    cs.constrain(x);

    bit_vars
}

fn lakey_trunc(x: &Vec<Vec<Variable>>) -> Vec<LinearCombination> {
    x.iter()
        .map(|y| {
            let y2: Vec<LinearCombination> = y[LOG2Q - LOG2P..LOG2Q]
                .iter()
                .map(|v| LinearCombination::from(*v))
                .collect();
            lakey_acc(&y2)
        })
        .collect()
}

fn lakey_acc(x: &[LinearCombination]) -> LinearCombination {
    if x.len() > u64::BITS as usize {
        panic!("Input is too large");
    }
    x.iter()
        .enumerate()
        .fold(LinearCombination::default(), |acc, (i, xi)| {
            acc + Scalar::from(1u64 << i) * xi.clone()
        })
}

/// Constrains Y = G * F(k, x) && K == Com(k), where F(k, x) = Acc(Trunc(H(x) * k)).
fn lakey_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    K: &[Variable],
    k: Option<&[Scalar]>,
    x: &[u8],
    Y: Variable,
) {
    let A: Vec<Vec<Scalar>> = lakey_hash::<Sha3_256, ChaChaRng>(x).unwrap();
    let Y1: Vec<LinearCombination> = mat_mul_var(&A, K);

    let y1_bits: Vec<Option<Vec<Scalar>>> = if let Some(k) = k {
        let y1: Vec<Scalar> = mat_mul_scalar(&A, k);
        let y1_bits: Vec<Vec<Scalar>> = bin(&y1);
        y1_bits.into_iter().map(|x| Some(x)).collect::<Vec<_>>()
    } else {
        (0..ROW_COUNT).map(|_| None).collect()
    };

    // let Y1_bits: Vec<Vec<Variable>> = bin_equality_gadget(cs, Y1, y1_bits); // Y1 == Com(Acc(y1_bits)) && y1_bits in {0,1}^*
    let Y1_bits: Vec<Vec<Variable>> = Y1
        .iter()
        .zip(y1_bits)
        .map(|(yi, yi_bits)| bin_equality_gadget(cs, yi.clone(), yi_bits))
        .collect();

    let Y2: Vec<LinearCombination> = lakey_trunc(&Y1_bits);
    let Y3: LinearCombination = lakey_acc(&Y2);

    cs.constrain(Y - Y3); // Y == Y3
}

// Prover's scope
fn lakey_gadget_proof(
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    k: &[Scalar],
    K_open: &[Scalar],
    x: &[u8],
    y: Scalar,
    Y_open: Scalar,
) -> Result<R1CSProof, R1CSError> {
    let mut transcript = Transcript::new(b"R1CSLakeyGadget");

    // 1. Create a prover
    let mut prover = Prover::new(pc_gens, &mut transcript);

    // 2. Commit high-level variables
    // let (commitments, vars): (Vec<_>, Vec<_>) = [a1, a2, b1, b2, c1]
    //     .into_iter()
    //     .map(|x| prover.commit(Scalar::from(*x), Scalar::random(&mut thread_rng())))
    //     .unzip();
    let (_, K_vars): (Vec<_>, Vec<_>) = k
        .iter()
        .zip(K_open)
        .map(|(ki, ri)| prover.commit(*ki, *ri))
        .unzip();
    let (_, Y_var) = prover.commit(y, Y_open);

    // 3. Build a CS
    lakey_gadget(&mut prover, &K_vars, Some(k), x, Y_var);

    // 4. Make a proof
    let proof = prover.prove(bp_gens)?;

    Ok(proof)
}

// Verifier logic
fn lakey_gadget_verify(
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    K: &[CompressedRistretto],
    x: &[u8],
    Y: CompressedRistretto,
    proof: R1CSProof,
) -> Result<(), R1CSError> {
    let mut transcript = Transcript::new(b"R1CSLakeyGadget");

    // 1. Create a verifier
    let mut verifier = Verifier::new(&mut transcript);

    // 2. Commit high-level variables
    // let vars: Vec<_> = commitments.iter().map(|V| verifier.commit(*V)).collect();
    let K_vars: Vec<_> = K.iter().map(|ki| verifier.commit(*ki)).collect();
    let Y_var = verifier.commit(Y);

    // 3. Build a CS
    lakey_gadget(&mut verifier, &K_vars, None, x, Y_var);

    // 4. Verify the proof
    verifier
        .verify(&proof, &pc_gens, &bp_gens)
        .map_err(|_| R1CSError::VerificationError)
}

fn lakey_gadget_roundtrip_helper(
    k: &[Scalar],
    K: &[CompressedRistretto],
    K_open: &Vec<Scalar>,
    x: &[u8],
    y: Scalar,
    Y: CompressedRistretto,
    Y_open: Scalar,
) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

    let proof = lakey_gadget_proof(&pc_gens, &bp_gens, k, &K_open, x, y, Y_open)?;

    lakey_gadget_verify(&pc_gens, &bp_gens, K, x, Y, proof)
}

fn lakey_gadget_roundtrip_serialization_helper(
    k: &[Scalar],
    K: &[CompressedRistretto],
    K_open: &Vec<Scalar>,
    x: &[u8],
    y: Scalar,
    Y: CompressedRistretto,
    Y_open: Scalar,
) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

    let proof = lakey_gadget_proof(&pc_gens, &bp_gens, k, &K_open, x, y, Y_open)?;

    let proof = proof.to_bytes();

    let proof = R1CSProof::from_bytes(&proof)?;

    lakey_gadget_verify(&pc_gens, &bp_gens, K, x, Y, proof)
}

#[test]
fn lakey_gadget_test() {
    // (3 + 4) * (6 + 1) = (40 + 9)
    assert!(lakey_gadget_roundtrip_helper(3, 4, 6, 1, 40, 9).is_ok());
    // (3 + 4) * (6 + 1) != (40 + 10)
    assert!(lakey_gadget_roundtrip_helper(3, 4, 6, 1, 40, 10).is_err());
}

#[test]
fn lakey_gadget_serialization_test() {
    // (3 + 4) * (6 + 1) = (40 + 9)
    assert!(lakey_gadget_roundtrip_serialization_helper(3, 4, 6, 1, 40, 9).is_ok());
    // (3 + 4) * (6 + 1) != (40 + 10)
    assert!(lakey_gadget_roundtrip_serialization_helper(3, 4, 6, 1, 40, 10).is_err());
}

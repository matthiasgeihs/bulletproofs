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
use sha3::Digest;

const LATTICE_DIM: usize = 512;
const KEY_LEN: usize = 32;
const LOG2Q: usize = 12;

/// Hash input `x` onto a matrix of size `l x dim`.
pub fn lakey_hash<D: Digest, R: RngCore + SeedableRng<Seed = [u8; 32]>>(
    x: &[u8],
) -> Result<Vec<Vec<Scalar>>, Box<dyn Error>> {
    // Derive PRG seed from `x`.
    let hash = D::digest(x);
    let mut rng = R::from_seed(hash.as_slice().try_into()?);

    // Generate matrix from PRG.
    let l = KEY_LEN;
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

fn mat_mul_var(A: &Vec<Vec<Scalar>>, K: &Vec<Variable>) -> Vec<LinearCombination> {
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

fn mat_mul_scalar(A: &Vec<Vec<Scalar>>, k: &Vec<Scalar>) -> Vec<Scalar> {
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
            (0..LOG2Q)
                .map(|i| {
                    let xi_u64 = u64_from_scalar(xi);
                    (xi_u64 >> i).into()
                })
                .collect()
        })
        .collect()
}

/// Constrains Y = G * F(k, x) && K == Com(k), where F(k, x) = Acc(Trunc(H(x) * k)).
fn lakey_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    K: Vec<Variable>,
    k: Option<Vec<Scalar>>,
    x: &[u8],
    Y: CompressedRistretto,
) {
    let A: Vec<Vec<Scalar>> = lakey_hash(x).unwrap();
    let Y1: Vec<LinearCombination> = mat_mul_var(&A, &K);

    let y1_bits = if let Some(k) = k {
        let y1: Vec<Scalar> = mat_mul_scalar(&A, &k);
        let y1_bits: Vec<Vec<Scalar>> = bin(&y1);
        Some(y1_bits)
    } else {
        None
    };

    let Y1_bits: Vec<LinearCombination> = bin_equality_gadget(cs, Y1, y1_bits); // Y1 == Acc(Com(y1_bits)) && y1_bits in {0,1}^*

    let Y2: Vec<LinearCombination> = lakey_trunc(Y1_bits);
    let Y3: LinearCombination = lakey_acc(Y2);

    cs.constrain(Y.into() - Y3); // Y == Y3
}

// Prover's scope
fn lakey_gadget_proof(
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    a1: u64,
    a2: u64,
    b1: u64,
    b2: u64,
    c1: u64,
    c2: u64,
) -> Result<(R1CSProof, Vec<CompressedRistretto>), R1CSError> {
    let mut transcript = Transcript::new(b"R1CSLakeyGadget");

    // 1. Create a prover
    let mut prover = Prover::new(pc_gens, &mut transcript);

    // 2. Commit high-level variables
    let (commitments, vars): (Vec<_>, Vec<_>) = [a1, a2, b1, b2, c1]
        .into_iter()
        .map(|x| prover.commit(Scalar::from(*x), Scalar::random(&mut thread_rng())))
        .unzip();

    // 3. Build a CS
    lakey_gadget(
        &mut prover,
        vars[0].into(),
        vars[1].into(),
        vars[2].into(),
        vars[3].into(),
        vars[4].into(),
        Scalar::from(c2).into(),
    );

    // 4. Make a proof
    let proof = prover.prove(bp_gens)?;

    Ok((proof, commitments))
}

// Verifier logic
fn lakey_gadget_verify(
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    c2: u64,
    proof: R1CSProof,
    commitments: Vec<CompressedRistretto>,
) -> Result<(), R1CSError> {
    let mut transcript = Transcript::new(b"R1CSLakeyGadget");

    // 1. Create a verifier
    let mut verifier = Verifier::new(&mut transcript);

    // 2. Commit high-level variables
    let vars: Vec<_> = commitments.iter().map(|V| verifier.commit(*V)).collect();

    // 3. Build a CS
    lakey_gadget(
        &mut verifier,
        vars[0].into(),
        vars[1].into(),
        vars[2].into(),
        vars[3].into(),
        vars[4].into(),
        Scalar::from(c2).into(),
    );

    // 4. Verify the proof
    verifier
        .verify(&proof, &pc_gens, &bp_gens)
        .map_err(|_| R1CSError::VerificationError)
}

fn lakey_gadget_roundtrip_helper(
    a1: u64,
    a2: u64,
    b1: u64,
    b2: u64,
    c1: u64,
    c2: u64,
) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

    let (proof, commitments) = lakey_gadget_proof(&pc_gens, &bp_gens, a1, a2, b1, b2, c1, c2)?;

    lakey_gadget_verify(&pc_gens, &bp_gens, c2, proof, commitments)
}

fn lakey_gadget_roundtrip_serialization_helper(
    a1: u64,
    a2: u64,
    b1: u64,
    b2: u64,
    c1: u64,
    c2: u64,
) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

    let (proof, commitments) = lakey_gadget_proof(&pc_gens, &bp_gens, a1, a2, b1, b2, c1, c2)?;

    let proof = proof.to_bytes();

    let proof = R1CSProof::from_bytes(&proof)?;

    lakey_gadget_verify(&pc_gens, &bp_gens, c2, proof, commitments)
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

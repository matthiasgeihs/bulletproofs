#![allow(non_snake_case)]

extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use std::convert::TryInto;
use std::error::Error;
use std::iter::FromIterator;
use std::ops::{Add, Mul};

use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::{thread_rng, RngCore, SeedableRng};
use rand_chacha::ChaChaRng;
use rand_core::CryptoRngCore;
use sha3::{Digest, Sha3_256};

const LATTICE_DIM: usize = 512;
const ROW_COUNT: usize = 32;
const LOG2Q: usize = 12;
const LOG2P: usize = 8;
const MAX_INT_SIZE: usize = 2 * LOG2Q + LOG2P.ilog2() as usize + LOG2P.is_power_of_two() as usize;

/// Hash input `x` onto a matrix of size `l x dim`.
pub fn lakey_hash(x: &[u8]) -> Result<Vec<Vec<Scalar>>, Box<dyn Error>> {
    // Derive PRG seed from `x`.
    let hash = Sha3_256::digest(x);
    let mut rng = ChaChaRng::from_seed(hash.as_slice().try_into()?);

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

fn mat_mul<T: Copy, U: Default + Add<Output = U> + Mul<Scalar, Output = U> + From<T>>(
    m: &Vec<Vec<Scalar>>,
    v: &[T],
) -> Vec<U> {
    m.iter()
        .map(|ai| {
            if ai.len() != v.len() {
                panic!("Matrix and vector dimensions do not match");
            }
            ai.iter()
                .zip(v.iter())
                .fold(U::default(), |acc, (aij, kj)| acc + U::from(*kj) * *aij)
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

fn bin(x: &Scalar) -> Vec<Scalar> {
    let x_u64 = u64_from_scalar(x);
    (0..MAX_INT_SIZE)
        .map(|i| ((x_u64 >> i) & 1).into())
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

fn lakey_trunc(x: &[Vec<Variable>]) -> Vec<LinearCombination> {
    x.iter()
        .map(|y| {
            let y2: Vec<LinearCombination> = y[LOG2Q - LOG2P..LOG2Q]
                .iter()
                .map(|v| LinearCombination::from(*v))
                .collect();
            lakey_acc(&y2, 2u64.into())
        })
        .collect()
}

fn lakey_acc<T: Add<Output = T> + Mul<Scalar, Output = T> + Default + Clone>(
    x: &[T],
    base: Scalar,
) -> T {
    if x.len() > u64::BITS as usize {
        panic!("Input is too large");
    }
    let mut a = Scalar::ONE;
    x.iter().fold(T::default(), |acc, xi| {
        let acc = acc + xi.clone() * a;
        a = a * base;
        acc
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
    let A: Vec<Vec<Scalar>> = lakey_hash(x).unwrap();
    let Y1: Vec<LinearCombination> = mat_mul(&A, K);

    let y1_bits: Vec<Option<Vec<Scalar>>> = if let Some(k) = k {
        let y1: Vec<Scalar> = mat_mul(&A, k);
        let y1_bits: Vec<Vec<Scalar>> = y1.iter().map(bin).collect();
        y1_bits.into_iter().map(|x| Some(x)).collect::<Vec<_>>()
    } else {
        (0..ROW_COUNT).map(|_| None).collect()
    };

    // Y1 == Com(Acc(y1_bits)) && y1_bits in {0,1}^*
    let Y1_bits: Vec<Vec<Variable>> = Y1
        .iter()
        .zip(y1_bits)
        .map(|(yi, yi_bits)| bin_equality_gadget(cs, yi.clone(), yi_bits))
        .collect();

    let Y2: Vec<LinearCombination> = lakey_trunc(&Y1_bits);
    let Y3: LinearCombination = lakey_acc(&Y2, (1u64 << LOG2P).into());

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
) -> Result<R1CSProof, R1CSError> {
    let mut transcript = Transcript::new(b"R1CSLakeyGadget");

    // 1. Create a prover
    let mut prover = Prover::new(pc_gens, &mut transcript);

    // 2. Commit high-level variables
    let (_, K_vars): (Vec<_>, Vec<_>) = k
        .iter()
        .zip(K_open)
        .map(|(ki, ri)| prover.commit(*ki, *ri))
        .unzip();
    let (_, Y_var) = prover.commit(y, Scalar::ZERO);

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

struct PrivateKey {
    k: Vec<Scalar>,
    K_open: Vec<Scalar>,
    pc_gens: PedersenGens,
    bp_gens: BulletproofGens,
}

struct PublicKey {
    K: Vec<CompressedRistretto>,
    pc_gens: PedersenGens,
    bp_gens: BulletproofGens,
}

struct KeyPair {
    private: PrivateKey,
    public: PublicKey,
}

fn lakey_keygen<R: CryptoRngCore>(rng: &mut R) -> KeyPair {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(1024, 1);

    let q = 1 << LOG2Q;
    if q > u64::MAX {
        panic!("q is too large");
    }
    let k = (0..LATTICE_DIM)
        .map(|_| (rng.next_u64() % q).into())
        .collect::<Vec<_>>();
    let K_open = (0..LATTICE_DIM)
        .map(|_| Scalar::random(rng))
        .collect::<Vec<_>>();
    let K = k
        .iter()
        .zip(K_open.iter())
        .map(|(ki, ri)| pc_gens.commit(*ki, *ri).compress())
        .collect::<Vec<_>>();
    KeyPair {
        private: PrivateKey {
            k,
            K_open,
            pc_gens,
            bp_gens: bp_gens.clone(),
        },
        public: PublicKey {
            K,
            pc_gens,
            bp_gens,
        },
    }
}

fn lakey_trunc_scalar(x: &[Scalar]) -> Vec<Scalar> {
    x.iter()
        .map(|xi| {
            let xi_bits = bin(xi);
            let xi_trunc = &xi_bits[LOG2Q - LOG2P..LOG2Q];
            lakey_acc(xi_trunc, 2u64.into())
        })
        .collect()
}

struct EvalResult {
    y: Scalar,
    Y: CompressedRistretto,
    proof: R1CSProof,
}

fn lakey_eval(k: &PrivateKey, x: &[u8]) -> EvalResult {
    let A = lakey_hash(x).unwrap();
    let y1 = mat_mul(&A, &k.k);
    let y2 = lakey_trunc_scalar(&y1);
    let y: Scalar = lakey_acc(&y2, (1u64 << LOG2P).into());
    let Y = k.pc_gens.commit(y, Scalar::ZERO).compress();
    let proof = lakey_gadget_proof(&k.pc_gens, &k.bp_gens, &k.k, &k.K_open, x, y).unwrap();
    EvalResult { y, Y, proof }
}

fn lakey_verify(
    k: &PublicKey,
    x: &[u8],
    Y: CompressedRistretto,
    proof: R1CSProof,
) -> Result<(), R1CSError> {
    lakey_gadget_verify(&k.pc_gens, &k.bp_gens, &k.K, x, Y, proof)
}

#[test]
fn lakey_gadget_test() {
    let mut rng = thread_rng();

    // Key generation.
    let key_pair = lakey_keygen(&mut rng);

    // Evaluation.
    let x = rng.next_u64().to_be_bytes();
    let y = lakey_eval(&key_pair.private, &x);
    println!("PRF output: {:?}", y.y);
    println!("Proof size: {:?}", y.proof.serialized_size());

    assert!(lakey_verify(&key_pair.public, &x, y.Y, y.proof.clone()).is_ok());

    let Y_err = y.Y.decompress().unwrap().mul(Scalar::from(2u64)).compress();
    assert!(lakey_verify(&key_pair.public, &x, Y_err, y.proof).is_err());
}

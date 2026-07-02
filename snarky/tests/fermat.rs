//! Port of snarky's OCaml `src/tests/fermat.ml` example.
//!
//! The circuit proves knowledge of `(x, y)` such that `x³ + y³ = z³`, where
//! `z` is the public input. As in the OCaml version, the prover freely picks
//! `x` and derives the witness `y` as a cube root inside the witness
//! computation (the equivalent of the OCaml `As_prover` block).
//!
//! The OCaml example runs over a toy 41-element field with `p ≡ 2 (mod 3)`,
//! where cubing is a bijection and `c^((2p-1)/3)` is a cube root of any `c`.
//! The Pasta fields have `p ≡ 1 (mod 3)` instead, so cubing is 3-to-1 and only
//! a third of the elements are cubes. Since `p ≡ 4 (mod 9)` for Vesta's scalar
//! field, a cubic residue `c` has cube root `c^((2p+1)/9)`, and `c` is a cubic
//! residue iff `c^((p-1)/3) = 1`. The test therefore samples `x` until
//! `z³ - x³` is a cube, and passes it as the private input.

use ark_ff::{Field, One, PrimeField, UniformRand, Zero};
use mina_curves::pasta::{Fp, Vesta, VestaParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use num_bigint::BigUint;
use snarky::{loc, prelude::*};

type BaseSponge =
    DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
type Proof = poly_commitment::ipa::OpeningProof<Vesta, { snarky::FULL_ROUNDS }>;

fn modulus() -> BigUint {
    <Fp as PrimeField>::MODULUS.into()
}

fn cube(x: Fp) -> Fp {
    x * x * x
}

/// A cubic residue test: `c` is a cube iff `c^((p-1)/3) = 1` (or `c = 0`).
fn is_cube(c: Fp) -> bool {
    if c.is_zero() {
        return true;
    }
    let exp = (modulus() - 1u32) / 3u32;
    c.pow(exp.to_u64_digits()).is_one()
}

/// Cube root of a cubic residue, valid for `p ≡ 4 (mod 9)`:
/// `(c^((2p+1)/9))³ = c^((2(p-1))/3 + 1) = c · (c^((p-1)/3))² = c`.
fn cube_root(c: Fp) -> Fp {
    let exp = (2u32 * modulus() + 1u32) / 9u32;
    c.pow(exp.to_u64_digits())
}

struct FermatCircuit {}

impl SnarkyCircuit for FermatCircuit {
    type Curve = Vesta;
    type Proof = Proof;

    /// The prover's free choice of `x`.
    type PrivateInput = Fp;
    /// The public value `z`.
    type PublicInput = FieldVar<Fp>;
    type PublicOutput = ();

    fn circuit(
        &self,
        sys: &mut RunState<Fp>,
        z: Self::PublicInput,
        private: Option<&Self::PrivateInput>,
    ) -> SnarkyResult<Self::PublicOutput> {
        // You have free choice for the first variable.
        let x: FieldVar<Fp> = sys.compute(loc!(), |_| *private.unwrap())?;

        // Here we use the cube-root trick to compute the witness y.
        let y: FieldVar<Fp> = sys.compute(loc!(), |env| {
            let x = env.read_var(&x);
            let z = env.read_var(&z);
            cube_root(cube(z) - cube(x))
        })?;

        let mut cube_var = |a: &FieldVar<Fp>| -> SnarkyResult<FieldVar<Fp>> {
            let a2 = a.mul(a, None, loc!(), sys)?;
            a2.mul(a, None, loc!(), sys)
        };

        let x3 = cube_var(&x)?;
        let y3 = cube_var(&y)?;
        let z3 = cube_var(&z)?;

        (x3 + y3).assert_equals(sys, loc!(), &z3)?;

        Ok(())
    }
}

/// Samples a Fermat instance `(z, x)` such that `z³ - x³` is a cube,
/// so that the in-circuit witness computation of `y` succeeds.
fn sample_instance(rng: &mut impl rand::RngCore) -> (Fp, Fp) {
    let z = Fp::rand(rng);
    loop {
        let x = Fp::rand(rng);
        if is_cube(cube(z) - cube(x)) {
            return (z, x);
        }
    }
}

#[test]
fn cube_root_roundtrip() {
    let mut rng = o1_utils::tests::make_test_rng(None);
    for _ in 0..10 {
        let a = Fp::rand(&mut rng);
        let c = cube(a);
        assert!(is_cube(c));
        let root = cube_root(c);
        assert_eq!(cube(root), c);
    }
}

#[test]
fn fermat_prove_verify() {
    let circuit = FermatCircuit {};
    let (mut prover_index, verifier_index) = circuit.compile_to_indexes().unwrap();

    println!("{}", prover_index.asm());

    let mut rng = o1_utils::tests::make_test_rng(None);

    for _ in 0..2 {
        let (z, x) = sample_instance(&mut rng);

        let debug = true;
        let (proof, _public_output) = prover_index
            .prove::<BaseSponge, ScalarSponge>(z, x, debug)
            .unwrap();

        verifier_index.verify::<BaseSponge, ScalarSponge>(proof, z, ());
    }
}

#[test]
#[should_panic]
fn fermat_bad_witness_panics() {
    let circuit = FermatCircuit {};
    let (mut prover_index, _verifier_index) = circuit.compile_to_indexes().unwrap();

    let mut rng = o1_utils::tests::make_test_rng(None);

    // find (z, x) where z³ - x³ is NOT a cube: the witness computation of y
    // then produces a value that violates x³ + y³ = z³.
    let (z, x) = loop {
        let z = Fp::rand(&mut rng);
        let x = Fp::rand(&mut rng);
        if !is_cube(cube(z) - cube(x)) {
            break (z, x);
        }
    };

    let debug = true;
    let _ = prover_index
        .prove::<BaseSponge, ScalarSponge>(z, x, debug)
        .unwrap();
}

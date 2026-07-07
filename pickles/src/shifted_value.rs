//! Shifted-value scalar representations (pickles' `Shifted_value`,
//! `plonkish_prelude/shifted_value.ml`).
//!
//! Deferred scalars are carried across the Pasta cycle in a *shifted* form so
//! that they fit the `scale_fast` conventions of the curve gadgets. Two shifts
//! are used:
//!
//! - **Type1** (`scale_fast`): `to_field(t) = 2·t + 2^size + 1`, i.e. the value
//!   fed to [`crate::plonk_curve_ops::scale_fast`], which computes
//!   `(2·repr + 2^num_bits + 1)·base`. The inverse is
//!   `of_field(s) = (s − 2^size − 1) / 2`.
//! - **Type2** (`scale_fast2`): `to_field(t) = t + 2^size`, inverse
//!   `of_field(s) = s − 2^size`.
//!
//! `size` is the scalar field's `size_in_bits` (`F::MODULUS_BIT_SIZE`).
//!
//! # Cross-field embedding
//!
//! The scalars belong to the *other* curve's scalar field, but the shifted
//! representative is carried in the verifier circuit's field. For the Pasta
//! cycle this is lossless in the wrap→step direction: `Fp`'s modulus is larger
//! than `Fq`'s, so any `Fq` representative (an integer `< q < p`) embeds into
//! `Fp` without reduction. [`embed_repr`] performs that integer-preserving
//! embedding.

use ark_ff::{BigInteger, PrimeField};

/// `2^{F::MODULUS_BIT_SIZE}` — the `2^size` used by both shifts.
pub fn two_to_size<F: PrimeField>() -> F {
    let size = F::MODULUS_BIT_SIZE as u64;
    F::from(2u64).pow([size])
}

/// Type1 `to_field`: `2·t + 2^size + 1` — the value consumed by `scale_fast`.
pub fn type1_to_field<F: PrimeField>(repr: F) -> F {
    repr + repr + two_to_size::<F>() + F::one()
}

/// Type1 `of_field`: `(s − 2^size − 1) / 2` — the shifted representative of `s`.
pub fn type1_of_field<F: PrimeField>(s: F) -> F {
    let half = F::from(2u64).inverse().expect("2 is invertible");
    (s - two_to_size::<F>() - F::one()) * half
}

/// Type2 `to_field`: `t + 2^size`.
pub fn type2_to_field<F: PrimeField>(repr: F) -> F {
    repr + two_to_size::<F>()
}

/// Type2 `of_field`: `s − 2^size`.
pub fn type2_of_field<F: PrimeField>(s: F) -> F {
    s - two_to_size::<F>()
}

/// Embed a shifted representative from a smaller field `S` into the circuit
/// field `F` by preserving its integer value. Sound when `S`'s modulus is at
/// most `F`'s (e.g. `Fq` → `Fp` on the Pasta cycle), which holds for every
/// shifted representative crossing wrap→step.
pub fn embed_repr<S: PrimeField, F: PrimeField>(repr: S) -> F {
    F::from_le_bytes_mod_order(&repr.into_bigint().to_bytes_le())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;
    use mina_curves::pasta::{Fp, Fq, Pallas, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;
    use snarky::gadgets::curve::Point;
    use snarky::{api::SnarkyCircuit, loc, FieldVar, RunState, SnarkyResult};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    /// Type1/Type2 `to_field ∘ of_field = id` in `Fq`.
    #[test]
    fn shifted_value_round_trip() {
        let mut rng = o1_utils::tests::make_test_rng(None);
        for _ in 0..100 {
            let s = Fq::rand(&mut rng);
            assert_eq!(type1_to_field(type1_of_field(s)), s, "Type1");
            assert_eq!(type2_to_field(type2_of_field(s)), s, "Type2");
        }
    }

    struct Type1ScaleCircuit {
        repr: Fp, // embedded Fq representative
        g: (Fp, Fp),
    }
    impl SnarkyCircuit for Type1ScaleCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>);
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let repr: FieldVar<Fp> = sys.compute(loc!(), |_| self.repr)?;
            let g = Point::new(
                sys.compute(loc!(), |_| self.g.0)?,
                sys.compute(loc!(), |_| self.g.1)?,
            );
            // num_bits = Fq size_in_bits (the scalar field of the scaled point)
            let num_bits = Fq::MODULUS_BIT_SIZE as usize;
            let res = crate::plonk_curve_ops::scale_fast(sys, loc!(), &g, &repr, num_bits)?;
            Ok((res.x, res.y))
        }
    }

    /// The cross-field pipeline `s → type1_of_field → embed(Fq→Fp) →
    /// scale_fast` scales a Pallas point exactly by `s`, i.e. reproduces
    /// `s · g` even though the circuit is over `Fp`.
    #[test]
    fn type1_scale_fast_matches_scalar_mul() {
        let mut rng = o1_utils::tests::make_test_rng(None);
        assert_eq!(Fq::MODULUS_BIT_SIZE % 5, 0, "num_bits must be a multiple of 5");

        for _ in 0..2 {
            let s = Fq::rand(&mut rng);
            let g = (Pallas::generator() * Fq::rand(&mut rng)).into_affine();
            let expected = (g * s).into_affine();

            let repr_fq = type1_of_field(s);
            let repr_fp: Fp = embed_repr::<Fq, Fp>(repr_fq);

            let circ = Type1ScaleCircuit {
                repr: repr_fp,
                g: (g.x, g.y),
            };
            let (mut pi, ver) = circ.compile_to_indexes().unwrap();
            let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
            assert_eq!(*out, (expected.x, expected.y));
            ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
        }
    }
}

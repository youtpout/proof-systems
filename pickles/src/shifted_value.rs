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
//! representative is carried in the verifier circuit's field. On the Pasta
//! cycle **Fq (Tock) > Fp (Tick)**: a Tick (`Fp`) representative always fits
//! in `Fq` (Type1, single element — the wrap side), while a Tock (`Fq`) value
//! does *not* fit in `Fp` and is carried as the Type2 split pair
//! `(s_div_2, s_odd)` on the step side ([`split_repr`]). [`embed_repr`] is
//! the integer-preserving embedding for values known to fit.

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

/// Embed a representative from field `S` into field `F` by preserving its
/// integer value. Sound when the value is below `F`'s modulus: always for
/// `Fp` → `Fq` (p < q on Pasta); for `Fq` → `Fp` only when the value happens
/// to fit (a uniformly random `Fq` element exceeds `p` with probability
/// `(q-p)/q ≈ 2^-158` — Tock values that must cross reliably use
/// [`split_repr`] instead).
pub fn embed_repr<S: PrimeField, F: PrimeField>(repr: S) -> F {
    F::from_le_bytes_mod_order(&repr.into_bigint().to_bytes_le())
}

/// Split a value of the *bigger* field `S` into the Type2 carry pair for the
/// smaller circuit field `F`: `(bits[1..] packed, bit 0)` — i.e.
/// `value = 2·s_div_2 + s_odd` with `s_div_2 < 2^254` always fitting `F`.
/// This is kimchi's `absorb_fr` split and pickles' `Shifted_value.Type2`
/// in-circuit representation.
pub fn split_repr<S: PrimeField, F: PrimeField>(value: S) -> (F, bool) {
    let bits = value.into_bigint().to_bits_le();
    let mut half = F::zero();
    for &b in bits[1..].iter().rev() {
        half = half + half;
        if b {
            half += F::one();
        }
    }
    (half, bits[0])
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
    use snarky::{
        api::SnarkyCircuit, gadgets::curve::Point, loc, FieldVar, RunState, SnarkyResult,
    };

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
        assert_eq!(
            Fq::MODULUS_BIT_SIZE % 5,
            0,
            "num_bits must be a multiple of 5"
        );

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

/// `Impls.Step.Other_field.forbidden_shifted_values`: the 255-bit patterns
/// whose Type2 shifted decoding is ambiguous modulo the Tock (Fq) modulus,
/// split like the step-side `(low bits, high bit)` representation —
/// `lo = x >> 1` as an Fp element (dropped when `lo ≥ p`, the OCaml filter)
/// and `hi = bit 254 of x` (impls.ml:58-76).
pub fn forbidden_shifted_values_fp_pairs() -> Vec<(mina_curves::pasta::Fp, bool)> {
    use ark_ff::PrimeField;
    use num_bigint::BigInt;
    use num_traits::One;
    let modulus_p = BigInt::from_bytes_le(
        num_bigint::Sign::Plus,
        &ark_ff::BigInteger::to_bytes_le(&<mina_curves::pasta::Fp as PrimeField>::MODULUS),
    );
    let modulus_q = BigInt::from_bytes_le(
        num_bigint::Sign::Plus,
        &ark_ff::BigInteger::to_bytes_le(&<mina_curves::pasta::Fq as PrimeField>::MODULUS),
    );
    let two_to_n = BigInt::one() << 255;
    let mut out = Vec::new();
    for base in [-&two_to_n, -&two_to_n - BigInt::one()] {
        // all values equivalent to `base` mod q that fit in 255 bits
        let mut x: BigInt = ((&base % &modulus_q) + &modulus_q) % &modulus_q;
        while x < two_to_n {
            let hi = x.bit(254);
            let lo: BigInt = &x >> 1;
            if lo < modulus_p {
                let (_, bytes) = lo.to_bytes_le();
                out.push((mina_curves::pasta::Fp::from_le_bytes_mod_order(&bytes), hi));
            }
            x += &modulus_q;
        }
    }
    out
}

/// `Impls.Wrap.Other_field.forbidden_shifted_values`: the 255-bit patterns
/// whose Type1 shifted decoding is ambiguous modulo the Tick (Fp) modulus,
/// as Fq elements (patterns ≥ the Fq modulus are unrepresentable and
/// dropped, like the OCaml filter).
pub fn forbidden_shifted_values_fq() -> Vec<mina_curves::pasta::Fq> {
    use ark_ff::PrimeField;
    use num_bigint::BigInt;
    use num_traits::One;
    let modulus_p = BigInt::from_bytes_le(
        num_bigint::Sign::Plus,
        &ark_ff::BigInteger::to_bytes_le(&<mina_curves::pasta::Fp as PrimeField>::MODULUS),
    );
    let modulus_q = BigInt::from_bytes_le(
        num_bigint::Sign::Plus,
        &ark_ff::BigInteger::to_bytes_le(&<mina_curves::pasta::Fq as PrimeField>::MODULUS),
    );
    let two_to_n = BigInt::one() << 255;
    let mut out = Vec::new();
    for base in [-&two_to_n, -&two_to_n - BigInt::one()] {
        // all values equivalent to `base` mod p that fit in 255 bits
        let mut x: BigInt = ((&base % &modulus_p) + &modulus_p) % &modulus_p;
        while x < two_to_n {
            if x < modulus_q {
                let (_, bytes) = x.to_bytes_le();
                out.push(mina_curves::pasta::Fq::from_le_bytes_mod_order(&bytes));
            }
            x += &modulus_p;
        }
    }
    out.sort();
    out.dedup();
    out
}

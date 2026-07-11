//! Endomorphism coefficients for both sides of the cycle
//! (port of pickles' `endo.ml`).

use kimchi::curve::KimchiCurve;
use mina_curves::pasta::{Fp, Fq, Pallas, Vesta};

use crate::common::FULL_ROUNDS;

/// The endo coefficients used by step circuits (Tick side):
/// the base and scalar endo of the *other* curve (Pallas), as seen from Fp.
pub mod tick {
    use super::*;

    /// `Endo.Step_inner_curve.base` in OCaml.
    pub fn base() -> Fp {
        *<Vesta as KimchiCurve<FULL_ROUNDS>>::other_curve_endo()
    }
}

/// The endo coefficients used by wrap circuits (Tock side).
pub mod tock {
    use super::*;

    /// `Endo.Wrap_inner_curve.base` in OCaml.
    pub fn base() -> Fq {
        *<Pallas as KimchiCurve<FULL_ROUNDS>>::other_curve_endo()
    }
}

/// The scalar endo used by `to_field_checked`-style range asserts in either
/// circuit field (OCaml `Endo.Step_inner_curve.scalar` from a wrap circuit,
/// `Endo.Wrap_inner_curve.scalar` from a step circuit). Only the constraint
/// matters for those callers, but the value is the canonical endo of the
/// field's own proving curve pair.
pub fn endo_r_for_field<F: ark_ff::PrimeField>() -> F {
    use ark_ff::{BigInteger, PrimeField as _};
    if F::MODULUS.to_string() == Fp::MODULUS.to_string() {
        let endo: Fp = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1;
        F::from_le_bytes_mod_order(&endo.into_bigint().to_bytes_le())
    } else {
        assert_eq!(F::MODULUS.to_string(), Fq::MODULUS.to_string());
        let endo: Fq = <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1;
        F::from_le_bytes_mod_order(&endo.into_bigint().to_bytes_le())
    }
}

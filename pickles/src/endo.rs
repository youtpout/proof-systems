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

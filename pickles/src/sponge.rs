//! Field sponges for both sides of the cycle
//! (port of pickles' `tick_field_sponge.ml` / `tock_field_sponge.ml` /
//! `make_sponge.ml`).
//!
//! In-circuit hashing goes through the snarky poseidon gadget
//! ([snarky::gadgets::sponge::DuplexState]); out-of-circuit hashing through
//! [mina_poseidon]. Both use the kimchi parameters, so they agree — this was
//! validated by the snarky sponge parity tests.

use ark_ff::PrimeField;
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    poseidon::{ArithmeticSponge, ArithmeticSpongeParams, Sponge},
};

use crate::common::FULL_ROUNDS;

/// An out-of-circuit field sponge with the kimchi parameters.
pub type FieldSponge<F> = ArithmeticSponge<F, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

/// Creates an out-of-circuit sponge from the given parameters
/// (use `KimchiCurve::sponge_params()` of the side's curve).
pub fn make_sponge<F: PrimeField>(
    params: &'static ArithmeticSpongeParams<F, FULL_ROUNDS>,
) -> FieldSponge<F> {
    FieldSponge::new(params)
}

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

/// The in-circuit Poseidon sponge is snarky's [DuplexState] (fixed to
/// thread the capacity across permutations — it matches
/// [`mina_poseidon::poseidon::ArithmeticSponge`]).
pub use snarky::gadgets::sponge::DuplexState as PoseidonSponge;

/// The kimchi sponge parameters for the circuit field `F` (Fp → Vesta's,
/// Fq → Pallas'), for generic code that needs an out-of-circuit sponge.
pub fn params_for_field<F: PrimeField + 'static>() -> &'static ArithmeticSpongeParams<F, FULL_ROUNDS>
{
    use core::any::TypeId;
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Fq, Pallas, Vesta};
    if TypeId::of::<F>() == TypeId::of::<Fp>() {
        let params: &'static ArithmeticSpongeParams<Fp, FULL_ROUNDS> = Vesta::sponge_params();
        // SAFETY: F == Fp (checked by TypeId), so this is the identity.
        unsafe { core::mem::transmute(params) }
    } else if TypeId::of::<F>() == TypeId::of::<Fq>() {
        let params: &'static ArithmeticSpongeParams<Fq, FULL_ROUNDS> = Pallas::sponge_params();
        // SAFETY: F == Fq (checked by TypeId), so this is the identity.
        unsafe { core::mem::transmute(params) }
    } else {
        panic!("params_for_field: unsupported field");
    }
}

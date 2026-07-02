//! Constants used for poseidon.

use crate::FULL_ROUNDS;
use ark_ff::Field;
use kimchi::curve::KimchiCurve;
use mina_poseidon::poseidon::ArithmeticSpongeParams;

#[derive(Debug, Clone)]
pub struct Constants<F: Field> {
    pub poseidon: ArithmeticSpongeParams<F, FULL_ROUNDS>,
    pub endo: F,
    pub base: (F, F),
}

impl<F> Constants<F>
where
    F: Field,
{
    pub fn new<Curve: KimchiCurve<FULL_ROUNDS, ScalarField = F>>() -> Self {
        let poseidon = Curve::sponge_params().clone();
        let endo_q = Curve::other_curve_endo();
        let base = Curve::other_curve_generator();

        Self {
            poseidon,
            endo: *endo_q,
            base,
        }
    }
}

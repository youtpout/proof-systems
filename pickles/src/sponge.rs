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

//
// In-circuit Poseidon sponge (faithful to mina_poseidon::ArithmeticSponge)
//

use snarky::poseidon::permute;
use snarky::{FieldVar, RunState};
use std::borrow::Cow;

/// The sponge rate (`m - capacity = 3 - 1`).
const RATE: usize = 2;

#[derive(Clone, Copy, Debug)]
enum SpongeMode {
    Absorbed(usize),
    Squeezed(usize),
}

/// An in-circuit Poseidon sponge that maintains the full 3-element state
/// (including the capacity) across permutations — matching
/// [`mina_poseidon::poseidon::ArithmeticSponge`] exactly, unlike snarky's
/// `DuplexState` which resets the capacity on each permutation.
pub struct PoseidonSponge<F: PrimeField> {
    state: [FieldVar<F>; 3],
    mode: SpongeMode,
}

impl<F: PrimeField> Default for PoseidonSponge<F> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F: PrimeField> PoseidonSponge<F> {
    pub fn new() -> Self {
        Self {
            state: [FieldVar::zero(), FieldVar::zero(), FieldVar::zero()],
            mode: SpongeMode::Absorbed(0),
        }
    }

    fn permute_state(&mut self, sys: &mut RunState<F>, loc: Cow<'static, str>) {
        self.state = permute(sys, loc, self.state.clone());
    }

    /// Absorbs field elements (mirrors `ArithmeticSponge::absorb`).
    pub fn absorb(&mut self, sys: &mut RunState<F>, loc: Cow<'static, str>, xs: &[FieldVar<F>]) {
        for x in xs {
            match self.mode {
                SpongeMode::Absorbed(n) => {
                    if n == RATE {
                        self.permute_state(sys, loc.clone());
                        self.state[0] = &self.state[0] + x;
                        self.mode = SpongeMode::Absorbed(1);
                    } else {
                        self.state[n] = &self.state[n] + x;
                        self.mode = SpongeMode::Absorbed(n + 1);
                    }
                }
                SpongeMode::Squeezed(_) => {
                    self.state[0] = &self.state[0] + x;
                    self.mode = SpongeMode::Absorbed(1);
                }
            }
        }
    }

    /// Squeezes a field element (mirrors `ArithmeticSponge::squeeze`).
    pub fn squeeze(&mut self, sys: &mut RunState<F>, loc: Cow<'static, str>) -> FieldVar<F> {
        match self.mode {
            SpongeMode::Squeezed(n) => {
                if n == RATE {
                    self.permute_state(sys, loc);
                    self.mode = SpongeMode::Squeezed(1);
                    self.state[0].clone()
                } else {
                    self.mode = SpongeMode::Squeezed(n + 1);
                    self.state[n].clone()
                }
            }
            SpongeMode::Absorbed(_) => {
                self.permute_state(sys, loc);
                self.mode = SpongeMode::Squeezed(1);
                self.state[0].clone()
            }
        }
    }
}

#[cfg(test)]
mod sponge_tests {
    use super::*;
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::poseidon::ArithmeticSponge;
    #[allow(unused_imports)]
    use snarky::SnarkyResult;
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;
    use snarky::{api::SnarkyCircuit, loc};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    struct SpongeCircuit {
        inputs: Vec<Fp>,
    }
    impl SnarkyCircuit for SpongeCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        // three successive squeezes
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>, FieldVar<Fp>);
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let mut sponge = PoseidonSponge::new();
            let mut vars = vec![];
            for &v in &self.inputs {
                vars.push(sys.compute(loc!(), move |_| v)?);
            }
            sponge.absorb(sys, loc!(), &vars);
            let a = sponge.squeeze(sys, loc!());
            let b = sponge.squeeze(sys, loc!());
            let c = sponge.squeeze(sys, loc!());
            Ok((a, b, c))
        }
    }

    /// Our in-circuit sponge matches mina_poseidon's ArithmeticSponge, across
    /// input lengths and multiple squeezes (exercising cross-permute capacity
    /// carry — where snarky's DuplexState diverges).
    #[test]
    fn poseidon_sponge_matches_arithmetic_sponge() {
        for n_inputs in [1usize, 2, 3, 5, 8] {
            let inputs: Vec<Fp> = (0..n_inputs).map(|i| Fp::from(i as u64 + 1)).collect();
            let mut reference =
                ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>::new(
                    Vesta::sponge_params(),
                );
            reference.absorb(&inputs);
            let expected = (
                reference.squeeze(),
                reference.squeeze(),
                reference.squeeze(),
            );

            let circ = SpongeCircuit {
                inputs: inputs.clone(),
            };
            let (mut pi, ver) = circ.compile_to_indexes().unwrap();
            let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
            assert_eq!(*out, expected, "n_inputs = {n_inputs}");
            ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
        }
    }
}

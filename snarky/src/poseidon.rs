//! Functions associated to the Poseidon hash function.

use crate::{
    constraint_system::KimchiConstraint,
    prelude::{FieldVar, RunState},
    runner::Constraint,
};
use ark_ff::PrimeField;
use itertools::Itertools;
use kimchi::circuits::polynomials::poseidon::{ROUNDS_PER_HASH, ROUNDS_PER_ROW, SPONGE_WIDTH};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi, permutation::full_round,
    poseidon::ArithmeticSpongeParams,
};
use std::borrow::Cow;

use super::constraint_system::PoseidonInput;

pub fn poseidon<F: PrimeField>(
    runner: &mut RunState<F>,
    loc: Cow<'static, str>,
    preimage: (FieldVar<F>, FieldVar<F>),
) -> (FieldVar<F>, FieldVar<F>) {
    let [a, b, _] = permute(runner, loc, [preimage.0, preimage.1, FieldVar::zero()]);
    (a, b)
}

/// Applies the full in-circuit Poseidon permutation to an arbitrary state
/// (the building block of [poseidon] and of pickles' optional sponge).
pub fn permute<F: PrimeField>(
    runner: &mut RunState<F>,
    loc: Cow<'static, str>,
    initial_state: [FieldVar<F>; SPONGE_WIDTH],
) -> [FieldVar<F>; SPONGE_WIDTH] {
    let (constraint, out) = {
        let params = runner.poseidon_params();

        // all the intermediate states: the initial state followed by the
        // result of each of the ROUNDS_PER_HASH rounds
        // (note: don't use `iter::successors` here, it computes one
        // successor past the last item taken, which would apply an
        // out-of-bounds extra round)
        let mut all_states = Vec::with_capacity(ROUNDS_PER_HASH + 1);
        all_states.push(initial_state.clone());
        let mut current = initial_state;
        for i in 0..ROUNDS_PER_HASH {
            current = round(runner, loc.clone(), &current, i, &params);
            all_states.push(current.clone());
        }

        let mut iter = all_states.into_iter();

        let states: Vec<_> = iter
            .by_ref()
            .take(ROUNDS_PER_HASH)
            .chunks(ROUNDS_PER_ROW)
            .into_iter()
            .flat_map(|mut it| {
                let mut n = || it.next().unwrap();
                let (r0, r1, r2, r3, r4) = (n(), n(), n(), n(), n());
                [r0, r4, r1, r2, r3].into_iter()
            })
            .collect_vec();
        let last = iter.next().unwrap();
        let out = last.clone();
        let constraint = Constraint::KimchiConstraint(KimchiConstraint::Poseidon2(PoseidonInput {
            states: states.into_iter().map(|s| s.to_vec()).collect(),
            last: last.to_vec(),
        }));
        (constraint, out)
    };

    runner
        .add_constraint(constraint, Some("Poseidon".into()), loc)
        .expect("compiler bug");

    out
}

fn round<F: PrimeField>(
    runner: &mut RunState<F>,
    loc: Cow<'static, str>,
    elements: &[FieldVar<F>; SPONGE_WIDTH],
    round: usize,
    params: &ArithmeticSpongeParams<F, { crate::FULL_ROUNDS }>,
) -> [FieldVar<F>; SPONGE_WIDTH] {
    runner
        .compute(loc, |env| {
            let mut state = elements.clone().map(|var| env.read_var(&var)).to_vec();
            full_round::<F, PlonkSpongeConstantsKimchi, { crate::FULL_ROUNDS }>(
                params, &mut state, round,
            );
            state.try_into().unwrap()
        })
        .expect("compiler bug")
}

//
// Duplex API
//

/// The sponge rate (`m - capacity = 3 - 1`).
const RATE_SIZE: usize = 2;

#[derive(Clone, Copy, Debug)]
enum SpongeMode {
    Absorbed(usize),
    Squeezed(usize),
}

/// An in-circuit Poseidon sponge (duplex construction: absorb and squeeze
/// alternately). It maintains the full 3-element state — including the
/// capacity — across permutations, mirroring
/// [`mina_poseidon::poseidon::ArithmeticSponge`] exactly.
pub struct DuplexState<F>
where
    F: PrimeField,
{
    state: [FieldVar<F>; 3],
    mode: SpongeMode,
}

impl<F> Default for DuplexState<F>
where
    F: PrimeField,
{
    fn default() -> Self {
        let zero = FieldVar::zero();
        DuplexState {
            state: [zero.clone(), zero.clone(), zero],
            mode: SpongeMode::Absorbed(0),
        }
    }
}

impl<F> DuplexState<F>
where
    F: PrimeField,
{
    /// Creates a new sponge.
    pub fn new() -> DuplexState<F> {
        Default::default()
    }

    fn permute_state(&mut self, sys: &mut RunState<F>, loc: Cow<'static, str>) {
        self.state = permute(sys, loc, self.state.clone());
    }

    /// Absorbs field elements (mirrors `ArithmeticSponge::absorb`).
    pub fn absorb(
        &mut self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        inputs: &[FieldVar<F>],
    ) {
        for x in inputs {
            match self.mode {
                SpongeMode::Absorbed(n) => {
                    if n == RATE_SIZE {
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
                if n == RATE_SIZE {
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

// TODO: create a macro to derive this function automatically
pub trait CircuitAbsorb<F>
where
    F: PrimeField,
{
    fn absorb(&self, duplex: &mut DuplexState<F>, sys: &mut RunState<F>);
}

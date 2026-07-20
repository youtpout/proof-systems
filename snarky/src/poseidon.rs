//! Functions associated to the Poseidon hash function.

use crate::{
    constraint_system::KimchiConstraint,
    prelude::{FieldVar, RunState},
    runner::Constraint,
    Boolean, SnarkyResult,
};
use ark_ff::PrimeField;
use itertools::Itertools;
use kimchi::circuits::polynomials::poseidon::{ROUNDS_PER_HASH, ROUNDS_PER_ROW, SPONGE_WIDTH};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    permutation::full_round,
    poseidon::{ArithmeticSpongeParams, SpongeState as SpongeMode},
    sponge_machine::SpongeMachine,
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

/// An in-circuit Poseidon sponge (duplex construction: absorb and squeeze
/// alternately). It runs the shared [`SpongeMachine`] protocol over circuit
/// variables, so it matches `mina_poseidon::poseidon::ArithmeticSponge`
/// exactly (same absorb/squeeze state machine, capacity threaded across
/// permutations).
#[derive(Clone)]
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

    /// Resumes a sponge from a state computed *out of circuit* over a
    /// constant prefix (OCaml's `Wrap_hack` caches the sponge state after
    /// absorbing constant dummy challenge vectors, so only the variable
    /// suffix costs Poseidon rows). `absorbed` is the pending absorb count
    /// of the resumed mode, exactly as `ArithmeticSponge.sponge_state`.
    pub fn from_constant_state(state: [F; 3], absorbed: usize) -> DuplexState<F> {
        DuplexState {
            state: [
                FieldVar::constant(state[0]),
                FieldVar::constant(state[1]),
                FieldVar::constant(state[2]),
            ],
            mode: SpongeMode::Absorbed(absorbed),
        }
    }

    /// Resumes a sponge from an in-circuit state in `Squeezed(n)` mode — the
    /// opt-sponge -> plain-sponge conversion of pickles' wrap verifier
    /// (`wrap_verifier.ml:1294-1304`, IVC Step 13): the raw state array is
    /// carried over and squeezing continues from position `n`.
    pub fn from_var_state_squeezed(state: [FieldVar<F>; 3], squeezed: usize) -> DuplexState<F> {
        DuplexState {
            state,
            mode: SpongeMode::Squeezed(squeezed),
        }
    }

    /// Consumes a sponge that is currently absorbing and exposes its state
    /// plus the pending rate position. This is the faithful transition used
    /// by Pickles' `hash_messages_for_next_step_proof_opt`: a plain sponge
    /// absorbs the verification key and application state, then an
    /// `Opt_sponge` continues from exactly that state for branch-masked
    /// accumulator inputs.
    pub fn into_var_state_absorbed(self) -> ([FieldVar<F>; 3], usize) {
        match self.mode {
            SpongeMode::Absorbed(position) => (self.state, position),
            SpongeMode::Squeezed(_) => {
                panic!("DuplexState::into_var_state_absorbed: sponge is squeezed")
            }
        }
    }

    /// The in-circuit permutation, as the [`SpongeMachine`] permute closure.
    fn permute_closure<'a>(
        sys: &'a mut RunState<F>,
        loc: Cow<'static, str>,
    ) -> impl FnMut(&mut Vec<FieldVar<F>>) + 'a {
        move |state: &mut Vec<FieldVar<F>>| {
            let arr: [FieldVar<F>; 3] = core::array::from_fn(|i| state[i].clone());
            *state = permute(sys, loc.clone(), arr).to_vec();
        }
    }

    fn take_machine(&mut self) -> SpongeMachine<FieldVar<F>> {
        SpongeMachine {
            state: self.state.to_vec(),
            rate: RATE_SIZE,
            mode: self.mode.clone(),
        }
    }

    fn restore(&mut self, machine: SpongeMachine<FieldVar<F>>) {
        self.state = core::array::from_fn(|i| machine.state[i].clone());
        self.mode = machine.mode;
    }

    /// Absorbs field elements (the `ArithmeticSponge` state machine, but with
    /// OCaml pickles' sealing add: `add_assign ~state i x = state.(i) <-
    /// Utils.seal (state.(i) + x)` — sponge_inputs.ml:53). Sealing at absorb
    /// keeps every state slot a plain var, so a later permute emits NO
    /// reduction gates. Accumulating lincoms and reducing at permute time
    /// coincides with the sealed schedule only when the absorbs are adjacent
    /// to the permute; it diverges when other gadgets run in between
    /// (measured: the `sponge_after_index` squeeze in `verify_one`).
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
                        let arr: [FieldVar<F>; 3] =
                            core::array::from_fn(|i| self.state[i].clone());
                        self.state = permute(sys, loc.clone(), arr);
                        self.state[0] = (&self.state[0] + x)
                            .seal(sys, loc.clone())
                            .expect("sponge absorb seal");
                        self.mode = SpongeMode::Absorbed(1);
                    } else {
                        self.state[n] = (&self.state[n] + x)
                            .seal(sys, loc.clone())
                            .expect("sponge absorb seal");
                        self.mode = SpongeMode::Absorbed(n + 1);
                    }
                }
                SpongeMode::Squeezed(_) => {
                    self.state[0] = (&self.state[0] + x)
                        .seal(sys, loc.clone())
                        .expect("sponge absorb seal");
                    self.mode = SpongeMode::Absorbed(1);
                }
            }
        }
    }

    /// Squeezes a field element.
    pub fn squeeze(&mut self, sys: &mut RunState<F>, loc: Cow<'static, str>) -> FieldVar<F> {
        let mut machine = self.take_machine();
        let out = machine.squeeze(Self::permute_closure(sys, loc));
        self.restore(machine);
        out
    }

    /// Conditionally absorbs `inputs` (OCaml pickles'
    /// `simulate_optional_sponge_with_alignment`, wrap_verifier.ml:791): the
    /// absorb ALWAYS runs (its gates are emitted regardless), but the resulting
    /// state is kept only when `flag` is true, otherwise reverted to the state
    /// before. Requires the absorb to leave the rate position unchanged (the
    /// caller absorbs a full commitment = rate elements), so only the `state`
    /// array is conditionally selected, not the mode.
    pub fn absorb_maybe(
        &mut self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        flag: &Boolean<F>,
        inputs: &[FieldVar<F>],
    ) -> SnarkyResult<()> {
        let before = self.state.clone();
        self.absorb(sys, loc.clone(), inputs);
        for (slot, was) in self.state.iter_mut().zip(before) {
            *slot = sys.if_(loc.clone(), flag.clone(), slot.clone(), was)?;
        }
        Ok(())
    }
}

// TODO: create a macro to derive this function automatically
pub trait CircuitAbsorb<F>
where
    F: PrimeField,
{
    fn absorb(&self, duplex: &mut DuplexState<F>, sys: &mut RunState<F>);
}

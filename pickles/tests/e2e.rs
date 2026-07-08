//! End-to-end base-case pickles pipeline (proofs_verified = 0), through the
//! [`pickles::api`] surface: the application circuit below is wrapped into a
//! step proof on Vesta, whose full transcript is re-verified — bulletproof
//! equation included — inside the wrap circuit proved on Pallas. The returned
//! wrap proof *is* the base-case pickles proof.

use mina_curves::pasta::Fp;
use pickles::api::{prove_base_case, StepApp};
use snarky::{loc, FieldVar, RunState, SnarkyResult};

/// `z = x²`, with `z` as the application state.
struct SquareApp;

impl StepApp for SquareApp {
    type Witness = Fp;

    fn main(
        &self,
        sys: &mut RunState<Fp>,
        witness: Option<&Self::Witness>,
    ) -> SnarkyResult<Vec<FieldVar<Fp>>> {
        let x: FieldVar<Fp> = sys.compute(loc!(), |_| *witness.unwrap())?;
        let z = x.mul(&x, None, loc!(), sys)?;
        Ok(vec![z])
    }

    fn state(&self, witness: &Self::Witness) -> Vec<Fp> {
        vec![*witness * *witness]
    }
}

/// The step circuit compiles to a 2^9 domain (9 IPA rounds); real pickles
/// pads its domains so this is TICK_ROUNDS = 16 there.
const ROUNDS: usize = 9;
const STMT_LEN: usize = 13 + ROUNDS + 9;

#[test]
fn pickles_base_case_end_to_end() {
    // base case: the wrap VK is pinned by the *next* step proof, not this
    // one; fixed placeholder points keep the accumulator self-consistent.
    let wrap_vk_pts: Vec<(Fp, Fp)> = (0..28u64)
        .map(|i| (Fp::from(1000 + i), Fp::from(2000 + i)))
        .collect();

    let proof =
        prove_base_case::<SquareApp, ROUNDS, STMT_LEN>(SquareApp, Fp::from(7u64), wrap_vk_pts);
    // prove_base_case verifies the wrap proof internally; sanity on the shape
    assert_eq!(proof.statement.len(), STMT_LEN);
}

//! The first recursive step (proofs_verified = 1): a second step circuit runs
//! [`pickles::step_main::step_main`] over the base-case wrap proof —
//! finalizing the wrap statement's deferred values (the base step proof's
//! scalars) against that proof's evaluations, re-deriving the wrap proof's
//! whole transcript, recommitting the wrap statement through the real Pallas
//! Lagrange basis, and asserting the bulletproof equation — with
//! `must_verify = true`, so every check is real.

use kimchi::curve::KimchiCurve;
use mina_curves::pasta::Fp;
use snarky::{loc, FieldVar, RunState, SnarkyResult};

use pickles::api::{prove_base_case, StepApp};
use pickles::recursive_step::{
    prepare_next_recursive_step, prepare_recursive_step, prepare_recursive_step_width2,
    prove_first_recursive_cycle, prove_next_recursive_cycle, prove_recursive_step_width2,
    prove_stable_recursive_cycles, step_statement_len, width1_step_statement_len,
    wrap_unfinalized_from_base, wrap_unfinalized_from_recursive_cycle,
};

/// step proof #1's IPA rounds / wrap statement length (see tests/e2e.rs).
const ROUNDS: usize = 9;
const STMT_LEN: usize = 13 + ROUNDS + 9;
/// the wrap circuit's IPA rounds (its domain is 2^13 — matching pickles'
/// `wrap_domains(0)`).
const WROUNDS: usize = 13;
const R2: usize = 14;
/// the width-1 step statement: 5 Type2 pairs (cip, b, zsl, zds, perm of the
/// wrap proof), the wrap proof's sponge digest, beta/gamma, alpha/zeta/xi,
/// WROUNDS bulletproof challenges, should_finalize, then the new
/// messages_for_next_step digest and the messages_for_next_wrap digest.
const K2: usize = width1_step_statement_len(WROUNDS);
const WRAP2_STMT_LEN: usize = 13 + R2 + 9;
const WRAP2_PROOF_ROUNDS: usize = 14;
const K3: usize = width1_step_statement_len(WRAP2_PROOF_ROUNDS);
const R3: usize = 14;
const WRAP3_STMT_LEN: usize = 13 + R3 + 9;
const WRAP3_PROOF_ROUNDS: usize = 14;
const K4: usize = width1_step_statement_len(WRAP3_PROOF_ROUNDS);
const R4: usize = 14;
const WRAP4_STMT_LEN: usize = 13 + R4 + 9;
const K_WIDTH2: usize = step_statement_len(2, WROUNDS);

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

#[test]
fn pickles_recursive_step() {
    let wrap_vk_pts: Vec<(Fp, Fp)> = (0..28u64)
        .map(|i| (Fp::from(1000 + i), Fp::from(2000 + i)))
        .collect();
    let base = prove_base_case::<SquareApp, ROUNDS, STMT_LEN>(
        SquareApp,
        Fp::from(7u64),
        wrap_vk_pts.clone(),
    );
    let unfinalized = wrap_unfinalized_from_base(&base);
    let prev_wrap_digest = pickles::hash_messages::hash_messages_for_next_wrap_proof_ref(
        mina_curves::pasta::Pallas::sponge_params(),
        &unfinalized.hash_dummy_challenges,
        &unfinalized.old_bulletproof_challenges,
        unfinalized.prev_step_acc,
    );
    assert_eq!(prev_wrap_digest, base.statement[11]);

    let prev_app_state = vec![Fp::from(49u64)];

    let cycle = prove_first_recursive_cycle::<
        SquareApp,
        ROUNDS,
        WROUNDS,
        R2,
        STMT_LEN,
        K2,
        WRAP2_STMT_LEN,
    >(&base, wrap_vk_pts.clone(), prev_app_state);
    assert_eq!(cycle.step.statement.len(), K2);
    assert_eq!(cycle.wrap.statement.len(), WRAP2_STMT_LEN);
    assert_eq!(cycle.wrap.proof.proof.lr.len(), R2);

    let prepared3 = prepare_next_recursive_step::<
        ROUNDS,
        WROUNDS,
        R2,
        K2,
        WRAP2_STMT_LEN,
        WRAP2_PROOF_ROUNDS,
        K3,
    >(&cycle, wrap_vk_pts.clone(), vec![Fp::from(49u64)]);
    assert_eq!(prepared3.statement.len(), K3);
    assert_eq!(
        prepared3.data.messages_for_next_step_accumulators,
        vec![cycle.step.verified_wrap_accumulator]
    );
    assert!(prepared3
        .data
        .prev_challenge_polynomial_commitments
        .is_empty());
    assert_eq!(
        prepared3.data.prev_challenges,
        vec![cycle.step.finalized_step_challenges.clone()]
    );

    let cycle2 = prove_next_recursive_cycle::<
        ROUNDS,
        WROUNDS,
        R2,
        K2,
        WRAP2_STMT_LEN,
        WRAP2_PROOF_ROUNDS,
        K3,
        R3,
        WRAP3_STMT_LEN,
    >(&cycle, wrap_vk_pts.clone(), vec![Fp::from(49u64)]);

    let unfinalized2 = wrap_unfinalized_from_recursive_cycle(&cycle);
    let wrap2_digest = pickles::hash_messages::hash_messages_for_next_wrap_proof_ref(
        mina_curves::pasta::Pallas::sponge_params(),
        &unfinalized2.hash_dummy_challenges,
        &unfinalized2.hash_old_bulletproof_challenges,
        unfinalized2.prev_step_acc,
    );
    assert_eq!(wrap2_digest, cycle.wrap.statement[11]);

    assert_eq!(cycle2.step.statement.len(), K3);
    assert_eq!(cycle2.wrap.statement.len(), WRAP3_STMT_LEN);

    let cycle3 = prove_stable_recursive_cycles::<R3, K3, WRAP3_STMT_LEN>(
        cycle2,
        1,
        wrap_vk_pts,
        vec![Fp::from(49u64)],
    );
    assert_eq!(cycle3.step.statement.len(), K4);
    assert_eq!(cycle3.wrap.statement.len(), WRAP4_STMT_LEN);
}

#[test]
fn pickles_recursive_step_width2() {
    let wrap_vk_pts: Vec<(Fp, Fp)> = (0..28u64)
        .map(|i| (Fp::from(3000 + i), Fp::from(4000 + i)))
        .collect();
    let base = prove_base_case::<SquareApp, ROUNDS, STMT_LEN>(
        SquareApp,
        Fp::from(11u64),
        wrap_vk_pts.clone(),
    );
    let app_state = vec![Fp::from(121u64)];
    let first = prepare_recursive_step::<SquareApp, ROUNDS, WROUNDS, STMT_LEN, K2>(
        &base,
        wrap_vk_pts.clone(),
        app_state.clone(),
    );
    let second = prepare_recursive_step::<SquareApp, ROUNDS, WROUNDS, STMT_LEN, K2>(
        &base,
        wrap_vk_pts,
        app_state,
    );
    let prepared = prepare_recursive_step_width2::<WROUNDS, K2, K_WIDTH2>(first, second);
    assert_eq!(prepared.statement.len(), K_WIDTH2);
    let proof = prove_recursive_step_width2::<ROUNDS, WROUNDS, K2, K_WIDTH2>(prepared);
    assert_eq!(proof.statement.len(), K_WIDTH2);
    assert_eq!(proof.proof.prev_challenges.len(), 2);
}

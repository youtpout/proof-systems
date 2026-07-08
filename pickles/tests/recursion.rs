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
    prepare_recursive_wrap, prove_recursive_step, width1_step_statement_len,
    wrap_unfinalized_from_base,
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

    let proof2 = prove_recursive_step::<SquareApp, ROUNDS, WROUNDS, STMT_LEN, K2>(
        &base,
        wrap_vk_pts,
        prev_app_state,
    );
    assert_eq!(proof2.statement.len(), K2);

    let prepared_wrap =
        prepare_recursive_wrap::<SquareApp, ROUNDS, WROUNDS, R2, STMT_LEN, K2, WRAP2_STMT_LEN>(
            &base, &proof2,
        );
    assert_eq!(prepared_wrap.statement.len(), WRAP2_STMT_LEN);
    assert_eq!(prepared_wrap.data.unfinalized.len(), 1);
    assert_eq!(prepared_wrap.data.step_statement.len(), K2);
}

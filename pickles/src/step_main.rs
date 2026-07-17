//! The step circuit body (`step_main.ml`, verification half): loops
//! [`verify_one`] over the previous proofs, asserts they all verified, and
//! hashes the new `messages_for_next_step_proof` accumulator.
//!
//! ```text
//! for each previous proof i:
//!     (chals_i, ok_i) = verify_one(...)
//! Boolean.Assert.all [ok_i]
//! msgs_next_step = hash_messages_for_next_step_proof(
//!     app_state, dlog_plonk_index,
//!     [openings_i.challenge_polynomial_commitment],   // new accumulators
//!     [chals_i])                                      // new challenges
//! ```
//!
//! The application logic (`rule.main`) runs before this in the caller's
//! circuit; the unfinalized proofs and `messages_for_next_wrap_proof` digests
//! are witnessed pass-throughs that the caller packs into the step statement
//! ([`crate::composition_types::step`]). Base subset: fixed width, no dummy
//! padding (`proofs_verified == max_proofs_verified`).

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{gadgets::curve::Point, Boolean, FieldVar, RunState, SnarkyResult};

use crate::{
    composition_types::PlonkVerificationKeyEvals,
    finalize::FinalizeParams,
    incrementally_verify::{Advice, Messages, OpeningProof, VerificationKeyComm},
    step_verifier::{verify_one, Claimed, FinalizeEvals, WrapStatementVars},
};

/// Everything [`verify_one`] needs for one previous proof (the in-circuit
/// slice of `Per_proof_witness.t` + `Types_map.For_step.t` + `Unfinalized.t`).
pub struct PerProofInput<'a, F: PrimeField> {
    // finalize the previous step proof's deferred values
    pub finalize_params: FinalizeParams<'a, F>,
    pub finalize_evals: FinalizeEvals<F>,
    /// The wrap proof's statement (its `messages_for_next_step_proof` digest
    /// is recomputed in-circuit from the four fields below).
    pub stmt: WrapStatementVars<F>,
    // the wrap VK the previous accumulator digest absorbs; the index sponge
    // itself is (re)emitted inside `verify_one`, after finalize — OCaml's
    // per-proof `hash_messages_for_next_step_proof_opt` (step_main.ml:45).
    pub dlog_index: PlonkVerificationKeyEvals<Point<F>>,
    /// Transitional cycles whose statement was produced with a different VK
    /// recompute the verifier digest; stabilized cycles share this sponge.
    pub share_index_sponge: bool,
    pub prev_app_state: Vec<FieldVar<F>>,
    /// Accumulators committed by `messages_for_next_step_proof`.
    pub messages_for_next_step_accumulators: Vec<Point<F>>,
    /// Commitments folded into the wrap proof's IPA equation.
    pub prev_challenge_polynomial_commitments: Vec<Point<F>>,
    pub prev_challenges: Vec<Vec<FieldVar<F>>>,
    /// Kimchi-level previous challenges of the finalized step proof (padded
    /// to width 2 by Mina) — used by the Fr-sponge replay, not the digest.
    pub finalize_prev_challenges: Vec<Vec<FieldVar<F>>>,
    /// Dynamic mask derived from the wrapped proof's branch data. Present for
    /// a fixed-width multibranch program, absent on legacy fixed-arity paths.
    pub proofs_verified_mask: Option<Vec<Boolean<F>>>,
    // the wrap proof itself
    pub vk: VerificationKeyComm<F>,
    pub packed_lagranges: Vec<(Point<F>, Point<F>)>,
    pub flag_lagranges: Vec<Point<F>>,
    pub h_generator: Point<F>,
    pub messages: Messages<F>,
    pub openings: OpeningProof<F>,
    /// Accumulator committed by the next-step message. This is normally the
    /// opening proof's challenge-polynomial commitment, but a skipped padded
    /// slot uses Pickles' canonical dummy commitment instead.
    pub next_step_accumulator: Point<F>,
    /// Challenges committed by `next_step_accumulator`. A skipped padded slot
    /// uses the canonical dummy challenge vector.
    pub next_step_challenges: Option<Vec<FieldVar<F>>>,
    // the wrap proof's deferred values (from the step statement's Unfinalized)
    pub advice: Advice<F>,
    pub xi: FieldVar<F>,
    pub claimed: Claimed<F>,
    // control
    pub should_finalize: Boolean<F>,
    pub must_verify: Boolean<F>,
    pub is_base_case: Boolean<F>,
}

/// Runs the verification half of a step circuit and returns the new
/// `messages_for_next_step_proof` digest.
#[allow(clippy::too_many_arguments)]
pub fn step_main<F, C>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    app_state: &[FieldVar<F>],
    dlog_plonk_index: &PlonkVerificationKeyEvals<Point<F>>,
    proofs: &[PerProofInput<'_, F>],
    group_map_params: &groupmap::BWParameters<C>,
    endo_base: F,
    endo_scalar: <ark_ec::short_weierstrass::Affine<C> as ark_ec::AffineRepr>::ScalarField,
    num_bits: usize,
) -> SnarkyResult<FieldVar<F>>
where
    F: PrimeField,
    C: ark_ec::short_weierstrass::SWCurveConfig<BaseField = F>,
{
    use crate::hash_messages::{hash_messages_for_next_step_proof, sponge_after_index};

    // verify every previous proof
    let mut chalss: Vec<Vec<FieldVar<F>>> = Vec::with_capacity(proofs.len());
    let mut oks: Vec<Boolean<F>> = Vec::with_capacity(proofs.len());
    for p in proofs {
        let (chals, verified, finalized) = verify_one::<F, C>(
            sys,
            loc.clone(),
            &p.finalize_params,
            &p.finalize_evals,
            &p.stmt,
            &p.dlog_index,
            p.share_index_sponge,
            &p.prev_app_state,
            &p.messages_for_next_step_accumulators,
            &p.prev_challenge_polynomial_commitments,
            &p.prev_challenges,
            &p.finalize_prev_challenges,
            p.proofs_verified_mask.as_deref(),
            &p.vk,
            &p.packed_lagranges,
            &p.flag_lagranges,
            &p.h_generator,
            &p.messages,
            &p.openings,
            &p.advice,
            &p.xi,
            &p.claimed,
            &p.should_finalize,
            &p.must_verify,
            &p.is_base_case,
            group_map_params,
            endo_base,
            endo_scalar,
            num_bits,
        )?;
        // OCaml `step_main.ml:117`: the per-proof result is the single
        // expression `Boolean.(verified &&& finalized ||| not must_verify)`
        // — one `and` then one `or`, and NO per-proof assertion (the
        // conjunction is asserted once at the end).
        let verified_and_finalized =
            verified.and(&finalized, sys, Cow::Borrowed("wrap proof verified"));
        let ok = verified_and_finalized.or(
            &p.must_verify.not(),
            Cow::Borrowed("step proof finalized"),
            sys,
        );
        chalss.push(p.next_step_challenges.clone().unwrap_or(chals));
        oks.push(ok);
    }

    // `Boolean.Assert.all vs` (utils.ml): asserts the SUM of the booleans
    // equals their count — not a computed `Boolean.all` followed by an
    // is-true assertion.
    if !oks.is_empty() {
        let ok_vars: Vec<FieldVar<F>> = oks.iter().map(|b| b.to_field_var()).collect();
        let sum = FieldVar::sum(&ok_vars.iter().collect::<Vec<_>>());
        sum.assert_equals(
            sys,
            loc.clone(),
            &FieldVar::constant(F::from(oks.len() as u64)),
        )?;
    }

    // the new accumulator digest: this proof's app state, the verified proofs'
    // challenge-polynomial commitments, and the freshly-derived challenges
    let after_index = sponge_after_index(sys, loc.clone(), dlog_plonk_index);
    let cpcs: Vec<Point<F>> = proofs
        .iter()
        .map(|p| p.next_step_accumulator.clone())
        .collect();
    // OCaml `step_main` (step_main.ml:549) computes the NEW accumulator
    // digest with the PLAIN `hash_messages_for_next_step_proof` —
    // unconditional absorbs, no `Opt_sponge`. The `_opt` variant is only
    // used for the OLD digests inside `Step_verifier.verify`. The prover
    // computes the same digest out of circuit with the same unconditional
    // absorbs (`hash_messages_for_next_step_proof_ref`), dummy accumulators
    // included, so masking here would diverge from both.
    hash_messages_for_next_step_proof(sys, loc, &after_index, app_state, &cpcs, &chalss)
}

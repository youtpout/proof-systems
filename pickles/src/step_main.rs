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

use crate::composition_types::PlonkVerificationKeyEvals;
use crate::finalize::FinalizeParams;
use crate::incrementally_verify::{Advice, Messages, OpeningProof, VerificationKeyComm};
use crate::step_verifier::{verify_one, Claimed, FinalizeEvals, WrapStatementVars};

/// Everything [`verify_one`] needs for one previous proof (the in-circuit
/// slice of `Per_proof_witness.t` + `Types_map.For_step.t` + `Unfinalized.t`).
pub struct PerProofInput<'a, F: PrimeField> {
    // finalize the previous step proof's deferred values
    pub finalize_params: FinalizeParams<'a, F>,
    pub finalize_evals: FinalizeEvals<F>,
    /// The wrap proof's statement (its `messages_for_next_step_proof` digest
    /// is recomputed in-circuit from the four fields below).
    pub stmt: WrapStatementVars<F>,
    // the previous accumulator hashed into the wrap statement
    pub sponge_after_index: crate::sponge::PoseidonSponge<F>,
    pub prev_app_state: Vec<FieldVar<F>>,
    pub prev_challenge_polynomial_commitments: Vec<Point<F>>,
    pub prev_challenges: Vec<Vec<FieldVar<F>>>,
    // the wrap proof itself
    pub vk_digest: FieldVar<F>,
    pub vk: VerificationKeyComm<F>,
    pub packed_lagranges: Vec<(Point<F>, Point<F>)>,
    pub flag_lagranges: Vec<Point<F>>,
    pub h_generator: Point<F>,
    pub messages: Messages<F>,
    pub openings: OpeningProof<F>,
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
        let (chals, ok) = verify_one::<F, C>(
            sys,
            loc.clone(),
            &p.finalize_params,
            &p.finalize_evals,
            &p.stmt,
            &p.sponge_after_index,
            &p.prev_app_state,
            &p.prev_challenge_polynomial_commitments,
            &p.prev_challenges,
            &p.vk_digest,
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
        chalss.push(chals);
        oks.push(ok);
    }

    // Boolean.Assert.all vs
    if !oks.is_empty() {
        let all = Boolean::all(&oks, sys, loc.clone())?;
        all.to_field_var()
            .assert_equals(sys, loc.clone(), &FieldVar::constant(F::one()))?;
    }

    // the new accumulator digest: this proof's app state, the verified proofs'
    // challenge-polynomial commitments, and the freshly-derived challenges
    let after_index = sponge_after_index(sys, loc.clone(), dlog_plonk_index);
    let cpcs: Vec<Point<F>> = proofs
        .iter()
        .map(|p| p.openings.challenge_polynomial_commitment.clone())
        .collect();
    hash_messages_for_next_step_proof(sys, loc, &after_index, app_state, &cpcs, &chalss)
}

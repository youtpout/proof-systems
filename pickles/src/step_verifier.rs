//! Assembly of `Step_verifier.verify` (`step_verifier.ml`, lines ~1244–1317):
//! full verification of one wrap proof inside a step circuit.
//!
//! ```text
//! result  = incrementally_verify_proof(...)                  // x_hat + oracles + IPA
//! assert  result.sponge_digest == unfinalized.sponge_digest  // step 4a
//! assert  result.bulletproof_challenges == claimed           // step 4b
//!         (base case: bypassed — claimed compared to itself)
//! assert  result.oracles == statement plonk challenges       // assert_eq_plonk
//! return  result.success
//! ```
//!
//! The wrap statement arrives already packed as public-input [`Term`]s (the
//! caller flattens it in the `Wrap.Statement.to_data` order with the right bit
//! widths and attaches the Lagrange constants); the claimed plonk challenges
//! are the *raw* 128-bit scalar challenges from the statement.

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{gadgets::curve::Point, Boolean, FieldVar, RunState, SnarkyResult};

use crate::{
    incrementally_verify::{
        incrementally_verify_proof, Advice, IncrementalResult, IndexDigest, Messages, OpeningProof,
        VerificationKeyComm, XHatInput,
    },
    public_input::Term,
};

/// The claimed values `verify` checks the re-derived transcript against: the
/// statement's raw 128-bit plonk challenges, the sponge digest, and the
/// bulletproof prechallenges of the unfinalized proof.
pub struct Claimed<F: PrimeField> {
    pub beta: FieldVar<F>,
    pub gamma: FieldVar<F>,
    pub alpha: FieldVar<F>,
    pub zeta: FieldVar<F>,
    pub sponge_digest_before_evaluations: FieldVar<F>,
    pub bulletproof_challenges: Vec<FieldVar<F>>,
}

/// Full verification of one wrap proof (`Step_verifier.verify`). Returns the
/// bulletproof success boolean; everything else is asserted.
///
/// `is_base_case` bypasses the bulletproof-challenge comparison (a base-case
/// proof carries dummy challenges with no transcript to match). The digest and
/// plonk-challenge asserts are unconditional, as in OCaml.
#[allow(clippy::too_many_arguments)]
pub fn verify<F, C>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    index_digest: IndexDigest<'_, F>,
    // Wrap side: opt-sponge transcript (wrap_main.ml:479); step side: plain.
    use_opt_sponge: bool,
    vk: &VerificationKeyComm<F>,
    sg_old: &[Point<F>],
    sg_old_mask: &[Boolean<F>],
    x_hat_input: XHatInput<'_, F>,
    messages: &Messages<F>,
    openings: &OpeningProof<F>,
    advice: &Advice<F>,
    xi: &FieldVar<F>,
    claimed: &Claimed<F>,
    // Step side mirrors step_verifier.ml:1312 (base-case bypass through
    // `Field.if_`); the wrap side passes `None`: wrap_main.ml:515 asserts the
    // claimed statement challenges against the derived ones UNCONDITIONALLY,
    // so the copy constraint unions the public-input cells with the derived
    // challenge cells (required for wiring/VK parity).
    base_case_challenge_bypass: Option<&Boolean<F>>,
    group_map_params: &groupmap::BWParameters<C>,
    endo_base: F,
    endo_scalar: <ark_ec::short_weierstrass::Affine<C> as ark_ec::AffineRepr>::ScalarField,
    num_bits: usize,
) -> SnarkyResult<Boolean<F>>
where
    F: PrimeField,
    C: ark_ec::short_weierstrass::SWCurveConfig<BaseField = F>,
{
    // == oracles + IPA ==
    let IncrementalResult {
        success,
        oracles,
        sponge_digest,
        bulletproof_challenges,
    } = incrementally_verify_proof::<F, C>(
        sys,
        loc.clone(),
        index_digest,
        use_opt_sponge,
        vk,
        sg_old,
        sg_old_mask,
        x_hat_input,
        messages,
        openings,
        advice,
        xi,
        group_map_params,
        endo_base,
        endo_scalar,
        num_bits,
    )?;

    // == step 4a: the sponge digest must match the claimed one ==
    sponge_digest.assert_equals(
        sys,
        Cow::Borrowed("verify: sponge digest"),
        &claimed.sponge_digest_before_evaluations,
    )?;

    // == step 4b: bulletproof challenges must match (base case bypassed) ==
    assert_eq!(
        claimed.bulletproof_challenges.len(),
        bulletproof_challenges.len(),
        "verify: claimed/actual bulletproof challenge count"
    );
    for (c1, c2) in claimed
        .bulletproof_challenges
        .iter()
        .zip(&bulletproof_challenges)
    {
        match base_case_challenge_bypass {
            // step: in the base case compare c1 with itself, else with c2
            Some(is_base_case) => {
                let rhs = sys.if_(loc.clone(), is_base_case.clone(), c1.clone(), c2.clone())?;
                c1.assert_equals(sys, Cow::Borrowed("verify: bulletproof challenge"), &rhs)?;
            }
            // wrap: unconditional (wrap_main.ml:515) — unions the statement
            // cells with the derived challenge cells
            None => {
                c1.assert_equals(sys, Cow::Borrowed("verify: bulletproof challenge"), c2)?;
            }
        }
    }

    // == assert_eq_plonk: sampled raw challenges == statement's ==
    oracles
        .beta
        .assert_equals(sys, Cow::Borrowed("verify: beta"), &claimed.beta)?;
    oracles
        .gamma
        .assert_equals(sys, Cow::Borrowed("verify: gamma"), &claimed.gamma)?;
    oracles
        .alpha
        .assert_equals(sys, Cow::Borrowed("verify: alpha"), &claimed.alpha)?;
    oracles
        .zeta
        .assert_equals(sys, Cow::Borrowed("verify: zeta"), &claimed.zeta)?;

    Ok(success)
}

/// The wrap statement as circuit variables (base subset), in the
/// `Wrap.Statement.to_data` element order minus the in-circuit
/// `messages_for_next_step_proof` digest (computed by [`verify_one`]).
/// Challenges are raw 128-bit; the `fp` scalars are `Shifted_value.Type1`
/// representatives.
pub struct WrapStatementVars<F: PrimeField> {
    // fp (Type1 representatives, 255-bit)
    pub combined_inner_product: FieldVar<F>,
    pub b: FieldVar<F>,
    pub zeta_to_srs_length: FieldVar<F>,
    pub zeta_to_domain_size: FieldVar<F>,
    pub perm: FieldVar<F>,
    // challenges (raw 128-bit)
    pub beta: FieldVar<F>,
    pub gamma: FieldVar<F>,
    pub alpha: FieldVar<F>,
    pub zeta: FieldVar<F>,
    pub xi: FieldVar<F>,
    // digests (255-bit)
    pub sponge_digest_before_evaluations: FieldVar<F>,
    pub messages_for_next_wrap_proof_digest: FieldVar<F>,
    // bulletproof challenges of the previous step proof (raw 128-bit, 16)
    pub bulletproof_challenges: Vec<FieldVar<F>>,
    // packed branch data (10-bit)
    pub branch_data: FieldVar<F>,
    // feature flags (8 booleans)
    pub feature_flags: Vec<Boolean<F>>,
}

/// The bit widths of the packed (non-boolean) wrap statement elements, in
/// `to_data` order: `fp[5]` (255), `challenge[2]` (128), `scalar_challenge[3]`
/// (128), `digest[3]` (255), `bulletproof_challenges[rounds]` (128),
/// `branch_data[1]` (10). The 8 trailing feature flags are 1-bit conditional
/// terms, handled separately. `rounds` is the step proof's IPA round count
/// (TICK_ROUNDS = 16 with mina's padded domains).
pub fn wrap_statement_packed_widths(rounds: usize) -> Vec<usize> {
    let mut w = vec![255usize; 5];
    w.extend([128, 128]); // beta, gamma
    w.extend([128, 128, 128]); // alpha, zeta, xi
    w.extend([255, 255, 255]); // digests
    w.extend(std::iter::repeat_n(128, rounds)); // bulletproof challenges
    w.push(10); // branch_data
    w
}

/// Builds the x_hat [`Term`]s for the wrap statement: the packed elements in
/// `to_data` order (with `messages_for_next_step_proof` spliced in as the
/// third digest), then the 8 feature flags as conditional terms.
///
/// `packed_lagranges` pairs each packed element with its `(L_i, correction_i)`
/// constants; `flag_lagranges` are the plain `L_i` for the boolean flags.
pub fn wrap_statement_terms<F: PrimeField>(
    stmt: &WrapStatementVars<F>,
    messages_for_next_step_proof_digest: &FieldVar<F>,
    packed_lagranges: &[(Point<F>, Point<F>)],
    flag_lagranges: &[Point<F>],
) -> Vec<Term<F>> {
    let widths = wrap_statement_packed_widths(stmt.bulletproof_challenges.len());
    let mut values: Vec<FieldVar<F>> = vec![
        stmt.combined_inner_product.clone(),
        stmt.b.clone(),
        stmt.zeta_to_srs_length.clone(),
        stmt.zeta_to_domain_size.clone(),
        stmt.perm.clone(),
        stmt.beta.clone(),
        stmt.gamma.clone(),
        stmt.alpha.clone(),
        stmt.zeta.clone(),
        stmt.xi.clone(),
        stmt.sponge_digest_before_evaluations.clone(),
        stmt.messages_for_next_wrap_proof_digest.clone(),
        messages_for_next_step_proof_digest.clone(),
    ];
    values.extend(stmt.bulletproof_challenges.iter().cloned());
    values.push(stmt.branch_data.clone());
    assert_eq!(values.len(), widths.len(), "wrap statement element count");
    assert_eq!(packed_lagranges.len(), widths.len());
    assert_eq!(flag_lagranges.len(), stmt.feature_flags.len());

    let mut terms: Vec<Term<F>> = values
        .into_iter()
        .zip(&widths)
        .zip(packed_lagranges)
        .map(
            |((value, &num_bits), (lagrange, correction))| Term::Packed {
                value,
                num_bits,
                lagrange: lagrange.clone(),
                correction: correction.clone(),
            },
        )
        .collect();
    for (bit, lagrange) in stmt.feature_flags.iter().zip(flag_lagranges) {
        terms.push(Term::Cond {
            bit: bit.clone(),
            lagrange: lagrange.clone(),
        });
    }
    terms
}

/// The step-side x_hat inputs for [`crate::public_input::multiscale_known`]
/// (OCaml `incrementally_verify_proof` with a `Known` wrap domain): the wrap
/// statement's packed elements paired with their constant Lagrange
/// commitments. The boolean feature flags are compile-time constant `false`
/// in every o1js-compiled circuit, so — exactly as OCaml's constant partition
/// (`Field.Constant.(equal zero) c -> None`) — they contribute nothing.
pub fn wrap_statement_known_terms<F: PrimeField>(
    stmt: &WrapStatementVars<F>,
    messages_for_next_step_proof_digest: &FieldVar<F>,
    packed_lagranges: &[(Point<F>, Point<F>)],
) -> Vec<crate::public_input::KnownTerm<F>> {
    let widths = wrap_statement_packed_widths(stmt.bulletproof_challenges.len());
    let mut values: Vec<FieldVar<F>> = vec![
        stmt.combined_inner_product.clone(),
        stmt.b.clone(),
        stmt.zeta_to_srs_length.clone(),
        stmt.zeta_to_domain_size.clone(),
        stmt.perm.clone(),
        stmt.beta.clone(),
        stmt.gamma.clone(),
        stmt.alpha.clone(),
        stmt.zeta.clone(),
        stmt.xi.clone(),
        stmt.sponge_digest_before_evaluations.clone(),
        stmt.messages_for_next_wrap_proof_digest.clone(),
        messages_for_next_step_proof_digest.clone(),
    ];
    values.extend(stmt.bulletproof_challenges.iter().cloned());
    values.push(stmt.branch_data.clone());
    assert_eq!(values.len(), widths.len(), "wrap statement element count");
    assert_eq!(packed_lagranges.len(), widths.len());

    let as_constant = |v: &FieldVar<F>| -> F {
        match v {
            FieldVar::Constant(c) => *c,
            _ => panic!("wrap_statement_known_terms: Lagrange commitments must be constants"),
        }
    };
    values
        .into_iter()
        .zip(&widths)
        .zip(packed_lagranges)
        .map(
            |((value, &num_bits), (lagrange, _correction))| crate::public_input::KnownTerm {
                value,
                num_bits,
                lagrange: (as_constant(&lagrange.x), as_constant(&lagrange.y)),
            },
        )
        .collect()
}

/// One previous proof, fully handled inside a step circuit
/// (`step_main.ml::verify_one`):
///
/// ```text
/// assert (unfinalized.should_finalize == must_verify)
/// (finalized, chals) = finalize_deferred(statement's deferred values, evals)
/// msgs_step_digest   = hash_messages_for_next_step_proof(...)
/// statement_terms    = wrap statement + msgs_step_digest
/// verified           = verify(wrap proof, statement_terms, unfinalized claims)
/// return (chals, verified && finalized || !must_verify)
/// ```
///
/// `stmt` is the wrap proof's statement; `unfinalized_*`/`advice`/`claimed`
/// carry the wrap proof's own deferred values (from the step statement's
/// `Unfinalized`); `finalize_*` finalize the *previous step proof*'s deferred
/// values against `stmt`.
#[allow(clippy::too_many_arguments)]
pub fn verify_one<F, C>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    // finalize
    finalize_params: &crate::finalize::FinalizeParams<'_, F>,
    finalize_evals: &FinalizeEvals<F>,
    stmt: &WrapStatementVars<F>,
    // the wrap VK for the accumulator digest (the index sponge is emitted
    // here, after finalize — OCaml step_main.ml:45)
    dlog_index: &crate::composition_types::PlonkVerificationKeyEvals<Point<F>>,
    share_index_sponge: bool,
    app_state: &[FieldVar<F>],
    messages_for_next_step_accumulators: &[Point<F>],
    prev_challenge_polynomial_commitments: &[Point<F>],
    prev_challenges: &[Vec<FieldVar<F>>],
    finalize_prev_challenges: &[Vec<FieldVar<F>>],
    proofs_verified_mask: Option<&[Boolean<F>]>,
    // wrap proof verification. The same sponge that was initialized with the
    // verified wrap VK for the accumulator hash is copied and squeezed for
    // the verifier-index digest (step_verifier.ml:533-537).
    vk: &VerificationKeyComm<F>,
    packed_lagranges: &[(Point<F>, Point<F>)],
    flag_lagranges: &[Point<F>],
    h_generator: &Point<F>,
    messages: &Messages<F>,
    openings: &OpeningProof<F>,
    advice: &Advice<F>,
    xi: &FieldVar<F>,
    claimed: &Claimed<F>,
    // control booleans
    should_finalize: &Boolean<F>,
    must_verify: &Boolean<F>,
    is_base_case: &Boolean<F>,
    // constants
    group_map_params: &groupmap::BWParameters<C>,
    endo_base: F,
    endo_scalar: <ark_ec::short_weierstrass::Affine<C> as ark_ec::AffineRepr>::ScalarField,
    num_bits: usize,
) -> SnarkyResult<(Vec<FieldVar<F>>, Boolean<F>, Boolean<F>)>
where
    F: PrimeField,
    C: ark_ec::short_weierstrass::SWCurveConfig<BaseField = F>,
{
    use crate::{
        finalize::{finalize_deferred, FinalizeWitness},
        hash_messages::hash_messages_for_next_step_proof,
        scalar_challenge::scalar_to_field,
    };

    // Boolean.Assert (unfinalized.should_finalize == must_verify)
    should_finalize.to_field_var().assert_equals(
        sys,
        Cow::Owned(format!("{loc} | should_finalize==must_verify")),
        &must_verify.to_field_var(),
    )?;

    // finalize the previous step proof's deferred values (map_plonk_to_field:
    // alpha/zeta raw -> field via the endomorphism; beta/gamma used raw).
    // OCaml does NOT seal the converted challenges: the `endo·a + b` lincom
    // flows into every use and is re-reduced there (the `[c,1,-1,0,0]` rows
    // all over the env and linearization).
    let alpha_f = scalar_to_field(
        sys,
        Cow::Owned(format!("{loc} | alpha to_field")),
        &stmt.alpha,
        finalize_params.endo_r,
    )?;
    let zeta_f = scalar_to_field(
        sys,
        Cow::Owned(format!("{loc} | zeta to_field")),
        &stmt.zeta,
        finalize_params.endo_r,
    )?;
    let witness = FinalizeWitness {
        alpha: alpha_f,
        beta: stmt.beta.clone(),
        gamma: stmt.gamma.clone(),
        zeta: zeta_f,
        xi: stmt.xi.clone(),
        cip_repr: stmt.combined_inner_product.clone(),
        b_repr: stmt.b.clone(),
        perm_repr: stmt.perm.clone(),
        bulletproof_challenges: stmt.bulletproof_challenges.clone(),
        digest: stmt.sponge_digest_before_evaluations.clone(),
        prev_challenges: finalize_prev_challenges.to_vec(),
        prev_challenge_mask: proofs_verified_mask.map(<[Boolean<F>]>::to_vec),
        ft_eval1: finalize_evals.ft_eval1.clone(),
        public_evals: finalize_evals.public_evals.clone(),
        evals: finalize_evals.evals.clone(),
    };
    let fin = finalize_deferred(
        sys,
        Cow::Owned(format!("{loc} | finalize")),
        finalize_params,
        &witness,
    )?;
    for (label, check) in [
        ("finalize: xi", &fin.xi_correct),
        ("finalize: cip", &fin.cip_correct),
        ("finalize: b", &fin.b_correct),
        ("finalize: perm", &fin.perm_correct),
    ] {
        check
            .or(&must_verify.not(), Cow::Borrowed(label), sys)
            .to_field_var()
            .assert_equals(sys, Cow::Borrowed(label), &FieldVar::constant(F::one()))?;
    }

    // OCaml (step_main.ml:45): the wrap-VK index sponge is (re)emitted here,
    // per proof, AFTER finalize — `hash_messages_for_next_step_proof_opt
    // ~index:d.wrap_key` eagerly absorbs the 56 coordinates.
    let sponge_after_index = &crate::hash_messages::sponge_after_index(
        sys,
        Cow::Owned(format!("{loc} | index sponge")),
        dlog_index,
    );

    // the previous accumulator digest, recomputed in-circuit
    let msgs_step_digest = match proofs_verified_mask {
        Some(mask) => crate::hash_messages::hash_messages_for_next_step_proof_opt(
            sys,
            Cow::Owned(format!("{loc} | old digest opt")),
            sponge_after_index,
            app_state,
            messages_for_next_step_accumulators,
            prev_challenges,
            mask,
        )?,
        None => hash_messages_for_next_step_proof(
            sys,
            Cow::Owned(format!("{loc} | old digest")),
            sponge_after_index,
            app_state,
            messages_for_next_step_accumulators,
            prev_challenges,
        )?,
    };

    // the wrap statement public input, then the full wrap-proof check.
    // OCaml's step side commits over a KNOWN wrap domain via
    // `multiscale_known` (all scales first, one reduce, constants folded out
    // of circuit); the boolean feature flags are constant `false` and
    // contribute nothing.
    let _ = flag_lagranges;
    let terms = wrap_statement_known_terms(stmt, &msgs_step_digest, packed_lagranges);
    let sg_old_mask = vec![Boolean::true_(); prev_challenge_polynomial_commitments.len()];
    let index_digest = if share_index_sponge {
        IndexDigest::SpongeAfterIndex(sponge_after_index)
    } else {
        IndexDigest::ComputeFromVk
    };
    let verified = verify::<F, C>(
        sys,
        Cow::Owned(format!("{loc} | verify wrap proof")),
        index_digest,
        false,
        vk,
        prev_challenge_polynomial_commitments,
        &sg_old_mask,
        XHatInput::MultiscaleKnown {
            terms: &terms,
            h_generator,
        },
        messages,
        openings,
        advice,
        xi,
        claimed,
        Some(is_base_case),
        group_map_params,
        endo_base,
        endo_scalar,
        num_bits,
    )?;

    Ok((fin.challenges, verified, fin.finalized))
}

/// The previous step proof's evaluations consumed by the finalize half of
/// [`verify_one`] (the witness data not present in the wrap statement).
pub struct FinalizeEvals<F: PrimeField> {
    pub ft_eval1: FieldVar<F>,
    pub public_evals: [Vec<FieldVar<F>>; 2],
    pub evals: crate::fr_sponge::AbsorbEvalsVar<F>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{AdditiveGroup, BigInteger, One, UniformRand, Zero};
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Fq, Pallas, PallasParameters, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        poseidon::{ArithmeticSponge, Sponge as _},
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof as IpaProof;
    use snarky::{api::SnarkyCircuit, loc};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type RefSponge = ArithmeticSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    fn lowest_128(x: Fp) -> Fp {
        let bits = x.into_bigint().to_bits_le();
        let mut acc = Fp::zero();
        for &b in bits[..128].iter().rev() {
            acc.double_in_place();
            if b {
                acc += Fp::one();
            }
        }
        acc
    }

    const NUM_BITS: usize = 255;

    /// End-to-end structural run of `verify` in a base-case setting: the
    /// claimed digest and plonk challenges are produced by an out-of-circuit
    /// mirror of the oracle transcript (so the asserts hold), the bulletproof
    /// challenge check is bypassed by `is_base_case = true`, and the statement
    /// is committed through the x_hat gadget from packed terms. The success
    /// boolean is exposed (not asserted — needs a real pickles statement).
    struct VerifyCircuit {
        vk_digest: Fp,
        sg_old: Vec<(Fp, Fp)>,
        // packed statement inputs: (value, num_bits) with 128/255-bit mix
        inputs: Vec<(Fp, usize)>,
        lagranges: Vec<(Fp, Fp)>,
        corrections: Vec<(Fp, Fp)>,
        w_comm: Vec<Vec<(Fp, Fp)>>,
        z_comm: Vec<(Fp, Fp)>,
        t_comm: Vec<(Fp, Fp)>,
        generic: (Fp, Fp),
        psm: (Fp, Fp),
        complete_add: (Fp, Fp),
        mul: (Fp, Fp),
        emul: (Fp, Fp),
        endomul_scalar: (Fp, Fp),
        coefficients: Vec<(Fp, Fp)>,
        sigma_init: Vec<(Fp, Fp)>,
        sigma_last: Vec<(Fp, Fp)>,
        lr: Vec<((Fp, Fp), (Fp, Fp))>,
        delta: (Fp, Fp),
        cpc: (Fp, Fp),
        h: (Fp, Fp),
        xi: u128,
        cip: u128,
        b: u128,
        z1: u128,
        z2: u128,
        perm: u128,
        zeta_to_srs_length: u128,
        zeta_to_domain_size: u128,
        claimed_beta: Fp,
        claimed_gamma: Fp,
        claimed_alpha: Fp,
        claimed_zeta: Fp,
        claimed_digest: Fp,
        claimed_bp: Vec<Fp>,
    }

    impl SnarkyCircuit for VerifyCircuit {
        type Curve = Vesta;
        type Proof = IpaProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = Boolean<Fp>;
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let mkpt = |sys: &mut RunState<Fp>, p: (Fp, Fp)| -> SnarkyResult<Point<Fp>> {
                Ok(Point::new(
                    sys.compute(loc!(), move |_| p.0)?,
                    sys.compute(loc!(), move |_| p.1)?,
                ))
            };
            let mkpts = |sys: &mut RunState<Fp>, ps: &[(Fp, Fp)]| -> SnarkyResult<Vec<Point<Fp>>> {
                let mut out = vec![];
                for &p in ps {
                    out.push(mkpt(sys, p)?);
                }
                Ok(out)
            };
            let mksc = |sys: &mut RunState<Fp>, s: u128| sys.compute(loc!(), move |_| Fp::from(s));
            let cpt = |p: (Fp, Fp)| Point::new(FieldVar::constant(p.0), FieldVar::constant(p.1));

            let vk_digest: FieldVar<Fp> = sys.compute(loc!(), |_| self.vk_digest)?;
            let sg_old = mkpts(sys, &self.sg_old)?;

            // statement terms (all Packed in this test)
            let mut terms = vec![];
            for (i, &(v, n)) in self.inputs.iter().enumerate() {
                let value: FieldVar<Fp> = sys.compute(loc!(), move |_| v)?;
                terms.push(Term::Packed {
                    value,
                    num_bits: n,
                    lagrange: cpt(self.lagranges[i]),
                    correction: cpt(self.corrections[i]),
                });
            }

            let mut w_comm = vec![];
            for w in &self.w_comm {
                w_comm.push(mkpts(sys, w)?);
            }
            let vk = VerificationKeyComm {
                generic: mkpt(sys, self.generic)?,
                psm: mkpt(sys, self.psm)?,
                complete_add: mkpt(sys, self.complete_add)?,
                mul: mkpt(sys, self.mul)?,
                emul: mkpt(sys, self.emul)?,
                endomul_scalar: mkpt(sys, self.endomul_scalar)?,
                coefficients: mkpts(sys, &self.coefficients)?,
                sigma_init: mkpts(sys, &self.sigma_init)?,
                sigma_last: mkpts(sys, &self.sigma_last)?,
            };
            let messages = Messages {
                w_comm,
                z_comm: mkpts(sys, &self.z_comm)?,
                t_comm: mkpts(sys, &self.t_comm)?,
            };
            let mut lr = vec![];
            for &(l, r) in &self.lr {
                lr.push((mkpt(sys, l)?, mkpt(sys, r)?));
            }
            let h = cpt(self.h);
            let t1 = crate::plonk_curve_ops::ShiftedScalar::Type1;
            let openings = OpeningProof {
                lr,
                delta: mkpt(sys, self.delta)?,
                z1: t1(mksc(sys, self.z1)?),
                z2: t1(mksc(sys, self.z2)?),
                challenge_polynomial_commitment: mkpt(sys, self.cpc)?,
                h_generator: h.clone(),
            };
            let advice = Advice {
                combined_inner_product: t1(mksc(sys, self.cip)?),
                b: t1(mksc(sys, self.b)?),
                perm: t1(mksc(sys, self.perm)?),
                zeta_to_srs_length: t1(mksc(sys, self.zeta_to_srs_length)?),
                zeta_to_domain_size: t1(mksc(sys, self.zeta_to_domain_size)?),
            };
            let xi = mksc(sys, self.xi)?;

            let mut claimed_bp = vec![];
            for &c in &self.claimed_bp {
                claimed_bp.push(sys.compute(loc!(), move |_| c)?);
            }
            let claimed = Claimed {
                beta: sys.compute(loc!(), |_| self.claimed_beta)?,
                gamma: sys.compute(loc!(), |_| self.claimed_gamma)?,
                alpha: sys.compute(loc!(), |_| self.claimed_alpha)?,
                zeta: sys.compute(loc!(), |_| self.claimed_zeta)?,
                sponge_digest_before_evaluations: sys.compute(loc!(), |_| self.claimed_digest)?,
                bulletproof_challenges: claimed_bp,
            };
            let is_base_case: Boolean<Fp> = sys.compute(loc!(), |_| true)?;

            use groupmap::GroupMap;
            let params = groupmap::BWParameters::<PallasParameters>::setup();
            let success = verify::<Fp, PallasParameters>(
                sys,
                loc!(),
                IndexDigest::Precomputed(&vk_digest),
                false,
                &vk,
                &sg_old,
                &vec![Boolean::true_(); sg_old.len()],
                XHatInput::PublicInput {
                    terms: &terms,
                    h_generator: &h,
                },
                &messages,
                &openings,
                &advice,
                &xi,
                &claimed,
                Some(&is_base_case),
                &params,
                crate::endo::tick::base(),
                <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1,
                NUM_BITS,
            )?;
            let success = Boolean::create_unsafe(success.to_field_var().seal(sys, loc!())?);
            Ok(success)
        }
    }

    /// `verify` composes x_hat + IVP + asserts into one satisfiable circuit
    /// when the claimed digest/challenges come from a transcript mirror.
    #[test]
    fn verify_assembles_with_consistent_claims() {
        use groupmap::GroupMap;
        let mut rng = o1_utils::tests::make_test_rng(None);
        let rand_pt = |rng: &mut _| (Pallas::generator() * Fq::rand(rng)).into_affine();
        let pt = |rng: &mut _| {
            let p = rand_pt(rng);
            (p.x, p.y)
        };

        let vk_digest = Fp::rand(&mut rng);
        let sg_old_pts = [rand_pt(&mut rng)];
        // statement inputs: 2×128-bit + 1×255-bit
        let inputs: Vec<(Fp, usize)> = vec![
            (Fp::from(u128::rand(&mut rng)), 128),
            (Fp::from(u128::rand(&mut rng)), 128),
            (
                crate::shifted_value::embed_repr::<Fq, Fp>(Fq::rand(&mut rng)),
                255,
            ),
        ];
        let lagrange_pts: Vec<Pallas> = (0..3).map(|_| rand_pt(&mut rng)).collect();
        let corrections: Vec<Pallas> = lagrange_pts
            .iter()
            .zip(&inputs)
            .map(|(l, (_, n))| crate::public_input::lagrange_correction(l, *n))
            .collect();
        let h = rand_pt(&mut rng);

        let w_comm_pts: Vec<Pallas> = (0..15).map(|_| rand_pt(&mut rng)).collect();
        let z_comm_pt = rand_pt(&mut rng);
        let t_comm_pts: Vec<Pallas> = (0..7).map(|_| rand_pt(&mut rng)).collect();

        // out-of-circuit mirror: x_hat, then the oracle transcript
        let x_hat = {
            let mut sum = Pallas::zero().into_group();
            for ((v, _n), l) in inputs.iter().zip(&lagrange_pts) {
                // value · L  (recover the integer scalar from the Fp value)
                let scalar = Fq::from_le_bytes_mod_order(&v.into_bigint().to_bytes_le());
                sum += *l * scalar;
            }
            (-sum + h).into_affine()
        };
        let mut s = RefSponge::new(Vesta::sponge_params());
        let absorb_pt = |s: &mut RefSponge, p: &Pallas| {
            s.absorb(&[p.x]);
            s.absorb(&[p.y]);
        };
        s.absorb(&[vk_digest]);
        for sg in &sg_old_pts {
            absorb_pt(&mut s, sg);
        }
        absorb_pt(&mut s, &x_hat);
        for w in &w_comm_pts {
            absorb_pt(&mut s, w);
        }
        let claimed_beta = lowest_128(s.squeeze());
        let claimed_gamma = lowest_128(s.squeeze());
        absorb_pt(&mut s, &z_comm_pt);
        let claimed_alpha = lowest_128(s.squeeze());
        for t in &t_comm_pts {
            absorb_pt(&mut s, t);
        }
        let claimed_zeta = lowest_128(s.squeeze());
        let claimed_digest = s.squeeze();

        let params = groupmap::BWParameters::<PallasParameters>::setup();
        let _ = &params;

        let circ = VerifyCircuit {
            vk_digest,
            sg_old: sg_old_pts.iter().map(|p| (p.x, p.y)).collect(),
            inputs,
            lagranges: lagrange_pts.iter().map(|p| (p.x, p.y)).collect(),
            corrections: corrections.iter().map(|p| (p.x, p.y)).collect(),
            w_comm: w_comm_pts.iter().map(|p| vec![(p.x, p.y)]).collect(),
            z_comm: vec![(z_comm_pt.x, z_comm_pt.y)],
            t_comm: t_comm_pts.iter().map(|p| (p.x, p.y)).collect(),
            generic: pt(&mut rng),
            psm: pt(&mut rng),
            complete_add: pt(&mut rng),
            mul: pt(&mut rng),
            emul: pt(&mut rng),
            endomul_scalar: pt(&mut rng),
            coefficients: (0..15).map(|_| pt(&mut rng)).collect(),
            sigma_init: (0..6).map(|_| pt(&mut rng)).collect(),
            sigma_last: vec![pt(&mut rng)],
            lr: (0..2).map(|_| (pt(&mut rng), pt(&mut rng))).collect(),
            delta: pt(&mut rng),
            cpc: pt(&mut rng),
            h: (h.x, h.y),
            xi: u128::rand(&mut rng),
            cip: u128::rand(&mut rng),
            b: u128::rand(&mut rng),
            z1: u128::rand(&mut rng),
            z2: u128::rand(&mut rng),
            perm: u128::rand(&mut rng),
            zeta_to_srs_length: u128::rand(&mut rng),
            zeta_to_domain_size: u128::rand(&mut rng),
            claimed_beta,
            claimed_gamma,
            claimed_alpha,
            claimed_zeta,
            claimed_digest,
            // base case: compared against themselves
            claimed_bp: (0..2).map(|_| Fp::from(u128::rand(&mut rng))).collect(),
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        // success is not asserted true (random data cannot satisfy the IPA
        // equation) — the point is that every assert in `verify` held.
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }

    /// Structural run of `verify_one`: synthetic finalize data (its real-proof
    /// parity is covered by the finalize_deferred test), transcript-mirrored
    /// claims for the verify half, statement committed through the terms
    /// builder with the in-circuit accumulator digest spliced in.
    struct VerifyOneCircuit {
        // accumulator digest inputs
        vk28: Vec<(Fp, Fp)>,
        app_state: Vec<Fp>,
        prev_cpc: (Fp, Fp),
        prev_chals: Vec<Fp>,
        // wrap statement values (packed order minus the in-circuit digest)
        stmt_packed: Vec<Fp>, // 29 = 5 fp + 5 chals + 2 digests + 16 bp + 1 branch
        // lagrange constants for the 30 packed + 8 flag terms
        packed_lagranges: Vec<((Fp, Fp), (Fp, Fp))>,
        flag_lagranges: Vec<(Fp, Fp)>,
        // synthetic finalize inputs
        domain: ark_poly::Radix2EvaluationDomain<Fp>,
        shifts: Vec<Fp>,
        ft_eval1: Fp,
        public_evals: [Vec<Fp>; 2],
        evals_flat: Vec<(Fp, Fp)>, // z, 6 selectors, 15 w, 15 coeff, 6 s = 43
        // wrap proof (random)
        w_comm: Vec<Vec<(Fp, Fp)>>,
        z_comm: Vec<(Fp, Fp)>,
        t_comm: Vec<(Fp, Fp)>,
        ivp_vk: Vec<(Fp, Fp)>, // generic..endomul_scalar(6), coeff(15), sigma_init(6), sigma_last(1)
        lr: Vec<((Fp, Fp), (Fp, Fp))>,
        delta: (Fp, Fp),
        cpc: (Fp, Fp),
        h: (Fp, Fp),
        advice_scalars: [u128; 5],     // cip, b, perm, z2srs, z2dom
        opening_scalars: [u128; 3],    // xi, z1, z2
        claimed: (Fp, Fp, Fp, Fp, Fp), // beta, gamma, alpha, zeta, digest
        claimed_bp: Vec<Fp>,
    }

    impl SnarkyCircuit for VerifyOneCircuit {
        type Curve = Vesta;
        type Proof = IpaProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        /// the new `messages_for_next_step_proof` digest
        type PublicOutput = FieldVar<Fp>;
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            use kimchi::circuits::wires::{COLUMNS, PERMUTS};

            let mkpt = |sys: &mut RunState<Fp>, p: (Fp, Fp)| -> SnarkyResult<Point<Fp>> {
                Ok(Point::new(
                    sys.compute(loc!(), move |_| p.0)?,
                    sys.compute(loc!(), move |_| p.1)?,
                ))
            };
            let mkpts = |sys: &mut RunState<Fp>, ps: &[(Fp, Fp)]| -> SnarkyResult<Vec<Point<Fp>>> {
                let mut out = vec![];
                for &p in ps {
                    out.push(mkpt(sys, p)?);
                }
                Ok(out)
            };
            let w1 = |sys: &mut RunState<Fp>, v: Fp| sys.compute(loc!(), move |_| v);
            let wvec = |sys: &mut RunState<Fp>, vs: &[Fp]| -> SnarkyResult<Vec<FieldVar<Fp>>> {
                let mut out = vec![];
                for &v in vs {
                    out.push(sys.compute(loc!(), move |_| v)?);
                }
                Ok(out)
            };
            let cpt = |p: (Fp, Fp)| Point::new(FieldVar::constant(p.0), FieldVar::constant(p.1));

            // ---- accumulator inputs ----
            let vk28pts = mkpts(sys, &self.vk28)?;
            let mut it = vk28pts.into_iter();
            let vk28 = crate::composition_types::PlonkVerificationKeyEvals {
                sigma_comm: (0..PERMUTS).map(|_| it.next().unwrap()).collect(),
                coefficients_comm: (0..COLUMNS).map(|_| it.next().unwrap()).collect(),
                generic_comm: it.next().unwrap(),
                psm_comm: it.next().unwrap(),
                complete_add_comm: it.next().unwrap(),
                mul_comm: it.next().unwrap(),
                emul_comm: it.next().unwrap(),
                endomul_scalar_comm: it.next().unwrap(),
            };

            let app_state = wvec(sys, &self.app_state)?;
            let prev_cpcs = vec![mkpt(sys, self.prev_cpc)?];
            let prev_chals = vec![wvec(sys, &self.prev_chals)?];

            // ---- wrap statement vars ----
            let sp = wvec(sys, &self.stmt_packed)?;
            let stmt = WrapStatementVars {
                combined_inner_product: sp[0].clone(),
                b: sp[1].clone(),
                zeta_to_srs_length: sp[2].clone(),
                zeta_to_domain_size: sp[3].clone(),
                perm: sp[4].clone(),
                beta: sp[5].clone(),
                gamma: sp[6].clone(),
                alpha: sp[7].clone(),
                zeta: sp[8].clone(),
                xi: sp[9].clone(),
                sponge_digest_before_evaluations: sp[10].clone(),
                messages_for_next_wrap_proof_digest: sp[11].clone(),
                bulletproof_challenges: sp[12..28].to_vec(),
                branch_data: sp[28].clone(),
                feature_flags: {
                    let mut v = vec![];
                    for _ in 0..8 {
                        let b: Boolean<Fp> = sys.compute(loc!(), |_| false)?;
                        v.push(b);
                    }
                    v
                },
            };
            let packed_lagranges: Vec<(Point<Fp>, Point<Fp>)> = self
                .packed_lagranges
                .iter()
                .map(|&(l, c)| (cpt(l), cpt(c)))
                .collect();
            let flag_lagranges: Vec<Point<Fp>> =
                self.flag_lagranges.iter().map(|&l| cpt(l)).collect();

            // ---- synthetic finalize data ----
            let tokens = vec![kimchi::circuits::expr::PolishToken::Constant(
                kimchi::circuits::expr::ConstantTerm::Literal(Fp::zero()),
            )];
            let mds: Vec<Vec<Fp>> = Vesta::sponge_params()
                .mds
                .iter()
                .map(|r| r.to_vec())
                .collect();
            let (_, endo_r) = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();
            let finalize_params = crate::finalize::FinalizeParams {
                tokens: &tokens,
                domain: crate::ft_eval_circuit::FinalizeDomain::Fixed(self.domain),
                srs_log2: 12,
                endo: Fp::from(3u64),
                shifts: &self.shifts,
                endo_r: *endo_r,
                mds: &mds,
                shift: crate::finalize::ShiftKind::Type1,
            };
            let public_evals = [
                wvec(sys, &self.public_evals[0])?,
                wvec(sys, &self.public_evals[1])?,
            ];
            let mut fe = self.evals_flat.iter();
            let mut next_pe =
                |sys: &mut RunState<Fp>| -> SnarkyResult<crate::fr_sponge::PointEvalVar<Fp>> {
                    let &(a, b) = fe.next().unwrap();
                    Ok((vec![w1(sys, a)?], vec![w1(sys, b)?]))
                };
            let evals = crate::fr_sponge::AbsorbEvalsVar {
                w: (0..COLUMNS)
                    .map(|_| next_pe(sys))
                    .collect::<SnarkyResult<Vec<_>>>()?,
                coefficients: (0..COLUMNS)
                    .map(|_| next_pe(sys))
                    .collect::<SnarkyResult<Vec<_>>>()?,
                z: next_pe(sys)?,
                s: (0..PERMUTS - 1)
                    .map(|_| next_pe(sys))
                    .collect::<SnarkyResult<Vec<_>>>()?,
                generic_selector: next_pe(sys)?,
                poseidon_selector: next_pe(sys)?,
                complete_add_selector: next_pe(sys)?,
                mul_selector: next_pe(sys)?,
                emul_selector: next_pe(sys)?,
                endomul_scalar_selector: next_pe(sys)?,
            };
            let finalize_evals = FinalizeEvals {
                ft_eval1: w1(sys, self.ft_eval1)?,
                public_evals,
                evals,
            };

            // ---- wrap proof pieces (random) ----
            let mut w_comm = vec![];
            for w in &self.w_comm {
                w_comm.push(mkpts(sys, w)?);
            }
            let ivp = mkpts(sys, &self.ivp_vk)?;
            let vk = VerificationKeyComm {
                generic: ivp[0].clone(),
                psm: ivp[1].clone(),
                complete_add: ivp[2].clone(),
                mul: ivp[3].clone(),
                emul: ivp[4].clone(),
                endomul_scalar: ivp[5].clone(),
                coefficients: ivp[6..21].to_vec(),
                sigma_init: ivp[21..27].to_vec(),
                sigma_last: vec![ivp[27].clone()],
            };
            let messages = Messages {
                w_comm,
                z_comm: mkpts(sys, &self.z_comm)?,
                t_comm: mkpts(sys, &self.t_comm)?,
            };
            let mut lr = vec![];
            for &(l, r) in &self.lr {
                lr.push((mkpt(sys, l)?, mkpt(sys, r)?));
            }
            let h = cpt(self.h);
            let mksc = |sys: &mut RunState<Fp>, s: u128| sys.compute(loc!(), move |_| Fp::from(s));
            let t1 = crate::plonk_curve_ops::ShiftedScalar::Type1;
            let openings = OpeningProof {
                lr,
                delta: mkpt(sys, self.delta)?,
                z1: t1(mksc(sys, self.opening_scalars[1])?),
                z2: t1(mksc(sys, self.opening_scalars[2])?),
                challenge_polynomial_commitment: mkpt(sys, self.cpc)?,
                h_generator: h.clone(),
            };
            let advice = Advice {
                combined_inner_product: t1(mksc(sys, self.advice_scalars[0])?),
                b: t1(mksc(sys, self.advice_scalars[1])?),
                perm: t1(mksc(sys, self.advice_scalars[2])?),
                zeta_to_srs_length: t1(mksc(sys, self.advice_scalars[3])?),
                zeta_to_domain_size: t1(mksc(sys, self.advice_scalars[4])?),
            };
            let xi = mksc(sys, self.opening_scalars[0])?;
            let claimed = Claimed {
                beta: w1(sys, self.claimed.0)?,
                gamma: w1(sys, self.claimed.1)?,
                alpha: w1(sys, self.claimed.2)?,
                zeta: w1(sys, self.claimed.3)?,
                sponge_digest_before_evaluations: w1(sys, self.claimed.4)?,
                bulletproof_challenges: wvec(sys, &self.claimed_bp)?,
            };
            // must_verify = should_finalize = false: with synthetic finalize
            // data and random IPA data the ok boolean is !must_verify = true,
            // so step_main's Boolean.Assert.all is satisfiable.
            let fals: Boolean<Fp> = sys.compute(loc!(), |_| false)?;
            let tru: Boolean<Fp> = sys.compute(loc!(), |_| true)?;

            use groupmap::GroupMap;
            let params = groupmap::BWParameters::<PallasParameters>::setup();
            let next_step_accumulator = openings.challenge_polynomial_commitment.clone();
            let proof_input = crate::step_main::PerProofInput {
                finalize_params,
                finalize_evals,
                stmt,
                dlog_index: vk28.clone(),
                share_index_sponge: true,
                prev_app_state: app_state.clone(),
                messages_for_next_step_accumulators: prev_cpcs.clone(),
                prev_challenge_polynomial_commitments: prev_cpcs,
                prev_challenges: prev_chals,
                finalize_prev_challenges: vec![],
                proofs_verified_mask: None,
                vk,
                packed_lagranges,
                flag_lagranges,
                h_generator: h,
                messages,
                openings,
                next_step_accumulator,
                next_step_challenges: None,
                advice,
                xi,
                claimed,
                should_finalize: fals.clone(),
                must_verify: fals,
                is_base_case: tru,
                witness_must_verify: false,
            };
            crate::step_main::step_main::<Fp, PallasParameters>(
                sys,
                loc!(),
                &app_state,
                &vk28,
                std::slice::from_ref(&proof_input),
                &params,
                crate::endo::tick::base(),
                <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1,
                NUM_BITS,
            )
        }
    }

    /// `step_main` (looping `verify_one`) wires finalize, the accumulator
    /// digest, the statement terms, `verify` and `Boolean.Assert.all` into one
    /// satisfiable circuit (claims from a transcript mirror that includes the
    /// in-circuit accumulator digest and x_hat), and its output digest matches
    /// the out-of-circuit accumulator mirror.
    #[test]
    fn step_main_assembles() {
        use ark_poly::EvaluationDomain;
        use groupmap::GroupMap;
        use kimchi::circuits::wires::{COLUMNS, PERMUTS};
        let mut rng = o1_utils::tests::make_test_rng(None);
        let rand_pt = |rng: &mut _| (Pallas::generator() * Fq::rand(rng)).into_affine();
        let pt = |rng: &mut _| {
            let p = rand_pt(rng);
            (p.x, p.y)
        };

        // The accumulator hash and the incremental verifier share the same
        // wrap VK. `ivp_vk` stores selectors, coefficients, sigmas; `vk28`
        // is its canonical sigma, coefficients, selectors absorption order.
        let ivp_vk: Vec<(Fp, Fp)> = (0..28).map(|_| pt(&mut rng)).collect();
        let vk28: Vec<(Fp, Fp)> = (21..28)
            .chain(6..21)
            .chain(0..6)
            .map(|i| ivp_vk[i])
            .collect();
        let app_state: Vec<Fp> = (0..2).map(|_| Fp::rand(&mut rng)).collect();
        let prev_cpc = pt(&mut rng);
        let prev_chals: Vec<Fp> = (0..crate::common::TICK_ROUNDS)
            .map(|_| Fp::rand(&mut rng))
            .collect();

        // mirror the accumulator digest
        let msgs_step_digest = {
            let mut s = RefSponge::new(Vesta::sponge_params());
            for (x, y) in &vk28 {
                s.absorb(&[*x]);
                s.absorb(&[*y]);
            }
            for x in &app_state {
                s.absorb(&[*x]);
            }
            s.absorb(&[prev_cpc.0]);
            s.absorb(&[prev_cpc.1]);
            for c in &prev_chals {
                s.absorb(&[*c]);
            }
            s.squeeze()
        };

        // wrap statement packed values (29): widths [255×5, 128×5, 255×2,
        // 128×16, 10]
        let widths = wrap_statement_packed_widths(16);
        let mut stmt_packed: Vec<Fp> = vec![];
        for (i, &w) in widths.iter().enumerate() {
            if i == 12 {
                continue; // msgs_step digest — in-circuit
            }
            let v = match w {
                255 => crate::shifted_value::embed_repr::<Fq, Fp>(Fq::rand(&mut rng)),
                128 => Fp::from(u128::rand(&mut rng)),
                _ => Fp::from(u64::rand(&mut rng) % (1 << w)),
            };
            stmt_packed.push(v);
        }
        // splice the digest back for the mirror's full value list
        let mut stmt_values = stmt_packed.clone();
        stmt_values.insert(12, msgs_step_digest);

        let lagrange_pts: Vec<Pallas> = (0..widths.len()).map(|_| rand_pt(&mut rng)).collect();
        let corrections: Vec<Pallas> = lagrange_pts
            .iter()
            .zip(&widths)
            .map(|(l, &n)| crate::public_input::lagrange_correction(l, n))
            .collect();
        let flag_lagrange_pts: Vec<Pallas> = (0..8).map(|_| rand_pt(&mut rng)).collect();
        let h = rand_pt(&mut rng);

        // mirror x_hat (flags all false)
        let x_hat = {
            let mut sum = Pallas::zero().into_group();
            for (v, l) in stmt_values.iter().zip(&lagrange_pts) {
                let scalar = Fq::from_le_bytes_mod_order(&v.into_bigint().to_bytes_le());
                sum += *l * scalar;
            }
            (-sum + h).into_affine()
        };

        // wrap proof pieces
        // ivp_vk layout: generic..endomul_scalar(6), coeff(15), sigma_init(6),
        // sigma_last(1). The circuit derives the index digest in-circuit
        // (IndexDigest::ComputeFromVk order: sigma_init, sigma_last,
        // coefficients, then the 6 selector commitments) — mirror that here.
        let vk_digest = {
            let mut isp = RefSponge::new(Vesta::sponge_params());
            for idx in (21..28).chain(6..21).chain(0..6) {
                let (x, y) = ivp_vk[idx];
                isp.absorb(&[x]);
                isp.absorb(&[y]);
            }
            isp.squeeze()
        };
        let w_comm_pts: Vec<Pallas> = (0..15).map(|_| rand_pt(&mut rng)).collect();
        let z_comm_pt = rand_pt(&mut rng);
        let t_comm_pts: Vec<Pallas> = (0..7).map(|_| rand_pt(&mut rng)).collect();

        // transcript mirror (sg_old = prev_cpc)
        let mut s = RefSponge::new(Vesta::sponge_params());
        let absorb_pt = |s: &mut RefSponge, p: (Fp, Fp)| {
            s.absorb(&[p.0]);
            s.absorb(&[p.1]);
        };
        s.absorb(&[vk_digest]);
        absorb_pt(&mut s, prev_cpc);
        absorb_pt(&mut s, (x_hat.x, x_hat.y));
        for w in &w_comm_pts {
            absorb_pt(&mut s, (w.x, w.y));
        }
        let claimed_beta = lowest_128(s.squeeze());
        let claimed_gamma = lowest_128(s.squeeze());
        absorb_pt(&mut s, (z_comm_pt.x, z_comm_pt.y));
        let claimed_alpha = lowest_128(s.squeeze());
        for t in &t_comm_pts {
            absorb_pt(&mut s, (t.x, t.y));
        }
        let claimed_zeta = lowest_128(s.squeeze());
        let claimed_digest = s.squeeze();

        // mirror of step_main's output digest: the new accumulator hash over
        // the wrap VK, this app state, the wrap proof's challenge-polynomial
        // commitment and the field images of the statement's prechallenges
        let wrap_cpc = pt(&mut rng);
        let (_, endo_r) = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();
        let expected_digest = {
            let mut s = RefSponge::new(Vesta::sponge_params());
            for (x, y) in &vk28 {
                s.absorb(&[*x]);
                s.absorb(&[*y]);
            }
            for x in &app_state {
                s.absorb(&[*x]);
            }
            s.absorb(&[wrap_cpc.0]);
            s.absorb(&[wrap_cpc.1]);
            for raw in &stmt_values[13..29] {
                let f = crate::scalar_challenge::ScalarChallenge(*raw).to_field(*endo_r);
                s.absorb(&[f]);
            }
            s.squeeze()
        };

        let circ = VerifyOneCircuit {
            vk28,
            app_state,
            prev_cpc,
            prev_chals,
            stmt_packed,
            packed_lagranges: lagrange_pts
                .iter()
                .zip(&corrections)
                .map(|(l, c)| ((l.x, l.y), (c.x, c.y)))
                .collect(),
            flag_lagranges: flag_lagrange_pts.iter().map(|p| (p.x, p.y)).collect(),
            domain: ark_poly::Radix2EvaluationDomain::new(1 << 10).unwrap(),
            shifts: (0..PERMUTS).map(|_| Fp::rand(&mut rng)).collect(),
            ft_eval1: Fp::rand(&mut rng),
            public_evals: [vec![Fp::rand(&mut rng)], vec![Fp::rand(&mut rng)]],
            evals_flat: (0..1 + 6 + 2 * COLUMNS + PERMUTS - 1)
                .map(|_| (Fp::rand(&mut rng), Fp::rand(&mut rng)))
                .collect(),
            w_comm: w_comm_pts.iter().map(|p| vec![(p.x, p.y)]).collect(),
            z_comm: vec![(z_comm_pt.x, z_comm_pt.y)],
            t_comm: t_comm_pts.iter().map(|p| (p.x, p.y)).collect(),
            ivp_vk,
            lr: (0..2).map(|_| (pt(&mut rng), pt(&mut rng))).collect(),
            delta: pt(&mut rng),
            cpc: wrap_cpc,
            h: (h.x, h.y),
            advice_scalars: core::array::from_fn(|_| u128::rand(&mut rng)),
            opening_scalars: core::array::from_fn(|_| u128::rand(&mut rng)),
            claimed: (
                claimed_beta,
                claimed_gamma,
                claimed_alpha,
                claimed_zeta,
                claimed_digest,
            ),
            claimed_bp: (0..2).map(|_| Fp::from(u128::rand(&mut rng))).collect(),
        };
        let params = groupmap::BWParameters::<PallasParameters>::setup();
        let _ = &params;
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(*out, expected_digest, "messages_for_next_step_proof digest");
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }
}

//! The arithmetic core of `finalize_other_proof` (pickles `wrap_verifier.ml`),
//! assembled in-circuit from the previously-ported and separately-validated
//! primitives:
//!
//! - [`crate::fr_sponge::squeeze_xi_r`] — resamples the 128-bit challenges
//!   `xi` (polyscale) and `r` (evalscale) from the Fiat-Shamir transcript;
//! - [`crate::scalar_challenge::scalar_to_field`] — the endo interpretation of
//!   those challenges as full field elements;
//! - [`crate::ft_eval_circuit`] — the in-circuit `ft_eval0`;
//! - [`crate::ipa::combined_inner_product_circuit`] — the deferred inner
//!   product `Σ_i xi^i (zeta_i + r·zetaw_i)`.
//!
//! This covers steps 4–8 of the OCaml `finalize_other_proof`: reconstruct the
//! sponge, squeeze and check `xi`, and check the combined inner product. The
//! remaining two conjuncts of the returned `Boolean.all` — `b_correct` (the new
//! bulletproof-challenge polynomial) and `plonk_checks_passed` (the full
//! per-gate PlonK relation) — are left for later.
//!
//! The `xi_correct` check compares the *raw 128-bit* squeezed challenge against
//! the claimed `xi` (as OCaml does on `Scalar_challenge.inner`); the field form
//! used by the inner product then comes from `scalar_to_field` of the claimed
//! `xi` (equal to the squeezed one whenever the check passes).

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{Boolean, FieldVar, RunState, SnarkyResult};

use crate::{
    fr_sponge::{squeeze_xi_r, FrSpongeInputs},
    ipa::{
        challenge_polynomial_circuit, combined_inner_product_circuit,
        combined_inner_product_circuit_masked,
    },
    scalar_challenge::scalar_to_field,
};

/// The result of the finalize arithmetic core: the derived field challenges and
/// the reconstructed inner product, plus the `xi_correct` boolean.
pub struct FinalizeCore<F: PrimeField> {
    /// `xi` (polyscale) as a full field element.
    pub xi_field: FieldVar<F>,
    /// `r` (evalscale) as a full field element.
    pub r_field: FieldVar<F>,
    /// The reconstructed combined inner product.
    pub combined_inner_product: FieldVar<F>,
    /// Whether the squeezed `xi` matched the claimed one (raw 128-bit compare).
    pub xi_correct: Boolean<F>,
}

/// Runs the finalize arithmetic core.
///
/// - `sponge_inputs` feeds the Fr-sponge (see [`FrSpongeInputs`]);
/// - `claimed_xi` is the deferred/claimed 128-bit `xi` from the statement;
/// - `ft_eval0` is the in-circuit `ft_eval0` (from [`crate::ft_eval_circuit`]);
/// - `cip_entries` are the inner-product columns in kimchi's order, as
///   `(eval_at_zeta, eval_at_zetaw)` field pairs (public, `[ft0, ft1]`, then the
///   mandatory columns);
/// - `endo` is the scalar endomorphism coefficient of the proof's curve.
pub fn finalize_core<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    sponge_inputs: &FrSpongeInputs<F>,
    claimed_xi: &FieldVar<F>,
    cip_entries: &[(FieldVar<F>, FieldVar<F>)],
    endo: F,
) -> SnarkyResult<FinalizeCore<F>> {
    finalize_core_with_mask(sys, loc, sponge_inputs, claimed_xi, &[], cip_entries, endo)
}

fn finalize_core_with_mask<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    sponge_inputs: &FrSpongeInputs<F>,
    claimed_xi: &FieldVar<F>,
    masked_prefix: &[(Boolean<F>, FieldVar<F>, FieldVar<F>)],
    cip_entries: &[(FieldVar<F>, FieldVar<F>)],
    endo: F,
) -> SnarkyResult<FinalizeCore<F>> {
    // steps 4-5: reconstruct the sponge, squeeze xi and r (128-bit challenges)
    let (xi_actual, r_actual) = squeeze_xi_r(sys, loc.clone(), sponge_inputs)?;

    // xi_correct: the squeezed xi matches the claimed one (raw 128-bit compare)
    let xi_correct = xi_actual.equal(sys, loc.clone(), claimed_xi)?;

    // convert the (claimed) xi and r to field elements via the endomorphism
    let xi_field = scalar_to_field(
        sys,
        Cow::Owned(format!("{loc} | xi to_field")),
        claimed_xi,
        endo,
    )?;
    let r_field = scalar_to_field(
        sys,
        Cow::Owned(format!("{loc} | r to_field")),
        &r_actual,
        endo,
    )?;

    // step 8: the combined inner product from those challenges
    let combined_inner_product = if masked_prefix.is_empty() {
        combined_inner_product_circuit(sys, loc, &xi_field, &r_field, cip_entries)?
    } else {
        combined_inner_product_circuit_masked(
            sys,
            loc,
            &xi_field,
            &r_field,
            masked_prefix,
            cip_entries,
        )?
    };

    Ok(FinalizeCore {
        xi_field,
        r_field,
        combined_inner_product,
        xi_correct,
    })
}

/// The bulletproof `b` value, reconstructed from the *new* bulletproof
/// challenges (step 9 of `finalize_other_proof`):
/// `b = h(zeta) + r * h(zetaw)` where `h(X) = prod_i (1 + chals[i] X^{2^{k-1-i}})`
/// is the challenge polynomial and `zetaw = domain_generator * zeta`.
///
/// `chals` are the challenges already in field form (via
/// [`crate::ipa::compute_challenges`] / [`scalar_to_field`]).
pub fn b_actual<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    chals: &[FieldVar<F>],
    zeta: &FieldVar<F>,
    zetaw: &FieldVar<F>,
    r: &FieldVar<F>,
) -> SnarkyResult<FieldVar<F>> {
    let zetaw = zetaw.clone();
    let h_zeta = challenge_polynomial_circuit(sys, loc.clone(), chals, zeta)?;
    let h_zetaw = challenge_polynomial_circuit(sys, loc.clone(), chals, &zetaw)?;
    let r_h_zetaw = r.mul(&h_zetaw, None, loc, sys)?;
    Ok(&h_zeta + &r_h_zetaw)
}

/// Recovers a field element from its `Shifted_value.Type1` representation,
/// in-circuit: `to_field(repr) = 2·repr + 2^size + 1`.
///
/// This is the shift the *step*-side `finalize_other_proof` uses for the
/// claimed `combined_inner_product`, `b` and `perm` (`step_verifier.ml`,
/// `shift1` — `Shifted_value.Type1.to_field`). It mirrors the constant
/// [`crate::shifted_value::type1_to_field`] but over a `FieldVar`.
pub fn type1_to_field<F: PrimeField>(repr: &FieldVar<F>) -> FieldVar<F> {
    let c = crate::shifted_value::two_to_size::<F>() + F::one();
    &(repr + repr) + &FieldVar::constant(c)
}

/// Recovers a field element from its `Shifted_value.Type2` representation,
/// in-circuit: `to_field(repr) = repr + 2^size` — the shift the *wrap*-side
/// `finalize_other_proof` uses (`wrap_verifier.ml`, `shift2`).
pub fn type2_to_field<F: PrimeField>(repr: &FieldVar<F>) -> FieldVar<F> {
    repr + &FieldVar::constant(crate::shifted_value::two_to_size::<F>())
}

/// Which `Shifted_value` convention the claimed deferred values use:
/// [`ShiftKind::Type1`] on the step side, [`ShiftKind::Type2`] on the wrap
/// side.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShiftKind {
    Type1,
    Type2,
}

impl ShiftKind {
    /// The in-circuit `Shifted_value.to_field` for this convention.
    pub fn to_field<F: PrimeField>(self, repr: &FieldVar<F>) -> FieldVar<F> {
        match self {
            ShiftKind::Type1 => type1_to_field(repr),
            ShiftKind::Type2 => type2_to_field(repr),
        }
    }
}

/// Combines the four `finalize_other_proof` conjuncts into the single boolean
/// `Boolean.all [xi_correct; combined_inner_product_correct; b_correct;
/// plonk_checks_passed]`.
///
/// `xi_correct` is the (already-computed) 128-bit challenge comparison; the
/// other three compare an in-circuit *derived* value against the *claimed*
/// value recovered from the statement via [`type1_to_field`]
/// (`Shifted_value.Type1.to_field` with `shift1`).
#[allow(clippy::too_many_arguments)]
pub fn finalize_all<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    xi_correct: &Boolean<F>,
    cip_derived: &FieldVar<F>,
    cip_claimed: &FieldVar<F>,
    b_derived: &FieldVar<F>,
    b_claimed: &FieldVar<F>,
    perm_derived: &FieldVar<F>,
    perm_claimed: &FieldVar<F>,
) -> SnarkyResult<Boolean<F>> {
    let cip_correct = cip_derived.equal(sys, loc.clone(), cip_claimed)?;
    let b_correct = b_derived.equal(sys, loc.clone(), b_claimed)?;
    let perm_correct = perm_derived.equal(sys, loc.clone(), perm_claimed)?;
    Boolean::all(
        &[xi_correct.clone(), cip_correct, b_correct, perm_correct],
        sys,
        loc,
    )
}

/// The complete in-circuit `finalize_other_proof` (`step_verifier.ml`):
/// re-derives the deferred values (`xi`, `combined_inner_product`, `b`) and
/// combines the four conjuncts into the single `Boolean.all`.
///
/// `perm_derived` is the permutation scalar computed by the caller (via
/// [`crate::ft_eval_circuit::perm_scalar_circuit`], sharing the same
/// `scalars_env`/evals as `ft_eval0`). The claimed values
/// (`*_claimed_repr`) are the statement's `Shifted_value.Type1` representatives,
/// recovered with [`type1_to_field`]. `b_chals` are the *new* bulletproof
/// challenges in field form; `domain_generator` gives `zetaw = domain_generator·zeta`.
#[allow(clippy::too_many_arguments)]
pub fn finalize_other_proof<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    sponge_inputs: &FrSpongeInputs<F>,
    claimed_xi: &FieldVar<F>,
    cip_entries: &[(FieldVar<F>, FieldVar<F>)],
    cip_claimed_repr: &FieldVar<F>,
    b_chals: &[FieldVar<F>],
    zeta: &FieldVar<F>,
    domain_generator: F,
    b_claimed_repr: &FieldVar<F>,
    perm_derived: &FieldVar<F>,
    perm_claimed_repr: &FieldVar<F>,
    endo: F,
) -> SnarkyResult<Boolean<F>> {
    let core = finalize_core(
        sys,
        loc.clone(),
        sponge_inputs,
        claimed_xi,
        cip_entries,
        endo,
    )?;
    let zetaw = zeta.scale(domain_generator);
    let b_derived = b_actual(sys, loc.clone(), b_chals, zeta, &zetaw, &core.r_field)?;
    let cip_claimed = type1_to_field(cip_claimed_repr);
    let b_claimed = type1_to_field(b_claimed_repr);
    let perm_claimed = type1_to_field(perm_claimed_repr);
    finalize_all(
        sys,
        loc,
        &core.xi_correct,
        &core.combined_inner_product,
        &cip_claimed,
        &b_derived,
        &b_claimed,
        perm_derived,
        &perm_claimed,
    )
}

/// Compile-time data for [`finalize_deferred`]: the linearization
/// constant-term tokens, the step domain, and the field constants.
pub struct FinalizeParams<'a, F: PrimeField> {
    /// The linearization constant-term (from the step verifier index).
    pub tokens: &'a [kimchi::circuits::expr::PolishToken<
        F,
        kimchi::circuits::berkeley_columns::Column,
        kimchi::circuits::berkeley_columns::BerkeleyChallengeTerm,
    >],
    /// The step proof's evaluation domain (fixed constant or the pseudo
    /// domain one-hot selected by the previous proof's `branch_data`).
    pub domain: crate::ft_eval_circuit::FinalizeDomain<F>,
    /// log2 of the SRS length.
    pub srs_log2: u32,
    /// The expression-evaluation endo coefficient (`index.endo`).
    pub endo: F,
    /// The permutation shifts of the verifier index.
    pub shifts: &'a [F],
    /// The scalar endomorphism for challenge-to-field conversion.
    pub endo_r: F,
    /// The Poseidon MDS matrix of the proof curve's sponge (for `Mds` tokens
    /// in the linearization).
    pub mds: &'a [Vec<F>],
    /// The `Shifted_value` convention of the claimed deferred values
    /// ([`ShiftKind::Type1`] in a step circuit, [`ShiftKind::Type2`] in a wrap
    /// circuit).
    pub shift: ShiftKind,
}

/// The witness [`finalize_deferred`] consumes: the statement's deferred values
/// and the previous proof's evaluations, all as circuit variables.
///
/// `alpha`/`zeta` are already converted to field form (the raw scalar
/// challenges go through [`scalar_to_field`] in the caller — OCaml's
/// `map_plonk_to_field`); `beta`/`gamma` are the raw 128-bit challenges used
/// directly as field elements. The bulletproof prechallenges are *raw* and
/// converted in here (`compute_challenges ~scalar`).
pub struct FinalizeWitness<F: PrimeField> {
    // plonk challenges (field form for alpha/zeta, raw for beta/gamma)
    pub alpha: FieldVar<F>,
    pub beta: FieldVar<F>,
    pub gamma: FieldVar<F>,
    pub zeta: FieldVar<F>,
    // claimed deferred values
    /// Claimed `xi`, raw 128-bit.
    pub xi: FieldVar<F>,
    /// `Shifted_value.Type1` representative of the claimed combined inner product.
    pub cip_repr: FieldVar<F>,
    /// `Shifted_value.Type1` representative of the claimed `b`.
    pub b_repr: FieldVar<F>,
    /// `Shifted_value.Type1` representative of the claimed `perm` scalar.
    pub perm_repr: FieldVar<F>,
    /// The new bulletproof prechallenges, raw 128-bit.
    pub bulletproof_challenges: Vec<FieldVar<F>>,
    // proof evaluations
    /// `sponge_digest_before_evaluations` (seeds the Fr-sponge).
    pub digest: FieldVar<F>,
    /// Previous challenge digests (logically empty in a base branch, or
    /// physically padded for a fixed-width program).
    pub prev_challenges: Vec<Vec<FieldVar<F>>>,
    /// Dynamic branch mask for a fixed-width previous-challenge vector.
    /// `None` preserves the historical fixed-arity path.
    pub prev_challenge_mask: Option<Vec<Boolean<F>>>,
    pub ft_eval1: FieldVar<F>,
    pub public_evals: [Vec<FieldVar<F>>; 2],
    /// All column evaluations, chunked (`AbsorbEvalsVar`); single-chunk in the
    /// base case.
    pub evals: crate::fr_sponge::AbsorbEvalsVar<F>,
}

/// The output of [`finalize_deferred`]: the conjunction boolean and the new
/// bulletproof challenges in field form (threaded into the statement by
/// `verify_one`), plus the intermediate values for white-box testing.
pub struct FinalizedDeferred<F: PrimeField> {
    pub finalized: Boolean<F>,
    /// The bulletproof challenges converted to field form
    /// (`compute_challenges`).
    pub challenges: Vec<FieldVar<F>>,
    /// `xi` as a field element (from the claimed raw challenge).
    pub xi_field: FieldVar<F>,
    /// `r` as a field element (squeezed from the Fr-sponge).
    pub r_field: FieldVar<F>,
    /// The re-derived combined inner product.
    pub combined_inner_product: FieldVar<F>,
    /// The raw 128-bit `xi` comparison conjunct.
    pub xi_correct: Boolean<F>,
    pub cip_correct: Boolean<F>,
    pub b_correct: Boolean<F>,
    pub perm_correct: Boolean<F>,
}

/// Resolves a linearization column to its `(zeta, zeta_omega)` evaluation
/// chunk-0 variables (the in-circuit `combined.evaluate(col)` for the
/// single-chunk case).
fn column_eval<'a, F: PrimeField>(
    evals: &'a crate::fr_sponge::AbsorbEvalsVar<F>,
    col: &kimchi::circuits::berkeley_columns::Column,
) -> &'a crate::fr_sponge::PointEvalVar<F> {
    use kimchi::circuits::{berkeley_columns::Column, gate::GateType};
    match col {
        Column::Witness(i) => &evals.w[*i],
        Column::Z => &evals.z,
        Column::Index(GateType::Generic) => &evals.generic_selector,
        Column::Index(GateType::Poseidon) => &evals.poseidon_selector,
        Column::Index(GateType::CompleteAdd) => &evals.complete_add_selector,
        Column::Index(GateType::VarBaseMul) => &evals.mul_selector,
        Column::Index(GateType::EndoMul) => &evals.emul_selector,
        Column::Index(GateType::EndoMulScalar) => &evals.endomul_scalar_selector,
        Column::Coefficient(i) => &evals.coefficients[*i],
        Column::Permutation(i) => &evals.s[*i],
        c => panic!("finalize_deferred: unsupported column {c:?}"),
    }
}

/// The full deferred-value finalization from statement witness data (the body
/// of OCaml's `finalize_other_proof` including its steps 1–3, which the
/// [`finalize_other_proof`] entry point above leaves to the caller):
/// builds the in-circuit scalars environment from the plonk challenges,
/// evaluates the linearization constant term and `ft_eval0`, derives the
/// permutation scalar, converts the bulletproof prechallenges to field form,
/// assembles the inner-product entries (public, `[ft0, ft1]`, mandatory
/// columns) and runs the four-conjunct check.
///
/// Base subset: single-chunk evaluations, no lookups.
pub fn finalize_deferred<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    params: &FinalizeParams<'_, F>,
    witness: &FinalizeWitness<F>,
) -> SnarkyResult<FinalizedDeferred<F>> {
    use crate::{
        ft_eval_circuit::{scalars_env_circuit, EvalsVar},
        plonk_checks::ZK_ROWS,
    };
    use kimchi::circuits::gate::CurrOrNext;

    let evals = &witness.evals;

    // == OCaml finalize_other_proof order (wrap_verifier.ml:1495-1786) ==

    // Step 1b (step side): OCaml `domain_for_compiled` (step_verifier.ml:
    // 876-887) materializes the pseudo-domain one-hot HERE — its equality
    // gadgets sit between the caller's plonk scalar conversions and the
    // `zetaw` multiply.
    let domain: crate::ft_eval_circuit::FinalizeDomain<F> = match &params.domain {
        crate::ft_eval_circuit::FinalizeDomain::SelectFrom { log2s, domain_log2 } => {
            crate::ft_eval_circuit::FinalizeDomain::Selected(
                crate::ft_eval_circuit::SelectedDomain::create(
                    sys,
                    loc.clone(),
                    log2s,
                    domain_log2,
                )?,
            )
        }
        other => other.clone(),
    };

    // Step 2: zetaw = domain generator * zeta (the generator is a constant
    // for a Fixed domain and a mask-constants linear combination for a
    // Selected pseudo-domain — no rows before the multiply itself).
    let zetaw = match &domain {
        crate::ft_eval_circuit::FinalizeDomain::Fixed(d) => witness.zeta.scale(d.group_gen),
        crate::ft_eval_circuit::FinalizeDomain::Selected(sel) => {
            sel.generator_var()
                .mul(&witness.zeta, None, loc.clone(), sys)?
        }
        crate::ft_eval_circuit::FinalizeDomain::SelectFrom { .. } => {
            unreachable!("materialized above")
        }
    };

    // Step 3: sg_evals — the OLD challenge polynomials evaluated at zeta,
    // then all of them at zetaw (`(sg_evals zeta, sg_evals zetaw)`).
    let mut sg_at_zeta = Vec::with_capacity(witness.prev_challenges.len());
    let mut sg_at_zetaw = Vec::with_capacity(witness.prev_challenges.len());
    for old_challenges in &witness.prev_challenges {
        sg_at_zeta.push(crate::ipa::challenge_polynomial_circuit(
            sys,
            loc.clone(),
            old_challenges,
            &witness.zeta,
        )?);
    }
    for old_challenges in &witness.prev_challenges {
        sg_at_zetaw.push(crate::ipa::challenge_polynomial_circuit(
            sys,
            loc.clone(),
            old_challenges,
            &zetaw,
        )?);
    }
    let mut masked_cip_entries = Vec::new();
    let mut cip_entries = Vec::with_capacity(witness.prev_challenges.len() + 2);
    for (index, (at_zeta, at_zetaw)) in sg_at_zeta.into_iter().zip(sg_at_zetaw).enumerate() {
        if let Some(mask) = &witness.prev_challenge_mask {
            assert_eq!(mask.len(), witness.prev_challenges.len());
            masked_cip_entries.push((mask[index].clone(), at_zeta, at_zetaw));
        } else {
            cip_entries.push((at_zeta, at_zetaw));
        }
    }

    // Steps 4-5: reconstruct the fr-sponge, squeeze xi and r, convert.
    let sponge_inputs = FrSpongeInputs {
        digest: witness.digest.clone(),
        prev_challenges: witness.prev_challenges.clone(),
        prev_challenge_mask: witness.prev_challenge_mask.clone(),
        ft_eval1: witness.ft_eval1.clone(),
        public_evals: witness.public_evals.clone(),
        evals: evals.clone(),
        // step (Type1) constrains both xi halves; wrap (Type2) only the high
        xi_constrain_low_bits: matches!(params.shift, ShiftKind::Type1),
    };
    let (xi_actual, r_actual) = squeeze_xi_r(sys, loc.clone(), &sponge_inputs)?;
    let xi_correct = xi_actual.equal(sys, loc.clone(), &witness.xi)?;
    let xi_field = scalar_to_field(
        sys,
        Cow::Owned(format!("{loc} | xi to_field")),
        &witness.xi,
        params.endo_r,
    )?;
    let r_field = scalar_to_field(
        sys,
        Cow::Owned(format!("{loc} | r to_field")),
        &r_actual,
        params.endo_r,
    )?;

    // Step 6: combined_evals. Single-chunk evaluations combine to
    // themselves, but OCaml still emits the `zeta^{2^n}` / `zetaw^{2^n}`
    // squaring chains (the "zeta_n is recomputed in env" TODO wart,
    // wrap_verifier.ml:1628-1630) — byte parity requires the dead rows.
    {
        let mut zeta_n = witness.zeta.clone();
        let mut zetaw_n = zetaw.clone();
        let chain_loc: Cow<'static, str> = Cow::Owned(format!("{loc} | dead pow chains"));
        for _ in 0..params.srs_log2 {
            zeta_n = crate::expr_eval::square_circuit(sys, chain_loc.clone(), &zeta_n)?;
        }
        for _ in 0..params.srs_log2 {
            zetaw_n = crate::expr_eval::square_circuit(sys, chain_loc.clone(), &zetaw_n)?;
        }
    }

    // Step 7: scalars environment from the (field-form) challenges
    let env = scalars_env_circuit(
        sys,
        Cow::Owned(format!("{loc} | env")),
        &domain,
        params.srs_log2,
        &witness.alpha,
        witness.beta.clone(),
        witness.gamma.clone(),
        &witness.zeta,
    )?;

    // single-chunk combined evaluations for ft_eval0 / perm
    let chunk0 = |pe: &crate::fr_sponge::PointEvalVar<F>| -> (FieldVar<F>, FieldVar<F>) {
        assert_eq!(pe.0.len(), 1, "finalize_deferred: single-chunk only");
        (pe.0[0].clone(), pe.1[0].clone())
    };
    let ft_evals = EvalsVar {
        w: evals.w.iter().map(&chunk0).collect(),
        s: evals.s.iter().map(&chunk0).collect(),
        z: chunk0(&evals.z),
    };

    // Step 8a: ft_eval0 — the linearization constant term, evaluated on the
    // same witness columns, then the ft_eval0 formula.
    let column = |col: kimchi::circuits::berkeley_columns::Column, row: CurrOrNext| {
        let pe = column_eval(evals, &col);
        match row {
            CurrOrNext::Curr => pe.0[0].clone(),
            CurrOrNext::Next => pe.1[0].clone(),
        }
    };
    // The linearization constant term follows the EXACT generated-code tree
    // of OCaml's `Scalars.{Tick,Tock}.constant_term` — kimchi's PolishToken
    // stream computes the same value with a different gadget sequence.
    let scalars_env = crate::scalars_ml::ScalarsMlEnv {
        column: &column,
        alpha_pows: &env.alpha_pows,
        beta: witness.beta.clone(),
        gamma: witness.gamma.clone(),
        endo_coefficient: params.endo,
        mds: params.mds,
        zk_polynomial: env.zk_polynomial.clone(),
        zeta_to_n_minus_1: env.zeta_to_n_minus_1.clone(),
        domain: match &domain {
            crate::ft_eval_circuit::FinalizeDomain::Fixed(d) => {
                crate::scalars_ml::ScalarsMlDomain::Fixed(*d)
            }
            crate::ft_eval_circuit::FinalizeDomain::Selected(_) => {
                crate::scalars_ml::ScalarsMlDomain::Selected {
                    omegas: env.omegas.clone(),
                    omega_to_zk_minus_1: std::cell::RefCell::new(None),
                }
            }
            crate::ft_eval_circuit::FinalizeDomain::SelectFrom { .. } => {
                unreachable!("materialized above")
            }
        },
        zeta: witness.zeta.clone(),
        zk_rows: ZK_ROWS as u64,
    };
    // OCaml ft_eval0 order (plonk_checks.ml:349-399): the ft body and the
    // nominator/denominator division come FIRST; `Sc.constant_term env` is
    // evaluated LAST and subtracted.
    let ft_prefix = crate::ft_eval_circuit::ft_eval0_prefix_circuit(
        sys,
        Cow::Owned(format!("{loc} | ft_eval0")),
        &env,
        params.shifts,
        &ft_evals,
        &witness.public_evals[0],
    )?;
    let constant_term = crate::scalars_ml::eval_constant_term(
        sys,
        Cow::Owned(format!("{loc} | linearization")),
        match params.shift {
            ShiftKind::Type1 => crate::scalars_ml::ScalarsKind::Tick,
            ShiftKind::Type2 => crate::scalars_ml::ScalarsKind::Tock,
        },
        &scalars_env,
    )?;
    let ft_eval0 = &ft_prefix - &constant_term;

    // Step 8b-8c: the combined inner product fold and its check
    cip_entries.extend([
        (
            witness.public_evals[0][0].clone(),
            witness.public_evals[1][0].clone(),
        ),
        (ft_eval0, witness.ft_eval1.clone()),
    ]);
    for col in crate::ipa::mandatory_columns() {
        cip_entries.push(chunk0(column_eval(evals, &col)));
    }
    let combined_inner_product = if masked_cip_entries.is_empty() {
        combined_inner_product_circuit(
            sys,
            Cow::Owned(format!("{loc} | cip fold")),
            &xi_field,
            &r_field,
            &cip_entries,
        )?
    } else {
        combined_inner_product_circuit_masked(
            sys,
            Cow::Owned(format!("{loc} | cip fold masked")),
            &xi_field,
            &r_field,
            &masked_cip_entries,
            &cip_entries,
        )?
    };
    let cip_claimed = params.shift.to_field(&witness.cip_repr);
    let cip_correct = combined_inner_product.equal(sys, loc.clone(), &cip_claimed)?;

    // Step 9: the NEW bulletproof challenges to field form, then b_correct
    let mut challenges = Vec::with_capacity(witness.bulletproof_challenges.len());
    for pre in &witness.bulletproof_challenges {
        challenges.push(scalar_to_field(
            sys,
            Cow::Owned(format!("{loc} | bp-challenge to_field")),
            pre,
            params.endo_r,
        )?);
    }
    let b_derived = b_actual(
        sys,
        loc.clone(),
        &challenges,
        &witness.zeta,
        &zetaw,
        &r_field,
    )?;
    let b_claimed = params.shift.to_field(&witness.b_repr);
    let b_correct = b_derived.equal(sys, loc.clone(), &b_claimed)?;

    // Step 10: the PlonK relation (the deferred permutation scalar).
    // OCaml `derive_plonk` computes the perm fold, then builds the derived
    // record — whose `zeta_to_srs_length = Lazy.force env.zeta_to_srs_length`
    // FORCES the lazy `ζ^{2^srs_log2}` mul chain HERE (plonk_checks.ml:436),
    // its first (and only) use in a single-chunk finalize. The value itself
    // is discarded (`checked` compares `perm` only).
    let perm_derived = crate::ft_eval_circuit::perm_scalar_circuit(
        sys,
        Cow::Owned(format!("{loc} | perm scalar")),
        &env,
        &ft_evals,
    )?;
    let _zeta_to_srs_length = crate::expr_eval::pow_circuit(
        sys,
        Cow::Owned(format!("{loc} | perm scalar")),
        &witness.zeta,
        1u64 << params.srs_log2,
    )?;
    let perm_claimed = params.shift.to_field(&witness.perm_repr);
    let perm_correct = perm_derived.equal(sys, loc.clone(), &perm_claimed)?;

    // Step 11: combine all checks
    let finalized = finalize_all(
        sys,
        loc,
        &xi_correct,
        &combined_inner_product,
        &cip_claimed,
        &b_derived,
        &b_claimed,
        &perm_derived,
        &perm_claimed,
    )?;

    Ok(FinalizedDeferred {
        finalized,
        challenges,
        xi_field,
        r_field,
        combined_inner_product,
        xi_correct,
        cip_correct,
        b_correct,
        perm_correct,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        fr_sponge::{AbsorbEvalsVar, PointEvalVar},
        plonk_checks::ZK_ROWS,
    };
    use ark_ff::{One, Zero};
    use ark_poly::Radix2EvaluationDomain as D;
    use kimchi::{
        circuits::{
            berkeley_columns::{BerkeleyChallengeTerm, Column},
            expr::PolishToken,
        },
        curve::KimchiCurve,
        proof::PointEvaluations,
    };
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::{commitment::PolyComm, ipa::OpeningProof, SRS};
    use snarky::{api::SnarkyCircuit, loc};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    struct SmallCircuit {}
    impl SnarkyCircuit for SmallCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = Fp;
        type PublicInput = FieldVar<Fp>;
        type PublicOutput = ();
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            z: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<()> {
            let x: FieldVar<Fp> = sys.compute(loc!(), |_| *private.unwrap())?;
            let xx = x.mul(&x, None, loc!(), sys)?;
            xx.assert_equals(sys, loc!(), &z)?;
            let _ = sys.poseidon(loc!(), (x, z));
            Ok(())
        }
    }

    /// Everything `finalize_deferred` needs, captured from a real proof.
    struct FinalizeCircuit {
        // compile-time params
        tokens: Vec<PolishToken<Fp, Column, BerkeleyChallengeTerm>>,
        domain: D<Fp>,
        srs_log2: u32,
        endo: Fp,
        shifts: Vec<Fp>,
        endo_r: Fp,
        // plonk challenges (field form for alpha/zeta)
        alpha: Fp,
        beta: Fp,
        gamma: Fp,
        zeta: Fp,
        // fr-sponge / evaluation inputs
        digest: Fp,
        ft_eval1: Fp,
        public_evals: [Vec<Fp>; 2],
        e_z: (Vec<Fp>, Vec<Fp>),
        generic: (Vec<Fp>, Vec<Fp>),
        poseidon: (Vec<Fp>, Vec<Fp>),
        complete_add: (Vec<Fp>, Vec<Fp>),
        mul: (Vec<Fp>, Vec<Fp>),
        emul: (Vec<Fp>, Vec<Fp>),
        endomul_scalar: (Vec<Fp>, Vec<Fp>),
        e_w: Vec<(Vec<Fp>, Vec<Fp>)>,
        coefficients: Vec<(Vec<Fp>, Vec<Fp>)>,
        e_s: Vec<(Vec<Fp>, Vec<Fp>)>,
        // claimed deferred values: raw xi, raw bulletproof prechallenges, and
        // the Type1-shifted cip/b/perm
        claimed_xi: Fp,
        bp_prechals: Vec<Fp>,
        cip_claimed_repr: Fp,
        b_claimed_repr: Fp,
        perm_claimed_repr: Fp,
    }

    impl SnarkyCircuit for FinalizeCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        // (((xi_field, r_field), (combined_inner_product, xi_correct)),
        //  finalize_other_proof_result)
        // (nested because SnarkyType tuples top out at arity 3)
        #[allow(clippy::type_complexity)]
        type PublicOutput = (
            ((FieldVar<Fp>, FieldVar<Fp>), (FieldVar<Fp>, FieldVar<Fp>)),
            FieldVar<Fp>,
        );

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            _private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let w1 = |sys: &mut RunState<Fp>, v: Fp| sys.compute(loc!(), move |_| v);
            let wvec = |sys: &mut RunState<Fp>, vs: &[Fp]| -> SnarkyResult<Vec<FieldVar<Fp>>> {
                let mut out = vec![];
                for &v in vs {
                    out.push(sys.compute(loc!(), move |_| v)?);
                }
                Ok(out)
            };
            let wvpair = |sys: &mut RunState<Fp>,
                          p: &(Vec<Fp>, Vec<Fp>)|
             -> SnarkyResult<PointEvalVar<Fp>> {
                Ok((wvec(sys, &p.0)?, wvec(sys, &p.1)?))
            };

            let mds: Vec<Vec<Fp>> = Vesta::sponge_params()
                .mds
                .iter()
                .map(|r| r.to_vec())
                .collect();
            let params = FinalizeParams {
                tokens: &self.tokens,
                domain: crate::ft_eval_circuit::FinalizeDomain::Fixed(self.domain),
                srs_log2: self.srs_log2,
                endo: self.endo,
                shifts: &self.shifts,
                endo_r: self.endo_r,
                mds: &mds,
                shift: ShiftKind::Type1,
            };
            let witness = FinalizeWitness {
                alpha: w1(sys, self.alpha)?,
                beta: w1(sys, self.beta)?,
                gamma: w1(sys, self.gamma)?,
                zeta: w1(sys, self.zeta)?,
                xi: w1(sys, self.claimed_xi)?,
                cip_repr: w1(sys, self.cip_claimed_repr)?,
                b_repr: w1(sys, self.b_claimed_repr)?,
                perm_repr: w1(sys, self.perm_claimed_repr)?,
                bulletproof_challenges: wvec(sys, &self.bp_prechals)?,
                digest: w1(sys, self.digest)?,
                prev_challenges: vec![],
                prev_challenge_mask: None,
                ft_eval1: w1(sys, self.ft_eval1)?,
                public_evals: [
                    wvec(sys, &self.public_evals[0])?,
                    wvec(sys, &self.public_evals[1])?,
                ],
                evals: AbsorbEvalsVar {
                    z: wvpair(sys, &self.e_z)?,
                    generic_selector: wvpair(sys, &self.generic)?,
                    poseidon_selector: wvpair(sys, &self.poseidon)?,
                    complete_add_selector: wvpair(sys, &self.complete_add)?,
                    mul_selector: wvpair(sys, &self.mul)?,
                    emul_selector: wvpair(sys, &self.emul)?,
                    endomul_scalar_selector: wvpair(sys, &self.endomul_scalar)?,
                    w: {
                        let mut v = vec![];
                        for p in &self.e_w {
                            v.push(wvpair(sys, p)?);
                        }
                        v
                    },
                    coefficients: {
                        let mut v = vec![];
                        for p in &self.coefficients {
                            v.push(wvpair(sys, p)?);
                        }
                        v
                    },
                    s: {
                        let mut v = vec![];
                        for p in &self.e_s {
                            v.push(wvpair(sys, p)?);
                        }
                        v
                    },
                },
            };

            let out = finalize_deferred(sys, loc!(), &params, &witness)?;

            Ok((
                (
                    (out.xi_field, out.r_field),
                    (out.combined_inner_product, out.xi_correct.to_field_var()),
                ),
                out.finalized.to_field_var(),
            ))
        }
    }

    /// captured (field-form) bulletproof challenges + points, replayed to check
    /// the in-circuit `b_actual` against the out-of-circuit reference.
    struct BActualCircuit {
        chals: Vec<Fp>,
        zeta: Fp,
        gen: Fp,
        r: Fp,
    }
    impl SnarkyCircuit for BActualCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = FieldVar<Fp>;
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<FieldVar<Fp>> {
            let mut chals = vec![];
            for &c in &self.chals {
                chals.push(sys.compute(loc!(), move |_| c)?);
            }
            let zeta: FieldVar<Fp> = sys.compute(loc!(), |_| self.zeta)?;
            let r: FieldVar<Fp> = sys.compute(loc!(), |_| self.r)?;
            let zetaw = zeta.scale(self.gen);
            b_actual(sys, loc!(), &chals, &zeta, &zetaw, &r)
        }
    }

    /// In-circuit `b_actual` = h(zeta) + r*h(zetaw) equals the out-of-circuit
    /// reference on challenges derived from real prechallenges.
    #[test]
    fn b_actual_matches_reference() {
        use crate::{
            common::TOCK_ROUNDS,
            ipa::{challenge_polynomial, compute_challenges},
            scalar_challenge::ScalarChallenge,
        };
        use ark_ff::UniformRand;

        let mut rng = o1_utils::tests::make_test_rng(None);
        let (_, endo_r) = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();

        let prechallenges: Vec<_> = (0..TOCK_ROUNDS)
            .map(|_| crate::composition_types::BulletproofChallenge {
                prechallenge: ScalarChallenge(Fp::from(u128::rand(&mut rng))),
            })
            .collect();
        let chals = compute_challenges(&prechallenges, *endo_r);

        let domain_gen = {
            use ark_poly::EvaluationDomain;
            D::<Fp>::new(1 << 5).unwrap().group_gen
        };
        let zeta = Fp::rand(&mut rng);
        let r = Fp::rand(&mut rng);
        let zetaw = domain_gen * zeta;
        let expected = challenge_polynomial(&chals, zeta) + r * challenge_polynomial(&chals, zetaw);

        let circ = BActualCircuit {
            chals,
            zeta,
            gen: domain_gen,
            r,
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(*out, expected, "in-circuit b_actual matches reference");
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }

    /// The full finalize arithmetic core (sponge -> scalar_to_field -> cip, with
    /// in-circuit ft_eval0) reproduces kimchi's oracles on a real proof.
    #[test]
    fn finalize_core_matches_kimchi() {
        let mut pi = SmallCircuit {}.compile_to_indexes().unwrap().0;
        let vi = SmallCircuit {}.compile_to_indexes().unwrap().1;
        let vi = &vi.index;
        let x = Fp::from(8u64);
        let z = x * x;
        let (proof, _) = pi.prove::<BaseSponge, ScalarSponge>(z, x, true).unwrap();

        let public_input = vec![z];
        let lgr = vi.srs().get_lagrange_basis(vi.domain);
        let com: Vec<_> = lgr.iter().take(vi.public).collect();
        let elm: Vec<_> = public_input.iter().map(|s| -*s).collect();
        let pc = PolyComm::<Vesta>::multi_scalar_mul(&com, &elm);
        let public_comm = vi
            .srs()
            .mask_custom(pc.clone(), &pc.map(|_| Fp::one()))
            .unwrap()
            .commitment;
        let o = proof
            .oracles::<BaseSponge, ScalarSponge, _>(vi, &public_comm, Some(&public_input))
            .unwrap();
        let oracles = &o.oracles;
        let combined = proof.evals.combine(&o.powers_of_eval_points_for_chunks);

        let srs_log2 = u64::BITS - 1 - (vi.max_poly_size as u64).leading_zeros();

        // fr-sponge column captures
        let e = &proof.evals;
        let pair = |p: &PointEvaluations<Vec<Fp>>| (p.zeta.clone(), p.zeta_omega.clone());

        let (_, endo_r) = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();

        // ---- prover-side deferred values (expand_deferred) for the claimed
        //      Type1-shifted cip/b/perm and the new bulletproof challenges ----
        let domain = crate::plonk_checks::Domain::<Fp> {
            log2_size: vi.domain.log_size_of_group,
            generator: vi.domain.group_gen,
        };
        let minimal = crate::composition_types::plonk::Minimal::<Fp, Fp, bool> {
            alpha: oracles.alpha,
            beta: oracles.beta,
            gamma: oracles.gamma,
            zeta: oracles.zeta,
            joint_combiner: None,
            feature_flags: crate::composition_types::Features::none(),
        };
        let env_ooc = crate::plonk_checks::scalars_env::<Fp, bool>(&domain, srs_log2, &minimal);
        let evals_ooc = crate::plonk_checks::Evals {
            w: combined.w.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
            s: combined.s.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
            z: (combined.z.zeta, combined.z.zeta_omega),
        };
        let ft_eval0_ooc = {
            use kimchi::circuits::{berkeley_columns::BerkeleyChallenges, expr::Constants};
            let constants = Constants {
                endo_coefficient: vi.endo,
                mds: &Vesta::sponge_params().mds,
                zk_rows: ZK_ROWS as u64,
            };
            let challenges = BerkeleyChallenges {
                alpha: oracles.alpha,
                beta: oracles.beta,
                gamma: oracles.gamma,
                joint_combiner: Fp::zero(),
            };
            let ct = PolishToken::evaluate(
                &vi.linearization.constant_term,
                vi.domain,
                oracles.zeta,
                &combined,
                &constants,
                &challenges,
            )
            .unwrap();
            crate::plonk_checks::ft_eval0(&env_ooc, &vi.shift, &evals_ooc, &o.public_evals[0], ct)
        };
        let zeta_v = oracles.zeta;
        let zetaw_v = zeta_v * vi.domain.group_gen;
        use ark_ff::UniformRand;
        let mut rng = o1_utils::tests::make_test_rng(None);
        let prechallenges: Vec<
            crate::composition_types::BulletproofChallenge<
                crate::scalar_challenge::ScalarChallenge<Fp>,
            >,
        > = (0..16)
            .map(|_| crate::composition_types::BulletproofChallenge {
                prechallenge: crate::scalar_challenge::ScalarChallenge(Fp::from(u128::rand(
                    &mut rng,
                ))),
            })
            .collect();
        let dv = crate::wrap_deferred_values::expand_deferred(
            oracles.v,
            oracles.u,
            &[],
            &o.public_evals,
            ft_eval0_ooc,
            proof.ft_eval1,
            &proof.evals,
            zeta_v,
            zetaw_v,
            &prechallenges,
            *endo_r,
            &env_ooc,
            &evals_ooc,
        );

        // the raw 128-bit `v_chal` (opaque in RandomOracles) — replay the
        // Fr-sponge out of circuit via the public `squeeze` API, exactly as
        // `challenge()` does (`squeeze(CHALLENGE_LENGTH_IN_LIMBS)`).
        let claimed_xi = {
            use kimchi::plonk_sponge::FrSponge as _;
            let params = Vesta::sponge_params();
            let mut fr = ScalarSponge::from(params);
            fr.absorb(&o.digest);
            let pcd = ScalarSponge::from(params).digest();
            fr.absorb(&pcd);
            fr.absorb(&proof.ft_eval1);
            fr.absorb_multiple(&o.public_evals[0]);
            fr.absorb_multiple(&o.public_evals[1]);
            fr.absorb_evaluations(&proof.evals);
            fr.squeeze(mina_poseidon::sponge::CHALLENGE_LENGTH_IN_LIMBS)
        };

        let circ = FinalizeCircuit {
            tokens: vi.linearization.constant_term.clone(),
            domain: vi.domain,
            srs_log2,
            endo: vi.endo,
            shifts: vi.shift.to_vec(),
            endo_r: *endo_r,
            alpha: oracles.alpha,
            beta: oracles.beta,
            gamma: oracles.gamma,
            zeta: oracles.zeta,
            digest: o.digest,
            ft_eval1: proof.ft_eval1,
            public_evals: o.public_evals.clone(),
            e_z: pair(&e.z),
            generic: pair(&e.generic_selector),
            poseidon: pair(&e.poseidon_selector),
            complete_add: pair(&e.complete_add_selector),
            mul: pair(&e.mul_selector),
            emul: pair(&e.emul_selector),
            endomul_scalar: pair(&e.endomul_scalar_selector),
            e_w: e.w.iter().map(pair).collect(),
            coefficients: e.coefficients.iter().map(pair).collect(),
            e_s: e.s.iter().map(pair).collect(),
            claimed_xi,
            bp_prechals: prechallenges.iter().map(|c| c.prechallenge.0).collect(),
            cip_claimed_repr: dv.combined_inner_product,
            b_claimed_repr: dv.b,
            perm_claimed_repr: dv.perm,
        };

        let (mut fpi, fver) = circ.compile_to_indexes().unwrap();
        let (fproof, out) = fpi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        let (((xi_field, r_field), (cip, xi_correct)), finalized) = *out.clone();

        assert_eq!(xi_field, oracles.v, "xi (field) matches kimchi");
        assert_eq!(r_field, oracles.u, "r (field) matches kimchi");
        assert_eq!(
            cip, o.combined_inner_product,
            "combined inner product matches"
        );
        assert_eq!(xi_correct, Fp::one(), "xi_correct is true");
        // full finalize_other_proof accepts: derived == claimed for all four
        // conjuncts (cip/b/perm recovered from expand_deferred's Type1 reprs)
        assert_eq!(
            finalized,
            Fp::one(),
            "finalize_other_proof accepts a real proof"
        );

        fver.verify::<BaseSponge, ScalarSponge>(fproof, (), *out);
    }

    /// Exercises the `finalize_all` combiner: the four derived values are
    /// compared to the claimed ones and AND-ed together. Witnesses the pairs
    /// directly so the test isolates the combiner (each derivation is validated
    /// in its own module).
    struct CombineCircuit {
        xi_actual: Fp,
        xi_claimed: Fp,
        cip_derived: Fp,
        cip_claimed: Fp,
        b_derived: Fp,
        b_claimed: Fp,
        perm_derived: Fp,
        perm_claimed: Fp,
    }
    impl SnarkyCircuit for CombineCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = FieldVar<Fp>;
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<FieldVar<Fp>> {
            let w = |sys: &mut RunState<Fp>, v: Fp| sys.compute(loc!(), move |_| v);
            let xi_a: FieldVar<Fp> = w(sys, self.xi_actual)?;
            let xi_c: FieldVar<Fp> = w(sys, self.xi_claimed)?;
            let xi_correct = xi_a.equal(sys, loc!(), &xi_c)?;
            let cip_d: FieldVar<Fp> = w(sys, self.cip_derived)?;
            let cip_c: FieldVar<Fp> = w(sys, self.cip_claimed)?;
            let b_d: FieldVar<Fp> = w(sys, self.b_derived)?;
            let b_c: FieldVar<Fp> = w(sys, self.b_claimed)?;
            let perm_d: FieldVar<Fp> = w(sys, self.perm_derived)?;
            let perm_c: FieldVar<Fp> = w(sys, self.perm_claimed)?;
            let all = finalize_all(
                sys,
                loc!(),
                &xi_correct,
                &cip_d,
                &cip_c,
                &b_d,
                &b_c,
                &perm_d,
                &perm_c,
            )?;
            all.to_field_var().seal(sys, loc!())
        }
    }

    /// finalize_all yields 1 iff all four conjuncts match, 0 otherwise.
    #[test]
    fn finalize_all_accepts_and_rejects() {
        let base = CombineCircuit {
            xi_actual: Fp::from(11u64),
            xi_claimed: Fp::from(11u64),
            cip_derived: Fp::from(22u64),
            cip_claimed: Fp::from(22u64),
            b_derived: Fp::from(33u64),
            b_claimed: Fp::from(33u64),
            perm_derived: Fp::from(44u64),
            perm_claimed: Fp::from(44u64),
        };
        let run = |c: CombineCircuit| {
            let (mut pi, ver) = c.compile_to_indexes().unwrap();
            let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
            ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
            *out
        };

        // all match -> true
        assert_eq!(run(base_clone(&base)), Fp::one());

        // tamper each conjunct in turn -> false
        let mut c = CombineCircuit {
            xi_claimed: Fp::from(99u64),
            ..base_clone(&base)
        };
        assert_eq!(run(c), Fp::zero(), "xi mismatch rejects");
        c = CombineCircuit {
            cip_claimed: Fp::from(99u64),
            ..base_clone(&base)
        };
        assert_eq!(run(c), Fp::zero(), "cip mismatch rejects");
        c = CombineCircuit {
            b_claimed: Fp::from(99u64),
            ..base_clone(&base)
        };
        assert_eq!(run(c), Fp::zero(), "b mismatch rejects");
        c = CombineCircuit {
            perm_claimed: Fp::from(99u64),
            ..base_clone(&base)
        };
        assert_eq!(run(c), Fp::zero(), "perm mismatch rejects");
    }

    fn base_clone(b: &CombineCircuit) -> CombineCircuit {
        CombineCircuit {
            xi_actual: b.xi_actual,
            xi_claimed: b.xi_claimed,
            cip_derived: b.cip_derived,
            cip_claimed: b.cip_claimed,
            b_derived: b.b_derived,
            b_claimed: b.b_claimed,
            perm_derived: b.perm_derived,
            perm_claimed: b.perm_claimed,
        }
    }

    struct Type1RecoverCircuit {
        repr: Fp,
    }
    impl SnarkyCircuit for Type1RecoverCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = FieldVar<Fp>;
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<FieldVar<Fp>> {
            let repr: FieldVar<Fp> = sys.compute(loc!(), |_| self.repr)?;
            Ok(type1_to_field(&repr))
        }
    }

    /// The in-circuit `type1_to_field` inverts `expand_deferred`'s Type1 shift:
    /// `finalize` recovers the same field value the prover shifted with
    /// [`crate::shifted_value::type1_of_field`] (the `shift1` convention of
    /// `finalize_other_proof`, not Type2).
    #[test]
    fn type1_recovery_inverts_of_field() {
        use ark_ff::UniformRand;
        let mut rng = o1_utils::tests::make_test_rng(None);
        for _ in 0..2 {
            let s = Fp::rand(&mut rng);
            let repr = crate::shifted_value::type1_of_field(s);
            let circ = Type1RecoverCircuit { repr };
            let (mut pi, ver) = circ.compile_to_indexes().unwrap();
            let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
            assert_eq!(*out, s, "in-circuit Type1 recovery");
            ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
        }
    }
}

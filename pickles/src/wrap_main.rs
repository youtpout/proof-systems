//! The wrap circuit body (`wrap_main.ml`, lines ~330–525): finalizes each
//! unfinalized proof carried by the step statement, recomputes the previous
//! `messages_for_next_wrap_proof` digests, commits to the step statement and
//! fully verifies the step proof.
//!
//! ```text
//! for each unfinalized i in the step statement:
//!     (finalized_i, chals_i) = finalize_deferred(Type2, ...)
//!     Boolean.Assert.any [finalized_i; not should_finalize_i]
//! prev_msgs_wrap_i = hash_messages_for_next_wrap_proof(old_chals_i, sg_old_i)
//! terms  = step statement (full-field elements split via split_field)
//! result = verify(step proof, terms, ...)         // x_hat + IVP + asserts
//! Boolean.Assert.is_true result                   // unlike the step side
//! assert msgs_next_wrap_digest ==
//!     hash_messages_for_next_wrap_proof([chals_i], openings.sg)
//! ```
//!
//! The step-proof transcript asserts (sponge digest, bulletproof challenges,
//! plonk challenges) are unconditional on this side (no base case), which
//! [`verify`] realises unconditionally.

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{
    gadgets::curve::Point, runner::WitnessGeneration, Boolean, FieldVar, RunState, SnarkyResult,
};

pub use crate::public_input::StatementElement as StepStatementElement;
use crate::{
    finalize::{finalize_deferred, FinalizeParams, FinalizeWitness},
    hash_messages::hash_messages_for_next_wrap_proof,
    incrementally_verify::{
        Advice, IndexDigest, Messages, OpeningProof, VerificationKeyComm, XHatInput,
    },
    scalar_challenge::scalar_to_field,
    step_verifier::{verify, Claimed},
};

/// One unfinalized proof of the step statement, as handled by [`wrap_main`].
pub struct PerUnfinalized<'a, F: PrimeField> {
    /// Finalization parameters ([`crate::finalize::ShiftKind::Type2`] on this
    /// side) for the wrap proof the unfinalized entry refers to. The `domain`
    /// carried here is replaced inside [`wrap_main`] by the one-hot-selected
    /// pseudo domain (OCaml witnesses `Req.Wrap_domain_indices` and selects
    /// among the three possible wrap domains in-circuit, wrap_main.ml:352-368).
    pub finalize_params: FinalizeParams<'a, F>,
    /// The witnessed wrap-domain index (`Common.actual_wrap_domain_size`:
    /// log2 13 → 0, 14 → 1, 15 → 2) of the wrap proof being finalized.
    pub wrap_domain_index: F,
    pub finalize_evals: crate::step_verifier::FinalizeEvals<F>,
    // the unfinalized deferred values (raw challenges, Type2 representatives)
    pub alpha: FieldVar<F>,
    pub beta: FieldVar<F>,
    pub gamma: FieldVar<F>,
    pub zeta: FieldVar<F>,
    pub xi: FieldVar<F>,
    pub cip_repr: FieldVar<F>,
    pub b_repr: FieldVar<F>,
    pub perm_repr: FieldVar<F>,
    pub bulletproof_challenges: Vec<FieldVar<F>>,
    pub sponge_digest_before_evaluations: FieldVar<F>,
    pub should_finalize: Boolean<F>,
    /// The previous accumulator this unfinalized proof carries: its old
    /// bulletproof challenges and challenge-polynomial commitment (`sg_old`).
    pub old_bulletproof_challenges: Vec<Vec<FieldVar<F>>>,
    pub prev_step_acc: Point<F>,
    /// Dummy challenge-vector constants padding the accumulator hash
    /// (`Wrap_hack`; empty at full width).
    pub hash_dummy_challenges: Vec<Vec<F>>,
    /// Old challenges included in the accumulator hash. They are separate
    /// from the proof's Fr-sponge `old_bulletproof_challenges`.
    pub hash_old_bulletproof_challenges: Vec<Vec<FieldVar<F>>>,
}

/// The output of [`wrap_main`]: the recomputed previous
/// `messages_for_next_wrap_proof` digests (part of the step statement this
/// circuit commits to) and the new bulletproof challenges per unfinalized.
pub struct WrapMainOutput<F: PrimeField> {
    pub prev_messages_for_next_wrap_proof: Vec<FieldVar<F>>,
    pub new_bulletproof_challenges: Vec<Vec<FieldVar<F>>>,
}

/// Runs the wrap circuit body. `step_statement_elements`/`lagranges` describe
/// the step proof's public input; `claimed` carries this wrap statement's own
/// deferred transcript values (asserted unconditionally);
/// `messages_for_next_wrap_proof_digest` is this statement's digest,
/// asserted against the recomputed hash of the *new* accumulator.
#[allow(clippy::too_many_arguments)]
pub fn wrap_main<F, C, W>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    unfinalized: &[PerUnfinalized<'_, F>],
    // `Wrap_verifier.mask (which_branch, step_widths)` (wrap_main.ml:165) —
    // computed by the caller right after `which_branch`, where OCaml emits it.
    actual_proofs_verified_mask: &[Boolean<F>],
    // Physical backend accumulators, padded independently of `unfinalized`.
    sg_olds: &[Point<F>],
    // the step proof + its statement (the verifier-index digest is computed
    // inside `incrementally_verify_proof` from `vk`, as in OCaml)
    vk: &VerificationKeyComm<F>,
    step_statement_elements: &[StepStatementElement<F>],
    lagranges: &crate::public_input::StatementLagranges<'_, F>,
    h_generator: &Point<F>,
    // Witnesses `openings_proof` (wrap_main.ml:440) then `messages` (:470):
    // called after the finalize/hash-prev block so the `exists` constraints
    // land exactly where OCaml emits them.
    witness_proof: W,
    advice: &Advice<F>,
    xi: &FieldVar<F>,
    claimed: &Claimed<F>,
    // this statement's accumulator digest
    messages_for_next_wrap_proof_digest: &FieldVar<F>,
    new_acc_dummy_challenges: &[Vec<F>],
    // constants
    group_map_params: &groupmap::BWParameters<C>,
    endo_base: F,
    endo_scalar: <ark_ec::short_weierstrass::Affine<C> as ark_ec::AffineRepr>::ScalarField,
    num_bits: usize,
) -> SnarkyResult<WrapMainOutput<F>>
where
    F: PrimeField,
    C: ark_ec::short_weierstrass::SWCurveConfig<BaseField = F>,
    W: FnOnce(&mut RunState<F>) -> SnarkyResult<(OpeningProof<F>, Messages<F>)>,
{
    // == select each unfinalized proof's wrap domain in-circuit ==
    // OCaml witnesses `Req.Wrap_domain_indices` as ONE vector (wrap_main.ml:
    // 356-358) — every index var is allocated before any selection gadget.
    let domain_loc = Cow::Borrowed("wrap_main: wrap domain");
    let mut wrap_domain_index_vars = Vec::with_capacity(unfinalized.len());
    for u in unfinalized {
        let value = u.wrap_domain_index;
        let index_var: FieldVar<F> = sys.compute(domain_loc.clone(), move |_| value)?;
        wrap_domain_index_vars.push(index_var);
    }
    // `Vector.map wrap_domain_indices ~f:(one_hot; to_domain)` (:360-367).
    // vector.ml's `map` conses right-to-left, so `f` runs for the LAST proof
    // first; the resulting vector stays in proof order.
    let all_wrap_log2s: Vec<u32> = vec![13, 14, 15];
    let mut selected_domains: Vec<Option<crate::ft_eval_circuit::SelectedDomain<F>>> =
        (0..unfinalized.len()).map(|_| None).collect();
    for k in (0..unfinalized.len()).rev() {
        let index = &wrap_domain_index_vars[k];
        // `One_hot_vector.of_index i ~length` is `Vector.init length
        // ~f:(fun j -> Field.equal (Field.of_int j) i)` — `init` also conses
        // right-to-left, so the equalities are emitted for j = length-1 down
        // to 0 — followed by `Boolean.Assert.any`, which Snarky implements as
        // `assert_non_zero (sum bits)`: witness the inverse and constrain
        // `inverse * sum = 1`.
        let mut which = Vec::with_capacity(all_wrap_log2s.len());
        for j in (0..all_wrap_log2s.len()).rev() {
            which.push(FieldVar::constant(F::from(j as u64)).equal(
                sys,
                domain_loc.clone(),
                index,
            )?);
        }
        which.reverse();
        let bit_sum = which
            .iter()
            .fold(FieldVar::zero(), |sum, bit| sum + bit.to_field_var());
        let bit_sum_for_witness = bit_sum.clone();
        let bit_sum_inv: FieldVar<F> =
            sys.compute(domain_loc.clone(), move |env: &dyn WitnessGeneration<F>| {
                env.read_var(&bit_sum_for_witness)
                    .inverse()
                    .unwrap_or_else(F::zero)
            })?;
        sys.assert_r1cs(
            Some("wrap domain one-hot any".into()),
            domain_loc.clone(),
            bit_sum,
            bit_sum_inv,
            FieldVar::constant(F::one()),
        )?;
        selected_domains[k] = Some(crate::ft_eval_circuit::SelectedDomain {
            log2s: all_wrap_log2s.clone(),
            which,
        });
    }

    // == finalize each unfinalized proof (Type2 claimed values) ==
    let mut new_bulletproof_challenges = Vec::with_capacity(unfinalized.len());
    let mut prev_msgs_wrap = Vec::with_capacity(unfinalized.len());
    for (u, selected) in unfinalized.iter().zip(selected_domains) {
        let finalize_loc = Cow::Borrowed("wrap_main: finalize unfinalized");
        // `Finalize` builds the checked challenge record right-to-left: zeta
        // is converted before alpha, while the record keeps its logical
        // field names.
        let zeta_f = scalar_to_field(
            sys,
            Cow::Borrowed("wrap_main: finalize | zeta to_field"),
            &u.zeta,
            u.finalize_params.endo_r,
        )?;
        let alpha_f = scalar_to_field(
            sys,
            Cow::Borrowed("wrap_main: finalize | alpha to_field"),
            &u.alpha,
            u.finalize_params.endo_r,
        )?;
        let witness = FinalizeWitness {
            alpha: alpha_f,
            beta: u.beta.clone(),
            gamma: u.gamma.clone(),
            zeta: zeta_f,
            xi: u.xi.clone(),
            cip_repr: u.cip_repr.clone(),
            b_repr: u.b_repr.clone(),
            perm_repr: u.perm_repr.clone(),
            bulletproof_challenges: u.bulletproof_challenges.clone(),
            digest: u.sponge_digest_before_evaluations.clone(),
            prev_challenges: u.old_bulletproof_challenges.clone(),
            prev_challenge_mask: None,
            ft_eval1: u.finalize_evals.ft_eval1.clone(),
            public_evals: u.finalize_evals.public_evals.clone(),
            evals: u.finalize_evals.evals.clone(),
        };
        // OCaml passes the pseudo `wrap_domain` selected above into
        // `finalize_other_proof` (wrap_main.ml:409-416) — never the constant.
        let params = FinalizeParams {
            domain: crate::ft_eval_circuit::FinalizeDomain::Selected(
                selected.expect("one selected domain per unfinalized proof"),
            ),
            ..u.finalize_params.clone()
        };
        let fin = finalize_deferred(sys, finalize_loc.clone(), &params, &witness)?;

        // `Boolean.Assert.any [finalized; not should_finalize]`
        // (wrap_main.ml:418). Snarky's `Assert.any` is
        // `assert_non_zero (num_true bs)` (utils.ml:361) — NO `or` gate:
        // the boolean sum stays a lincom, its inverse is witnessed and one
        // r1cs `sum · inv = 1` is emitted.
        let ok_sum = fin.finalized.to_field_var() + u.should_finalize.not().to_field_var();
        let ok_sum_for_witness = ok_sum.clone();
        let ok_sum_inv: FieldVar<F> = sys.compute(
            finalize_loc.clone(),
            move |env: &dyn WitnessGeneration<F>| {
                env.read_var(&ok_sum_for_witness)
                    .inverse()
                    .unwrap_or_else(F::zero)
            },
        )?;
        sys.assert_r1cs(
            Some("finalize ok any".into()),
            finalize_loc,
            ok_sum,
            ok_sum_inv,
            FieldVar::constant(F::one()),
        )?;

        new_bulletproof_challenges.push(fin.challenges);
    }
    // OCaml computes the previous accumulator digests in a SECOND pass over
    // the unfinalized proofs (wrap_main.ml:423-427), after every finalize.
    for u in unfinalized.iter().rev() {
        prev_msgs_wrap.push(sys.with_label(
            Some(Cow::Borrowed("wrap_main: previous accumulator hash")),
            |sys| {
                hash_messages_for_next_wrap_proof(
                    sys,
                    loc.clone(),
                    &u.hash_dummy_challenges,
                    &u.hash_old_bulletproof_challenges,
                    &u.prev_step_acc,
                )
            },
        ));
    }
    prev_msgs_wrap.reverse();

    // OCaml `exists openings_proof` (:440) then `exists messages` (:470):
    // witnessed here, after finalize/hash-prev, before the verifier.
    let (openings, messages) = witness_proof(sys)?;

    // OCaml evaluates `~public_input:(Array.map (pack_statement ...) ...)`
    // (wrap_main.ml:486-493) at the CALL to incrementally_verify_proof —
    // after the openings/messages witnesses, before the verifier-index
    // absorb. Each full-field element is split THERE (`split_field`,
    // wrap_main.ml:57): one boolean check + one `2·y + odd − x` row per
    // element, rows the x_hat terms loop does not carry. The terms loop
    // then re-asserts booleanity of every 1-bit entry (wrap_verifier.ml:917)
    // — the odd bits travel on as `Bool` so `statement_terms` emits exactly
    // that second assert.
    let mut expanded_elements: Vec<StepStatementElement<F>> =
        Vec::with_capacity(step_statement_elements.len() * 2);
    let previous_wrap_digest_start = step_statement_elements.len() - prev_msgs_wrap.len();
    for (index, element) in step_statement_elements.iter().enumerate() {
        let computed_wrap_digest = (index >= previous_wrap_digest_start)
            .then(|| prev_msgs_wrap[index - previous_wrap_digest_start].clone());
        match element {
            StepStatementElement::Split(x) => {
                let (y, odd) = crate::plonk_curve_ops::split_field(sys, loc.clone(), x)?;
                expanded_elements.push(StepStatementElement::Packed {
                    value: y,
                    num_bits: 255,
                });
                expanded_elements.push(StepStatementElement::Bool(odd));
            }
            StepStatementElement::Packed { value, num_bits } => {
                expanded_elements.push(StepStatementElement::Packed {
                    value: computed_wrap_digest.unwrap_or_else(|| value.clone()),
                    num_bits: *num_bits,
                });
            }
            StepStatementElement::Bool(b) => {
                expanded_elements.push(StepStatementElement::Bool(b.clone()));
            }
        }
    }

    // == commit to the step statement and fully verify the step proof ==
    // The dynamic proofs-verified mask, aligned to the physical sg_old
    // layout. `Util.ones_vector` marks the ACTIVE slots first
    // ([true; active] ++ [false; inactive]) while our physical padding puts
    // the dummy accumulators at the FRONT (`Vector.extend_front_exn`
    // semantics, wrap_main.ml:185) — so the mask is reversed to pair
    // dummy slots with `false` and real slots with `true`.
    assert_eq!(
        actual_proofs_verified_mask.len(),
        sg_olds.len(),
        "one mask bit per physical sg_old"
    );
    let sg_old_mask: Vec<Boolean<F>> = actual_proofs_verified_mask.iter().rev().cloned().collect();
    let verifier_sg_olds: Vec<Point<F>> = sg_olds.iter().rev().cloned().collect();
    let verify_loc = Cow::Borrowed("wrap_main: verify step proof");
    let success = verify::<F, C>(
        sys,
        verify_loc.clone(),
        IndexDigest::ComputeFromVk,
        true,
        vk,
        &verifier_sg_olds,
        &sg_old_mask,
        XHatInput::Statement {
            elements: &expanded_elements,
            lagranges,
            h_generator,
        },
        &messages,
        &openings,
        advice,
        xi,
        claimed,
        None,
        group_map_params,
        endo_base,
        endo_scalar,
        num_bits,
    )?;
    // Boolean.Assert.is_true bulletproof_success (unlike the step side, which
    // threads it into the per-proof ok boolean)
    success
        .to_field_var()
        .assert_equals(sys, verify_loc, &FieldVar::constant(F::one()))?;

    // == this statement's accumulator digest ==
    let new_digest = sys.with_label(
        Some(Cow::Borrowed("wrap_main: new accumulator hash")),
        |sys| {
            hash_messages_for_next_wrap_proof(
                sys,
                loc.clone(),
                new_acc_dummy_challenges,
                &new_bulletproof_challenges,
                &openings.challenge_polynomial_commitment,
            )
        },
    );
    new_digest.assert_equals(
        sys,
        Cow::Borrowed("wrap_main: new accumulator digest"),
        messages_for_next_wrap_proof_digest,
    )?;

    Ok(WrapMainOutput {
        prev_messages_for_next_wrap_proof: prev_msgs_wrap,
        new_bulletproof_challenges,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{AdditiveGroup, BigInteger, Field, One, UniformRand, Zero};
    use kimchi::{
        circuits::wires::{COLUMNS, PERMUTS},
        curve::KimchiCurve,
    };
    use mina_curves::pasta::{Fp, Fq, Pallas, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        poseidon::{ArithmeticSponge, Sponge as _},
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof as IpaProof;
    use snarky::{api::SnarkyCircuit, loc};

    // the wrap circuit is a Pallas proof over Fq; the inner curve is Vesta
    type BaseSponge = DefaultFqSponge<
        mina_curves::pasta::PallasParameters,
        PlonkSpongeConstantsKimchi,
        { snarky::FULL_ROUNDS },
    >;
    type ScalarSponge = DefaultFrSponge<Fq, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type RefSponge = ArithmeticSponge<Fq, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    /// dlog-tracked point: `k · Vesta::generator()`, with `k` in Fp (the
    /// Vesta scalar field).
    #[derive(Clone, Copy)]
    struct Tracked {
        k: Fp,
        pt: Vesta,
    }
    fn track(rng: &mut impl rand::Rng) -> Tracked {
        let k = Fp::rand(rng);
        Tracked {
            k,
            pt: (Vesta::generator() * k).into_affine(),
        }
    }

    fn lowest_128(x: Fq) -> Fq {
        let bits = x.into_bigint().to_bits_le();
        let mut acc = Fq::zero();
        for &b in bits[..128].iter().rev() {
            acc.double_in_place();
            if b {
                acc += Fq::one();
            }
        }
        acc
    }

    /// `Shifted_value.Type1.to_field` over Fp: `2t + 2^255 + 1`.
    fn t1(t: Fp) -> Fp {
        Fp::from(2u64) * t + Fp::from(2u64).pow([255]) + Fp::one()
    }
    /// `Type1.of_field`: `(s - 2^255 - 1) / 2` over Fp.
    fn t1_inv(s: Fp) -> Fp {
        (s - Fp::from(2u64).pow([255]) - Fp::one()) * Fp::from(2u64).inverse().unwrap()
    }
    /// raw 128-bit challenge (as Fq) -> Fp endo field image.
    fn endo_fp(raw: Fq) -> Fp {
        let raw_fp = Fp::from_le_bytes_mod_order(&raw.into_bigint().to_bytes_le());
        let endo_scalar = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1;
        crate::scalar_challenge::ScalarChallenge(raw_fp).to_field(endo_scalar)
    }

    const NUM_BITS: usize = 255;

    struct WrapMainCircuit {
        // step statement (mini): [Split(v0), Packed(v1,128), Bool(true)]
        v0: Fq,
        v1: u128,
        lagranges: Vec<((Fq, Fq), (Fq, Fq))>, // 4 slots
        // unfinalized (synthetic finalize data)
        domain: ark_poly::Radix2EvaluationDomain<Fq>,
        shifts: Vec<Fq>,
        ft_eval1: Fq,
        public_evals: [Vec<Fq>; 2],
        evals_flat: Vec<(Fq, Fq)>,
        unf_scalars: [u128; 9], // alpha,beta,gamma,zeta,xi,cip,b,perm + digest-ish
        unf_bp: Vec<Fq>,        // 15 raw
        old_chals: Vec<Fq>,     // 15
        prev_acc: (Fq, Fq),
        hash_dummies: Vec<Fq>, // 15 constants
        // step proof (dlog-tracked points as coordinates)
        vk28: Vec<(Fq, Fq)>, // generic,psm,cadd,mul,emul,endosc + 15 coeff + 6 sig_init + 1 sig_last
        w_comm: Vec<(Fq, Fq)>,
        z_comm: (Fq, Fq),
        t_comm: Vec<(Fq, Fq)>,
        lr: Vec<((Fq, Fq), (Fq, Fq))>,
        delta: (Fq, Fq),
        cpc: (Fq, Fq),
        h: (Fq, Fq),
        // deferred scalars
        xi: u128,
        cip: u128,
        z1: u128,
        b_repr: Fq,
        z2_repr: Fq,
        perm: u128,
        zsl: u128,
        zds: u128,
        // claimed transcript values (mirror outputs)
        claimed: (Fq, Fq, Fq, Fq, Fq), // beta,gamma,alpha,zeta,digest
        claimed_bp: Vec<Fq>,           // 2 (the real transcript prechallenges)
        msgs_wrap_digest: Fq,
        new_acc_dummies: Vec<Fq>, // 15
    }

    impl SnarkyCircuit for WrapMainCircuit {
        type Curve = Pallas;
        type Proof = IpaProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        /// prev_messages_for_next_wrap_proof[0]
        type PublicOutput = FieldVar<Fq>;
        fn circuit(
            &self,
            sys: &mut RunState<Fq>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let mkpt = |sys: &mut RunState<Fq>, p: (Fq, Fq)| -> SnarkyResult<Point<Fq>> {
                Ok(Point::new(
                    sys.compute(loc!(), move |_| p.0)?,
                    sys.compute(loc!(), move |_| p.1)?,
                ))
            };
            let w1 = |sys: &mut RunState<Fq>, v: Fq| sys.compute(loc!(), move |_| v);
            let wvec = |sys: &mut RunState<Fq>, vs: &[Fq]| -> SnarkyResult<Vec<FieldVar<Fq>>> {
                let mut out = vec![];
                for &v in vs {
                    out.push(sys.compute(loc!(), move |_| v)?);
                }
                Ok(out)
            };
            let mksc = |sys: &mut RunState<Fq>, s: u128| sys.compute(loc!(), move |_| Fq::from(s));
            let cpt = |p: (Fq, Fq)| Point::new(FieldVar::constant(p.0), FieldVar::constant(p.1));

            // ---- step statement elements ----
            let v0 = w1(sys, self.v0)?;
            let v1: FieldVar<Fq> = mksc(sys, self.v1)?;
            let bool_true: Boolean<Fq> = sys.compute(loc!(), |_| true)?;
            let elements = vec![
                StepStatementElement::Split(v0),
                StepStatementElement::Packed {
                    value: v1,
                    num_bits: 128,
                },
                StepStatementElement::Bool(bool_true),
            ];
            let lagranges: Vec<(Point<Fq>, Point<Fq>)> = self
                .lagranges
                .iter()
                .map(|&(l, c)| (cpt(l), cpt(c)))
                .collect();

            // ---- unfinalized (synthetic finalize, Type2) ----
            let tokens = vec![kimchi::circuits::expr::PolishToken::Constant(
                kimchi::circuits::expr::ConstantTerm::Literal(Fq::zero()),
            )];
            let mds: Vec<Vec<Fq>> = Pallas::sponge_params()
                .mds
                .iter()
                .map(|r| r.to_vec())
                .collect();
            let (_, endo_r_fq) = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();
            let finalize_params = FinalizeParams {
                tokens: &tokens,
                domain: crate::ft_eval_circuit::FinalizeDomain::Fixed(self.domain),
                srs_log2: 12,
                endo: Fq::from(3u64),
                shifts: &self.shifts,
                endo_r: *endo_r_fq,
                mds: &mds,
                shift: crate::finalize::ShiftKind::Type2,
            };
            let public_evals = [
                wvec(sys, &self.public_evals[0])?,
                wvec(sys, &self.public_evals[1])?,
            ];
            let mut fe = self.evals_flat.iter();
            let mut next_pe =
                |sys: &mut RunState<Fq>| -> SnarkyResult<crate::fr_sponge::PointEvalVar<Fq>> {
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
            let finalize_evals = crate::step_verifier::FinalizeEvals {
                ft_eval1: w1(sys, self.ft_eval1)?,
                public_evals,
                evals,
            };
            let fals: Boolean<Fq> = sys.compute(loc!(), |_| false)?;
            let per_unf = PerUnfinalized {
                finalize_params,
                finalize_evals,
                // The synthetic witness has `should_finalize = false`, so the
                // finalize outcome is masked; any in-range index satisfies the
                // domain one-hot.
                wrap_domain_index: Fq::zero(),
                alpha: mksc(sys, self.unf_scalars[0])?,
                beta: mksc(sys, self.unf_scalars[1])?,
                gamma: mksc(sys, self.unf_scalars[2])?,
                zeta: mksc(sys, self.unf_scalars[3])?,
                xi: mksc(sys, self.unf_scalars[4])?,
                cip_repr: mksc(sys, self.unf_scalars[5])?,
                b_repr: mksc(sys, self.unf_scalars[6])?,
                perm_repr: mksc(sys, self.unf_scalars[7])?,
                bulletproof_challenges: wvec(sys, &self.unf_bp)?,
                sponge_digest_before_evaluations: mksc(sys, self.unf_scalars[8])?,
                should_finalize: fals,
                old_bulletproof_challenges: vec![wvec(sys, &self.old_chals)?],
                prev_step_acc: mkpt(sys, self.prev_acc)?,
                hash_dummy_challenges: vec![self.hash_dummies.clone()],
                hash_old_bulletproof_challenges: vec![wvec(sys, &self.old_chals)?],
            };

            // ---- step proof pieces ----
            let vkpts = self
                .vk28
                .iter()
                .map(|&p| mkpt(sys, p))
                .collect::<SnarkyResult<Vec<_>>>()?;
            let vk = VerificationKeyComm {
                generic: vkpts[0].clone(),
                psm: vkpts[1].clone(),
                complete_add: vkpts[2].clone(),
                mul: vkpts[3].clone(),
                emul: vkpts[4].clone(),
                endomul_scalar: vkpts[5].clone(),
                coefficients: vkpts[6..21].to_vec(),
                sigma_init: vkpts[21..27].to_vec(),
                sigma_last: vec![vkpts[27].clone()],
                lookup: None,
            };
            let h = cpt(self.h);
            let t1 = crate::plonk_curve_ops::ShiftedScalar::Type1;
            let h_for_openings = h.clone();
            let witness_proof =
                |sys: &mut RunState<Fq>| -> SnarkyResult<(OpeningProof<Fq>, Messages<Fq>)> {
                    let mut lr = vec![];
                    for &(l, r) in &self.lr {
                        lr.push((mkpt(sys, l)?, mkpt(sys, r)?));
                    }
                    let openings = OpeningProof {
                        lr,
                        delta: mkpt(sys, self.delta)?,
                        z1: t1(mksc(sys, self.z1)?),
                        z2: t1(w1(sys, self.z2_repr)?),
                        challenge_polynomial_commitment: mkpt(sys, self.cpc)?,
                        h_generator: h_for_openings.clone(),
                    };
                    let messages = Messages {
                        w_comm: self
                            .w_comm
                            .iter()
                            .map(|&p| Ok(vec![mkpt(sys, p)?]))
                            .collect::<SnarkyResult<Vec<_>>>()?,
                        z_comm: vec![mkpt(sys, self.z_comm)?],
                        t_comm: self
                            .t_comm
                            .iter()
                            .map(|&p| mkpt(sys, p))
                            .collect::<SnarkyResult<Vec<_>>>()?,
                        lookup: None,
                    };
                    Ok((openings, messages))
                };
            let advice = Advice {
                combined_inner_product: t1(mksc(sys, self.cip)?),
                b: t1(w1(sys, self.b_repr)?),
                perm: t1(mksc(sys, self.perm)?),
                zeta_to_srs_length: t1(mksc(sys, self.zsl)?),
                zeta_to_domain_size: t1(mksc(sys, self.zds)?),
            };
            let xi = mksc(sys, self.xi)?;
            let claimed = Claimed {
                beta: w1(sys, self.claimed.0)?,
                gamma: w1(sys, self.claimed.1)?,
                alpha: w1(sys, self.claimed.2)?,
                zeta: w1(sys, self.claimed.3)?,
                sponge_digest_before_evaluations: w1(sys, self.claimed.4)?,
                bulletproof_challenges: wvec(sys, &self.claimed_bp)?,
            };
            let msgs_wrap_digest = w1(sys, self.msgs_wrap_digest)?;

            use groupmap::GroupMap;
            let params = groupmap::BWParameters::<VestaParameters>::setup();
            let out = wrap_main::<Fq, VestaParameters, _>(
                sys,
                loc!(),
                std::slice::from_ref(&per_unf),
                &[Boolean::true_()],
                std::slice::from_ref(&per_unf.prev_step_acc),
                &vk,
                &elements,
                &crate::public_input::StatementLagranges::Prepared(&lagranges),
                &h,
                witness_proof,
                &advice,
                &xi,
                &claimed,
                &msgs_wrap_digest,
                std::slice::from_ref(&self.new_acc_dummies),
                &params,
                crate::endo::tock::base(),
                <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1,
                NUM_BITS,
            )?;
            out.prev_messages_for_next_wrap_proof[0]
                .clone()
                .seal(sys, loc!())
        }
    }

    /// The full wrap_main circuit is satisfiable on dlog-tracked data — the
    /// bulletproof equation `equal_g == true` is asserted, exercised for the
    /// first time end-to-end in-circuit (the `b` and `z2` advice are solved
    /// from the transcript mirror), along with the Type2 finalize, the
    /// split-field statement commitment and both accumulator digests.
    #[test]
    fn wrap_main_assembles_with_satisfying_ipa() {
        use groupmap::GroupMap;
        let mut rng = o1_utils::tests::make_test_rng(None);
        let co = |t: &Tracked| (t.pt.x, t.pt.y);

        // ---- step statement + lagranges (4 slots) ----
        let v0 = Fq::rand(&mut rng);
        let v1 = u128::rand(&mut rng);
        let lag: Vec<Tracked> = (0..4).map(|_| track(&mut rng)).collect();
        // corrections for the two Packed slots (0: 255 bits, 2: 128 bits)
        let corr = |t: &Tracked, n: usize| crate::public_input::lagrange_correction(&t.pt, n);
        let corrections = [
            corr(&lag[0], 255),
            lag[1].pt, // Cond slot: unused
            corr(&lag[2], 128),
            lag[3].pt, // Cond slot: unused
        ];

        // x_hat dlog: scalars act in Fp (the Vesta group order)
        let embed = |x: Fq| Fp::from_le_bytes_mod_order(&x.into_bigint().to_bytes_le());
        let (y0, odd0) = {
            let bits = v0.into_bigint().to_bits_le();
            let mut half = Fq::zero();
            for &b in bits[1..].iter().rev() {
                half = half + half;
                if b {
                    half += Fq::one();
                }
            }
            (half, bits[0])
        };
        let h_t = track(&mut rng);
        let x_hat_k = -(embed(y0) * lag[0].k
            + if odd0 { lag[1].k } else { Fp::zero() }
            + Fp::from(v1) * lag[2].k
            + lag[3].k)
            + h_t.k;
        let x_hat_pt = (Vesta::generator() * x_hat_k).into_affine();

        // ---- dlog-tracked step proof points ----
        let prev_acc = track(&mut rng);
        let vk28: Vec<Tracked> = (0..28).map(|_| track(&mut rng)).collect();
        let w_comm: Vec<Tracked> = (0..15).map(|_| track(&mut rng)).collect();
        let z_comm = track(&mut rng);
        let t_comm: Vec<Tracked> = (0..7).map(|_| track(&mut rng)).collect();
        let lr: Vec<(Tracked, Tracked)> =
            (0..2).map(|_| (track(&mut rng), track(&mut rng))).collect();
        let delta = track(&mut rng);
        let cpc = track(&mut rng);
        // The circuit derives the verifier-index digest from the 28 VK points
        // (fresh index sponge over the 56 coordinates, in
        // `index_to_field_elements` order); mirror that here.
        let vk_digest = {
            let mut isp = RefSponge::new(Pallas::sponge_params());
            // sigma_init (vk28[21..27]), sigma_last (vk28[27]),
            // coefficients (vk28[6..21]), then the 6 selector commitments
            // (vk28[0..6]).
            for idx in (21..28).chain(6..21).chain(0..6) {
                let (x, y) = co(&vk28[idx]);
                isp.absorb(&[x]);
                isp.absorb(&[y]);
            }
            isp.squeeze()
        };

        // ---- free deferred scalars ----
        let xi = u128::rand(&mut rng);
        let cip = u128::rand(&mut rng);
        let z1 = u128::rand(&mut rng);
        let perm = u128::rand(&mut rng);
        let zsl = u128::rand(&mut rng);
        let zds = u128::rand(&mut rng);

        // ---- transcript mirror ----
        let mut s = RefSponge::new(Pallas::sponge_params());
        let ab = |s: &mut RefSponge, p: (Fq, Fq)| {
            s.absorb(&[p.0]);
            s.absorb(&[p.1]);
        };
        s.absorb(&[vk_digest]);
        ab(&mut s, co(&prev_acc));
        ab(&mut s, (x_hat_pt.x, x_hat_pt.y));
        for w in &w_comm {
            ab(&mut s, co(w));
        }
        let claimed_beta = lowest_128(s.squeeze());
        let claimed_gamma = lowest_128(s.squeeze());
        ab(&mut s, co(&z_comm));
        let claimed_alpha = lowest_128(s.squeeze());
        for t in &t_comm {
            ab(&mut s, co(t));
        }
        let claimed_zeta = lowest_128(s.squeeze());
        let mut ipa = s.clone(); // fork before the digest squeeze
        let claimed_digest = s.squeeze();

        // IPA transcript on the fork
        ipa.absorb(&[Fq::from(cip)]);
        let gm = groupmap::BWParameters::<VestaParameters>::setup();
        let (ux, uy) = gm.to_group(ipa.squeeze());
        let u_pt = Vesta::new_unchecked(ux, uy);
        let pre: Vec<Fq> = lr
            .iter()
            .map(|(l, r)| {
                ab(&mut ipa, co(l));
                ab(&mut ipa, co(r));
                lowest_128(ipa.squeeze())
            })
            .collect();
        ab(&mut ipa, co(&delta));
        let c_raw = lowest_128(ipa.squeeze());

        // ---- dlog of the combined polynomial ----
        // ft = t1(perm)·sigma_last + tred - t1(zds)·tred
        let tred = {
            let mut k = t_comm[6].k;
            for t in t_comm[..6].iter().rev() {
                k = t.k + t1(Fp::from(zsl)) * k;
            }
            k
        };
        let ft_k = t1(Fp::from(perm)) * vk28[27].k + tred - t1(Fp::from(zds)) * tred;
        // commitment order: sg_old, x_hat, ft, z, 6 named, w[15], coeff[15], sigma_init[6]
        let mut ks: Vec<Fp> = vec![prev_acc.k, x_hat_k, ft_k, z_comm.k];
        ks.extend(vk28[..6].iter().map(|t| t.k));
        ks.extend(w_comm.iter().map(|t| t.k));
        ks.extend(vk28[6..21].iter().map(|t| t.k));
        ks.extend(vk28[21..27].iter().map(|t| t.k));
        let xi_e = endo_fp(Fq::from(xi));
        let mut combined_k = *ks.last().unwrap();
        for k in ks[..ks.len() - 1].iter().rev() {
            combined_k = *k + xi_e * combined_k;
        }
        // lr_prod
        let mut lr_k = Fp::zero();
        for ((l, r), p) in lr.iter().zip(&pre) {
            let pe = endo_fp(*p);
            lr_k += l.k * pe.inverse().unwrap() + r.k * pe;
        }

        // ---- solve b and z2 so that equal_g holds ----
        let cip1 = t1(Fp::from(cip));
        let c_e = endo_fp(c_raw);
        let z1_1 = t1(Fp::from(z1));
        let b1 = c_e * cip1 * z1_1.inverse().unwrap();
        let b_repr_fp = t1_inv(b1);
        let q_p = combined_k + lr_k;
        let z2_1 = (c_e * q_p + delta.k - z1_1 * cpc.k) * h_t.k.inverse().unwrap();
        let z2_repr_fp = t1_inv(z2_1);
        let back = |x: Fp| Fq::from_le_bytes_mod_order(&x.into_bigint().to_bytes_le());
        // sanity: the representatives fit in Fq (whp — the moduli differ by ~2^96)
        assert_eq!(embed(back(b_repr_fp)), b_repr_fp, "b_repr fits");
        assert_eq!(embed(back(z2_repr_fp)), z2_repr_fp, "z2_repr fits");

        // sanity out-of-circuit: c·Q + delta == z1·(G + b·U) + z2·H
        {
            let q = Vesta::generator() * q_p + u_pt * cip1;
            let lhs = q * c_e + delta.pt.into_group();
            let rhs = (cpc.pt.into_group() + u_pt * b1) * z1_1 + h_t.pt * z2_1;
            assert_eq!(lhs.into_affine(), rhs.into_affine(), "mirror equal_g");
        }

        // ---- unfinalized + accumulator digests ----
        let (_, endo_r_fq) = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();
        let unf_bp: Vec<Fq> = (0..crate::common::TOCK_ROUNDS)
            .map(|_| Fq::from(u128::rand(&mut rng)))
            .collect();
        let old_chals: Vec<Fq> = (0..crate::common::TOCK_ROUNDS)
            .map(|_| Fq::rand(&mut rng))
            .collect();
        let hash_dummies: Vec<Fq> = (0..crate::common::TOCK_ROUNDS)
            .map(|_| Fq::rand(&mut rng))
            .collect();
        let new_acc_dummies: Vec<Fq> = (0..crate::common::TOCK_ROUNDS)
            .map(|_| Fq::rand(&mut rng))
            .collect();
        // prev accumulator digest mirror (the circuit's public output)
        let prev_digest = {
            let mut s = RefSponge::new(Pallas::sponge_params());
            for c in hash_dummies.iter().chain(&old_chals) {
                s.absorb(&[*c]);
            }
            ab(&mut s, co(&prev_acc));
            s.squeeze()
        };
        // new accumulator digest mirror (asserted in-circuit)
        let msgs_wrap_digest = {
            let mut s = RefSponge::new(Pallas::sponge_params());
            for c in &new_acc_dummies {
                s.absorb(&[*c]);
            }
            for raw in &unf_bp {
                s.absorb(&[crate::scalar_challenge::ScalarChallenge(*raw).to_field(*endo_r_fq)]);
            }
            ab(&mut s, co(&cpc));
            s.squeeze()
        };

        use ark_poly::EvaluationDomain;
        let circ = WrapMainCircuit {
            v0,
            v1,
            lagranges: lag
                .iter()
                .zip(&corrections)
                .map(|(l, c)| ((l.pt.x, l.pt.y), (c.x, c.y)))
                .collect(),
            domain: ark_poly::Radix2EvaluationDomain::new(1 << 10).unwrap(),
            shifts: (0..PERMUTS).map(|_| Fq::rand(&mut rng)).collect(),
            ft_eval1: Fq::rand(&mut rng),
            public_evals: [vec![Fq::rand(&mut rng)], vec![Fq::rand(&mut rng)]],
            evals_flat: (0..1 + 6 + 2 * COLUMNS + PERMUTS - 1)
                .map(|_| (Fq::rand(&mut rng), Fq::rand(&mut rng)))
                .collect(),
            unf_scalars: core::array::from_fn(|_| u128::rand(&mut rng)),
            unf_bp,
            old_chals,
            prev_acc: co(&prev_acc),
            hash_dummies,
            vk28: vk28.iter().map(co).collect(),
            w_comm: w_comm.iter().map(co).collect(),
            z_comm: co(&z_comm),
            t_comm: t_comm.iter().map(co).collect(),
            lr: lr.iter().map(|(l, r)| (co(l), co(r))).collect(),
            delta: co(&delta),
            cpc: co(&cpc),
            h: co(&h_t),
            xi,
            cip,
            z1,
            b_repr: back(b_repr_fp),
            z2_repr: back(z2_repr_fp),
            perm,
            zsl,
            zds,
            claimed: (
                claimed_beta,
                claimed_gamma,
                claimed_alpha,
                claimed_zeta,
                claimed_digest,
            ),
            claimed_bp: pre,
            msgs_wrap_digest,
            new_acc_dummies,
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(*out, prev_digest, "prev accumulator digest");
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }
}

//! Helpers for the first non-base step proof.
//!
//! This module keeps the recursion test focused on witness construction while
//! the step circuit plumbing lives in the crate.

use ark_ff::{BigInteger, PrimeField};
use groupmap::GroupMap;
use kimchi::circuits::wires::{COLUMNS, PERMUTS};
use kimchi::curve::KimchiCurve;
use mina_curves::pasta::{Fp, Fq, Pallas, PallasParameters, Vesta};
use poly_commitment::ipa::OpeningProof as IpaProof;
use snarky::{api::SnarkyCircuit, loc, Boolean, FieldVar, RunState, SnarkyResult};

use crate::common::FULL_ROUNDS;
use crate::finalize::{FinalizeParams, ShiftKind};
use crate::incrementally_verify::{Advice, Messages, OpeningProof, VerificationKeyComm};
use crate::plonk_curve_ops::ShiftedScalar;
use crate::step_main::{step_main, PerProofInput};
use crate::step_verifier::{Claimed, FinalizeEvals, WrapStatementVars};

pub type StepPolishToken = kimchi::circuits::expr::PolishToken<
    Fp,
    kimchi::circuits::berkeley_columns::Column,
    kimchi::circuits::berkeley_columns::BerkeleyChallengeTerm,
>;

pub const fn width1_step_statement_len(wrap_rounds: usize) -> usize {
    10 + 1 + 2 + 3 + wrap_rounds + 1 + 2
}

pub fn embed_fq_to_fp(x: Fq) -> Fp {
    Fp::from_le_bytes_mod_order(&x.into_bigint().to_bytes_le())
}

/// Plain witness data for a recursive step circuit that verifies one wrap
/// proof and folds it into the next step accumulator.
pub struct RecursiveStepData {
    pub finalize_tokens: Vec<StepPolishToken>,
    pub finalize_domain: ark_poly::Radix2EvaluationDomain<Fp>,
    pub finalize_srs_log2: u32,
    pub finalize_endo: Fp,
    pub finalize_shifts: Vec<Fp>,
    pub ft_eval1: Fp,
    pub public_evals: [Vec<Fp>; 2],
    pub evals_flat: Vec<(Fp, Fp)>,
    pub stmt: Vec<Fp>,
    pub wrap_vk_pts: Vec<(Fp, Fp)>,
    pub prev_app_state: Vec<Fp>,
    pub wrap_vk_digest: Fp,
    pub generic: (Fp, Fp),
    pub psm: (Fp, Fp),
    pub complete_add: (Fp, Fp),
    pub mul: (Fp, Fp),
    pub emul: (Fp, Fp),
    pub endomul_scalar: (Fp, Fp),
    pub coefficients: Vec<(Fp, Fp)>,
    pub sigma_init: Vec<(Fp, Fp)>,
    pub sigma_last: Vec<(Fp, Fp)>,
    pub w_comm: Vec<(Fp, Fp)>,
    pub z_comm: (Fp, Fp),
    pub t_comm: Vec<(Fp, Fp)>,
    pub lr: Vec<((Fp, Fp), (Fp, Fp))>,
    pub delta: (Fp, Fp),
    pub sg: (Fp, Fp),
    pub h: (Fp, Fp),
    pub z1: (Fp, bool),
    pub z2: (Fp, bool),
    pub packed_lagranges: Vec<((Fp, Fp), (Fp, Fp))>,
    pub flag_lagranges: Vec<(Fp, Fp)>,
}

pub struct RecursiveStepCircuit<
    const PREV_ROUNDS: usize,
    const WRAP_ROUNDS: usize,
    const PUBLIC_INPUT_LEN: usize,
> {
    pub d: RecursiveStepData,
}

impl<const PREV_ROUNDS: usize, const WRAP_ROUNDS: usize, const PUBLIC_INPUT_LEN: usize>
    SnarkyCircuit for RecursiveStepCircuit<PREV_ROUNDS, WRAP_ROUNDS, PUBLIC_INPUT_LEN>
{
    type Curve = Vesta;
    const PREV_CHALLENGES: usize = 1;
    type Proof = IpaProof<Self::Curve, FULL_ROUNDS>;
    type PrivateInput = ();
    type PublicInput = [FieldVar<Fp>; PUBLIC_INPUT_LEN];
    type PublicOutput = ();

    fn circuit(
        &self,
        sys: &mut RunState<Fp>,
        stmt2: Self::PublicInput,
        _private: Option<&Self::PrivateInput>,
    ) -> SnarkyResult<()> {
        use crate::composition_types::PlonkVerificationKeyEvals;
        use snarky::gadgets::curve::Point;

        assert_eq!(PUBLIC_INPUT_LEN, width1_step_statement_len(WRAP_ROUNDS));

        let d = &self.d;
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
        let t2s = |sys: &mut RunState<Fp>,
                   half: FieldVar<Fp>,
                   odd: FieldVar<Fp>|
         -> SnarkyResult<ShiftedScalar<Fp>> {
            sys.assert_r1cs(
                Some("stmt2 odd bit".into()),
                loc!(),
                odd.clone(),
                odd.clone(),
                odd.clone(),
            )?;
            Ok(ShiftedScalar::Type2(half, Boolean::create_unsafe(odd)))
        };

        let mds: Vec<Vec<Fp>> = Vesta::sponge_params()
            .mds
            .iter()
            .map(|r| r.to_vec())
            .collect();
        let (_, endo_p) = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos();
        let finalize_params = FinalizeParams {
            tokens: &d.finalize_tokens,
            domain: d.finalize_domain,
            srs_log2: d.finalize_srs_log2,
            endo: d.finalize_endo,
            shifts: &d.finalize_shifts,
            endo_r: *endo_p,
            mds: &mds,
            shift: ShiftKind::Type1,
        };
        let mut fe = d.evals_flat.iter();
        let mut next_pe =
            |sys: &mut RunState<Fp>| -> SnarkyResult<crate::fr_sponge::PointEvalVar<Fp>> {
                let &(a, b) = fe.next().unwrap();
                Ok((vec![w1(sys, a)?], vec![w1(sys, b)?]))
            };
        let evals = crate::fr_sponge::AbsorbEvalsVar {
            z: next_pe(sys)?,
            generic_selector: next_pe(sys)?,
            poseidon_selector: next_pe(sys)?,
            complete_add_selector: next_pe(sys)?,
            mul_selector: next_pe(sys)?,
            emul_selector: next_pe(sys)?,
            endomul_scalar_selector: next_pe(sys)?,
            w: (0..COLUMNS)
                .map(|_| next_pe(sys))
                .collect::<SnarkyResult<Vec<_>>>()?,
            coefficients: (0..COLUMNS)
                .map(|_| next_pe(sys))
                .collect::<SnarkyResult<Vec<_>>>()?,
            s: (0..PERMUTS - 1)
                .map(|_| next_pe(sys))
                .collect::<SnarkyResult<Vec<_>>>()?,
        };
        let finalize_evals = FinalizeEvals {
            ft_eval1: w1(sys, d.ft_eval1)?,
            public_evals: [
                wvec(sys, &d.public_evals[0])?,
                wvec(sys, &d.public_evals[1])?,
            ],
            evals,
        };

        let sv = wvec(sys, &d.stmt)?;
        let stmt = WrapStatementVars {
            combined_inner_product: sv[0].clone(),
            b: sv[1].clone(),
            zeta_to_srs_length: sv[2].clone(),
            zeta_to_domain_size: sv[3].clone(),
            perm: sv[4].clone(),
            beta: sv[5].clone(),
            gamma: sv[6].clone(),
            alpha: sv[7].clone(),
            zeta: sv[8].clone(),
            xi: sv[9].clone(),
            sponge_digest_before_evaluations: sv[10].clone(),
            messages_for_next_wrap_proof_digest: sv[11].clone(),
            bulletproof_challenges: sv[13..13 + PREV_ROUNDS].to_vec(),
            branch_data: sv[13 + PREV_ROUNDS].clone(),
            feature_flags: {
                let mut v = vec![];
                for _ in 0..8 {
                    let b: Boolean<Fp> = sys.compute(loc!(), |_| false)?;
                    v.push(b);
                }
                v
            },
        };

        let mut vk_pts = vec![];
        for i in 0..28 {
            let (px, py) = (
                sys.compute(loc!(), move |_| d.wrap_vk_pts[i].0)?,
                sys.compute(loc!(), move |_| d.wrap_vk_pts[i].1)?,
            );
            vk_pts.push(Point::new(px, py));
        }
        let mut it = vk_pts.into_iter();
        let dlog_index = PlonkVerificationKeyEvals {
            sigma_comm: (0..PERMUTS).map(|_| it.next().unwrap()).collect(),
            coefficients_comm: (0..COLUMNS).map(|_| it.next().unwrap()).collect(),
            generic_comm: it.next().unwrap(),
            psm_comm: it.next().unwrap(),
            complete_add_comm: it.next().unwrap(),
            mul_comm: it.next().unwrap(),
            emul_comm: it.next().unwrap(),
            endomul_scalar_comm: it.next().unwrap(),
        };
        let after_index = crate::hash_messages::sponge_after_index(sys, loc!(), &dlog_index);
        let prev_app_state = wvec(sys, &d.prev_app_state)?;

        let wrap_vk_digest = w1(sys, d.wrap_vk_digest)?;
        let vk = VerificationKeyComm {
            generic: mkpt(sys, d.generic)?,
            psm: mkpt(sys, d.psm)?,
            complete_add: mkpt(sys, d.complete_add)?,
            mul: mkpt(sys, d.mul)?,
            emul: mkpt(sys, d.emul)?,
            endomul_scalar: mkpt(sys, d.endomul_scalar)?,
            coefficients: mkpts(sys, &d.coefficients)?,
            sigma_init: mkpts(sys, &d.sigma_init)?,
            sigma_last: mkpts(sys, &d.sigma_last)?,
        };
        let messages = Messages {
            w_comm: d
                .w_comm
                .iter()
                .map(|&p| Ok(vec![mkpt(sys, p)?]))
                .collect::<SnarkyResult<Vec<_>>>()?,
            z_comm: vec![mkpt(sys, d.z_comm)?],
            t_comm: d
                .t_comm
                .iter()
                .map(|&p| mkpt(sys, p))
                .collect::<SnarkyResult<Vec<_>>>()?,
        };
        let mut lr = vec![];
        for &(l, r) in &d.lr {
            lr.push((mkpt(sys, l)?, mkpt(sys, r)?));
        }
        let h = cpt(d.h);
        let wt2 = |sys: &mut RunState<Fp>, p: (Fp, bool)| -> SnarkyResult<ShiftedScalar<Fp>> {
            let half = sys.compute(loc!(), move |_| p.0)?;
            let odd: Boolean<Fp> = sys.compute(loc!(), move |_| p.1)?;
            Ok(ShiftedScalar::Type2(half, odd))
        };
        let openings = OpeningProof {
            lr,
            delta: mkpt(sys, d.delta)?,
            z1: wt2(sys, d.z1)?,
            z2: wt2(sys, d.z2)?,
            challenge_polynomial_commitment: mkpt(sys, d.sg)?,
            h_generator: h.clone(),
        };
        let advice = Advice {
            combined_inner_product: t2s(sys, stmt2[0].clone(), stmt2[1].clone())?,
            b: t2s(sys, stmt2[2].clone(), stmt2[3].clone())?,
            zeta_to_srs_length: t2s(sys, stmt2[4].clone(), stmt2[5].clone())?,
            zeta_to_domain_size: t2s(sys, stmt2[6].clone(), stmt2[7].clone())?,
            perm: t2s(sys, stmt2[8].clone(), stmt2[9].clone())?,
        };
        let claimed = Claimed {
            sponge_digest_before_evaluations: stmt2[10].clone(),
            beta: stmt2[11].clone(),
            gamma: stmt2[12].clone(),
            alpha: stmt2[13].clone(),
            zeta: stmt2[14].clone(),
            bulletproof_challenges: stmt2[16..16 + WRAP_ROUNDS].to_vec(),
        };
        let xi2 = stmt2[15].clone();
        let sf = stmt2[16 + WRAP_ROUNDS].clone();
        sys.assert_r1cs(
            Some("should_finalize bit".into()),
            loc!(),
            sf.clone(),
            sf.clone(),
            sf.clone(),
        )?;
        let tru: Boolean<Fp> = Boolean::create_unsafe(sf);
        let fals: Boolean<Fp> = sys.compute(loc!(), |_| false)?;

        let packed_lagranges: Vec<(Point<Fp>, Point<Fp>)> = d
            .packed_lagranges
            .iter()
            .map(|&(l, c)| (cpt(l), cpt(c)))
            .collect();
        let flag_lagranges: Vec<Point<Fp>> = d.flag_lagranges.iter().map(|&l| cpt(l)).collect();

        let per_proof = PerProofInput {
            finalize_params,
            finalize_evals,
            stmt,
            sponge_after_index: after_index,
            prev_app_state,
            prev_challenge_polynomial_commitments: vec![],
            prev_challenges: vec![],
            vk_digest: wrap_vk_digest,
            vk,
            packed_lagranges,
            flag_lagranges,
            h_generator: h,
            messages,
            openings,
            advice,
            xi: xi2,
            claimed,
            should_finalize: tru.clone(),
            must_verify: tru.clone(),
            is_base_case: fals,
        };

        let params = groupmap::BWParameters::<PallasParameters>::setup();
        let app_state = wvec(sys, &d.prev_app_state)?;
        let digest = step_main::<Fp, PallasParameters>(
            sys,
            loc!(),
            &app_state,
            &dlog_index,
            std::slice::from_ref(&per_proof),
            &params,
            crate::endo::tick::base(),
            <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1,
            255,
        )?;
        digest.assert_equals(sys, loc!(), &stmt2[17 + WRAP_ROUNDS])?;
        Ok(())
    }
}

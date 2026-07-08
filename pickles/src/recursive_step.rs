//! Helpers for the first non-base step proof.
//!
//! This module keeps the recursion test focused on witness construction while
//! the step circuit plumbing lives in the crate.

use ark_ff::{BigInteger, One, PrimeField};
use groupmap::GroupMap;
use kimchi::circuits::wires::{COLUMNS, PERMUTS};
use kimchi::curve::KimchiCurve;
use mina_curves::pasta::{Fp, Fq, Pallas, PallasParameters, Vesta, VestaParameters};
use mina_poseidon::constants::PlonkSpongeConstantsKimchi;
use mina_poseidon::sponge::{DefaultFqSponge, DefaultFrSponge};
use poly_commitment::commitment::PolyComm;
use poly_commitment::ipa::OpeningProof as IpaProof;
use poly_commitment::SRS;
use snarky::{api::SnarkyCircuit, loc, Boolean, FieldVar, RunState, SnarkyResult};

use crate::api::{BaseCaseProof, StepApp};
use crate::common::FULL_ROUNDS;
use crate::composition_types::{plonk, Features};
use crate::finalize::{FinalizeParams, ShiftKind};
use crate::incrementally_verify::{Advice, Messages, OpeningProof, VerificationKeyComm};
use crate::plonk_curve_ops::ShiftedScalar;
use crate::step_main::{step_main, PerProofInput};
use crate::step_verifier::{Claimed, FinalizeEvals, WrapStatementVars};

type VestaBase = DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type VestaScalar = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type PallasBase = DefaultFqSponge<PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type PallasScalar = DefaultFrSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

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

pub struct PreparedRecursiveStep<const PUBLIC_INPUT_LEN: usize> {
    pub data: RecursiveStepData,
    pub statement: [Fp; PUBLIC_INPUT_LEN],
    pub recursion: kimchi::proof::RecursionChallenge<Vesta>,
}

/// Builds the witness, width-1 statement and recursion challenge for the first
/// recursive step over a base-case wrap proof.
#[allow(clippy::too_many_lines)]
pub fn prepare_recursive_step<
    A: StepApp,
    const PREV_ROUNDS: usize,
    const WRAP_ROUNDS: usize,
    const PREV_STMT_LEN: usize,
    const PUBLIC_INPUT_LEN: usize,
>(
    base: &BaseCaseProof<A, PREV_ROUNDS, PREV_STMT_LEN>,
    wrap_vk_pts: Vec<(Fp, Fp)>,
    prev_app_state: Vec<Fp>,
) -> PreparedRecursiveStep<PUBLIC_INPUT_LEN> {
    assert_eq!(PUBLIC_INPUT_LEN, width1_step_statement_len(WRAP_ROUNDS));

    let svi = &base.step_verifier.index;
    let step_proof = &base.step_proof;
    let step_public = vec![embed_fq_to_fp(base.statement[12])];
    let lgr = svi.srs().get_lagrange_basis(svi.domain);
    let com: Vec<_> = lgr.iter().take(svi.public).collect();
    let elm: Vec<_> = step_public.iter().map(|s| -*s).collect();
    let pc = PolyComm::<Vesta>::multi_scalar_mul(&com, &elm);
    let step_public_comm = svi
        .srs()
        .mask_custom(pc.clone(), &pc.map(|_| Fp::one()))
        .unwrap()
        .commitment;
    let so = step_proof
        .oracles::<VestaBase, VestaScalar, _>(svi, &step_public_comm, Some(&step_public))
        .unwrap();
    let e = &step_proof.evals;
    let pair = |p: &kimchi::proof::PointEvaluations<Vec<Fp>>| (p.zeta[0], p.zeta_omega[0]);
    let mut evals_flat: Vec<(Fp, Fp)> = vec![
        pair(&e.z),
        pair(&e.generic_selector),
        pair(&e.poseidon_selector),
        pair(&e.complete_add_selector),
        pair(&e.mul_selector),
        pair(&e.emul_selector),
        pair(&e.endomul_scalar_selector),
    ];
    evals_flat.extend(e.w.iter().map(pair));
    evals_flat.extend(e.coefficients.iter().map(pair));
    evals_flat.extend(e.s.iter().map(pair));
    let step_srs_log2 = u64::BITS - 1 - (svi.max_poly_size as u64).leading_zeros();

    let wvi = &base.wrap_verifier.index;
    let wrap_proof = &base.proof;
    let wlgr = wvi.srs().get_lagrange_basis(wvi.domain);
    let wcom: Vec<_> = wlgr.iter().take(wvi.public).collect();
    let welm: Vec<_> = base.statement.iter().map(|s| -*s).collect();
    let wpc = PolyComm::<Pallas>::multi_scalar_mul(&wcom, &welm);
    let wrap_public_comm = wvi
        .srs()
        .mask_custom(wpc.clone(), &wpc.map(|_| Fq::one()))
        .unwrap()
        .commitment;
    let wo = wrap_proof
        .oracles::<PallasBase, PallasScalar, _>(wvi, &wrap_public_comm, Some(&base.statement))
        .unwrap();
    let woracles = &wo.oracles;

    let wcombined = wrap_proof
        .evals
        .combine(&wo.powers_of_eval_points_for_chunks);
    let wrap_srs_log2 = u64::BITS - 1 - (wvi.max_poly_size as u64).leading_zeros();
    let wdomain = crate::plonk_checks::Domain::<Fq> {
        log2_size: wvi.domain.log_size_of_group,
        generator: wvi.domain.group_gen,
    };
    let wminimal = plonk::Minimal::<Fq, Fq, bool> {
        alpha: woracles.alpha,
        beta: woracles.beta,
        gamma: woracles.gamma,
        zeta: woracles.zeta,
        joint_combiner: None,
        feature_flags: Features::none(),
    };
    let wenv = crate::plonk_checks::scalars_env::<Fq, bool>(&wdomain, wrap_srs_log2, &wminimal);
    let wevals = crate::plonk_checks::Evals {
        w: wcombined.w.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
        s: wcombined.s.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
        z: (wcombined.z.zeta, wcombined.z.zeta_omega),
    };
    let wperm = crate::plonk_checks::perm_scalar(&wenv, &wevals);

    let sw = crate::step_witness::step_witness(
        wvi.max_poly_size as u64,
        wvi.domain.size,
        wvi.domain.group_gen,
        wrap_proof,
        &wrap_public_comm,
        wvi.digest::<PallasBase>(),
        wo.combined_inner_product,
        woracles.zeta,
        woracles.u,
        wperm,
    );

    let xi2_raw: Fq = {
        use kimchi::plonk_sponge::FrSponge as _;
        let params = Pallas::sponge_params();
        let mut fr = PallasScalar::from(params);
        fr.absorb(&wo.digest);
        let pcd = PallasScalar::from(params).digest();
        fr.absorb(&pcd);
        fr.absorb(&wrap_proof.ft_eval1);
        fr.absorb_multiple(&wo.public_evals[0]);
        fr.absorb_multiple(&wo.public_evals[1]);
        fr.absorb_evaluations(&wrap_proof.evals);
        fr.squeeze(mina_poseidon::sponge::CHALLENGE_LENGTH_IN_LIMBS)
    };

    let widths = crate::step_verifier::wrap_statement_packed_widths(PREV_ROUNDS);
    let packed_lagranges: Vec<((Fp, Fp), (Fp, Fp))> = widths
        .iter()
        .enumerate()
        .map(|(i, &n)| {
            let l = wlgr[i].chunks[0];
            let c = crate::public_input::lagrange_correction(&l, n);
            ((l.x, l.y), (c.x, c.y))
        })
        .collect();
    let flag_lagranges: Vec<(Fp, Fp)> = (0..8)
        .map(|i| {
            let l = wlgr[widths.len() + i].chunks[0];
            (l.x, l.y)
        })
        .collect();

    let co = |p: &Pallas| (p.x, p.y);
    let wh = wvi.srs().h;
    let data = RecursiveStepData {
        finalize_tokens: svi.linearization.constant_term.clone(),
        finalize_domain: svi.domain,
        finalize_srs_log2: step_srs_log2,
        finalize_endo: svi.endo,
        finalize_shifts: svi.shift.to_vec(),
        ft_eval1: step_proof.ft_eval1,
        public_evals: so.public_evals.clone(),
        evals_flat,
        stmt: base.statement.iter().map(|&v| embed_fq_to_fp(v)).collect(),
        wrap_vk_pts,
        prev_app_state: prev_app_state.clone(),
        wrap_vk_digest: wvi.digest::<PallasBase>(),
        generic: co(&wvi.generic_comm.chunks[0]),
        psm: co(&wvi.psm_comm.chunks[0]),
        complete_add: co(&wvi.complete_add_comm.chunks[0]),
        mul: co(&wvi.mul_comm.chunks[0]),
        emul: co(&wvi.emul_comm.chunks[0]),
        endomul_scalar: co(&wvi.endomul_scalar_comm.chunks[0]),
        coefficients: wvi
            .coefficients_comm
            .iter()
            .map(|c| co(&c.chunks[0]))
            .collect(),
        sigma_init: wvi.sigma_comm[..PERMUTS - 1]
            .iter()
            .map(|c| co(&c.chunks[0]))
            .collect(),
        sigma_last: vec![co(&wvi.sigma_comm[PERMUTS - 1].chunks[0])],
        w_comm: wrap_proof
            .commitments
            .w_comm
            .iter()
            .map(|c| co(&c.chunks[0]))
            .collect(),
        z_comm: co(&wrap_proof.commitments.z_comm.chunks[0]),
        t_comm: wrap_proof
            .commitments
            .t_comm
            .chunks
            .iter()
            .map(co)
            .collect(),
        lr: wrap_proof
            .proof
            .lr
            .iter()
            .map(|(l, r)| (co(l), co(r)))
            .collect(),
        delta: co(&wrap_proof.proof.delta),
        sg: co(&wrap_proof.proof.sg),
        h: (wh.x, wh.y),
        z1: sw.z1,
        z2: sw.z2,
        packed_lagranges,
        flag_lagranges,
    };

    let endo_p = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1;
    let chals_step1: Vec<Fp> = base.statement[13..13 + PREV_ROUNDS]
        .iter()
        .map(|&raw| crate::scalar_challenge::ScalarChallenge(embed_fq_to_fp(raw)).to_field(endo_p))
        .collect();
    let sg_check = crate::dummy::compute_sg(svi.srs(), &chals_step1);
    assert_eq!(
        sg_check, base.step_proof.proof.sg,
        "sg_step1 == commit(b_poly(chals_step1))"
    );

    let new_digest = crate::hash_messages::hash_messages_for_next_step_proof_ref(
        Vesta::sponge_params(),
        &data.wrap_vk_pts,
        &prev_app_state,
        &[data.sg],
        &[chals_step1.clone()],
    );

    let pair = |p: (Fp, bool)| [p.0, if p.1 { Fp::one() } else { Fp::from(0u64) }];
    let mut statement: Vec<Fp> = vec![];
    statement.extend(pair(sw.cip));
    statement.extend(pair(sw.b));
    statement.extend(pair(sw.zeta_to_srs_length));
    statement.extend(pair(sw.zeta_to_domain_size));
    statement.extend(pair(sw.perm));
    statement.push(embed_fq_to_fp(sw.sponge_digest));
    statement.push(sw.beta_raw);
    statement.push(sw.gamma_raw);
    statement.push(sw.alpha_raw);
    statement.push(sw.zeta_raw);
    statement.push(embed_fq_to_fp(xi2_raw));
    statement.extend(sw.bulletproof_prechallenges.iter().copied());
    statement.push(Fp::one());
    statement.push(new_digest);
    statement.push(Fp::from(0u64));
    assert_eq!(statement.len(), PUBLIC_INPUT_LEN);

    let recursion = kimchi::proof::RecursionChallenge {
        chals: chals_step1,
        comm: PolyComm {
            chunks: vec![base.step_proof.proof.sg],
        },
    };

    PreparedRecursiveStep {
        data,
        statement: statement.try_into().unwrap_or_else(|_| unreachable!()),
        recursion,
    }
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

//! The first recursive step (proofs_verified = 1): a second step circuit runs
//! [`pickles::step_main::step_main`] over the base-case wrap proof —
//! finalizing the wrap statement's deferred values (the base step proof's
//! scalars) against that proof's evaluations, re-deriving the wrap proof's
//! whole transcript, recommitting the wrap statement through the real Pallas
//! Lagrange basis, and asserting the bulletproof equation — with
//! `must_verify = true`, so every check is real.

use ark_ff::{BigInteger, One, PrimeField};
use kimchi::circuits::wires::{COLUMNS, PERMUTS};
use kimchi::curve::KimchiCurve;
use mina_curves::pasta::{Fp, Fq, Pallas, PallasParameters, Vesta};
use mina_poseidon::constants::PlonkSpongeConstantsKimchi;
use mina_poseidon::sponge::{DefaultFqSponge, DefaultFrSponge};
use poly_commitment::commitment::PolyComm;
use poly_commitment::ipa::OpeningProof as IpaProof;
use poly_commitment::SRS;
use snarky::{api::SnarkyCircuit, loc, Boolean, FieldVar, RunState, SnarkyResult};

use pickles::api::{prove_base_case, StepApp};
use pickles::composition_types::{plonk, Features};
use pickles::finalize::{FinalizeParams, ShiftKind};
use pickles::incrementally_verify::{Advice, Messages, OpeningProof, VerificationKeyComm};
use pickles::plonk_curve_ops::ShiftedScalar;
use pickles::step_main::{step_main, PerProofInput};
use pickles::step_verifier::{Claimed, FinalizeEvals, WrapStatementVars};

const FULL_ROUNDS: usize = snarky::FULL_ROUNDS;

type VestaBase = DefaultFqSponge<
    mina_curves::pasta::VestaParameters,
    PlonkSpongeConstantsKimchi,
    FULL_ROUNDS,
>;
type VestaScalar = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type PallasBase = DefaultFqSponge<PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type PallasScalar = DefaultFrSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

/// step proof #1's IPA rounds / wrap statement length (see tests/e2e.rs).
const ROUNDS: usize = 9;
const STMT_LEN: usize = 13 + ROUNDS + 9;
/// the wrap circuit's IPA rounds (its domain is 2^13 — matching pickles'
/// `wrap_domains(0)`).
const WROUNDS: usize = 13;
/// the width-1 step statement: 5 Type2 pairs (cip, b, zsl, zds, perm of the
/// wrap proof), the wrap proof's sponge digest, beta/gamma, alpha/zeta/xi,
/// WROUNDS bulletproof challenges, should_finalize, then the new
/// messages_for_next_step digest and the messages_for_next_wrap digest.
const K2: usize = 10 + 1 + 2 + 3 + WROUNDS + 1 + 2;

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

fn fq_to_fp(x: Fq) -> Fp {
    Fp::from_le_bytes_mod_order(&x.into_bigint().to_bytes_le())
}

/// Everything the recursive step circuit witnesses (plain values).
struct Step2Data {
    // ---- finalize: the base step proof's deferred values + evaluations ----
    finalize_tokens: Vec<
        kimchi::circuits::expr::PolishToken<
            Fp,
            kimchi::circuits::berkeley_columns::Column,
            kimchi::circuits::berkeley_columns::BerkeleyChallengeTerm,
        >,
    >,
    finalize_domain: ark_poly::Radix2EvaluationDomain<Fp>,
    finalize_srs_log2: u32,
    finalize_endo: Fp,
    finalize_shifts: Vec<Fp>,
    ft_eval1: Fp,
    public_evals: [Vec<Fp>; 2],
    evals_flat: Vec<(Fp, Fp)>, // z, 6 selectors, 15 w, 15 coeff, 6 s
    // ---- the wrap statement (Fq values converted to Fp — all fit whp) ----
    stmt: Vec<Fp>, // STMT_LEN values in to_data order
    // ---- the previous accumulator (base case: app state + placeholder VK) ----
    wrap_vk_pts: Vec<(Fp, Fp)>,
    prev_app_state: Vec<Fp>,
    // ---- the wrap proof (Pallas: Fp coordinates) ----
    wrap_vk_digest: Fp,
    generic: (Fp, Fp),
    psm: (Fp, Fp),
    complete_add: (Fp, Fp),
    mul: (Fp, Fp),
    emul: (Fp, Fp),
    endomul_scalar: (Fp, Fp),
    coefficients: Vec<(Fp, Fp)>,
    sigma_init: Vec<(Fp, Fp)>,
    sigma_last: Vec<(Fp, Fp)>,
    w_comm: Vec<(Fp, Fp)>,
    z_comm: (Fp, Fp),
    t_comm: Vec<(Fp, Fp)>,
    lr: Vec<((Fp, Fp), (Fp, Fp))>,
    delta: (Fp, Fp),
    sg: (Fp, Fp),
    h: (Fp, Fp),
    // Type2 split pairs of the wrap proof's opening scalars (witness data)
    z1: (Fp, bool),
    z2: (Fp, bool),
    // x_hat constants: (L, correction) per packed slot + flag lagranges
    packed_lagranges: Vec<((Fp, Fp), (Fp, Fp))>,
    flag_lagranges: Vec<(Fp, Fp)>,
}

struct Step2Circuit {
    d: Step2Data,
}

impl SnarkyCircuit for Step2Circuit {
    type Curve = Vesta;
    // TODO: raise to 1 and fold the accumulator once kimchi's cross-size
    // folding is fixed (see dummy::tests::recursion_challenge_cross_size_folding)
    const PREV_CHALLENGES: usize = 0;
    type Proof = IpaProof<Self::Curve, FULL_ROUNDS>;
    type PrivateInput = ();
    /// the width-1 step statement (see [`K2`])
    type PublicInput = [FieldVar<Fp>; K2];
    type PublicOutput = ();

    fn circuit(
        &self,
        sys: &mut RunState<Fp>,
        stmt2: Self::PublicInput,
        _private: Option<&Self::PrivateInput>,
    ) -> SnarkyResult<()> {
        use groupmap::GroupMap;
        use pickles::composition_types::PlonkVerificationKeyEvals;
        use snarky::gadgets::curve::Point;

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
        // a Type2 pair read from two statement slots; the odd slot is
        // boolean-constrained here
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

        // ---- finalize params + evals ----
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
            |sys: &mut RunState<Fp>| -> SnarkyResult<pickles::fr_sponge::PointEvalVar<Fp>> {
                let &(a, b) = fe.next().unwrap();
                Ok((vec![w1(sys, a)?], vec![w1(sys, b)?]))
            };
        let evals = pickles::fr_sponge::AbsorbEvalsVar {
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
            public_evals: [wvec(sys, &d.public_evals[0])?, wvec(sys, &d.public_evals[1])?],
            evals,
        };

        // ---- the wrap statement vars (to_data order) ----
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
            bulletproof_challenges: sv[13..13 + ROUNDS].to_vec(),
            branch_data: sv[13 + ROUNDS].clone(),
            feature_flags: {
                let mut v = vec![];
                for _ in 0..8 {
                    let b: Boolean<Fp> = sys.compute(loc!(), |_| false)?;
                    v.push(b);
                }
                v
            },
        };
        // note: sv[12] (the previous messages_for_next_step_proof digest) is
        // recomputed in-circuit by verify_one from the accumulator below.

        // ---- previous accumulator ----
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
            coefficients_comm: (0..15).map(|_| it.next().unwrap()).collect(),
            generic_comm: it.next().unwrap(),
            psm_comm: it.next().unwrap(),
            complete_add_comm: it.next().unwrap(),
            mul_comm: it.next().unwrap(),
            emul_comm: it.next().unwrap(),
            endomul_scalar_comm: it.next().unwrap(),
        };
        let after_index = pickles::hash_messages::sponge_after_index(sys, loc!(), &dlog_index);
        let prev_app_state = wvec(sys, &d.prev_app_state)?;

        // ---- the wrap proof pieces ----
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
        // the wrap proof's z1/z2 stay witness data (opening proof); the
        // deferred scalars, transcript claims and bulletproof challenges come
        // from the statement (stmt2 layout: see K2)
        let wt2 = |sys: &mut RunState<Fp>,
                   p: (Fp, bool)|
         -> SnarkyResult<ShiftedScalar<Fp>> {
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
            bulletproof_challenges: stmt2[16..16 + WROUNDS].to_vec(),
        };
        let xi2 = stmt2[15].clone();
        // should_finalize (boolean-constrained statement bit) == must_verify
        let sf = stmt2[16 + WROUNDS].clone();
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
        // the recursive step's own app state: reuse the previous one
        let app_state = wvec(sys, &d.prev_app_state)?;
        let digest = step_main::<Fp, PallasParameters>(
            sys,
            loc!(),
            &app_state,
            &dlog_index,
            std::slice::from_ref(&per_proof),
            &params,
            pickles::endo::tick::base(),
            <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1,
            255,
        )?;
        digest.assert_equals(sys, loc!(), &stmt2[17 + WROUNDS])?;
        // stmt2[18 + WROUNDS]: the messages_for_next_wrap_proof digest —
        // asserted by the wrap circuit, a passthrough here
        Ok(())
    }
}

#[test]
fn pickles_recursive_step() {
    use mina_poseidon::poseidon::Sponge as _;
    type FpSponge = mina_poseidon::poseidon::ArithmeticSponge<
        Fp,
        PlonkSpongeConstantsKimchi,
        FULL_ROUNDS,
    >;

    // ---- 1. the base-case pickles proof ----
    let wrap_vk_pts: Vec<(Fp, Fp)> = (0..28u64)
        .map(|i| (Fp::from(1000 + i), Fp::from(2000 + i)))
        .collect();
    let base = prove_base_case::<SquareApp, ROUNDS, STMT_LEN>(
        SquareApp,
        Fp::from(7u64),
        wrap_vk_pts.clone(),
    );
    let prev_app_state = vec![Fp::from(49u64)];

    // ---- 2. finalize data: the base step proof's oracles + evaluations ----
    let svi = &base.step_verifier.index;
    let step_proof = &base.step_proof;
    let step_public = vec![{
        // the base statement digest, as the step proof's public input
        fq_to_fp(base.statement[12])
    }];
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
    let pair = |p: &kimchi::proof::PointEvaluations<Vec<Fp>>| {
        (p.zeta[0], p.zeta_omega[0])
    };
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

    // ---- 3. the wrap proof's transcript witness (step_witness) ----
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

    // the wrap proof's perm scalar (over Fq)
    let wcombined = wrap_proof.evals.combine(&wo.powers_of_eval_points_for_chunks);
    let wrap_srs_log2 = u64::BITS - 1 - (wvi.max_poly_size as u64).leading_zeros();
    let wdomain = pickles::plonk_checks::Domain::<Fq> {
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
    let wenv = pickles::plonk_checks::scalars_env::<Fq, bool>(&wdomain, wrap_srs_log2, &wminimal);
    let wevals = pickles::plonk_checks::Evals {
        w: wcombined.w.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
        s: wcombined.s.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
        z: (wcombined.z.zeta, wcombined.z.zeta_omega),
    };
    let wperm = pickles::plonk_checks::perm_scalar(&wenv, &wevals);

    let sw = pickles::step_witness::step_witness(
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

    // the wrap proof's raw polyscale challenge (Fr-sponge replay over Fq)
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

    // ---- 4. x_hat lagrange constants over the wrap domain ----
    // widths for the wrap statement at ROUNDS=9, with the digest terms as
    // 255-bit packed slots and 8 flag slots
    let widths = pickles::step_verifier::wrap_statement_packed_widths(ROUNDS);
    let packed_lagranges: Vec<((Fp, Fp), (Fp, Fp))> = widths
        .iter()
        .enumerate()
        .map(|(i, &n)| {
            let l = wlgr[i].chunks[0];
            let c = pickles::public_input::lagrange_correction(&l, n);
            ((l.x, l.y), (c.x, c.y))
        })
        .collect();
    let flag_lagranges: Vec<(Fp, Fp)> = (0..8)
        .map(|i| {
            let l = wlgr[widths.len() + i].chunks[0];
            (l.x, l.y)
        })
        .collect();

    // ---- 5. assemble the circuit data ----
    let co = |p: &Pallas| (p.x, p.y);
    let wh = wvi.srs().h;
    let d = Step2Data {
        finalize_tokens: svi.linearization.constant_term.clone(),
        finalize_domain: svi.domain,
        finalize_srs_log2: step_srs_log2,
        finalize_endo: svi.endo,
        finalize_shifts: svi.shift.to_vec(),
        ft_eval1: step_proof.ft_eval1,
        public_evals: so.public_evals.clone(),
        evals_flat,
        stmt: base.statement.iter().map(|&v| fq_to_fp(v)).collect(),
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

    // ---- 6. the new accumulator digest (prover mirror) ----
    let new_digest = {
        let mut s = FpSponge::new(Vesta::sponge_params());
        for (px, py) in &d.wrap_vk_pts {
            s.absorb(&[*px]);
            s.absorb(&[*py]);
        }
        for v in &prev_app_state {
            s.absorb(&[*v]);
        }
        // the verified proof's challenge-polynomial commitment
        s.absorb(&[d.sg.0]);
        s.absorb(&[d.sg.1]);
        // the finalize-output challenges: the field images of the *statement's*
        // bulletproof challenges (the base step proof's), exactly what
        // step_main's accumulator hash absorbs (fin.challenges)
        let endo_p = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1;
        for &raw_fq in &base.statement[13..13 + ROUNDS] {
            let raw = fq_to_fp(raw_fq);
            let f = pickles::scalar_challenge::ScalarChallenge(raw).to_field(endo_p);
            s.absorb(&[f]);
        }
        s.squeeze()
    };

    // ---- 7. the width-1 step statement (layout: see K2) ----
    let pair = |p: (Fp, bool)| [p.0, if p.1 { Fp::one() } else { Fp::from(0u64) }];
    let mut stmt2: Vec<Fp> = vec![];
    stmt2.extend(pair(sw.cip));
    stmt2.extend(pair(sw.b));
    stmt2.extend(pair(sw.zeta_to_srs_length));
    stmt2.extend(pair(sw.zeta_to_domain_size));
    stmt2.extend(pair(sw.perm));
    stmt2.push(fq_to_fp(sw.sponge_digest));
    stmt2.push(sw.beta_raw);
    stmt2.push(sw.gamma_raw);
    stmt2.push(sw.alpha_raw);
    stmt2.push(sw.zeta_raw);
    stmt2.push(fq_to_fp(xi2_raw));
    stmt2.extend(sw.bulletproof_prechallenges.iter().copied());
    stmt2.push(Fp::one()); // should_finalize
    stmt2.push(new_digest);
    stmt2.push(Fp::from(0u64)); // messages_for_next_wrap digest (passthrough)
    assert_eq!(stmt2.len(), K2);
    let stmt2_arr: [Fp; K2] = stmt2.try_into().unwrap();

    // ---- 8. prove the recursive step ----
    // The accumulator (sg_step1, chals_step1) is validated here out of
    // circuit; folding it into the step2 proof's opening awaits the kimchi
    // cross-size folding fix (see
    // dummy::tests::recursion_challenge_cross_size_folding) — the in-circuit
    // verification above is complete either way.
    let endo_p = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1;
    let chals_step1: Vec<Fp> = base.statement[13..13 + ROUNDS]
        .iter()
        .map(|&raw| {
            pickles::scalar_challenge::ScalarChallenge(fq_to_fp(raw)).to_field(endo_p)
        })
        .collect();
    {
        let sg_check = pickles::dummy::compute_sg(svi.srs(), &chals_step1);
        assert_eq!(
            sg_check, base.step_proof.proof.sg,
            "sg_step1 == commit(b_poly(chals_step1))"
        );
    }
    let (mut pi2, ver2) = Step2Circuit { d }.compile_to_indexes().unwrap();
    let (proof2, _) = pi2
        .prove::<VestaBase, VestaScalar>(stmt2_arr, (), true)
        .unwrap();
    ver2.verify::<VestaBase, VestaScalar>(proof2, stmt2_arr, ());
}

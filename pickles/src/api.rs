//! The base-case (width 0) pickles API: wrap an application circuit into a
//! step proof and produce the wrap proof — the pickles proof — in one call.
//!
//! ```text
//! let (proof, statement) = prove_base_case(&app, witness, wrap_vk)?;
//! ```
//!
//! The pipeline is the one validated end-to-end in `tests/e2e.rs`:
//! step proof on Vesta (public input = the accumulator digest), transcript
//! witness via [`crate::wrap::wrap_witness`], statement packing via
//! [`crate::composition_types::wrap::wrap_statement_to_field_elements`], and
//! the wrap proof on Pallas running [`crate::wrap_main::wrap_main`] with the
//! bulletproof equation asserted.
//!
//! Recursion (width ≥ 1) adds `verify_one`/`step_main` on the step side and
//! the finalize loop on the wrap side — the circuit pieces exist; the
//! surrounding data plumbing lands with the recursive API.

use ark_ff::{BigInteger, One, PrimeField};
use kimchi::circuits::wires::PERMUTS;
use kimchi::curve::KimchiCurve;
use mina_curves::pasta::{Fp, Fq, Pallas, Vesta, VestaParameters};
use mina_poseidon::constants::PlonkSpongeConstantsKimchi;
use mina_poseidon::poseidon::{ArithmeticSponge, Sponge as _};
use mina_poseidon::sponge::{DefaultFqSponge, DefaultFrSponge};
use poly_commitment::commitment::PolyComm;
use poly_commitment::ipa::OpeningProof as IpaProof;
use poly_commitment::SRS;
use snarky::{api::SnarkyCircuit, loc, FieldVar, RunState, SnarkyResult};

use crate::common::FULL_ROUNDS;
use crate::composition_types::{plonk, BranchData, BulletproofChallenge, Features, ProofsVerified};
use crate::incrementally_verify::{Advice, Messages, OpeningProof, VerificationKeyComm};
use crate::plonk_curve_ops::ShiftedScalar;
use crate::scalar_challenge::ScalarChallenge;
use crate::step_verifier::Claimed;
use crate::wrap_main::{wrap_main, StepStatementElement};

type VestaBase = DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type VestaScalar = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type PallasBase =
    DefaultFqSponge<mina_curves::pasta::PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type PallasScalar = DefaultFrSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type FpSponge = ArithmeticSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

/// An application circuit hosted by a base-case step proof.
pub trait StepApp {
    /// The private witness of one execution.
    type Witness;

    /// Runs the application logic in-circuit and returns the app state
    /// exposed through the accumulator digest.
    fn main(
        &self,
        sys: &mut RunState<Fp>,
        witness: Option<&Self::Witness>,
    ) -> SnarkyResult<Vec<FieldVar<Fp>>>;

    /// The out-of-circuit app state values for a witness (must match what
    /// [`StepApp::main`] computes — used by the prover to build the digest).
    fn state(&self, witness: &Self::Witness) -> Vec<Fp>;
}

/// The step circuit hosting an application: `main` plus the width-0 statement
/// (public input = the accumulator digest `hash(wrap_vk, app_state)`).
pub struct StepCircuit<A: StepApp> {
    pub app: A,
}

impl<A: StepApp> SnarkyCircuit for StepCircuit<A> {
    type Curve = Vesta;
    type Proof = IpaProof<Self::Curve, FULL_ROUNDS>;
    /// (app witness, the wrap VK's 28 commitment coordinates)
    type PrivateInput = (A::Witness, Vec<(Fp, Fp)>);
    type PublicInput = FieldVar<Fp>;
    type PublicOutput = ();

    fn circuit(
        &self,
        sys: &mut RunState<Fp>,
        digest: Self::PublicInput,
        private: Option<&Self::PrivateInput>,
    ) -> SnarkyResult<()> {
        use crate::composition_types::PlonkVerificationKeyEvals;
        use crate::hash_messages::{hash_messages_for_next_step_proof, sponge_after_index};
        use snarky::gadgets::curve::Point;

        let app_state = self.app.main(sys, private.map(|p| &p.0))?;

        let mut pts = vec![];
        for i in 0..28 {
            let (px, py) = (
                sys.compute(loc!(), move |_| private.unwrap().1[i].0)?,
                sys.compute(loc!(), move |_| private.unwrap().1[i].1)?,
            );
            pts.push(Point::new(px, py));
        }
        let mut it = pts.into_iter();
        let vk = PlonkVerificationKeyEvals {
            sigma_comm: (0..PERMUTS).map(|_| it.next().unwrap()).collect(),
            coefficients_comm: (0..15).map(|_| it.next().unwrap()).collect(),
            generic_comm: it.next().unwrap(),
            psm_comm: it.next().unwrap(),
            complete_add_comm: it.next().unwrap(),
            mul_comm: it.next().unwrap(),
            emul_comm: it.next().unwrap(),
            endomul_scalar_comm: it.next().unwrap(),
        };
        let after_index = sponge_after_index(sys, loc!(), &vk);
        let computed =
            hash_messages_for_next_step_proof(sys, loc!(), &after_index, &app_state, &[], &[])?;
        computed.assert_equals(sys, loc!(), &digest)?;
        Ok(())
    }
}

/// Everything the wrap circuit witnesses about the step proof.
pub struct WrapWitnessData {
    pub step_vk_digest: Fq,
    pub generic: (Fq, Fq),
    pub psm: (Fq, Fq),
    pub complete_add: (Fq, Fq),
    pub mul: (Fq, Fq),
    pub emul: (Fq, Fq),
    pub endomul_scalar: (Fq, Fq),
    pub coefficients: Vec<(Fq, Fq)>,
    pub sigma_init: Vec<(Fq, Fq)>,
    pub sigma_last: Vec<(Fq, Fq)>,
    pub w_comm: Vec<(Fq, Fq)>,
    pub z_comm: (Fq, Fq),
    pub t_comm: Vec<(Fq, Fq)>,
    pub lr: Vec<((Fq, Fq), (Fq, Fq))>,
    pub delta: (Fq, Fq),
    pub sg: (Fq, Fq),
    pub z1_repr: Fq,
    pub z2_repr: Fq,
    pub lagrange: (Fq, Fq),
    pub correction: (Fq, Fq),
    pub h: (Fq, Fq),
    pub new_acc_dummies: Vec<Vec<Fq>>,
}

/// The base-case wrap circuit: [`wrap_main`] over one step proof, public
/// input = the wrap statement (13 scalars, `ROUNDS` bulletproof challenges,
/// branch data, 8 feature flags; `STMT_LEN = 13 + ROUNDS + 9`).
pub struct WrapCircuit<const ROUNDS: usize, const STMT_LEN: usize> {
    pub w: WrapWitnessData,
}

impl<const ROUNDS: usize, const STMT_LEN: usize> SnarkyCircuit for WrapCircuit<ROUNDS, STMT_LEN> {
    type Curve = Pallas;
    type Proof = IpaProof<Self::Curve, FULL_ROUNDS>;
    type PrivateInput = ();
    type PublicInput = [FieldVar<Fq>; STMT_LEN];
    type PublicOutput = ();

    fn circuit(
        &self,
        sys: &mut RunState<Fq>,
        stmt: Self::PublicInput,
        _private: Option<&Self::PrivateInput>,
    ) -> SnarkyResult<()> {
        use groupmap::GroupMap;
        use snarky::gadgets::curve::Point;

        let w = &self.w;
        let mkpt = |sys: &mut RunState<Fq>, p: (Fq, Fq)| -> SnarkyResult<Point<Fq>> {
            Ok(Point::new(
                sys.compute(loc!(), move |_| p.0)?,
                sys.compute(loc!(), move |_| p.1)?,
            ))
        };
        let mkpts = |sys: &mut RunState<Fq>, ps: &[(Fq, Fq)]| -> SnarkyResult<Vec<Point<Fq>>> {
            let mut out = vec![];
            for &p in ps {
                out.push(mkpt(sys, p)?);
            }
            Ok(out)
        };
        let cpt = |p: (Fq, Fq)| Point::new(FieldVar::constant(p.0), FieldVar::constant(p.1));

        // destructure the statement (to_data order)
        let cip = stmt[0].clone();
        let b = stmt[1].clone();
        let zsl = stmt[2].clone();
        let zds = stmt[3].clone();
        let perm = stmt[4].clone();
        let beta = stmt[5].clone();
        let gamma = stmt[6].clone();
        let alpha = stmt[7].clone();
        let zeta = stmt[8].clone();
        let xi = stmt[9].clone();
        let sponge_digest = stmt[10].clone();
        let msgs_wrap_digest = stmt[11].clone();
        let msgs_step_digest = stmt[12].clone();
        let bp: Vec<FieldVar<Fq>> = stmt[13..13 + ROUNDS].to_vec();

        let vk_digest: FieldVar<Fq> = sys.compute(loc!(), |_| w.step_vk_digest)?;
        let vk = VerificationKeyComm {
            generic: mkpt(sys, w.generic)?,
            psm: mkpt(sys, w.psm)?,
            complete_add: mkpt(sys, w.complete_add)?,
            mul: mkpt(sys, w.mul)?,
            emul: mkpt(sys, w.emul)?,
            endomul_scalar: mkpt(sys, w.endomul_scalar)?,
            coefficients: mkpts(sys, &w.coefficients)?,
            sigma_init: mkpts(sys, &w.sigma_init)?,
            sigma_last: mkpts(sys, &w.sigma_last)?,
        };
        let messages = Messages {
            w_comm: w
                .w_comm
                .iter()
                .map(|&p| Ok(vec![mkpt(sys, p)?]))
                .collect::<SnarkyResult<Vec<_>>>()?,
            z_comm: vec![mkpt(sys, w.z_comm)?],
            t_comm: w
                .t_comm
                .iter()
                .map(|&p| mkpt(sys, p))
                .collect::<SnarkyResult<Vec<_>>>()?,
        };
        let mut lr = vec![];
        for &(l, r) in &w.lr {
            lr.push((mkpt(sys, l)?, mkpt(sys, r)?));
        }
        let h = cpt(w.h);
        let t1 = ShiftedScalar::Type1;
        let openings = OpeningProof {
            lr,
            delta: mkpt(sys, w.delta)?,
            z1: t1(sys.compute(loc!(), |_| w.z1_repr)?),
            z2: t1(sys.compute(loc!(), |_| w.z2_repr)?),
            challenge_polynomial_commitment: mkpt(sys, w.sg)?,
            h_generator: h.clone(),
        };
        let advice = Advice {
            combined_inner_product: t1(cip),
            b: t1(b),
            perm: t1(perm),
            zeta_to_srs_length: t1(zsl),
            zeta_to_domain_size: t1(zds),
        };
        let claimed = Claimed {
            beta,
            gamma,
            alpha,
            zeta,
            sponge_digest_before_evaluations: sponge_digest,
            bulletproof_challenges: bp,
        };

        let elements = vec![StepStatementElement::Packed {
            value: msgs_step_digest,
            num_bits: 255,
        }];
        let lagranges = vec![(cpt(w.lagrange), cpt(w.correction))];

        let params = groupmap::BWParameters::<VestaParameters>::setup();
        let _out = wrap_main::<Fq, VestaParameters>(
            sys,
            loc!(),
            &[],
            &vk_digest,
            &vk,
            &elements,
            &lagranges,
            &h,
            &messages,
            &openings,
            &advice,
            &xi,
            &claimed,
            &msgs_wrap_digest,
            &w.new_acc_dummies,
            &params,
            crate::endo::tock::base(),
            <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1,
            255,
        )?;
        Ok(())
    }
}

fn fp_to_fq(x: Fp) -> Fq {
    Fq::from_le_bytes_mod_order(&x.into_bigint().to_bytes_le())
}

/// The base-case pickles proof plus everything the *next* (recursive) step
/// proof consumes: the wrap proof and its statement, both verifier wrappers,
/// and the underlying step proof (whose evaluations the recursive finalize
/// re-checks).
pub struct BaseCaseProof<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize> {
    pub statement: Vec<Fq>,
    pub proof: kimchi::proof::ProverProof<Pallas, IpaProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS>,
    pub step_proof: kimchi::proof::ProverProof<Vesta, IpaProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS>,
    pub step_verifier: snarky::api::VerifierIndexWrapper<StepCircuit<A>>,
    pub wrap_verifier: snarky::api::VerifierIndexWrapper<WrapCircuit<ROUNDS, STMT_LEN>>,
}

/// Proves one application execution through the full base-case pipeline and
/// verifies the resulting wrap proof. `ROUNDS` must match the step circuit's
/// IPA round count (log2 of its compiled domain).
pub fn prove_base_case<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize>(
    app: A,
    witness: A::Witness,
    wrap_vk_pts: Vec<(Fp, Fp)>,
) -> BaseCaseProof<A, ROUNDS, STMT_LEN> {
    assert_eq!(STMT_LEN, 13 + ROUNDS + 9, "STMT_LEN mismatch");
    // ---- step proof ----
    let app_state = app.state(&witness);
    let step = StepCircuit { app };
    let (mut step_pi, step_ver) = step.compile_to_indexes().unwrap();
    let svi = &step_ver.index;

    let digest = {
        let mut s = FpSponge::new(Vesta::sponge_params());
        for (px, py) in &wrap_vk_pts {
            s.absorb(&[*px]);
            s.absorb(&[*py]);
        }
        for v in &app_state {
            s.absorb(&[*v]);
        }
        s.squeeze()
    };
    let (step_proof, _) = step_pi
        .prove::<VestaBase, VestaScalar>(digest, (witness, wrap_vk_pts), true)
        .unwrap();

    // ---- wrap witness ----
    let public_input = vec![digest];
    let lgr = svi.srs().get_lagrange_basis(svi.domain);
    let com: Vec<_> = lgr.iter().take(svi.public).collect();
    let elm: Vec<_> = public_input.iter().map(|s| -*s).collect();
    let pc = PolyComm::<Vesta>::multi_scalar_mul(&com, &elm);
    let public_comm = svi
        .srs()
        .mask_custom(pc.clone(), &pc.map(|_| Fp::one()))
        .unwrap()
        .commitment;
    let o = step_proof
        .oracles::<VestaBase, VestaScalar, _>(svi, &public_comm, Some(&public_input))
        .unwrap();
    let oracles = &o.oracles;

    let combined = step_proof.evals.combine(&o.powers_of_eval_points_for_chunks);
    let srs_log2 = u64::BITS - 1 - (svi.max_poly_size as u64).leading_zeros();
    let domain = crate::plonk_checks::Domain::<Fp> {
        log2_size: svi.domain.log_size_of_group,
        generator: svi.domain.group_gen,
    };
    let minimal = plonk::Minimal::<Fp, Fp, bool> {
        alpha: oracles.alpha,
        beta: oracles.beta,
        gamma: oracles.gamma,
        zeta: oracles.zeta,
        joint_combiner: None,
        feature_flags: Features::none(),
    };
    let env = crate::plonk_checks::scalars_env::<Fp, bool>(&domain, srs_log2, &minimal);
    let evals = crate::plonk_checks::Evals {
        w: combined.w.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
        s: combined.s.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
        z: (combined.z.zeta, combined.z.zeta_omega),
    };
    let perm = crate::plonk_checks::perm_scalar(&env, &evals);

    let ww = crate::wrap::wrap_witness(
        svi.max_poly_size as u64,
        svi.domain.size,
        svi.domain.group_gen,
        &step_proof,
        &public_comm,
        svi.digest::<VestaBase>(),
        &[],
        o.combined_inner_product,
        oracles.zeta,
        oracles.u,
        perm,
    );

    let claimed_xi_raw: Fp = {
        use kimchi::plonk_sponge::FrSponge as _;
        let params = Vesta::sponge_params();
        let mut fr = VestaScalar::from(params);
        fr.absorb(&o.digest);
        let pcd = VestaScalar::from(params).digest();
        fr.absorb(&pcd);
        fr.absorb(&step_proof.ft_eval1);
        fr.absorb_multiple(&o.public_evals[0]);
        fr.absorb_multiple(&o.public_evals[1]);
        fr.absorb_evaluations(&step_proof.evals);
        fr.squeeze(mina_poseidon::sponge::CHALLENGE_LENGTH_IN_LIMBS)
    };

    // ---- statement ----
    let dummy_wrap_chals: Vec<Vec<Fq>> = {
        let endo_wrap = <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1;
        let endo_step = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1;
        crate::dummy::pad_wrap_challenges::<Fq, Fp>(&[], endo_wrap, endo_step)
    };
    let sg_pt = step_proof.proof.sg;
    let msgs_wrap_digest = crate::hash_messages::hash_messages_for_next_wrap_proof_ref(
        Pallas::sponge_params(),
        &dummy_wrap_chals,
        &[],
        (sg_pt.x, sg_pt.y),
    );

    let plonk_vals = plonk::InCircuit::<Fq, ScalarChallenge<Fq>, bool> {
        alpha: ScalarChallenge(ww.alpha_raw),
        beta: ww.beta_raw,
        gamma: ww.gamma_raw,
        zeta: ScalarChallenge(ww.zeta_raw),
        zeta_to_srs_length: fp_to_fq(ww.zeta_to_srs_length_repr),
        zeta_to_domain_size: fp_to_fq(ww.zeta_to_domain_size_repr),
        perm: fp_to_fq(ww.perm_repr),
        feature_flags: Features::none(),
        joint_combiner: None,
    };
    let bp_chals: Vec<BulletproofChallenge<ScalarChallenge<Fq>>> = ww
        .bulletproof_prechallenges
        .iter()
        .map(|&c| BulletproofChallenge {
            prechallenge: ScalarChallenge(c),
        })
        .collect();
    let branch = BranchData {
        proofs_verified: ProofsVerified::N0,
        domain_log2: svi.domain.log_size_of_group as u8,
    };
    let statement = crate::composition_types::wrap::wrap_statement_to_field_elements(
        &plonk_vals,
        fp_to_fq(ww.cip_repr),
        fp_to_fq(ww.b_repr),
        &ScalarChallenge(fp_to_fq(claimed_xi_raw)),
        &bp_chals,
        &branch,
        fp_to_fq(ww.sponge_digest),
        msgs_wrap_digest,
        fp_to_fq(digest),
    );
    assert_eq!(statement.len(), STMT_LEN, "statement length");

    // ---- wrap proof ----
    let co = |p: &Vesta| (p.x, p.y);
    let l0 = lgr[0].chunks[0];
    drop(lgr); // release the SRS cache guard so step_ver can move below
    let correction = crate::public_input::lagrange_correction(&l0, 255);
    let srs_h = svi.srs().h;
    let wdata = WrapWitnessData {
        step_vk_digest: svi.digest::<VestaBase>(),
        generic: co(&svi.generic_comm.chunks[0]),
        psm: co(&svi.psm_comm.chunks[0]),
        complete_add: co(&svi.complete_add_comm.chunks[0]),
        mul: co(&svi.mul_comm.chunks[0]),
        emul: co(&svi.emul_comm.chunks[0]),
        endomul_scalar: co(&svi.endomul_scalar_comm.chunks[0]),
        coefficients: svi
            .coefficients_comm
            .iter()
            .map(|c| co(&c.chunks[0]))
            .collect(),
        sigma_init: svi.sigma_comm[..PERMUTS - 1]
            .iter()
            .map(|c| co(&c.chunks[0]))
            .collect(),
        sigma_last: vec![co(&svi.sigma_comm[PERMUTS - 1].chunks[0])],
        w_comm: step_proof
            .commitments
            .w_comm
            .iter()
            .map(|c| co(&c.chunks[0]))
            .collect(),
        z_comm: co(&step_proof.commitments.z_comm.chunks[0]),
        t_comm: step_proof
            .commitments
            .t_comm
            .chunks
            .iter()
            .map(co)
            .collect(),
        lr: step_proof
            .proof
            .lr
            .iter()
            .map(|(l, r)| (co(l), co(r)))
            .collect(),
        delta: co(&step_proof.proof.delta),
        sg: co(&sg_pt),
        z1_repr: fp_to_fq(ww.z1_repr),
        z2_repr: fp_to_fq(ww.z2_repr),
        lagrange: co(&l0),
        correction: co(&correction),
        h: (srs_h.x, srs_h.y),
        new_acc_dummies: dummy_wrap_chals,
    };

    let stmt_arr: [Fq; STMT_LEN] = statement.clone().try_into().unwrap_or_else(|_| unreachable!());
    let (mut wrap_pi, wrap_ver) = WrapCircuit::<ROUNDS, STMT_LEN> { w: wdata }
        .compile_to_indexes()
        .unwrap();
    let (wrap_proof, _) = wrap_pi
        .prove::<PallasBase, PallasScalar>(stmt_arr, (), true)
        .unwrap();
    wrap_ver.verify::<PallasBase, PallasScalar>(wrap_proof.clone(), stmt_arr, ());

    BaseCaseProof {
        statement,
        proof: wrap_proof,
        step_proof,
        step_verifier: step_ver,
        wrap_verifier: wrap_ver,
    }
}

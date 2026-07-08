//! The first recursive step (proofs_verified = 1): a second step circuit runs
//! [`pickles::step_main::step_main`] over the base-case wrap proof —
//! finalizing the wrap statement's deferred values (the base step proof's
//! scalars) against that proof's evaluations, re-deriving the wrap proof's
//! whole transcript, recommitting the wrap statement through the real Pallas
//! Lagrange basis, and asserting the bulletproof equation — with
//! `must_verify = true`, so every check is real.

use ark_ff::One;
use kimchi::circuits::wires::PERMUTS;
use kimchi::curve::KimchiCurve;
use mina_curves::pasta::{Fp, Fq, Pallas, PallasParameters, Vesta};
use mina_poseidon::constants::PlonkSpongeConstantsKimchi;
use mina_poseidon::sponge::{DefaultFqSponge, DefaultFrSponge};
use poly_commitment::commitment::PolyComm;
use poly_commitment::SRS;
use snarky::{api::SnarkyCircuit, loc, FieldVar, RunState, SnarkyResult};

use pickles::api::{prove_base_case, StepApp};
use pickles::composition_types::{plonk, Features};
use pickles::recursive_step::{
    embed_fq_to_fp, width1_step_statement_len, RecursiveStepCircuit, RecursiveStepData,
};

const FULL_ROUNDS: usize = snarky::FULL_ROUNDS;

type VestaBase =
    DefaultFqSponge<mina_curves::pasta::VestaParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
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
const K2: usize = width1_step_statement_len(WROUNDS);

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
        embed_fq_to_fp(base.statement[12])
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
    let wcombined = wrap_proof
        .evals
        .combine(&wo.powers_of_eval_points_for_chunks);
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
    let d = RecursiveStepData {
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
    let chals_step1: Vec<Fp> = base.statement[13..13 + ROUNDS]
        .iter()
        .map(|&raw| {
            pickles::scalar_challenge::ScalarChallenge(embed_fq_to_fp(raw)).to_field(endo_p)
        })
        .collect();

    // ---- 6. the new accumulator digest (prover mirror) ----
    let new_digest = pickles::hash_messages::hash_messages_for_next_step_proof_ref(
        Vesta::sponge_params(),
        &d.wrap_vk_pts,
        &prev_app_state,
        &[d.sg],
        &[chals_step1.clone()],
    );

    // ---- 7. the width-1 step statement (layout: see K2) ----
    let pair = |p: (Fp, bool)| [p.0, if p.1 { Fp::one() } else { Fp::from(0u64) }];
    let mut stmt2: Vec<Fp> = vec![];
    stmt2.extend(pair(sw.cip));
    stmt2.extend(pair(sw.b));
    stmt2.extend(pair(sw.zeta_to_srs_length));
    stmt2.extend(pair(sw.zeta_to_domain_size));
    stmt2.extend(pair(sw.perm));
    stmt2.push(embed_fq_to_fp(sw.sponge_digest));
    stmt2.push(sw.beta_raw);
    stmt2.push(sw.gamma_raw);
    stmt2.push(sw.alpha_raw);
    stmt2.push(sw.zeta_raw);
    stmt2.push(embed_fq_to_fp(xi2_raw));
    stmt2.extend(sw.bulletproof_prechallenges.iter().copied());
    stmt2.push(Fp::one()); // should_finalize
    stmt2.push(new_digest);
    stmt2.push(Fp::from(0u64)); // messages_for_next_wrap digest (passthrough)
    assert_eq!(stmt2.len(), K2);
    let stmt2_arr: [Fp; K2] = stmt2.try_into().unwrap();

    // ---- 8. prove the recursive step, folding the accumulator ----
    // The step2 proof opens the base step proof's challenge-polynomial
    // commitment (sg) with its field-form challenges: kimchi absorbs the
    // commitment into the transcript and folds b(X) into the opening — the
    // term the next wrap circuit's combined commitment covers as sg_old.
    {
        let sg_check = pickles::dummy::compute_sg(svi.srs(), &chals_step1);
        assert_eq!(
            sg_check, base.step_proof.proof.sg,
            "sg_step1 == commit(b_poly(chals_step1))"
        );
    }
    let recursion = kimchi::proof::RecursionChallenge {
        chals: chals_step1,
        comm: PolyComm {
            chunks: vec![base.step_proof.proof.sg],
        },
    };
    let (mut pi2, ver2) = RecursiveStepCircuit::<ROUNDS, WROUNDS, K2> { d }
        .compile_to_indexes()
        .unwrap();
    let (proof2, _) = pi2
        .prove_with_recursion::<VestaBase, VestaScalar>(stmt2_arr, (), true, vec![recursion])
        .unwrap();
    ver2.verify::<VestaBase, VestaScalar>(proof2, stmt2_arr, ());
}

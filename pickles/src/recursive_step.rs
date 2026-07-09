//! Helpers for the first non-base step proof.
//!
//! This module keeps the recursion test focused on witness construction while
//! the step circuit plumbing lives in the crate.

use ark_ff::{AdditiveGroup, BigInteger, Field, One, PrimeField, Zero};
use groupmap::GroupMap;
use kimchi::{
    circuits::wires::{COLUMNS, PERMUTS},
    curve::KimchiCurve,
    verifier_index::VerifierIndex,
};
use mina_curves::pasta::{Fp, Fq, Pallas, PallasParameters, Vesta, VestaParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use poly_commitment::{commitment::PolyComm, ipa::OpeningProof as IpaProof, SRS};
use snarky::{api::SnarkyCircuit, loc, Boolean, FieldVar, RunState, SnarkyResult};

use crate::{
    api::{
        BaseCaseProof, StepApp, WrapCircuit, WrapStepStatementSlot, WrapUnfinalizedWitnessData,
        WrapWitnessData,
    },
    common::FULL_ROUNDS,
    composition_types::{plonk, BranchData, BulletproofChallenge, Features, ProofsVerified},
    finalize::{FinalizeParams, ShiftKind},
    incrementally_verify::{Advice, Messages, OpeningProof, VerificationKeyComm},
    plonk_curve_ops::ShiftedScalar,
    scalar_challenge::ScalarChallenge,
    step_main::{step_main, PerProofInput},
    step_verifier::{Claimed, FinalizeEvals, WrapStatementVars},
};

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
    step_statement_len(1, wrap_rounds)
}

pub const fn step_statement_len(proofs: usize, wrap_rounds: usize) -> usize {
    proofs * (17 + wrap_rounds) + 2
}

pub fn embed_fq_to_fp(x: Fq) -> Fp {
    Fp::from_le_bytes_mod_order(&x.into_bigint().to_bytes_le())
}

pub fn embed_fp_to_fq(x: Fp) -> Fq {
    Fq::from_le_bytes_mod_order(&x.into_bigint().to_bytes_le())
}

pub fn type2_pair_to_fields(p: (Fp, bool)) -> [Fp; 2] {
    [p.0, if p.1 { Fp::one() } else { Fp::from(0u64) }]
}

pub fn type2_pair_to_fq_repr(p: (Fp, bool)) -> Fq {
    let mut repr = embed_fp_to_fq(p.0);
    repr += repr;
    if p.1 {
        repr += Fq::one();
    }
    repr
}

pub fn build_width1_step_statement<const WRAP_ROUNDS: usize, const PUBLIC_INPUT_LEN: usize>(
    witness: &crate::step_witness::StepWitness,
    xi_raw: Fq,
    messages_for_next_step_digest: Fp,
    messages_for_next_wrap_digest: Fp,
    should_finalize: bool,
) -> [Fp; PUBLIC_INPUT_LEN] {
    assert_eq!(PUBLIC_INPUT_LEN, width1_step_statement_len(WRAP_ROUNDS));
    let statement = build_step_statement::<WRAP_ROUNDS>(
        &[(witness, xi_raw, should_finalize)],
        messages_for_next_step_digest,
        messages_for_next_wrap_digest,
    );
    statement.try_into().unwrap_or_else(|_| unreachable!())
}

pub fn build_step_statement<const WRAP_ROUNDS: usize>(
    proofs: &[(&crate::step_witness::StepWitness, Fq, bool)],
    messages_for_next_step_digest: Fp,
    messages_for_next_wrap_digest: Fp,
) -> Vec<Fp> {
    let mut statement = Vec::with_capacity(step_statement_len(proofs.len(), WRAP_ROUNDS));
    for &(witness, xi_raw, should_finalize) in proofs {
        assert_eq!(witness.bulletproof_prechallenges.len(), WRAP_ROUNDS);
        statement.extend(type2_pair_to_fields(witness.cip));
        statement.extend(type2_pair_to_fields(witness.b));
        statement.extend(type2_pair_to_fields(witness.zeta_to_srs_length));
        statement.extend(type2_pair_to_fields(witness.zeta_to_domain_size));
        statement.extend(type2_pair_to_fields(witness.perm));
        statement.push(embed_fq_to_fp(witness.sponge_digest));
        statement.push(witness.beta_raw);
        statement.push(witness.gamma_raw);
        statement.push(witness.alpha_raw);
        statement.push(witness.zeta_raw);
        statement.push(embed_fq_to_fp(xi_raw));
        statement.extend(witness.bulletproof_prechallenges.iter().copied());
        statement.push(if should_finalize {
            Fp::one()
        } else {
            Fp::zero()
        });
    }
    statement.push(messages_for_next_step_digest);
    statement.push(messages_for_next_wrap_digest);
    statement
}

pub fn width1_step_statement_slots<const WRAP_ROUNDS: usize>(
    statement: &[Fp],
) -> Vec<WrapStepStatementSlot> {
    step_statement_slots::<WRAP_ROUNDS>(statement, 1)
}

pub fn step_statement_slots<const WRAP_ROUNDS: usize>(
    statement: &[Fp],
    proofs: usize,
) -> Vec<WrapStepStatementSlot> {
    assert_eq!(statement.len(), step_statement_len(proofs, WRAP_ROUNDS));
    let mut slots = Vec::with_capacity(statement.len());
    let per_proof = 17 + WRAP_ROUNDS;
    for proof in 0..proofs {
        let base = proof * per_proof;
        for i in (base..base + 10).step_by(2) {
            slots.push(WrapStepStatementSlot::Packed {
                value: embed_fp_to_fq(statement[i]),
                num_bits: 255,
            });
            slots.push(WrapStepStatementSlot::Bool(!statement[i + 1].is_zero()));
        }
        slots.push(WrapStepStatementSlot::Packed {
            value: embed_fp_to_fq(statement[base + 10]),
            num_bits: 255,
        });
        for i in base + 11..base + 16 + WRAP_ROUNDS {
            slots.push(WrapStepStatementSlot::Packed {
                value: embed_fp_to_fq(statement[i]),
                num_bits: 128,
            });
        }
        slots.push(WrapStepStatementSlot::Bool(
            !statement[base + 16 + WRAP_ROUNDS].is_zero(),
        ));
    }
    for &value in &statement[proofs * per_proof..] {
        slots.push(WrapStepStatementSlot::Packed {
            value: embed_fp_to_fq(value),
            num_bits: 255,
        });
    }
    debug_assert_eq!(slots.len(), statement.len());
    slots
}

pub fn flatten_proof_evaluations(
    evals: &kimchi::proof::ProofEvaluations<kimchi::proof::PointEvaluations<Vec<Fp>>>,
) -> Vec<(Fp, Fp)> {
    let pair = |p: &kimchi::proof::PointEvaluations<Vec<Fp>>| (p.zeta[0], p.zeta_omega[0]);
    let mut out = vec![
        pair(&evals.z),
        pair(&evals.generic_selector),
        pair(&evals.poseidon_selector),
        pair(&evals.complete_add_selector),
        pair(&evals.mul_selector),
        pair(&evals.emul_selector),
        pair(&evals.endomul_scalar_selector),
    ];
    out.extend(evals.w.iter().map(pair));
    out.extend(evals.coefficients.iter().map(pair));
    out.extend(evals.s.iter().map(pair));
    out
}

pub fn flatten_wrap_proof_evaluations(
    evals: &kimchi::proof::ProofEvaluations<kimchi::proof::PointEvaluations<Vec<Fq>>>,
) -> Vec<(Fq, Fq)> {
    let pair = |p: &kimchi::proof::PointEvaluations<Vec<Fq>>| (p.zeta[0], p.zeta_omega[0]);
    let mut out = vec![
        pair(&evals.z),
        pair(&evals.generic_selector),
        pair(&evals.poseidon_selector),
        pair(&evals.complete_add_selector),
        pair(&evals.mul_selector),
        pair(&evals.emul_selector),
        pair(&evals.endomul_scalar_selector),
    ];
    out.extend(evals.w.iter().map(pair));
    out.extend(evals.coefficients.iter().map(pair));
    out.extend(evals.s.iter().map(pair));
    out
}

pub fn wrap_x_hat_lagranges(
    lagrange_basis: &[PolyComm<Pallas>],
    prev_rounds: usize,
) -> (Vec<((Fp, Fp), (Fp, Fp))>, Vec<(Fp, Fp)>) {
    let widths = crate::step_verifier::wrap_statement_packed_widths(prev_rounds);
    let packed_lagranges = widths
        .iter()
        .enumerate()
        .map(|(i, &num_bits)| {
            let l = lagrange_basis[i].chunks[0];
            let c = crate::public_input::lagrange_correction(&l, num_bits);
            ((l.x, l.y), (c.x, c.y))
        })
        .collect();
    let flag_lagranges = (0..8)
        .map(|i| {
            let l = lagrange_basis[widths.len() + i].chunks[0];
            (l.x, l.y)
        })
        .collect();
    (packed_lagranges, flag_lagranges)
}

pub fn statement_challenges_to_field<const ROUNDS: usize>(statement: &[Fq]) -> Vec<Fp> {
    let endo_p = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1;
    statement[13..13 + ROUNDS]
        .iter()
        .map(|&raw| crate::scalar_challenge::ScalarChallenge(embed_fq_to_fp(raw)).to_field(endo_p))
        .collect()
}

pub fn recursion_challenge(
    srs: &poly_commitment::ipa::SRS<Vesta>,
    step_proof: &kimchi::proof::ProverProof<Vesta, IpaProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS>,
    chals: Vec<Fp>,
) -> kimchi::proof::RecursionChallenge<Vesta> {
    let sg_check = crate::dummy::compute_sg(srs, &chals);
    assert_eq!(
        sg_check, step_proof.proof.sg,
        "sg_step1 == commit(b_poly(chals_step1))"
    );
    kimchi::proof::RecursionChallenge {
        chals,
        comm: PolyComm {
            chunks: vec![step_proof.proof.sg],
        },
    }
}

/// Builds the wrap-side unfinalized witness for the base wrap proof carried by
/// the first recursive step statement.
pub fn wrap_unfinalized_from_base<
    A: StepApp,
    const PREV_ROUNDS: usize,
    const PREV_STMT_LEN: usize,
>(
    base: &BaseCaseProof<A, PREV_ROUNDS, PREV_STMT_LEN>,
) -> WrapUnfinalizedWitnessData {
    let dummy_wrap_chals: Vec<Vec<Fq>> = {
        let endo_wrap = <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1;
        let endo_step = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1;
        crate::dummy::pad_wrap_challenges::<Fq, Fp>(&[], endo_wrap, endo_step)
    };
    wrap_unfinalized_from_parts(
        &base.wrap_verifier.index,
        &base.proof,
        &base.statement,
        (base.step_proof.proof.sg.x, base.step_proof.proof.sg.y),
        dummy_wrap_chals,
        vec![],
    )
}

fn wrap_unfinalized_from_parts(
    wvi: &VerifierIndex<FULL_ROUNDS, Pallas, poly_commitment::ipa::SRS<Pallas>>,
    wrap_proof: &kimchi::proof::ProverProof<Pallas, IpaProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS>,
    wrap_statement: &[Fq],
    prev_step_acc: (Fq, Fq),
    hash_dummy_challenges: Vec<Vec<Fq>>,
    hash_old_bulletproof_challenges: Vec<Vec<Fq>>,
) -> WrapUnfinalizedWitnessData {
    let wlgr = wvi.srs().get_lagrange_basis(wvi.domain);
    let wcom: Vec<_> = wlgr.iter().take(wvi.public).collect();
    let welm: Vec<_> = wrap_statement.iter().map(|s| -*s).collect();
    let wpc = PolyComm::<Pallas>::multi_scalar_mul(&wcom, &welm);
    let wrap_public_comm = wvi
        .srs()
        .mask_custom(wpc.clone(), &wpc.map(|_| Fq::one()))
        .unwrap()
        .commitment;
    let wo = wrap_proof
        .oracles::<PallasBase, PallasScalar, _>(wvi, &wrap_public_comm, Some(wrap_statement))
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

    let xi_raw: Fq = {
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

    let (_, endo_r) = <Pallas as KimchiCurve<FULL_ROUNDS>>::endos();

    WrapUnfinalizedWitnessData {
        finalize_tokens: wvi.linearization.constant_term.clone(),
        finalize_domain: wvi.domain,
        finalize_srs_log2: wrap_srs_log2,
        finalize_endo: wvi.endo,
        finalize_endo_r: *endo_r,
        finalize_shifts: wvi.shift.to_vec(),
        ft_eval1: wrap_proof.ft_eval1,
        public_evals: wo.public_evals.clone(),
        evals_flat: flatten_wrap_proof_evaluations(&wrap_proof.evals),
        alpha: embed_fp_to_fq(sw.alpha_raw),
        beta: embed_fp_to_fq(sw.beta_raw),
        gamma: embed_fp_to_fq(sw.gamma_raw),
        zeta: embed_fp_to_fq(sw.zeta_raw),
        xi: xi_raw,
        cip_repr: type2_pair_to_fq_repr(sw.cip),
        b_repr: type2_pair_to_fq_repr(sw.b),
        perm_repr: type2_pair_to_fq_repr(sw.perm),
        bulletproof_challenges: sw
            .bulletproof_prechallenges
            .iter()
            .copied()
            .map(embed_fp_to_fq)
            .collect(),
        sponge_digest_before_evaluations: sw.sponge_digest,
        should_finalize: true,
        old_bulletproof_challenges: vec![],
        prev_step_acc,
        hash_dummy_challenges,
        hash_old_bulletproof_challenges,
    }
}

/// Plain witness data for a recursive step circuit that verifies one wrap
/// proof and folds it into the next step accumulator.
#[derive(Clone)]
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
    pub messages_for_next_step_accumulators: Vec<(Fp, Fp)>,
    pub prev_challenge_polynomial_commitments: Vec<(Fp, Fp)>,
    pub prev_challenges: Vec<Vec<Fp>>,
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
    const WIDTH: usize = 1,
> {
    pub d: [RecursiveStepData; WIDTH],
}

pub struct PreparedRecursiveStep<const PUBLIC_INPUT_LEN: usize> {
    pub data: RecursiveStepData,
    pub statement: [Fp; PUBLIC_INPUT_LEN],
    pub recursion: kimchi::proof::RecursionChallenge<Vesta>,
    pub verified_wrap_accumulator: (Fp, Fp),
    pub finalized_step_challenges: Vec<Fp>,
}

pub struct PreparedRecursiveStepWidth2<const WIDTH1_INPUT_LEN: usize, const PUBLIC_INPUT_LEN: usize>
{
    pub proofs: [RecursiveStepData; 2],
    pub dummy_slots: [bool; 2],
    pub app_state: Vec<Fp>,
    pub statement: [Fp; PUBLIC_INPUT_LEN],
    pub recursions: [kimchi::proof::RecursionChallenge<Vesta>; 2],
}

pub struct RecursiveStepWidth2Circuit<
    const PREV_ROUNDS: usize,
    const WRAP_ROUNDS: usize,
    const WIDTH1_INPUT_LEN: usize,
    const PUBLIC_INPUT_LEN: usize,
> {
    pub proofs: [RecursiveStepData; 2],
    pub dummy_slots: [bool; 2],
    pub app_state: Vec<Fp>,
}

pub struct RecursiveStepWidth2Proof<
    const PREV_ROUNDS: usize,
    const WRAP_ROUNDS: usize,
    const WIDTH1_INPUT_LEN: usize,
    const PUBLIC_INPUT_LEN: usize,
> {
    pub statement: [Fp; PUBLIC_INPUT_LEN],
    pub proof: kimchi::proof::ProverProof<Vesta, IpaProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS>,
    pub verifier: snarky::api::VerifierIndexWrapper<
        RecursiveStepWidth2Circuit<PREV_ROUNDS, WRAP_ROUNDS, WIDTH1_INPUT_LEN, PUBLIC_INPUT_LEN>,
    >,
}

/// A proved width-1 recursive step, ready to be wrapped by the next Pickles
/// layer once the generic wrap-proof plumbing is exposed.
pub struct RecursiveStepProof<
    const PREV_ROUNDS: usize,
    const WRAP_ROUNDS: usize,
    const PUBLIC_INPUT_LEN: usize,
> {
    pub statement: [Fp; PUBLIC_INPUT_LEN],
    pub proof: kimchi::proof::ProverProof<Vesta, IpaProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS>,
    pub verifier: snarky::api::VerifierIndexWrapper<
        RecursiveStepCircuit<PREV_ROUNDS, WRAP_ROUNDS, PUBLIC_INPUT_LEN>,
    >,
    pub verified_wrap_accumulator: (Fp, Fp),
    pub finalized_step_challenges: Vec<Fp>,
}

pub struct PreparedRecursiveWrap<const STEP_ROUNDS: usize, const WRAP_STMT_LEN: usize> {
    pub data: WrapWitnessData,
    pub statement: [Fq; WRAP_STMT_LEN],
    pub domain_log2: u32,
    pub next_wrap_old_challenges: Vec<Vec<Fq>>,
    pub next_wrap_dummy_challenges: Vec<Vec<Fq>>,
}

pub struct RecursiveWrapProof<const STEP_ROUNDS: usize, const WRAP_STMT_LEN: usize> {
    pub statement: [Fq; WRAP_STMT_LEN],
    pub proof: kimchi::proof::ProverProof<Pallas, IpaProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS>,
    pub verifier: snarky::api::VerifierIndexWrapper<WrapCircuit<STEP_ROUNDS, WRAP_STMT_LEN>>,
    pub next_wrap_old_challenges: Vec<Vec<Fq>>,
    pub next_wrap_dummy_challenges: Vec<Vec<Fq>>,
}

/// One complete recursive Pickles cycle: a step proof that verifies the
/// previous wrap proof, followed by the wrap proof for that new step.
pub struct RecursiveCycleProof<
    const PREV_ROUNDS: usize,
    const VERIFIED_WRAP_ROUNDS: usize,
    const STEP_PROOF_ROUNDS: usize,
    const STEP_STMT_LEN: usize,
    const WRAP_STMT_LEN: usize,
> {
    pub step: RecursiveStepProof<PREV_ROUNDS, VERIFIED_WRAP_ROUNDS, STEP_STMT_LEN>,
    pub wrap: RecursiveWrapProof<STEP_PROOF_ROUNDS, WRAP_STMT_LEN>,
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
    let step_public = [embed_fq_to_fp(base.statement[12])];
    prepare_recursive_step_from_parts::<PREV_ROUNDS, WRAP_ROUNDS, PUBLIC_INPUT_LEN>(
        &base.step_verifier.index,
        &base.step_proof,
        &step_public,
        &base.wrap_verifier.index,
        &base.proof,
        &base.statement,
        vec![],
        vec![],
        vec![],
        wrap_vk_pts,
        prev_app_state,
    )
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prepare_recursive_step_from_parts<
    const PREV_ROUNDS: usize,
    const WRAP_ROUNDS: usize,
    const PUBLIC_INPUT_LEN: usize,
>(
    svi: &VerifierIndex<FULL_ROUNDS, Vesta, poly_commitment::ipa::SRS<Vesta>>,
    step_proof: &kimchi::proof::ProverProof<Vesta, IpaProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS>,
    step_public: &[Fp],
    wvi: &VerifierIndex<FULL_ROUNDS, Pallas, poly_commitment::ipa::SRS<Pallas>>,
    wrap_proof: &kimchi::proof::ProverProof<Pallas, IpaProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS>,
    wrap_statement: &[Fq],
    messages_for_next_step_accumulators: Vec<(Fp, Fp)>,
    prev_challenge_polynomial_commitments: Vec<(Fp, Fp)>,
    prev_challenges: Vec<Vec<Fp>>,
    wrap_vk_pts: Vec<(Fp, Fp)>,
    prev_app_state: Vec<Fp>,
) -> PreparedRecursiveStep<PUBLIC_INPUT_LEN> {
    assert_eq!(PUBLIC_INPUT_LEN, width1_step_statement_len(WRAP_ROUNDS));

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
    let evals_flat = flatten_proof_evaluations(&step_proof.evals);
    let step_srs_log2 = u64::BITS - 1 - (svi.max_poly_size as u64).leading_zeros();

    let wlgr = wvi.srs().get_lagrange_basis(wvi.domain);
    let wcom: Vec<_> = wlgr.iter().take(wvi.public).collect();
    let welm: Vec<_> = wrap_statement.iter().map(|s| -*s).collect();
    let wpc = PolyComm::<Pallas>::multi_scalar_mul(&wcom, &welm);
    let wrap_public_comm = wvi
        .srs()
        .mask_custom(wpc.clone(), &wpc.map(|_| Fq::one()))
        .unwrap()
        .commitment;
    let wo = wrap_proof
        .oracles::<PallasBase, PallasScalar, _>(wvi, &wrap_public_comm, Some(wrap_statement))
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

    let (packed_lagranges, flag_lagranges) = wrap_x_hat_lagranges(&wlgr, PREV_ROUNDS);

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
        stmt: wrap_statement.iter().map(|&v| embed_fq_to_fp(v)).collect(),
        wrap_vk_pts,
        prev_app_state: prev_app_state.clone(),
        messages_for_next_step_accumulators,
        prev_challenge_polynomial_commitments,
        prev_challenges,
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

    let raw_step_challenges: Vec<BulletproofChallenge<ScalarChallenge<Fp>>> = wrap_statement
        [13..13 + PREV_ROUNDS]
        .iter()
        .map(|&raw| BulletproofChallenge {
            prechallenge: ScalarChallenge(embed_fq_to_fp(raw)),
        })
        .collect();
    let prepared_messages = crate::reduced_messages::Step {
        app_state: prev_app_state.clone(),
        challenge_polynomial_commitments: vec![data.sg],
        old_bulletproof_challenges: vec![raw_step_challenges],
    }
    .prepare(
        crate::reduced_messages::plonk_verification_key_from_list(&data.wrap_vk_pts),
        <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1,
    );
    let chals_step1 = prepared_messages.old_bulletproof_challenges[0].clone();

    let new_digest = crate::hash_messages::hash_messages_for_next_step_proof_ref(
        Vesta::sponge_params(),
        &prepared_messages
            .dlog_plonk_index
            .to_list()
            .into_iter()
            .copied()
            .collect::<Vec<_>>(),
        &prepared_messages.app_state,
        &prepared_messages.challenge_polynomial_commitments,
        &prepared_messages.old_bulletproof_challenges,
    );

    let statement = build_width1_step_statement::<WRAP_ROUNDS, PUBLIC_INPUT_LEN>(
        &sw,
        xi2_raw,
        new_digest,
        Fp::from(0u64),
        true,
    );

    let recursion = recursion_challenge(svi.srs(), step_proof, chals_step1);
    let verified_wrap_accumulator = data.sg;

    PreparedRecursiveStep {
        data,
        statement,
        recursion,
        verified_wrap_accumulator,
        finalized_step_challenges: statement_challenges_to_field::<PREV_ROUNDS>(wrap_statement),
    }
}

/// Proves and verifies the first recursive step over a base-case wrap proof.
///
/// This is the reusable Rust-side counterpart of the test harness: it keeps
/// witness construction, statement construction, recursive proving and local
/// verification in one API step while the general multi-branch `compile` API is
/// still being ported.
pub fn prove_recursive_step<
    A: StepApp,
    const PREV_ROUNDS: usize,
    const WRAP_ROUNDS: usize,
    const PREV_STMT_LEN: usize,
    const PUBLIC_INPUT_LEN: usize,
>(
    base: &BaseCaseProof<A, PREV_ROUNDS, PREV_STMT_LEN>,
    wrap_vk_pts: Vec<(Fp, Fp)>,
    prev_app_state: Vec<Fp>,
) -> RecursiveStepProof<PREV_ROUNDS, WRAP_ROUNDS, PUBLIC_INPUT_LEN> {
    let prepared =
        prepare_recursive_step::<A, PREV_ROUNDS, WRAP_ROUNDS, PREV_STMT_LEN, PUBLIC_INPUT_LEN>(
            base,
            wrap_vk_pts,
            prev_app_state,
        );

    let verified_wrap_accumulator = prepared.verified_wrap_accumulator;
    let finalized_step_challenges = prepared.finalized_step_challenges.clone();
    let (mut prover, verifier) =
        RecursiveStepCircuit::<PREV_ROUNDS, WRAP_ROUNDS, PUBLIC_INPUT_LEN> { d: [prepared.data] }
            .compile_to_indexes()
            .unwrap();
    let (proof, _) = prover
        .prove_with_recursion::<VestaBase, VestaScalar>(
            prepared.statement,
            (),
            true,
            vec![prepared.recursion],
        )
        .unwrap();
    verifier.verify::<VestaBase, VestaScalar>(proof.clone(), prepared.statement, ());

    RecursiveStepProof {
        statement: prepared.statement,
        proof,
        verifier,
        verified_wrap_accumulator,
        finalized_step_challenges,
    }
}

pub fn prepare_recursive_step_width2<
    const WRAP_ROUNDS: usize,
    const WIDTH1_INPUT_LEN: usize,
    const PUBLIC_INPUT_LEN: usize,
>(
    first: PreparedRecursiveStep<WIDTH1_INPUT_LEN>,
    second: PreparedRecursiveStep<WIDTH1_INPUT_LEN>,
    app_state: Vec<Fp>,
) -> PreparedRecursiveStepWidth2<WIDTH1_INPUT_LEN, PUBLIC_INPUT_LEN> {
    assert_eq!(WIDTH1_INPUT_LEN, width1_step_statement_len(WRAP_ROUNDS));
    assert_eq!(PUBLIC_INPUT_LEN, step_statement_len(2, WRAP_ROUNDS));
    assert_eq!(first.data.wrap_vk_pts, second.data.wrap_vk_pts);
    assert_eq!(
        first.statement[WIDTH1_INPUT_LEN - 1],
        second.statement[WIDTH1_INPUT_LEN - 1]
    );

    let cpcs = [
        first.verified_wrap_accumulator,
        second.verified_wrap_accumulator,
    ];
    let challenges = [
        first.finalized_step_challenges.clone(),
        second.finalized_step_challenges.clone(),
    ];
    let combined_digest = crate::hash_messages::hash_messages_for_next_step_proof_ref(
        Vesta::sponge_params(),
        &first.data.wrap_vk_pts,
        &app_state,
        &cpcs,
        &challenges,
    );
    let per_proof = 17 + WRAP_ROUNDS;
    let mut statement = Vec::with_capacity(PUBLIC_INPUT_LEN);
    statement.extend_from_slice(&first.statement[..per_proof]);
    statement.extend_from_slice(&second.statement[..per_proof]);
    statement.push(combined_digest);
    statement.push(first.statement[WIDTH1_INPUT_LEN - 1]);

    PreparedRecursiveStepWidth2 {
        proofs: [first.data, second.data],
        dummy_slots: [false, false],
        app_state,
        statement: statement.try_into().unwrap_or_else(|_| unreachable!()),
        recursions: [first.recursion, second.recursion],
    }
}

/// Pads one real previous proof to Kimchi's physical width two. The leading
/// slot is skipped by the step verifier and contributes Pickles' canonical
/// dummy accumulator/challenges; the trailing slot is the real proof.
pub fn prepare_recursive_step_n1<
    const WRAP_ROUNDS: usize,
    const WIDTH1_INPUT_LEN: usize,
    const PUBLIC_INPUT_LEN: usize,
>(
    real: PreparedRecursiveStep<WIDTH1_INPUT_LEN>,
    app_state: Vec<Fp>,
) -> PreparedRecursiveStepWidth2<WIDTH1_INPUT_LEN, PUBLIC_INPUT_LEN> {
    use poly_commitment::{commitment::PolyComm, ipa::SRS, SRS as _};

    assert_eq!(WIDTH1_INPUT_LEN, width1_step_statement_len(WRAP_ROUNDS));
    assert_eq!(PUBLIC_INPUT_LEN, step_statement_len(2, WRAP_ROUNDS));

    let (dummy_wrap, dummy_step) = crate::dummy::ipa_wrap_and_step::<Fq, Fp>(
        <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1,
        <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1,
    );
    let wrap_srs = SRS::<Pallas>::create(1 << crate::common::TOCK_ROUNDS);
    let dummy_wrap_sg = crate::dummy::compute_sg(&wrap_srs, &dummy_wrap.challenges_computed);
    let dummy_accumulator = (dummy_wrap_sg.x, dummy_wrap_sg.y);

    let combined_digest = crate::hash_messages::hash_messages_for_next_step_proof_ref(
        Vesta::sponge_params(),
        &real.data.wrap_vk_pts,
        &app_state,
        &[dummy_accumulator, real.verified_wrap_accumulator],
        &[
            dummy_step.challenges_computed.clone(),
            real.finalized_step_challenges.clone(),
        ],
    );

    let per_proof = 17 + WRAP_ROUNDS;
    let mut dummy_statement = real.statement[..per_proof].to_vec();
    dummy_statement[16 + WRAP_ROUNDS] = Fp::zero();
    let mut statement = Vec::with_capacity(PUBLIC_INPUT_LEN);
    statement.extend(dummy_statement);
    statement.extend_from_slice(&real.statement[..per_proof]);
    statement.push(combined_digest);
    statement.push(real.statement[WIDTH1_INPUT_LEN - 1]);

    let step_srs = SRS::<Vesta>::create(1 << crate::common::TICK_ROUNDS);
    let dummy_step_sg = crate::dummy::compute_sg(&step_srs, &dummy_step.challenges_computed);
    let dummy_recursion = kimchi::proof::RecursionChallenge {
        chals: dummy_step.challenges_computed,
        comm: PolyComm {
            chunks: vec![dummy_step_sg],
        },
    };

    PreparedRecursiveStepWidth2 {
        proofs: [real.data.clone(), real.data],
        dummy_slots: [true, false],
        app_state,
        statement: statement.try_into().unwrap_or_else(|_| unreachable!()),
        recursions: [dummy_recursion, real.recursion],
    }
}

pub fn prove_recursive_step_width2<
    const PREV_ROUNDS: usize,
    const WRAP_ROUNDS: usize,
    const WIDTH1_INPUT_LEN: usize,
    const PUBLIC_INPUT_LEN: usize,
>(
    prepared: PreparedRecursiveStepWidth2<WIDTH1_INPUT_LEN, PUBLIC_INPUT_LEN>,
) -> RecursiveStepWidth2Proof<PREV_ROUNDS, WRAP_ROUNDS, WIDTH1_INPUT_LEN, PUBLIC_INPUT_LEN> {
    let statement = prepared.statement;
    let circuit = RecursiveStepWidth2Circuit::<
        PREV_ROUNDS,
        WRAP_ROUNDS,
        WIDTH1_INPUT_LEN,
        PUBLIC_INPUT_LEN,
    > {
        proofs: prepared.proofs,
        dummy_slots: prepared.dummy_slots,
        app_state: prepared.app_state,
    };
    let (mut prover, verifier) = circuit
        .compile_to_indexes_with_minimum_domain_log2(crate::common::TICK_ROUNDS as u32)
        .unwrap();
    let (proof, _) = prover
        .prove_with_recursion::<VestaBase, VestaScalar>(
            statement,
            (),
            true,
            prepared.recursions.to_vec(),
        )
        .unwrap();
    verifier.verify::<VestaBase, VestaScalar>(proof.clone(), statement, ());
    RecursiveStepWidth2Proof {
        statement,
        proof,
        verifier,
    }
}

pub fn prepare_recursive_wrap<
    A: StepApp,
    const BASE_ROUNDS: usize,
    const VERIFIED_WRAP_ROUNDS: usize,
    const STEP_PROOF_ROUNDS: usize,
    const BASE_STMT_LEN: usize,
    const STEP_STMT_LEN: usize,
    const WRAP_STMT_LEN: usize,
>(
    base: &BaseCaseProof<A, BASE_ROUNDS, BASE_STMT_LEN>,
    step: &RecursiveStepProof<BASE_ROUNDS, VERIFIED_WRAP_ROUNDS, STEP_STMT_LEN>,
) -> PreparedRecursiveWrap<STEP_PROOF_ROUNDS, WRAP_STMT_LEN> {
    prepare_recursive_wrap_from_parts::<STEP_PROOF_ROUNDS, WRAP_STMT_LEN>(
        &step.verifier.index,
        &step.proof,
        &step.statement,
        width1_step_statement_slots::<VERIFIED_WRAP_ROUNDS>(&step.statement),
        vec![wrap_unfinalized_from_base(base)],
        vec![base.step_proof.proof.sg],
        ProofsVerified::N1,
    )
}

fn prepare_recursive_wrap_from_parts<const STEP_PROOF_ROUNDS: usize, const WRAP_STMT_LEN: usize>(
    svi: &VerifierIndex<FULL_ROUNDS, Vesta, poly_commitment::ipa::SRS<Vesta>>,
    step_proof: &kimchi::proof::ProverProof<Vesta, IpaProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS>,
    step_statement_values: &[Fp],
    step_statement: Vec<WrapStepStatementSlot>,
    unfinalized: Vec<WrapUnfinalizedWitnessData>,
    sg_olds: Vec<Vesta>,
    proofs_verified: ProofsVerified,
) -> PreparedRecursiveWrap<STEP_PROOF_ROUNDS, WRAP_STMT_LEN> {
    assert_eq!(WRAP_STMT_LEN, 13 + STEP_PROOF_ROUNDS + 9);
    assert_eq!(step_proof.proof.lr.len(), STEP_PROOF_ROUNDS);
    assert_eq!(unfinalized.len(), proofs_verified.to_usize());

    let step_public = step_statement_values.to_vec();
    let lgr = svi.srs().get_lagrange_basis(svi.domain);
    let com: Vec<_> = lgr.iter().take(svi.public).collect();
    let elm: Vec<_> = step_public.iter().map(|s| -*s).collect();
    let pc = PolyComm::<Vesta>::multi_scalar_mul(&com, &elm);
    let public_comm = svi
        .srs()
        .mask_custom(pc.clone(), &pc.map(|_| Fp::one()))
        .unwrap()
        .commitment;
    let o = step_proof
        .oracles::<VestaBase, VestaScalar, _>(svi, &public_comm, Some(&step_public))
        .unwrap();
    let oracles = &o.oracles;

    let combined = step_proof
        .evals
        .combine(&o.powers_of_eval_points_for_chunks);
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
        step_proof,
        &public_comm,
        svi.digest::<VestaBase>(),
        &sg_olds,
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
        let pcd = {
            let mut prev = VestaScalar::from(params);
            for challenge in &step_proof.prev_challenges {
                prev.absorb_multiple(&challenge.chals);
            }
            prev.digest()
        };
        fr.absorb(&pcd);
        fr.absorb(&step_proof.ft_eval1);
        fr.absorb_multiple(&o.public_evals[0]);
        fr.absorb_multiple(&o.public_evals[1]);
        fr.absorb_evaluations(&step_proof.evals);
        fr.squeeze(mina_poseidon::sponge::CHALLENGE_LENGTH_IN_LIMBS)
    };

    let raw_unfinalized_bp: Vec<Vec<BulletproofChallenge<ScalarChallenge<Fq>>>> = unfinalized
        .iter()
        .map(|u| {
            u.bulletproof_challenges
                .iter()
                .copied()
                .map(|c| BulletproofChallenge {
                    prechallenge: ScalarChallenge(c),
                })
                .collect()
        })
        .collect();
    let prepared_wrap_messages = crate::reduced_messages::Wrap {
        challenge_polynomial_commitment: (step_proof.proof.sg.x, step_proof.proof.sg.y),
        old_bulletproof_challenges: raw_unfinalized_bp,
    }
    .prepare(unfinalized[0].finalize_endo_r);
    let new_chals = prepared_wrap_messages.old_bulletproof_challenges.clone();
    let padded_wrap_challenges = crate::dummy::pad_wrap_challenges::<Fq, Fp>(
        &new_chals,
        <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1,
        <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1,
    );
    let next_wrap_dummy_challenges =
        padded_wrap_challenges[..crate::common::MAX_PROOFS_VERIFIED - new_chals.len()].to_vec();
    let msgs_wrap_digest = crate::hash_messages::hash_messages_for_next_wrap_proof_ref(
        Pallas::sponge_params(),
        &next_wrap_dummy_challenges,
        &prepared_wrap_messages.old_bulletproof_challenges,
        prepared_wrap_messages.challenge_polynomial_commitment,
    );

    let plonk_vals = plonk::InCircuit::<Fq, ScalarChallenge<Fq>, bool> {
        alpha: ScalarChallenge(ww.alpha_raw),
        beta: ww.beta_raw,
        gamma: ww.gamma_raw,
        zeta: ScalarChallenge(ww.zeta_raw),
        zeta_to_srs_length: embed_fp_to_fq(ww.zeta_to_srs_length_repr),
        zeta_to_domain_size: embed_fp_to_fq(ww.zeta_to_domain_size_repr),
        perm: embed_fp_to_fq(ww.perm_repr),
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
    let domain_log2 = crate::common::wrap_domain_log2(proofs_verified.to_usize());
    let branch = BranchData {
        proofs_verified,
        domain_log2: domain_log2 as u8,
    };
    let statement = crate::composition_types::wrap::wrap_statement_to_field_elements(
        &plonk_vals,
        embed_fp_to_fq(ww.cip_repr),
        embed_fp_to_fq(ww.b_repr),
        &ScalarChallenge(embed_fp_to_fq(claimed_xi_raw)),
        &bp_chals,
        &branch,
        embed_fp_to_fq(ww.sponge_digest),
        msgs_wrap_digest,
        embed_fp_to_fq(step_statement_values[step_statement_values.len() - 2]),
    );
    assert_eq!(statement.len(), WRAP_STMT_LEN);

    let co = |p: &Vesta| (p.x, p.y);
    let step_statement_lagranges: Vec<((Fq, Fq), (Fq, Fq))> = step_statement
        .iter()
        .enumerate()
        .map(|(i, slot)| {
            let l = lgr[i].chunks[0];
            let c = match slot {
                WrapStepStatementSlot::Packed { num_bits, .. } => {
                    crate::public_input::lagrange_correction(&l, *num_bits)
                }
                WrapStepStatementSlot::Bool(_) => l,
            };
            ((l.x, l.y), (c.x, c.y))
        })
        .collect();
    let srs_h = svi.srs().h;
    let reconstructed_public_comm =
        reconstruct_step_statement_commitment(&step_statement, &step_statement_lagranges, srs_h);
    assert_eq!(
        reconstructed_public_comm, public_comm.chunks[0],
        "recursive wrap step statement x_hat"
    );
    let data = WrapWitnessData {
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
        sg: co(&step_proof.proof.sg),
        z1_repr: embed_fp_to_fq(ww.z1_repr),
        z2_repr: embed_fp_to_fq(ww.z2_repr),
        sg_olds: sg_olds.iter().map(co).collect(),
        unfinalized,
        step_statement,
        step_statement_lagranges,
        h: (srs_h.x, srs_h.y),
        new_acc_dummies: next_wrap_dummy_challenges.clone(),
    };

    PreparedRecursiveWrap {
        data,
        statement: statement.try_into().unwrap_or_else(|_| unreachable!()),
        domain_log2,
        next_wrap_old_challenges: new_chals,
        next_wrap_dummy_challenges,
    }
}

pub fn prepare_recursive_wrap_width2<
    A: StepApp,
    const BASE_ROUNDS: usize,
    const BASE_STMT_LEN: usize,
    const PREV_ROUNDS: usize,
    const WRAP_ROUNDS: usize,
    const WIDTH1_INPUT_LEN: usize,
    const STEP_STMT_LEN: usize,
    const STEP_PROOF_ROUNDS: usize,
    const WRAP_STMT_LEN: usize,
>(
    bases: [&BaseCaseProof<A, BASE_ROUNDS, BASE_STMT_LEN>; 2],
    step: &RecursiveStepWidth2Proof<PREV_ROUNDS, WRAP_ROUNDS, WIDTH1_INPUT_LEN, STEP_STMT_LEN>,
) -> PreparedRecursiveWrap<STEP_PROOF_ROUNDS, WRAP_STMT_LEN> {
    let sg_olds: Vec<Vesta> = step
        .proof
        .prev_challenges
        .iter()
        .flat_map(|challenge| challenge.comm.chunks.iter().copied())
        .collect();
    prepare_recursive_wrap_from_parts::<STEP_PROOF_ROUNDS, WRAP_STMT_LEN>(
        &step.verifier.index,
        &step.proof,
        &step.statement,
        step_statement_slots::<WRAP_ROUNDS>(&step.statement, 2),
        vec![
            wrap_unfinalized_from_base(bases[0]),
            wrap_unfinalized_from_base(bases[1]),
        ],
        sg_olds,
        ProofsVerified::N2,
    )
}

/// Wraps a physically width-two `[dummy, real]` step proof while carrying one
/// logical unfinalized proof (`ProofsVerified::N1`).
pub fn prepare_recursive_wrap_n1<
    A: StepApp,
    const BASE_ROUNDS: usize,
    const BASE_STMT_LEN: usize,
    const PREV_ROUNDS: usize,
    const WRAP_ROUNDS: usize,
    const WIDTH1_INPUT_LEN: usize,
    const STEP_STMT_LEN: usize,
    const STEP_PROOF_ROUNDS: usize,
    const WRAP_STMT_LEN: usize,
>(
    base: &BaseCaseProof<A, BASE_ROUNDS, BASE_STMT_LEN>,
    step: &RecursiveStepWidth2Proof<PREV_ROUNDS, WRAP_ROUNDS, WIDTH1_INPUT_LEN, STEP_STMT_LEN>,
) -> PreparedRecursiveWrap<STEP_PROOF_ROUNDS, WRAP_STMT_LEN> {
    let sg_olds: Vec<Vesta> = step
        .proof
        .prev_challenges
        .iter()
        .flat_map(|challenge| challenge.comm.chunks.iter().copied())
        .collect();
    assert_eq!(sg_olds.len(), 2, "N1 step proof must be physically padded");
    prepare_recursive_wrap_from_parts::<STEP_PROOF_ROUNDS, WRAP_STMT_LEN>(
        &step.verifier.index,
        &step.proof,
        &step.statement,
        step_statement_slots::<WRAP_ROUNDS>(&step.statement, 2),
        vec![wrap_unfinalized_from_base(base)],
        sg_olds,
        ProofsVerified::N1,
    )
}

pub fn prove_recursive_wrap<const STEP_ROUNDS: usize, const WRAP_STMT_LEN: usize>(
    prepared: PreparedRecursiveWrap<STEP_ROUNDS, WRAP_STMT_LEN>,
) -> RecursiveWrapProof<STEP_ROUNDS, WRAP_STMT_LEN> {
    let domain_log2 = prepared.domain_log2;
    let statement = prepared.statement;
    let next_wrap_old_challenges = prepared.next_wrap_old_challenges;
    let next_wrap_dummy_challenges = prepared.next_wrap_dummy_challenges;
    let circuit = WrapCircuit::<STEP_ROUNDS, WRAP_STMT_LEN> { w: prepared.data };
    let (mut prover, verifier) = circuit
        .compile_to_indexes_with_minimum_domain_log2(domain_log2)
        .unwrap();
    let (proof, _) = prover
        .prove::<PallasBase, PallasScalar>(statement, (), true)
        .unwrap();
    verifier.verify::<PallasBase, PallasScalar>(proof.clone(), statement, ());

    RecursiveWrapProof {
        statement,
        proof,
        verifier,
        next_wrap_old_challenges,
        next_wrap_dummy_challenges,
    }
}

/// Proves and locally verifies the first complete recursive step→wrap cycle.
///
/// This is the current high-level recursion primitive while the general
/// multi-rule compiler is still being ported. The returned step proof is kept
/// because its evaluations and accumulator are required by the next cycle.
#[allow(clippy::too_many_arguments)]
pub fn prove_first_recursive_cycle<
    A: StepApp,
    const BASE_ROUNDS: usize,
    const VERIFIED_WRAP_ROUNDS: usize,
    const STEP_PROOF_ROUNDS: usize,
    const BASE_STMT_LEN: usize,
    const STEP_STMT_LEN: usize,
    const WRAP_STMT_LEN: usize,
>(
    base: &BaseCaseProof<A, BASE_ROUNDS, BASE_STMT_LEN>,
    wrap_vk_pts: Vec<(Fp, Fp)>,
    prev_app_state: Vec<Fp>,
) -> RecursiveCycleProof<
    BASE_ROUNDS,
    VERIFIED_WRAP_ROUNDS,
    STEP_PROOF_ROUNDS,
    STEP_STMT_LEN,
    WRAP_STMT_LEN,
> {
    let step =
        prove_recursive_step::<A, BASE_ROUNDS, VERIFIED_WRAP_ROUNDS, BASE_STMT_LEN, STEP_STMT_LEN>(
            base,
            wrap_vk_pts,
            prev_app_state,
        );
    let prepared_wrap = prepare_recursive_wrap::<
        A,
        BASE_ROUNDS,
        VERIFIED_WRAP_ROUNDS,
        STEP_PROOF_ROUNDS,
        BASE_STMT_LEN,
        STEP_STMT_LEN,
        WRAP_STMT_LEN,
    >(base, &step);
    assert!(
        recursive_wrap_ipa_equation_holds(&prepared_wrap),
        "prepared recursive wrap IPA equation"
    );
    let wrap = prove_recursive_wrap(prepared_wrap);

    RecursiveCycleProof { step, wrap }
}

/// Proves the first recursive cycle using the verification key of the base
/// wrap proof itself. This is the production path after
/// [`crate::api::prove_base_case_two_pass`]; callers no longer thread an
/// unrelated 28-point placeholder into the recursive accumulator.
pub fn prove_first_recursive_cycle_with_real_vk<
    A: StepApp,
    const BASE_ROUNDS: usize,
    const VERIFIED_WRAP_ROUNDS: usize,
    const STEP_PROOF_ROUNDS: usize,
    const BASE_STMT_LEN: usize,
    const STEP_STMT_LEN: usize,
    const WRAP_STMT_LEN: usize,
>(
    base: &BaseCaseProof<A, BASE_ROUNDS, BASE_STMT_LEN>,
    prev_app_state: Vec<Fp>,
) -> RecursiveCycleProof<
    BASE_ROUNDS,
    VERIFIED_WRAP_ROUNDS,
    STEP_PROOF_ROUNDS,
    STEP_STMT_LEN,
    WRAP_STMT_LEN,
> {
    let wrap_vk_pts = crate::api::wrap_verification_key_points(&base.wrap_verifier);
    assert_eq!(
        base.wrap_vk_pts, wrap_vk_pts,
        "base step proof must hash its own wrap verification key"
    );
    prove_first_recursive_cycle::<
        A,
        BASE_ROUNDS,
        VERIFIED_WRAP_ROUNDS,
        STEP_PROOF_ROUNDS,
        BASE_STMT_LEN,
        STEP_STMT_LEN,
        WRAP_STMT_LEN,
    >(base, wrap_vk_pts, prev_app_state)
}

/// Prepares the next step after a complete recursive cycle.
///
/// Unlike [`prepare_recursive_step`], both the finalized step proof and the
/// wrap proof being verified come from the previous recursive cycle.
pub fn prepare_next_recursive_step<
    const PREV_ROUNDS: usize,
    const VERIFIED_WRAP_ROUNDS: usize,
    const PREV_STEP_PROOF_ROUNDS: usize,
    const PREV_STEP_STMT_LEN: usize,
    const PREV_WRAP_STMT_LEN: usize,
    const WRAP_PROOF_ROUNDS: usize,
    const PUBLIC_INPUT_LEN: usize,
>(
    previous: &RecursiveCycleProof<
        PREV_ROUNDS,
        VERIFIED_WRAP_ROUNDS,
        PREV_STEP_PROOF_ROUNDS,
        PREV_STEP_STMT_LEN,
        PREV_WRAP_STMT_LEN,
    >,
    wrap_vk_pts: Vec<(Fp, Fp)>,
    prev_app_state: Vec<Fp>,
) -> PreparedRecursiveStep<PUBLIC_INPUT_LEN> {
    assert_eq!(previous.wrap.proof.proof.lr.len(), WRAP_PROOF_ROUNDS);
    prepare_recursive_step_from_parts::<PREV_STEP_PROOF_ROUNDS, WRAP_PROOF_ROUNDS, PUBLIC_INPUT_LEN>(
        &previous.step.verifier.index,
        &previous.step.proof,
        &previous.step.statement,
        &previous.wrap.verifier.index,
        &previous.wrap.proof,
        &previous.wrap.statement,
        vec![previous.step.verified_wrap_accumulator],
        vec![],
        vec![previous.step.finalized_step_challenges.clone()],
        wrap_vk_pts,
        prev_app_state,
    )
}

/// Reconstructs the wrap-side unfinalized witness carried into the wrap after
/// the next recursive step.
pub fn wrap_unfinalized_from_recursive_cycle<
    const PREV_ROUNDS: usize,
    const VERIFIED_WRAP_ROUNDS: usize,
    const STEP_PROOF_ROUNDS: usize,
    const STEP_STMT_LEN: usize,
    const WRAP_STMT_LEN: usize,
>(
    previous: &RecursiveCycleProof<
        PREV_ROUNDS,
        VERIFIED_WRAP_ROUNDS,
        STEP_PROOF_ROUNDS,
        STEP_STMT_LEN,
        WRAP_STMT_LEN,
    >,
) -> WrapUnfinalizedWitnessData {
    wrap_unfinalized_from_parts(
        &previous.wrap.verifier.index,
        &previous.wrap.proof,
        &previous.wrap.statement,
        (
            previous.step.proof.proof.sg.x,
            previous.step.proof.proof.sg.y,
        ),
        previous.wrap.next_wrap_dummy_challenges.clone(),
        previous.wrap.next_wrap_old_challenges.clone(),
    )
}

pub fn prepare_next_recursive_wrap<
    const CYCLE_PREV_ROUNDS: usize,
    const CYCLE_VERIFIED_WRAP_ROUNDS: usize,
    const PREV_STEP_PROOF_ROUNDS: usize,
    const PREV_STEP_STMT_LEN: usize,
    const PREV_WRAP_STMT_LEN: usize,
    const WRAP_PROOF_ROUNDS: usize,
    const NEXT_STEP_STMT_LEN: usize,
    const NEXT_STEP_PROOF_ROUNDS: usize,
    const NEXT_WRAP_STMT_LEN: usize,
>(
    previous: &RecursiveCycleProof<
        CYCLE_PREV_ROUNDS,
        CYCLE_VERIFIED_WRAP_ROUNDS,
        PREV_STEP_PROOF_ROUNDS,
        PREV_STEP_STMT_LEN,
        PREV_WRAP_STMT_LEN,
    >,
    step: &RecursiveStepProof<PREV_STEP_PROOF_ROUNDS, WRAP_PROOF_ROUNDS, NEXT_STEP_STMT_LEN>,
) -> PreparedRecursiveWrap<NEXT_STEP_PROOF_ROUNDS, NEXT_WRAP_STMT_LEN> {
    let sg_olds: Vec<Vesta> = step
        .proof
        .prev_challenges
        .iter()
        .flat_map(|challenge| challenge.comm.chunks.iter().copied())
        .collect();
    prepare_recursive_wrap_from_parts::<NEXT_STEP_PROOF_ROUNDS, NEXT_WRAP_STMT_LEN>(
        &step.verifier.index,
        &step.proof,
        &step.statement,
        width1_step_statement_slots::<WRAP_PROOF_ROUNDS>(&step.statement),
        vec![wrap_unfinalized_from_recursive_cycle(previous)],
        sg_olds,
        ProofsVerified::N1,
    )
}

pub fn prove_next_recursive_step<
    const PREV_ROUNDS: usize,
    const VERIFIED_WRAP_ROUNDS: usize,
    const PREV_STEP_PROOF_ROUNDS: usize,
    const PREV_STEP_STMT_LEN: usize,
    const PREV_WRAP_STMT_LEN: usize,
    const WRAP_PROOF_ROUNDS: usize,
    const PUBLIC_INPUT_LEN: usize,
>(
    previous: &RecursiveCycleProof<
        PREV_ROUNDS,
        VERIFIED_WRAP_ROUNDS,
        PREV_STEP_PROOF_ROUNDS,
        PREV_STEP_STMT_LEN,
        PREV_WRAP_STMT_LEN,
    >,
    wrap_vk_pts: Vec<(Fp, Fp)>,
    prev_app_state: Vec<Fp>,
) -> RecursiveStepProof<PREV_STEP_PROOF_ROUNDS, WRAP_PROOF_ROUNDS, PUBLIC_INPUT_LEN> {
    let prepared = prepare_next_recursive_step::<
        PREV_ROUNDS,
        VERIFIED_WRAP_ROUNDS,
        PREV_STEP_PROOF_ROUNDS,
        PREV_STEP_STMT_LEN,
        PREV_WRAP_STMT_LEN,
        WRAP_PROOF_ROUNDS,
        PUBLIC_INPUT_LEN,
    >(previous, wrap_vk_pts, prev_app_state);
    let verified_wrap_accumulator = prepared.verified_wrap_accumulator;
    let finalized_step_challenges = prepared.finalized_step_challenges.clone();
    let (mut prover, verifier) =
        RecursiveStepCircuit::<PREV_STEP_PROOF_ROUNDS, WRAP_PROOF_ROUNDS, PUBLIC_INPUT_LEN> {
            d: [prepared.data],
        }
        .compile_to_indexes()
        .unwrap();
    let (proof, _) = prover
        .prove_with_recursion::<VestaBase, VestaScalar>(
            prepared.statement,
            (),
            true,
            vec![prepared.recursion],
        )
        .unwrap();
    verifier.verify::<VestaBase, VestaScalar>(proof.clone(), prepared.statement, ());
    RecursiveStepProof {
        statement: prepared.statement,
        proof,
        verifier,
        verified_wrap_accumulator,
        finalized_step_challenges,
    }
}

pub fn prove_next_recursive_cycle<
    const CYCLE_PREV_ROUNDS: usize,
    const CYCLE_VERIFIED_WRAP_ROUNDS: usize,
    const PREV_STEP_PROOF_ROUNDS: usize,
    const PREV_STEP_STMT_LEN: usize,
    const PREV_WRAP_STMT_LEN: usize,
    const WRAP_PROOF_ROUNDS: usize,
    const NEXT_STEP_STMT_LEN: usize,
    const NEXT_STEP_PROOF_ROUNDS: usize,
    const NEXT_WRAP_STMT_LEN: usize,
>(
    previous: &RecursiveCycleProof<
        CYCLE_PREV_ROUNDS,
        CYCLE_VERIFIED_WRAP_ROUNDS,
        PREV_STEP_PROOF_ROUNDS,
        PREV_STEP_STMT_LEN,
        PREV_WRAP_STMT_LEN,
    >,
    wrap_vk_pts: Vec<(Fp, Fp)>,
    prev_app_state: Vec<Fp>,
) -> RecursiveCycleProof<
    PREV_STEP_PROOF_ROUNDS,
    WRAP_PROOF_ROUNDS,
    NEXT_STEP_PROOF_ROUNDS,
    NEXT_STEP_STMT_LEN,
    NEXT_WRAP_STMT_LEN,
> {
    let step = prove_next_recursive_step::<
        CYCLE_PREV_ROUNDS,
        CYCLE_VERIFIED_WRAP_ROUNDS,
        PREV_STEP_PROOF_ROUNDS,
        PREV_STEP_STMT_LEN,
        PREV_WRAP_STMT_LEN,
        WRAP_PROOF_ROUNDS,
        NEXT_STEP_STMT_LEN,
    >(previous, wrap_vk_pts, prev_app_state);
    let prepared_wrap = prepare_next_recursive_wrap::<
        CYCLE_PREV_ROUNDS,
        CYCLE_VERIFIED_WRAP_ROUNDS,
        PREV_STEP_PROOF_ROUNDS,
        PREV_STEP_STMT_LEN,
        PREV_WRAP_STMT_LEN,
        WRAP_PROOF_ROUNDS,
        NEXT_STEP_STMT_LEN,
        NEXT_STEP_PROOF_ROUNDS,
        NEXT_WRAP_STMT_LEN,
    >(previous, &step);
    assert!(
        recursive_wrap_ipa_equation_holds(&prepared_wrap),
        "prepared next recursive wrap IPA equation"
    );
    let wrap = prove_recursive_wrap(prepared_wrap);
    RecursiveCycleProof { step, wrap }
}

/// Proves the next cycle with the previous cycle's actual wrap verification
/// key in the reduced message.
pub fn prove_next_recursive_cycle_with_real_vk<
    const CYCLE_PREV_ROUNDS: usize,
    const CYCLE_VERIFIED_WRAP_ROUNDS: usize,
    const PREV_STEP_PROOF_ROUNDS: usize,
    const PREV_STEP_STMT_LEN: usize,
    const PREV_WRAP_STMT_LEN: usize,
    const WRAP_PROOF_ROUNDS: usize,
    const NEXT_STEP_STMT_LEN: usize,
    const NEXT_STEP_PROOF_ROUNDS: usize,
    const NEXT_WRAP_STMT_LEN: usize,
>(
    previous: &RecursiveCycleProof<
        CYCLE_PREV_ROUNDS,
        CYCLE_VERIFIED_WRAP_ROUNDS,
        PREV_STEP_PROOF_ROUNDS,
        PREV_STEP_STMT_LEN,
        PREV_WRAP_STMT_LEN,
    >,
    app_state: Vec<Fp>,
) -> RecursiveCycleProof<
    PREV_STEP_PROOF_ROUNDS,
    WRAP_PROOF_ROUNDS,
    NEXT_STEP_PROOF_ROUNDS,
    NEXT_STEP_STMT_LEN,
    NEXT_WRAP_STMT_LEN,
> {
    let wrap_vk_pts = crate::api::wrap_verification_key_points(&previous.wrap.verifier);
    prove_next_recursive_cycle::<
        CYCLE_PREV_ROUNDS,
        CYCLE_VERIFIED_WRAP_ROUNDS,
        PREV_STEP_PROOF_ROUNDS,
        PREV_STEP_STMT_LEN,
        PREV_WRAP_STMT_LEN,
        WRAP_PROOF_ROUNDS,
        NEXT_STEP_STMT_LEN,
        NEXT_STEP_PROOF_ROUNDS,
        NEXT_WRAP_STMT_LEN,
    >(previous, wrap_vk_pts, app_state)
}

/// Repeats recursive step→wrap cycles once the compiled domains and statement
/// lengths have stabilized. Pickles reaches this fixed shape after the first
/// growing transition in the current width-1 harness.
pub fn prove_stable_recursive_cycles<
    const ROUNDS: usize,
    const STEP_STMT_LEN: usize,
    const WRAP_STMT_LEN: usize,
>(
    mut cycle: RecursiveCycleProof<ROUNDS, ROUNDS, ROUNDS, STEP_STMT_LEN, WRAP_STMT_LEN>,
    count: usize,
    wrap_vk_pts: Vec<(Fp, Fp)>,
    app_state: Vec<Fp>,
) -> RecursiveCycleProof<ROUNDS, ROUNDS, ROUNDS, STEP_STMT_LEN, WRAP_STMT_LEN> {
    for _ in 0..count {
        cycle = prove_next_recursive_cycle::<
            ROUNDS,
            ROUNDS,
            ROUNDS,
            STEP_STMT_LEN,
            WRAP_STMT_LEN,
            ROUNDS,
            STEP_STMT_LEN,
            ROUNDS,
            WRAP_STMT_LEN,
        >(&cycle, wrap_vk_pts.clone(), app_state.clone());
    }
    cycle
}

pub fn reconstruct_step_statement_commitment(
    statement: &[WrapStepStatementSlot],
    lagranges: &[((Fq, Fq), (Fq, Fq))],
    h: Vesta,
) -> Vesta {
    use ark_ec::{AffineRepr, CurveGroup};

    assert_eq!(statement.len(), lagranges.len());
    let mut acc = Vesta::zero().into_group();
    for (slot, &((x, y), _)) in statement.iter().zip(lagranges) {
        let lagrange = Vesta::new(x, y);
        let scalar = match *slot {
            WrapStepStatementSlot::Packed { value, .. } => embed_fq_to_fp(value),
            WrapStepStatementSlot::Bool(bit) => {
                if bit {
                    Fp::one()
                } else {
                    Fp::from(0u64)
                }
            }
        };
        acc += lagrange * scalar;
    }
    (-acc + h.into_group()).into_affine()
}

pub fn recursive_wrap_ipa_equation_holds<const STEP_ROUNDS: usize, const WRAP_STMT_LEN: usize>(
    prepared: &PreparedRecursiveWrap<STEP_ROUNDS, WRAP_STMT_LEN>,
) -> bool {
    use ark_ec::{AffineRepr, CurveGroup};
    use mina_poseidon::poseidon::{ArithmeticSponge, Sponge as _};

    type RefSponge = ArithmeticSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

    let data = &prepared.data;
    let stmt = &prepared.statement;
    let pt = |p: (Fq, Fq)| Vesta::new(p.0, p.1);
    let abpt = |s: &mut RefSponge, p: Vesta| {
        s.absorb(&[p.x]);
        s.absorb(&[p.y]);
    };
    let low_128 = |x: Fq| {
        let bits = x.into_bigint().to_bits_le();
        let mut acc = Fq::zero();
        for &b in bits[..128].iter().rev() {
            acc.double_in_place();
            if b {
                acc += Fq::one();
            }
        }
        acc
    };
    let t1 = |repr_fq: Fq| crate::shifted_value::type1_to_field(embed_fq_to_fp(repr_fq));
    let to_chal = |raw: Fq| {
        let raw_fp = embed_fq_to_fp(raw);
        crate::scalar_challenge::ScalarChallenge(raw_fp)
            .to_field(<Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1)
    };

    let h = pt(data.h);
    let x_hat = reconstruct_step_statement_commitment(
        &data.step_statement,
        &data.step_statement_lagranges,
        h,
    );

    let mut sponge =
        RefSponge::new(<Vesta as KimchiCurve<FULL_ROUNDS>>::other_curve_sponge_params());
    sponge.absorb(&[data.step_vk_digest]);
    for &sg_old in &data.sg_olds {
        abpt(&mut sponge, pt(sg_old));
    }
    abpt(&mut sponge, x_hat);
    for &w in &data.w_comm {
        abpt(&mut sponge, pt(w));
    }
    let _beta = low_128(sponge.squeeze());
    let _gamma = low_128(sponge.squeeze());
    abpt(&mut sponge, pt(data.z_comm));
    let _alpha = low_128(sponge.squeeze());
    for &t in &data.t_comm {
        abpt(&mut sponge, pt(t));
    }
    let _zeta = low_128(sponge.squeeze());

    let mut ipa_sponge = sponge;
    ipa_sponge.absorb(&[stmt[0]]);
    let gm = groupmap::BWParameters::<VestaParameters>::setup();
    let (ux, uy) = gm.to_group(ipa_sponge.squeeze());
    let u = Vesta::new_unchecked(ux, uy);

    let mut lr_prod = Vesta::zero().into_group();
    for &((lx, ly), (rx, ry)) in &data.lr {
        let l = Vesta::new(lx, ly);
        let r = Vesta::new(rx, ry);
        abpt(&mut ipa_sponge, l);
        abpt(&mut ipa_sponge, r);
        let raw = low_128(ipa_sponge.squeeze());
        let chal = to_chal(raw);
        lr_prod += l * chal.inverse().unwrap() + r * chal;
    }
    let delta = pt(data.delta);
    abpt(&mut ipa_sponge, delta);
    let c = to_chal(low_128(ipa_sponge.squeeze()));

    let cip = t1(stmt[0]);
    let b = t1(stmt[1]);
    let zeta_to_srs_length = t1(stmt[2]);
    let zeta_to_domain_size = t1(stmt[3]);
    let perm = t1(stmt[4]);
    let xi = to_chal(stmt[9]);
    let z1 = t1(data.z1_repr);
    let z2 = t1(data.z2_repr);

    let mut t_red = pt(data.t_comm[6]).into_group();
    for &t in data.t_comm[..6].iter().rev() {
        t_red = pt(t).into_group() + t_red * zeta_to_srs_length;
    }
    let ft = pt(data.sigma_last[0]) * perm + t_red - t_red * zeta_to_domain_size;

    let mut commitments = Vec::new();
    commitments.extend(data.sg_olds.iter().map(|&p| pt(p).into_group()));
    commitments.push(x_hat.into_group());
    commitments.push(ft);
    commitments.push(pt(data.z_comm).into_group());
    commitments.push(pt(data.generic).into_group());
    commitments.push(pt(data.psm).into_group());
    commitments.push(pt(data.complete_add).into_group());
    commitments.push(pt(data.mul).into_group());
    commitments.push(pt(data.emul).into_group());
    commitments.push(pt(data.endomul_scalar).into_group());
    commitments.extend(data.w_comm.iter().map(|&p| pt(p).into_group()));
    commitments.extend(data.coefficients.iter().map(|&p| pt(p).into_group()));
    commitments.extend(data.sigma_init.iter().map(|&p| pt(p).into_group()));

    let mut combined = *commitments.last().unwrap();
    for p in commitments[..commitments.len() - 1].iter().rev() {
        combined = *p + combined * xi;
    }

    let q = combined + u * cip + lr_prod;
    let lhs = q * c + delta.into_group();
    let rhs = (pt(data.sg).into_group() + u * b) * z1 + h.into_group() * z2;
    lhs.into_affine() == rhs.into_affine()
}

fn recursive_per_proof_input<'a, const PREV_ROUNDS: usize, const WRAP_ROUNDS: usize>(
    sys: &mut RunState<Fp>,
    d: &'a RecursiveStepData,
    statement: &[FieldVar<Fp>],
    mds: &'a [Vec<Fp>],
    dummy_slot: bool,
) -> SnarkyResult<(
    PerProofInput<'a, Fp>,
    crate::composition_types::PlonkVerificationKeyEvals<snarky::gadgets::curve::Point<Fp>>,
    Vec<FieldVar<Fp>>,
)> {
    use crate::composition_types::PlonkVerificationKeyEvals;
    use snarky::gadgets::curve::Point;

    assert_eq!(statement.len(), 17 + WRAP_ROUNDS);
    let mkpt = |sys: &mut RunState<Fp>, p: (Fp, Fp)| -> SnarkyResult<Point<Fp>> {
        Ok(Point::new(
            sys.compute(loc!(), move |_| p.0)?,
            sys.compute(loc!(), move |_| p.1)?,
        ))
    };
    let mkpts = |sys: &mut RunState<Fp>, ps: &[(Fp, Fp)]| -> SnarkyResult<Vec<Point<Fp>>> {
        ps.iter().map(|&p| mkpt(sys, p)).collect()
    };
    let w1 = |sys: &mut RunState<Fp>, v: Fp| sys.compute(loc!(), move |_| v);
    let wvec = |sys: &mut RunState<Fp>, vs: &[Fp]| -> SnarkyResult<Vec<FieldVar<Fp>>> {
        vs.iter()
            .map(|&v| sys.compute(loc!(), move |_| v))
            .collect()
    };
    let cpt = |p: (Fp, Fp)| Point::new(FieldVar::constant(p.0), FieldVar::constant(p.1));
    let t2s = |sys: &mut RunState<Fp>,
               half: FieldVar<Fp>,
               odd: FieldVar<Fp>|
     -> SnarkyResult<ShiftedScalar<Fp>> {
        sys.assert_r1cs(
            Some("step statement Type2 odd bit".into()),
            loc!(),
            odd.clone(),
            odd.clone(),
            odd.clone(),
        )?;
        Ok(ShiftedScalar::Type2(half, Boolean::create_unsafe(odd)))
    };

    let (_, endo_p) = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos();
    let finalize_params = FinalizeParams {
        tokens: &d.finalize_tokens,
        domain: d.finalize_domain,
        srs_log2: d.finalize_srs_log2,
        endo: d.finalize_endo,
        shifts: &d.finalize_shifts,
        endo_r: *endo_p,
        mds,
        shift: ShiftKind::Type1,
    };
    let mut fe = d.evals_flat.iter();
    let mut next_pe = |sys: &mut RunState<Fp>| -> SnarkyResult<crate::fr_sponge::PointEvalVar<Fp>> {
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
        feature_flags: (0..8)
            .map(|_| sys.compute(loc!(), |_| false))
            .collect::<SnarkyResult<Vec<Boolean<Fp>>>>()?,
    };

    let vk_pts = d
        .wrap_vk_pts
        .iter()
        .map(|&p| mkpt(sys, p))
        .collect::<SnarkyResult<Vec<_>>>()?;
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
    let lr =
        d.lr.iter()
            .map(|&(l, r)| Ok((mkpt(sys, l)?, mkpt(sys, r)?)))
            .collect::<SnarkyResult<Vec<_>>>()?;
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
    let (next_step_accumulator, next_step_challenges) = if dummy_slot {
        use poly_commitment::SRS as _;
        let (dummy_wrap, dummy_step) = crate::dummy::ipa_wrap_and_step::<Fq, Fp>(
            <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1,
            <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1,
        );
        let srs = poly_commitment::ipa::SRS::<Pallas>::create(1 << crate::common::TOCK_ROUNDS);
        let sg = crate::dummy::compute_sg(&srs, &dummy_wrap.challenges_computed);
        (
            cpt((sg.x, sg.y)),
            Some(
                dummy_step
                    .challenges_computed
                    .into_iter()
                    .map(FieldVar::constant)
                    .collect(),
            ),
        )
    } else {
        (openings.challenge_polynomial_commitment.clone(), None)
    };
    let advice = Advice {
        combined_inner_product: t2s(sys, statement[0].clone(), statement[1].clone())?,
        b: t2s(sys, statement[2].clone(), statement[3].clone())?,
        zeta_to_srs_length: t2s(sys, statement[4].clone(), statement[5].clone())?,
        zeta_to_domain_size: t2s(sys, statement[6].clone(), statement[7].clone())?,
        perm: t2s(sys, statement[8].clone(), statement[9].clone())?,
    };
    let claimed = Claimed {
        sponge_digest_before_evaluations: statement[10].clone(),
        beta: statement[11].clone(),
        gamma: statement[12].clone(),
        alpha: statement[13].clone(),
        zeta: statement[14].clone(),
        bulletproof_challenges: statement[16..16 + WRAP_ROUNDS].to_vec(),
    };
    let should_finalize = statement[16 + WRAP_ROUNDS].clone();
    sys.assert_r1cs(
        Some("should_finalize bit".into()),
        loc!(),
        should_finalize.clone(),
        should_finalize.clone(),
        should_finalize.clone(),
    )?;
    let should_finalize = Boolean::create_unsafe(should_finalize);
    let is_base_case: Boolean<Fp> = sys.compute(loc!(), |_| false)?;

    let proof = PerProofInput {
        finalize_params,
        finalize_evals,
        stmt,
        sponge_after_index: after_index,
        prev_app_state,
        messages_for_next_step_accumulators: d
            .messages_for_next_step_accumulators
            .iter()
            .map(|&p| mkpt(sys, p))
            .collect::<SnarkyResult<Vec<_>>>()?,
        prev_challenge_polynomial_commitments: d
            .prev_challenge_polynomial_commitments
            .iter()
            .map(|&p| mkpt(sys, p))
            .collect::<SnarkyResult<Vec<_>>>()?,
        prev_challenges: d
            .prev_challenges
            .iter()
            .map(|chals| wvec(sys, chals))
            .collect::<SnarkyResult<Vec<_>>>()?,
        vk_digest: w1(sys, d.wrap_vk_digest)?,
        vk,
        packed_lagranges: d
            .packed_lagranges
            .iter()
            .map(|&(l, c)| (cpt(l), cpt(c)))
            .collect(),
        flag_lagranges: d.flag_lagranges.iter().map(|&l| cpt(l)).collect(),
        h_generator: h,
        messages,
        openings,
        next_step_accumulator,
        next_step_challenges,
        advice,
        xi: statement[15].clone(),
        claimed,
        should_finalize: should_finalize.clone(),
        must_verify: should_finalize,
        is_base_case,
    };
    let app_state = wvec(sys, &d.prev_app_state)?;
    Ok((proof, dlog_index, app_state))
}

impl<
        const PREV_ROUNDS: usize,
        const WRAP_ROUNDS: usize,
        const WIDTH1_INPUT_LEN: usize,
        const PUBLIC_INPUT_LEN: usize,
    > SnarkyCircuit
    for RecursiveStepWidth2Circuit<PREV_ROUNDS, WRAP_ROUNDS, WIDTH1_INPUT_LEN, PUBLIC_INPUT_LEN>
{
    type Curve = Vesta;
    const PREV_CHALLENGES: usize = 2;
    type Proof = IpaProof<Self::Curve, FULL_ROUNDS>;
    type PrivateInput = ();
    type PublicInput = [FieldVar<Fp>; PUBLIC_INPUT_LEN];
    type PublicOutput = ();

    fn circuit(
        &self,
        sys: &mut RunState<Fp>,
        statement: Self::PublicInput,
        _private: Option<&Self::PrivateInput>,
    ) -> SnarkyResult<()> {
        assert_eq!(WIDTH1_INPUT_LEN, width1_step_statement_len(WRAP_ROUNDS));
        assert_eq!(PUBLIC_INPUT_LEN, step_statement_len(2, WRAP_ROUNDS));
        let per_proof = 17 + WRAP_ROUNDS;
        let mds: Vec<Vec<Fp>> = Vesta::sponge_params()
            .mds
            .iter()
            .map(|row| row.to_vec())
            .collect();
        let mut proofs = Vec::with_capacity(2);
        let mut shared_index = None;
        for i in 0..2 {
            let segment = &statement[i * per_proof..(i + 1) * per_proof];
            let (proof, index, _previous_app_state) =
                recursive_per_proof_input::<PREV_ROUNDS, WRAP_ROUNDS>(
                    sys,
                    &self.proofs[i],
                    segment,
                    &mds,
                    self.dummy_slots[i],
                )?;
            if i == 0 {
                shared_index = Some(index);
            }
            proofs.push(proof);
        }
        let app_state = self
            .app_state
            .iter()
            .map(|&value| sys.compute(loc!(), move |_| value))
            .collect::<SnarkyResult<Vec<_>>>()?;
        let params = groupmap::BWParameters::<PallasParameters>::setup();
        let digest = step_main::<Fp, PallasParameters>(
            sys,
            loc!(),
            &app_state,
            &shared_index.unwrap(),
            &proofs,
            &params,
            crate::endo::tick::base(),
            <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1,
            255,
        )?;
        digest.assert_equals(sys, loc!(), &statement[PUBLIC_INPUT_LEN - 2])
    }
}

impl<
        const PREV_ROUNDS: usize,
        const WRAP_ROUNDS: usize,
        const PUBLIC_INPUT_LEN: usize,
        const WIDTH: usize,
    > SnarkyCircuit for RecursiveStepCircuit<PREV_ROUNDS, WRAP_ROUNDS, PUBLIC_INPUT_LEN, WIDTH>
{
    type Curve = Vesta;
    const PREV_CHALLENGES: usize = WIDTH;
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

        assert_eq!(PUBLIC_INPUT_LEN, step_statement_len(WIDTH, WRAP_ROUNDS));
        assert!((1..=crate::common::MAX_PROOFS_VERIFIED).contains(&WIDTH));
        let d = &self.d[0];
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
            messages_for_next_step_accumulators: d
                .messages_for_next_step_accumulators
                .iter()
                .map(|&p| mkpt(sys, p))
                .collect::<SnarkyResult<Vec<_>>>()?,
            prev_challenge_polynomial_commitments: d
                .prev_challenge_polynomial_commitments
                .iter()
                .map(|&p| mkpt(sys, p))
                .collect::<SnarkyResult<Vec<_>>>()?,
            prev_challenges: d
                .prev_challenges
                .iter()
                .map(|chals| wvec(sys, chals))
                .collect::<SnarkyResult<Vec<_>>>()?,
            vk_digest: wrap_vk_digest,
            vk,
            packed_lagranges,
            flag_lagranges,
            h_generator: h,
            messages,
            openings,
            next_step_accumulator: mkpt(sys, d.sg)?,
            next_step_challenges: None,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::step_witness::StepWitness;

    #[test]
    fn width1_step_statement_layout() {
        const WRAP_ROUNDS: usize = 3;
        const LEN: usize = width1_step_statement_len(WRAP_ROUNDS);
        let witness = StepWitness {
            cip: (Fp::from(1u64), false),
            b: (Fp::from(2u64), true),
            zeta_to_srs_length: (Fp::from(3u64), false),
            zeta_to_domain_size: (Fp::from(4u64), true),
            perm: (Fp::from(5u64), false),
            sponge_digest: Fq::from(6u64),
            beta_raw: Fp::from(7u64),
            gamma_raw: Fp::from(8u64),
            alpha_raw: Fp::from(9u64),
            zeta_raw: Fp::from(10u64),
            bulletproof_prechallenges: vec![Fp::from(11u64), Fp::from(12u64), Fp::from(13u64)],
            z1: (Fp::from(14u64), false),
            z2: (Fp::from(15u64), true),
        };

        let statement = build_width1_step_statement::<WRAP_ROUNDS, LEN>(
            &witness,
            Fq::from(16u64),
            Fp::from(17u64),
            Fp::from(18u64),
            true,
        );

        assert_eq!(
            statement,
            [
                Fp::from(1u64),
                Fp::from(0u64),
                Fp::from(2u64),
                Fp::one(),
                Fp::from(3u64),
                Fp::from(0u64),
                Fp::from(4u64),
                Fp::one(),
                Fp::from(5u64),
                Fp::from(0u64),
                Fp::from(6u64),
                Fp::from(7u64),
                Fp::from(8u64),
                Fp::from(9u64),
                Fp::from(10u64),
                Fp::from(16u64),
                Fp::from(11u64),
                Fp::from(12u64),
                Fp::from(13u64),
                Fp::one(),
                Fp::from(17u64),
                Fp::from(18u64),
            ]
        );

        let width2 = build_step_statement::<WRAP_ROUNDS>(
            &[
                (&witness, Fq::from(16u64), false),
                (&witness, Fq::from(16u64), true),
            ],
            Fp::from(17u64),
            Fp::from(18u64),
        );
        assert_eq!(width2.len(), step_statement_len(2, WRAP_ROUNDS));
        assert_eq!(&width2[..19], &statement[..19]);
        assert_eq!(width2[19], Fp::zero());
        assert_eq!(&width2[20..40], &statement[..20]);
        assert_eq!(&width2[40..], &statement[20..]);
    }

    #[test]
    fn width1_step_statement_slots_match_layout() {
        const WRAP_ROUNDS: usize = 2;
        const LEN: usize = width1_step_statement_len(WRAP_ROUNDS);
        let statement: Vec<Fp> = (0..LEN).map(|i| Fp::from((i + 1) as u64)).collect();
        let slots = width1_step_statement_slots::<WRAP_ROUNDS>(&statement);

        assert_eq!(slots.len(), LEN);
        for i in (0..10).step_by(2) {
            assert_eq!(
                slots[i],
                WrapStepStatementSlot::Packed {
                    value: embed_fp_to_fq(statement[i]),
                    num_bits: 255
                }
            );
            assert_eq!(slots[i + 1], WrapStepStatementSlot::Bool(true));
        }
        assert_eq!(
            slots[10],
            WrapStepStatementSlot::Packed {
                value: embed_fp_to_fq(statement[10]),
                num_bits: 255
            }
        );
        for i in 11..16 + WRAP_ROUNDS {
            assert_eq!(
                slots[i],
                WrapStepStatementSlot::Packed {
                    value: embed_fp_to_fq(statement[i]),
                    num_bits: 128
                }
            );
        }
        assert_eq!(slots[16 + WRAP_ROUNDS], WrapStepStatementSlot::Bool(true));
        for i in 17 + WRAP_ROUNDS..LEN {
            assert_eq!(
                slots[i],
                WrapStepStatementSlot::Packed {
                    value: embed_fp_to_fq(statement[i]),
                    num_bits: 255
                }
            );
        }

        let width2_statement: Vec<Fp> = (0..step_statement_len(2, WRAP_ROUNDS))
            .map(|i| Fp::from((i + 1) as u64))
            .collect();
        let width2 = step_statement_slots::<WRAP_ROUNDS>(&width2_statement, 2);
        let segment = 17 + WRAP_ROUNDS;
        assert_eq!(width2.len(), width2_statement.len());
        assert!(matches!(
            width2[segment],
            WrapStepStatementSlot::Packed { num_bits: 255, .. }
        ));
        assert!(matches!(
            width2[segment + 1],
            WrapStepStatementSlot::Bool(true)
        ));
        assert!(matches!(
            width2[2 * segment],
            WrapStepStatementSlot::Packed { num_bits: 255, .. }
        ));
    }
}

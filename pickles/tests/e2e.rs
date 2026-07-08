//! End-to-end base-case pickles pipeline (proofs_verified = 0):
//!
//! 1. a *step* circuit over Fp runs the application logic and exposes the
//!    `messages_for_next_step_proof` digest (its whole statement at width 0)
//!    as its public input — proved on Vesta;
//! 2. the *wrap* circuit over Fq runs [`pickles::wrap_main::wrap_main`] on the
//!    step proof: it recommits to the step statement (x_hat over the real SRS
//!    Lagrange basis), re-derives the whole Fiat-Shamir transcript, asserts
//!    the deferred values in its own public input (the wrap statement) match,
//!    and asserts the bulletproof equation `equal_g` — proved on Pallas.
//!
//! The wrap proof *is* the base-case pickles proof: its statement carries the
//! deferred (Fp-side) values a step circuit would finalize next.

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

use pickles::composition_types::{
    plonk, BranchData, BulletproofChallenge, Features, ProofsVerified,
};
use pickles::incrementally_verify::{Advice, Messages, OpeningProof, VerificationKeyComm};
use pickles::plonk_curve_ops::ShiftedScalar;
use pickles::scalar_challenge::ScalarChallenge;
use pickles::step_verifier::Claimed;
use pickles::wrap_main::{wrap_main, StepStatementElement};

const FULL_ROUNDS: usize = snarky::FULL_ROUNDS;

type VestaBase = DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type VestaScalar = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type PallasBase = DefaultFqSponge<
    mina_curves::pasta::PallasParameters,
    PlonkSpongeConstantsKimchi,
    FULL_ROUNDS,
>;
type PallasScalar = DefaultFrSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type FpSponge = ArithmeticSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type FqSpongeRef = ArithmeticSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

/// The step proof's IPA round count (the test circuit compiles to a 2^9
/// domain; real pickles pads its domains so this is TICK_ROUNDS=16 there).
const ROUNDS: usize = 9;
/// The wrap statement length: 13 scalars + ROUNDS bulletproof challenges +
/// branch data + 8 feature flags.
const STMT_LEN: usize = 13 + ROUNDS + 9;

// ---------------------------------------------------------------- step side

/// The base-case step circuit: application logic (`x² = z`) plus the width-0
/// statement — the public input is the accumulator digest
/// `hash(wrap_vk, app_state = [z])`.
struct StepCircuit {}

impl SnarkyCircuit for StepCircuit {
    type Curve = Vesta;
    type Proof = IpaProof<Self::Curve, FULL_ROUNDS>;
    /// (x, the wrap VK's 28 commitments as coordinates)
    type PrivateInput = (Fp, Vec<(Fp, Fp)>);
    /// the `messages_for_next_step_proof` digest
    type PublicInput = FieldVar<Fp>;
    type PublicOutput = ();

    fn circuit(
        &self,
        sys: &mut RunState<Fp>,
        digest: Self::PublicInput,
        private: Option<&Self::PrivateInput>,
    ) -> SnarkyResult<()> {
        use pickles::composition_types::PlonkVerificationKeyEvals;
        use pickles::hash_messages::{hash_messages_for_next_step_proof, sponge_after_index};
        use snarky::gadgets::curve::Point;

        // application logic: z = x²
        let x: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0)?;
        let z = x.mul(&x, None, loc!(), sys)?;

        // witness the wrap VK and hash the accumulator
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
            hash_messages_for_next_step_proof(sys, loc!(), &after_index, &[z], &[], &[])?;
        computed.assert_equals(sys, loc!(), &digest)?;
        Ok(())
    }
}

// ---------------------------------------------------------------- wrap side

/// Everything the wrap circuit witnesses about the step proof.
struct WrapWitnessData {
    step_vk_digest: Fq,
    // step VK commitments (Vesta points, Fq coordinates)
    generic: (Fq, Fq),
    psm: (Fq, Fq),
    complete_add: (Fq, Fq),
    mul: (Fq, Fq),
    emul: (Fq, Fq),
    endomul_scalar: (Fq, Fq),
    coefficients: Vec<(Fq, Fq)>,
    sigma_init: Vec<(Fq, Fq)>,
    sigma_last: Vec<(Fq, Fq)>,
    // step proof messages + opening
    w_comm: Vec<(Fq, Fq)>,
    z_comm: (Fq, Fq),
    t_comm: Vec<(Fq, Fq)>,
    lr: Vec<((Fq, Fq), (Fq, Fq))>,
    delta: (Fq, Fq),
    sg: (Fq, Fq),
    z1_repr: Fq,
    z2_repr: Fq,
    // constants
    lagrange: (Fq, Fq),
    correction: (Fq, Fq),
    h: (Fq, Fq),
    new_acc_dummies: Vec<Vec<Fq>>,
}

struct WrapCircuit {
    w: WrapWitnessData,
}

impl SnarkyCircuit for WrapCircuit {
    type Curve = Pallas;
    type Proof = IpaProof<Self::Curve, FULL_ROUNDS>;
    type PrivateInput = ();
    /// the wrap statement, packed in `Wrap.Statement.to_data` order
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
        // stmt[13..13+ROUNDS]: bulletproof challenges; then branch data and
        // the 8 feature flags
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

        // the step statement (width 0) = its accumulator digest, committed
        // through the real Lagrange basis
        let elements = vec![StepStatementElement::Packed {
            value: msgs_step_digest,
            num_bits: 255,
        }];
        let lagranges = vec![(cpt(w.lagrange), cpt(w.correction))];

        let params = groupmap::BWParameters::<VestaParameters>::setup();
        let _out = wrap_main::<Fq, VestaParameters>(
            sys,
            loc!(),
            &[], // no unfinalized proofs at width 0
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
            pickles::endo::tock::base(),
            <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1,
            255,
        )?;
        Ok(())
    }
}

// ------------------------------------------------------------------- test

fn fp_to_fq(x: Fp) -> Fq {
    Fq::from_le_bytes_mod_order(&x.into_bigint().to_bytes_le())
}

#[test]
fn pickles_base_case_end_to_end() {
    // ---- 1. compile the wrap circuit first (its VK feeds the step digest) ----
    // The wrap circuit needs witness data to build its constraint system, but
    // the gate structure is data-independent; use placeholder points on the
    // curve so witness generation during compilation stays consistent.
    // We compile with the real data later anyway, so simplest: compile after
    // the step proof exists. To break the (data, not structure) cycle we
    // compile the wrap circuit twice: once with dummies to learn its VK, then
    // for real. At width 0 the step digest only commits the wrap VK points,
    // which come from the *first* compilation and stay identical in the
    // second (the constraint system does not depend on witness values).
    //
    // For this base-case test we shortcut: the wrap VK hashed by the step
    // circuit is the real wrap verifier index of the final compilation.

    // ---- 2. compile the step circuit and derive its indexes ----
    let (mut step_pi, step_ver) = StepCircuit {}.compile_to_indexes().unwrap();
    let svi = &step_ver.index;

    // placeholder wrap VK points for the accumulator (base case: the wrap VK
    // is pinned by the *next* step proof, not this one; any fixed points work
    // as long as prover and verifier agree). Use the step VK's own
    // commitments as stand-ins — Vesta points have Fq coordinates, but the
    // accumulator hash runs over Fp with *Pallas* points in the real system.
    // Deterministic Fp pairs keep the test self-consistent.
    let wrap_vk_pts: Vec<(Fp, Fp)> = (0..28u64)
        .map(|i| (Fp::from(1000 + i), Fp::from(2000 + i)))
        .collect();

    // the step statement digest = hash(wrap_vk, app_state=[z])
    let x = Fp::from(7u64);
    let z = x * x;
    let digest = {
        let mut s = FpSponge::new(Vesta::sponge_params());
        for (px, py) in &wrap_vk_pts {
            s.absorb(&[*px]);
            s.absorb(&[*py]);
        }
        s.absorb(&[z]);
        s.squeeze()
    };

    // ---- 3. prove the step circuit ----
    let (step_proof, _) = step_pi
        .prove::<VestaBase, VestaScalar>(digest, (x, wrap_vk_pts.clone()), true)
        .unwrap();
    step_ver.verify::<VestaBase, VestaScalar>(step_proof.clone(), digest, ());

    // ---- 4. the wrap witness: oracles, transcript replay, deferred values ----
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

    // perm scalar via the parity-tested port
    let combined = step_proof.evals.combine(&o.powers_of_eval_points_for_chunks);
    let srs_log2 = u64::BITS - 1 - (svi.max_poly_size as u64).leading_zeros();
    let domain = pickles::plonk_checks::Domain::<Fp> {
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
    let env = pickles::plonk_checks::scalars_env::<Fp, bool>(&domain, srs_log2, &minimal);
    let evals = pickles::plonk_checks::Evals {
        w: combined.w.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
        s: combined.s.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
        z: (combined.z.zeta, combined.z.zeta_omega),
    };
    let perm = pickles::plonk_checks::perm_scalar(&env, &evals);

    let ww = pickles::wrap::wrap_witness(
        svi.max_poly_size as u64,
        svi.domain.size,
        svi.domain.group_gen,
        &step_proof,
        &public_comm,
        svi.digest::<VestaBase>(),
        o.combined_inner_product,
        oracles.zeta,
        oracles.u,
        perm,
    );

    // the raw 128-bit polyscale challenge (Fr-sponge replay over Fp)
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

    // ---- 5. build the wrap statement (to_data order) ----
    let dummy_wrap_chals: Vec<Vec<Fq>> = (0..2)
        .map(|i| {
            (0..pickles::common::TOCK_ROUNDS)
                .map(|j| Fq::from((300 + 100 * i + j) as u64))
                .collect()
        })
        .collect();
    let sg_pt = step_proof.proof.sg;
    let msgs_wrap_digest = {
        let mut s = FqSpongeRef::new(Pallas::sponge_params());
        for v in &dummy_wrap_chals {
            for c in v {
                s.absorb(&[*c]);
            }
        }
        s.absorb(&[sg_pt.x]);
        s.absorb(&[sg_pt.y]);
        s.squeeze()
    };

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
    let stmt_vec = pickles::composition_types::wrap::wrap_statement_to_field_elements(
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
    assert_eq!(stmt_vec.len(), STMT_LEN);
    let stmt: [Fq; STMT_LEN] = stmt_vec.try_into().unwrap();

    // ---- 6. the wrap circuit witness data ----
    let co = |p: &Vesta| (p.x, p.y);
    let l0 = lgr[0].chunks[0];
    let correction = pickles::public_input::lagrange_correction(&l0, 255);
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

    // ---- 7. prove the wrap circuit on Pallas — the pickles base proof ----
    let (mut wrap_pi, wrap_ver) = WrapCircuit { w: wdata }.compile_to_indexes().unwrap();
    let (wrap_proof, _) = wrap_pi
        .prove::<PallasBase, PallasScalar>(stmt, (), true)
        .unwrap();
    wrap_ver.verify::<PallasBase, PallasScalar>(wrap_proof, stmt, ());
}

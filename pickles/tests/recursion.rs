//! The first recursive step (proofs_verified = 1): a second step circuit runs
//! [`pickles::step_main::step_main`] over the base-case wrap proof —
//! finalizing the wrap statement's deferred values (the base step proof's
//! scalars) against that proof's evaluations, re-deriving the wrap proof's
//! whole transcript, recommitting the wrap statement through the real Pallas
//! Lagrange basis, and asserting the bulletproof equation — with
//! `must_verify = true`, so every check is real.

use kimchi::curve::KimchiCurve;
use mina_curves::pasta::Fp;
use snarky::{loc, FieldVar, RunState, SnarkyResult};

use pickles::{
    api::{
        prove_base_case, prove_base_case_two_pass, wrap_verification_key_points,
        BaseCaseBackendError, BaseCaseRuleBackend, StepApp,
    },
    composition_types::ProofsVerified,
    inductive_rule::{InductiveRule, PicklesProgram, ProgramExecutionError, RuleId},
    recursive_step::{
        prepare_next_recursive_step, prepare_recursive_step, prepare_recursive_step_n1,
        prepare_recursive_step_width2, prepare_recursive_wrap_n1, prepare_recursive_wrap_width2,
        prove_first_recursive_cycle, prove_next_recursive_cycle, prove_recursive_step_width2,
        prove_recursive_wrap, prove_stable_recursive_cycles, recursive_wrap_ipa_equation_holds,
        step_statement_len, width1_step_statement_len, wrap_unfinalized_from_base,
        wrap_unfinalized_from_recursive_cycle, DirectN1Backend, DirectN1Witness,
        DirectN2Backend, DirectN2Witness, DirectRecursiveBackendError,
    },
    side_loaded::SideLoadedVerificationKey,
};

/// step proof #1's IPA rounds / wrap statement length (see tests/e2e.rs).
const ROUNDS: usize = 9;
const STMT_LEN: usize = 13 + ROUNDS + 9;
/// the wrap circuit's IPA rounds (its domain is 2^13 — matching pickles'
/// `wrap_domains(0)`).
const WROUNDS: usize = 13;
const R2: usize = 14;
/// the width-1 step statement: 5 Type2 pairs (cip, b, zsl, zds, perm of the
/// wrap proof), the wrap proof's sponge digest, beta/gamma, alpha/zeta/xi,
/// WROUNDS bulletproof challenges, should_finalize, then the new
/// messages_for_next_step digest and the messages_for_next_wrap digest.
const K2: usize = width1_step_statement_len(WROUNDS);
const WRAP2_STMT_LEN: usize = 13 + R2 + 9;
const WRAP2_PROOF_ROUNDS: usize = 14;
const K3: usize = width1_step_statement_len(WRAP2_PROOF_ROUNDS);
const R3: usize = 14;
const WRAP3_STMT_LEN: usize = 13 + R3 + 9;
const WRAP3_PROOF_ROUNDS: usize = 14;
const K4: usize = width1_step_statement_len(WRAP3_PROOF_ROUNDS);
const R4: usize = 14;
const WRAP4_STMT_LEN: usize = 13 + R4 + 9;
const K_WIDTH2: usize = step_statement_len(2, WROUNDS);
const WIDTH2_STEP_ROUNDS: usize = pickles::common::TICK_ROUNDS;
const WIDTH2_WRAP_STMT_LEN: usize = 13 + WIDTH2_STEP_ROUNDS + 9;

#[derive(Clone, Copy)]
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
    let wrap_vk_pts: Vec<(Fp, Fp)> = (0..28u64)
        .map(|i| (Fp::from(1000 + i), Fp::from(2000 + i)))
        .collect();
    let base = prove_base_case::<SquareApp, ROUNDS, STMT_LEN>(
        SquareApp,
        Fp::from(7u64),
        wrap_vk_pts.clone(),
    );
    let unfinalized = wrap_unfinalized_from_base(&base);
    let prev_wrap_digest = pickles::hash_messages::hash_messages_for_next_wrap_proof_ref(
        mina_curves::pasta::Pallas::sponge_params(),
        &unfinalized.hash_dummy_challenges,
        &unfinalized.old_bulletproof_challenges,
        unfinalized.prev_step_acc,
    );
    assert_eq!(prev_wrap_digest, base.statement[11]);

    let prev_app_state = vec![Fp::from(49u64)];

    let cycle = prove_first_recursive_cycle::<
        SquareApp,
        ROUNDS,
        WROUNDS,
        R2,
        STMT_LEN,
        K2,
        WRAP2_STMT_LEN,
    >(&base, wrap_vk_pts.clone(), prev_app_state);
    assert_eq!(cycle.step.statement.len(), K2);
    assert_eq!(cycle.wrap.statement.len(), WRAP2_STMT_LEN);
    assert_eq!(cycle.wrap.proof.proof.lr.len(), R2);

    let prepared3 = prepare_next_recursive_step::<
        ROUNDS,
        WROUNDS,
        R2,
        K2,
        WRAP2_STMT_LEN,
        WRAP2_PROOF_ROUNDS,
        K3,
    >(&cycle, wrap_vk_pts.clone(), vec![Fp::from(49u64)]);
    assert_eq!(prepared3.statement.len(), K3);
    assert_eq!(
        prepared3.data.messages_for_next_step_accumulators,
        vec![cycle.step.verified_wrap_accumulator]
    );
    assert!(prepared3
        .data
        .prev_challenge_polynomial_commitments
        .is_empty());
    assert_eq!(
        prepared3.data.prev_challenges,
        vec![cycle.step.finalized_step_challenges.clone()]
    );

    let cycle2 = prove_next_recursive_cycle::<
        ROUNDS,
        WROUNDS,
        R2,
        K2,
        WRAP2_STMT_LEN,
        WRAP2_PROOF_ROUNDS,
        K3,
        R3,
        WRAP3_STMT_LEN,
    >(&cycle, wrap_vk_pts.clone(), vec![Fp::from(49u64)]);

    let unfinalized2 = wrap_unfinalized_from_recursive_cycle(&cycle);
    let wrap2_digest = pickles::hash_messages::hash_messages_for_next_wrap_proof_ref(
        mina_curves::pasta::Pallas::sponge_params(),
        &unfinalized2.hash_dummy_challenges,
        &unfinalized2.hash_old_bulletproof_challenges,
        unfinalized2.prev_step_acc,
    );
    assert_eq!(wrap2_digest, cycle.wrap.statement[11]);

    assert_eq!(cycle2.step.statement.len(), K3);
    assert_eq!(cycle2.wrap.statement.len(), WRAP3_STMT_LEN);

    let cycle3 = prove_stable_recursive_cycles::<R3, K3, WRAP3_STMT_LEN>(
        cycle2,
        1,
        wrap_vk_pts,
        vec![Fp::from(49u64)],
    );
    assert_eq!(cycle3.step.statement.len(), K4);
    assert_eq!(cycle3.wrap.statement.len(), WRAP4_STMT_LEN);
}

#[test]
fn pickles_recursive_step_width2() {
    let wrap_vk_pts: Vec<(Fp, Fp)> = (0..28u64)
        .map(|i| (Fp::from(3000 + i), Fp::from(4000 + i)))
        .collect();
    let base = prove_base_case::<SquareApp, ROUNDS, STMT_LEN>(
        SquareApp,
        Fp::from(11u64),
        wrap_vk_pts.clone(),
    );
    let second_base = prove_base_case::<SquareApp, ROUNDS, STMT_LEN>(
        SquareApp,
        Fp::from(13u64),
        wrap_vk_pts.clone(),
    );
    let first = prepare_recursive_step::<SquareApp, ROUNDS, WROUNDS, STMT_LEN, K2>(
        &base,
        wrap_vk_pts.clone(),
        vec![Fp::from(121u64)],
    );
    let second = prepare_recursive_step::<SquareApp, ROUNDS, WROUNDS, STMT_LEN, K2>(
        &second_base,
        wrap_vk_pts,
        vec![Fp::from(169u64)],
    );
    assert_ne!(
        first.verified_wrap_accumulator,
        second.verified_wrap_accumulator
    );
    let prepared = prepare_recursive_step_width2::<WROUNDS, K2, K_WIDTH2>(
        first,
        second,
        vec![Fp::from(290u64)],
    );
    assert_eq!(prepared.statement.len(), K_WIDTH2);
    let proof = prove_recursive_step_width2::<ROUNDS, WROUNDS, K2, K_WIDTH2>(prepared);
    assert_eq!(proof.statement.len(), K_WIDTH2);
    assert_eq!(proof.proof.prev_challenges.len(), 2);
    assert_eq!(proof.proof.proof.lr.len(), WIDTH2_STEP_ROUNDS);

    let prepared_wrap = prepare_recursive_wrap_width2::<
        SquareApp,
        ROUNDS,
        STMT_LEN,
        ROUNDS,
        WROUNDS,
        K2,
        K_WIDTH2,
        WIDTH2_STEP_ROUNDS,
        WIDTH2_WRAP_STMT_LEN,
    >([&base, &second_base], &proof);
    assert_eq!(prepared_wrap.data.unfinalized.len(), 2);
    assert_eq!(prepared_wrap.data.sg_olds.len(), 2);
    assert_eq!(
        prepared_wrap.data.sg_olds,
        proof
            .proof
            .prev_challenges
            .iter()
            .flat_map(|challenge| challenge.comm.chunks.iter().map(|point| (point.x, point.y)))
            .collect::<Vec<_>>()
    );
    assert!(recursive_wrap_ipa_equation_holds(&prepared_wrap));
    let wrapped = prove_recursive_wrap(prepared_wrap);
    assert_eq!(wrapped.statement.len(), WIDTH2_WRAP_STMT_LEN);
    assert_eq!(wrapped.proof.proof.lr.len(), pickles::common::TOCK_ROUNDS);
}

#[test]
fn pickles_recursive_step_n1_is_physically_padded() {
    let wrap_vk_pts: Vec<(Fp, Fp)> = (0..28u64)
        .map(|i| (Fp::from(5000 + i), Fp::from(6000 + i)))
        .collect();
    let base = prove_base_case::<SquareApp, ROUNDS, STMT_LEN>(
        SquareApp,
        Fp::from(17u64),
        wrap_vk_pts.clone(),
    );
    let real = prepare_recursive_step::<SquareApp, ROUNDS, WROUNDS, STMT_LEN, K2>(
        &base,
        wrap_vk_pts,
        vec![Fp::from(289u64)],
    );
    let prepared = prepare_recursive_step_n1::<WROUNDS, K2, K_WIDTH2>(real, vec![Fp::from(289u64)]);
    assert_eq!(prepared.dummy_slots, [true, false]);
    assert_eq!(prepared.statement[16 + WROUNDS], Fp::from(0u64));
    assert_eq!(
        prepared.statement[(17 + WROUNDS) + 16 + WROUNDS],
        Fp::from(1u64)
    );

    let step = prove_recursive_step_width2::<ROUNDS, WROUNDS, K2, K_WIDTH2>(prepared);
    assert_eq!(step.proof.prev_challenges.len(), 2);
    let prepared_wrap = prepare_recursive_wrap_n1::<
        SquareApp,
        ROUNDS,
        STMT_LEN,
        ROUNDS,
        WROUNDS,
        K2,
        K_WIDTH2,
        WIDTH2_STEP_ROUNDS,
        WIDTH2_WRAP_STMT_LEN,
    >(&base, &step);
    assert_eq!(prepared_wrap.data.unfinalized.len(), 1);
    assert_eq!(prepared_wrap.data.sg_olds.len(), 2);
    assert!(recursive_wrap_ipa_equation_holds(&prepared_wrap));
    let wrapped = prove_recursive_wrap(prepared_wrap);
    assert_eq!(wrapped.proof.proof.lr.len(), pickles::common::TOCK_ROUNDS);
}

#[test]
fn base_case_two_pass_hashes_the_real_wrap_vk() {
    let proof = prove_base_case_two_pass::<SquareApp, ROUNDS, STMT_LEN>(SquareApp, Fp::from(19u64));
    let actual = wrap_verification_key_points(&proof.wrap_verifier);
    assert_eq!(proof.wrap_vk_pts, actual);
    let side_loaded =
        SideLoadedVerificationKey::from_wrap_verifier(ROUNDS as u8, &proof.wrap_verifier).unwrap();
    assert_eq!(side_loaded.commitments(), actual);
    assert_ne!(
        proof.wrap_vk_pts[0],
        (Fp::from(1_000_000u64), Fp::from(2_000_000u64))
    );
}

#[test]
fn recursive_cycle_uses_the_real_wrap_vk() {
    let base = prove_base_case_two_pass::<SquareApp, ROUNDS, STMT_LEN>(SquareApp, Fp::from(23u64));
    let rule = InductiveRule::new(RuleId(1), "recursive", ProofsVerified::N1, 16);
    let mut backend =
        DirectN1Backend::<SquareApp, ROUNDS, WROUNDS, R2, STMT_LEN, K2, WRAP2_STMT_LEN>::compile(
            &rule,
        )
        .unwrap();
    use pickles::inductive_rule::CompiledRuleBackend;
    let proof = backend
        .prove(&vec![Fp::from(529u64)], DirectN1Witness { base })
        .unwrap();
    backend.verify(&vec![Fp::from(529u64)], &proof).unwrap();
    assert_eq!(proof.cycle.wrap.proof.proof.lr.len(), WRAP2_PROOF_ROUNDS);
}

#[test]
fn direct_n1_backend_exports_and_checks_mina_network_encoding() {
    let base = prove_base_case_two_pass::<SquareApp, ROUNDS, STMT_LEN>(SquareApp, Fp::from(41u64));
    let rule = InductiveRule::new(RuleId(1), "recursive", ProofsVerified::N1, 16);
    let mut backend =
        DirectN1Backend::<SquareApp, ROUNDS, WROUNDS, R2, STMT_LEN, K2, WRAP2_STMT_LEN>::compile(
            &rule,
        )
        .unwrap();
    let public = vec![Fp::from(41u64) * Fp::from(41u64)];
    let (proof, encoded) = backend
        .prove_with_mina_encoding(&public, DirectN1Witness { base })
        .unwrap();

    assert_eq!(encoded.statement, proof.cycle.wrap.statement.to_vec());
    assert!(!encoded.wrap_wire_proof.is_empty());
    assert_eq!(encoded.side_loaded_verification_key.len(), 2459);
    let stable_v3 = proof.to_mina_stable_v3().unwrap();
    assert_eq!(stable_v3.statement, proof.cycle.wrap.statement.to_vec());
    assert_eq!(stable_v3.prev_evals.ft_eval1, proof.cycle.step.proof.ft_eval1);
    assert_eq!(
        stable_v3.proof,
        pickles::mina_bin_prot::WrapWireProofV1::from_prover_proof(&proof.cycle.wrap.proof)
            .unwrap()
    );
    backend
        .verify_with_mina_encoding(&public, &proof, &encoded)
        .unwrap();

    let json = encoded.to_o1js_json_string().unwrap();
    let decoded = pickles::api::MinaWrapProof::from_o1js_json_string(&json).unwrap();
    backend
        .verify_with_mina_encoding(&public, &proof, &decoded)
        .unwrap();

    let mut tampered = decoded;
    tampered.wrap_wire_proof.push(0);
    assert_eq!(
        backend.verify_with_mina_encoding(&public, &proof, &tampered),
        Err(DirectRecursiveBackendError::MinaEncodingMismatch)
    );
}

#[test]
fn direct_n2_backend_exports_and_checks_mina_network_encoding() {
    let first_base =
        prove_base_case_two_pass::<SquareApp, ROUNDS, STMT_LEN>(SquareApp, Fp::from(43u64));
    let second_base =
        prove_base_case_two_pass::<SquareApp, ROUNDS, STMT_LEN>(SquareApp, Fp::from(47u64));
    let rule = InductiveRule::new(RuleId(2), "recursive-width2", ProofsVerified::N2, 16);
    let mut backend = DirectN2Backend::<
        SquareApp,
        ROUNDS,
        WROUNDS,
        STMT_LEN,
        K2,
        K_WIDTH2,
        WIDTH2_STEP_ROUNDS,
        WIDTH2_WRAP_STMT_LEN,
    >::compile(&rule)
    .unwrap();
    let public = vec![Fp::from(43u64) * Fp::from(43u64) + Fp::from(47u64) * Fp::from(47u64)];
    let (proof, encoded) = backend
        .prove_with_mina_encoding(
            &public,
            DirectN2Witness {
                bases: [first_base, second_base],
                previous_app_states: [
                    vec![Fp::from(43u64) * Fp::from(43u64)],
                    vec![Fp::from(47u64) * Fp::from(47u64)],
                ],
            },
        )
        .unwrap();

    assert_eq!(encoded.statement, proof.wrap.statement.to_vec());
    assert!(!encoded.wrap_wire_proof.is_empty());
    assert_eq!(encoded.side_loaded_verification_key.len(), 2459);
    let stable_v3 = proof.to_mina_stable_v3().unwrap();
    assert_eq!(stable_v3.statement, proof.wrap.statement.to_vec());
    assert_eq!(stable_v3.prev_evals.ft_eval1, proof.step.proof.ft_eval1);
    assert_eq!(
        stable_v3.proof,
        pickles::mina_bin_prot::WrapWireProofV1::from_prover_proof(&proof.wrap.proof).unwrap()
    );
    backend
        .verify_with_mina_encoding(&public, &proof, &encoded)
        .unwrap();

    let json = encoded.to_o1js_json_string().unwrap();
    let decoded = pickles::api::MinaWrapProof::from_o1js_json_string(&json).unwrap();
    backend
        .verify_with_mina_encoding(&public, &proof, &decoded)
        .unwrap();

    let mut tampered = decoded;
    tampered.wrap_wire_proof.push(0);
    assert_eq!(
        backend.verify_with_mina_encoding(&public, &proof, &tampered),
        Err(DirectRecursiveBackendError::MinaEncodingMismatch)
    );
}

#[test]
fn compiled_program_proves_and_verifies_a_real_base_rule() {
    let metadata = PicklesProgram::compile_metadata(
        "square",
        vec![InductiveRule::new(
            RuleId(0),
            "base",
            ProofsVerified::N0,
            ROUNDS as u8,
        )],
    )
    .unwrap();
    let mut program = metadata
        .compile(|rule| {
            BaseCaseRuleBackend::<SquareApp, ROUNDS, STMT_LEN>::compile(rule, SquareApp)
        })
        .unwrap();

    let public_state = vec![Fp::from(31u64) * Fp::from(31u64)];
    let proof = program
        .prove(RuleId(0), &public_state, Fp::from(31u64))
        .unwrap();
    program.verify(&public_state, &proof).unwrap();

    let wrong_state = vec![Fp::from(1u64)];
    assert_eq!(
        program.verify(&wrong_state, &proof),
        Err(ProgramExecutionError::Backend(
            BaseCaseBackendError::PublicStateMismatch
        ))
    );
}

#[test]
fn base_backend_exports_and_checks_mina_network_encoding() {
    let rule = InductiveRule::new(RuleId(0), "base", ProofsVerified::N0, ROUNDS as u8);
    let mut backend =
        BaseCaseRuleBackend::<SquareApp, ROUNDS, STMT_LEN>::compile(&rule, SquareApp).unwrap();
    let public_state = vec![Fp::from(37u64) * Fp::from(37u64)];
    let (proof, encoded) = backend
        .prove_with_mina_encoding(&public_state, Fp::from(37u64))
        .unwrap();

    assert_eq!(encoded.statement, proof.statement);
    assert!(!encoded.wrap_wire_proof.is_empty());
    assert_eq!(encoded.side_loaded_verification_key.len(), 2459);
    let stable_v3 = proof.to_mina_stable_v3().unwrap();
    assert_eq!(stable_v3.statement, proof.statement);
    assert_eq!(stable_v3.prev_evals.ft_eval1, proof.step_proof.ft_eval1);
    assert_eq!(
        stable_v3.proof,
        pickles::mina_bin_prot::WrapWireProofV1::from_prover_proof(&proof.proof).unwrap()
    );
    backend
        .verify_with_mina_encoding(&public_state, &proof, &encoded)
        .unwrap();

    let json = encoded.to_o1js_json_string().unwrap();
    let decoded = pickles::api::MinaWrapProof::from_o1js_json_string(&json).unwrap();
    assert_eq!(decoded, encoded);
    backend
        .verify_with_mina_encoding(&public_state, &proof, &decoded)
        .unwrap();

    let mut tampered = encoded;
    tampered.wrap_wire_proof.push(0);
    assert_eq!(
        backend.verify_with_mina_encoding(&public_state, &proof, &tampered),
        Err(BaseCaseBackendError::MinaEncodingMismatch)
    );

    let mut invalid_json = decoded.to_o1js_json_value();
    invalid_json.statement[0] = "not-a-field".to_string();
    assert_eq!(
        pickles::api::MinaWrapProof::from_o1js_json_value(invalid_json),
        Err(BaseCaseBackendError::O1jsJsonField)
    );
}

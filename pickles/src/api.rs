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
use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine as _};
use kimchi::circuits::wires::{COLUMNS, PERMUTS};
use kimchi::curve::KimchiCurve;
use mina_curves::pasta::{Fp, Fq, Pallas, Vesta, VestaParameters};
use mina_poseidon::constants::PlonkSpongeConstantsKimchi;
use mina_poseidon::sponge::{DefaultFqSponge, DefaultFrSponge};
use poly_commitment::commitment::PolyComm;
use poly_commitment::ipa::OpeningProof as IpaProof;
use poly_commitment::SRS;
use serde::{Deserialize, Serialize};
use snarky::{api::SnarkyCircuit, loc, Boolean, FieldVar, RunState, SnarkyResult};

use crate::common::FULL_ROUNDS;
use crate::composition_types::{plonk, BranchData, BulletproofChallenge, Features, ProofsVerified};
use crate::finalize::{FinalizeParams, ShiftKind};
use crate::incrementally_verify::{Advice, Messages, OpeningProof, VerificationKeyComm};
use crate::inductive_rule::{CompiledRuleBackend, InductiveRule, RuleId};
use crate::plonk_curve_ops::ShiftedScalar;
use crate::scalar_challenge::ScalarChallenge;
use crate::side_loaded::{SideLoadedKeyWitness, SideLoadedVerificationKey};
use crate::step_verifier::{Claimed, FinalizeEvals};
use crate::wrap_main::{wrap_main, PerUnfinalized, StepStatementElement};

type VestaBase = DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type VestaScalar = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type PallasBase =
    DefaultFqSponge<mina_curves::pasta::PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type PallasScalar = DefaultFrSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
pub type WrapPolishToken = kimchi::circuits::expr::PolishToken<
    Fq,
    kimchi::circuits::berkeley_columns::Column,
    kimchi::circuits::berkeley_columns::BerkeleyChallengeTerm,
>;

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

/// o1js' OCaml Pickles binding prepends a small set of dummy constraints to
/// every rule so that the optional EC selector columns are always present in
/// the proving key. VK parity requires the Rust step circuit to emit the same
/// selector shape before the user circuit.
fn o1js_dummy_constraints(sys: &mut RunState<Fp>) -> SnarkyResult<()> {
    use ark_ec::{AffineRepr, CurveGroup};
    use snarky::gadgets::curve::Point;

    let x: FieldVar<Fp> = sys.compute(loc!(), |_| Fp::from(3u64))?;
    let g = Pallas::generator().into_group().into_affine();
    let gx: FieldVar<Fp> = sys.compute(loc!(), move |_| g.x)?;
    let gy: FieldVar<Fp> = sys.compute(loc!(), move |_| g.y)?;
    let g = Point::new(gx, gy);
    g.assert_on_curve(sys, loc!(), Fp::from(0u64), Fp::from(5u64))?;

    let _ = crate::scalar_challenge::scalar_to_field_raw_with_bits(sys, loc!(), &x, 16)?;
    let _ = crate::plonk_curve_ops::scale_fast(sys, loc!(), &g, &x, 5)?;
    let _ = crate::scalar_challenge::endo(sys, loc!(), &g, &x, 4, crate::endo::tick::base())?;
    Ok(())
}

impl<A: StepApp> SnarkyCircuit for StepCircuit<A> {
    type Curve = Vesta;
    /// Mina step proofs always carry `MAX_PROOFS_VERIFIED` accumulators
    /// (dummies at the base case — `Wrap_hack.pad_accumulator`).
    const PREV_CHALLENGES: usize = crate::common::MAX_PROOFS_VERIFIED;
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

        o1js_dummy_constraints(sys)?;
        let app_state = self.app.main(sys, private.map(|p| &p.0))?;

        let mut pts = vec![];
        for i in 0..28 {
            let (px, py) = (
                sys.compute(loc!(), move |_| private.unwrap().1[i].0)?,
                sys.compute(loc!(), move |_| private.unwrap().1[i].1)?,
            );
            pts.push(Point::new(px, py));
        }
        // The wrap key crosses a trust boundary (it is only known at proving
        // time), so each commitment is constrained to the Pallas curve —
        // mirroring OCaml snarky_curve's `assert_on_curve` emitted by the
        // `exists Inner_curve.typ` in step_main: x² (square), x³ = x²·x
        // (r1cs), y² = x³ + b (square) with b = 5.
        for pt in &pts {
            let x = pt.x.clone();
            let y = pt.y.clone();
            let x2: FieldVar<Fp> = sys.compute(loc!(), {
                let x = x.clone();
                move |env| {
                    let v: Fp = env.read_var(&x);
                    v * v
                }
            })?;
            sys.add_constraint(
                snarky::runner::Constraint::BasicSnarkyConstraint(
                    snarky::constraint_system::BasicSnarkyConstraint::Square(x.clone(), x2.clone()),
                ),
                Some("vk point x^2".into()),
                loc!(),
            )?;
            let x3 = x2.mul(&x, Some("vk point x^3".into()), loc!(), sys)?;
            let rhs = x3 + FieldVar::Constant(Fp::from(5u64));
            sys.add_constraint(
                snarky::runner::Constraint::BasicSnarkyConstraint(
                    snarky::constraint_system::BasicSnarkyConstraint::Square(y, rhs),
                ),
                Some("vk point on curve".into()),
                loc!(),
            )?;
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

/// Application step circuit whose wrap VK is supplied at proving time and
/// validated in-circuit against one inductive rule.
pub struct SideLoadedStepCircuit<A: StepApp> {
    pub app: A,
    pub rule: InductiveRule,
}

impl<A: StepApp> SnarkyCircuit for SideLoadedStepCircuit<A> {
    type Curve = Vesta;
    type Proof = IpaProof<Self::Curve, FULL_ROUNDS>;
    type PrivateInput = (A::Witness, SideLoadedKeyWitness);
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

        o1js_dummy_constraints(sys)?;
        let app_state = self.app.main(sys, private.map(|input| &input.0))?;

        let step_domain: FieldVar<Fp> = sys.compute(loc!(), move |_| {
            Fp::from(u64::from(private.unwrap().1.step_domain_log2))
        })?;
        step_domain.assert_equals(
            sys,
            loc!(),
            &FieldVar::constant(Fp::from(u64::from(self.rule.step_domain_log2))),
        )?;
        let proofs_verified: FieldVar<Fp> = sys.compute(loc!(), move |_| {
            Fp::from(u64::from(private.unwrap().1.proofs_verified))
        })?;
        proofs_verified.assert_equals(
            sys,
            loc!(),
            &FieldVar::constant(Fp::from(self.rule.proofs_verified.to_usize() as u64)),
        )?;
        let expected_wrap_domain =
            crate::common::wrap_domain_log2(self.rule.proofs_verified.to_usize()) as u64;
        let wrap_domain: FieldVar<Fp> = sys.compute(loc!(), move |_| {
            Fp::from(u64::from(private.unwrap().1.wrap_domain_log2))
        })?;
        wrap_domain.assert_equals(
            sys,
            loc!(),
            &FieldVar::constant(Fp::from(expected_wrap_domain)),
        )?;

        let points = (0..crate::side_loaded::SideLoadedVerificationKey::COMMITMENT_COUNT)
            .map(|index| {
                let (x, y): (FieldVar<Fp>, FieldVar<Fp>) =
                    sys.compute(loc!(), move |_| private.unwrap().1.commitments[index])?;
                let point = Point::new(x, y);
                point.assert_on_curve(sys, loc!(), Fp::from(0u64), Fp::from(5u64))?;
                Ok(point)
            })
            .collect::<SnarkyResult<Vec<_>>>()?;
        let mut points = points.into_iter();
        let vk = PlonkVerificationKeyEvals {
            sigma_comm: (0..PERMUTS).map(|_| points.next().unwrap()).collect(),
            coefficients_comm: (0..COLUMNS).map(|_| points.next().unwrap()).collect(),
            generic_comm: points.next().unwrap(),
            psm_comm: points.next().unwrap(),
            complete_add_comm: points.next().unwrap(),
            mul_comm: points.next().unwrap(),
            emul_comm: points.next().unwrap(),
            endomul_scalar_comm: points.next().unwrap(),
        };
        let after_index = sponge_after_index(sys, loc!(), &vk);
        let computed =
            hash_messages_for_next_step_proof(sys, loc!(), &after_index, &app_state, &[], &[])?;
        computed.assert_equals(sys, loc!(), &digest)
    }
}

/// Everything the wrap circuit witnesses about the step proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WrapStepStatementSlot {
    Field(Fq),
    Packed { value: Fq, num_bits: usize },
    Bool(bool),
}

/// One previous proof-state carried by a recursive step statement and
/// finalized by the wrap circuit before it verifies the step proof.
pub struct WrapUnfinalizedWitnessData {
    pub finalize_tokens: Vec<WrapPolishToken>,
    pub finalize_domain: ark_poly::Radix2EvaluationDomain<Fq>,
    pub finalize_srs_log2: u32,
    pub finalize_endo: Fq,
    pub finalize_endo_r: Fq,
    pub finalize_shifts: Vec<Fq>,
    pub ft_eval1: Fq,
    pub public_evals: [Vec<Fq>; 2],
    pub evals_flat: Vec<(Fq, Fq)>,
    pub alpha: Fq,
    pub beta: Fq,
    pub gamma: Fq,
    pub zeta: Fq,
    pub xi: Fq,
    pub cip_repr: Fq,
    pub b_repr: Fq,
    pub perm_repr: Fq,
    pub bulletproof_challenges: Vec<Fq>,
    pub sponge_digest_before_evaluations: Fq,
    pub should_finalize: bool,
    pub old_bulletproof_challenges: Vec<Vec<Fq>>,
    pub prev_step_acc: (Fq, Fq),
    pub hash_dummy_challenges: Vec<Vec<Fq>>,
    pub hash_old_bulletproof_challenges: Vec<Vec<Fq>>,
}

pub struct WrapWitnessData {
    pub step_domain_log2: u8,
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
    /// Physical recursion accumulators folded by the Kimchi step proof.
    /// This is padded independently of the logical `unfinalized` entries.
    pub sg_olds: Vec<(Fq, Fq)>,
    pub unfinalized: Vec<WrapUnfinalizedWitnessData>,
    pub step_statement: Vec<WrapStepStatementSlot>,
    pub step_statement_lagranges: Vec<((Fq, Fq), (Fq, Fq))>,
    pub h: (Fq, Fq),
    pub new_acc_dummies: Vec<Vec<Fq>>,
}

/// The base-case wrap circuit: [`wrap_main`] over one step proof, public
/// input = the wrap statement (13 scalars, `ROUNDS` bulletproof challenges,
/// branch data, 8 feature flags, optional joint combiner
/// (`STMT_LEN = 13 + ROUNDS + 11` — the OCaml 40-slot layout).
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

        if let Some(system) = &mut sys.system {
            system.set_flush_generic_before_custom(true);
        }

        let w = &self.w;
        // Every witnessed point goes through OCaml's `exists Inner_curve.typ`,
        // whose check is `assert_on_curve` (Vesta: y² = x³ + 5).
        let mkpt = |sys: &mut RunState<Fq>, p: (Fq, Fq)| -> SnarkyResult<Point<Fq>> {
            let point = Point::new(
                sys.compute(loc!(), move |_| p.0)?,
                sys.compute(loc!(), move |_| p.1)?,
            );
            point.assert_on_curve(sys, loc!(), Fq::from(0u64), Fq::from(5u64))?;
            Ok(point)
        };
        let mkpts = |sys: &mut RunState<Fq>, ps: &[(Fq, Fq)]| -> SnarkyResult<Vec<Point<Fq>>> {
            let mut out = vec![];
            for &p in ps {
                out.push(mkpt(sys, p)?);
            }
            Ok(out)
        };
        let w1 = |sys: &mut RunState<Fq>, v: Fq| sys.compute(loc!(), move |_| v);
        let wvec = |sys: &mut RunState<Fq>, vs: &[Fq]| -> SnarkyResult<Vec<FieldVar<Fq>>> {
            let mut out = vec![];
            for &v in vs {
                out.push(w1(sys, v)?);
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
        let bp: Vec<FieldVar<Fq>> = stmt[13..13 + ROUNDS].to_vec();
        let branch_data = stmt[13 + ROUNDS].clone();
        // OCaml `Wrap.Other_field.check`: each deferred Tick-field slot of the
        // statement (cip, b, zeta_to_srs_length, zeta_to_domain_size, perm)
        // must not be one of the forbidden shifted values — the 255-bit
        // patterns whose Type1 decoding is ambiguous modulo the Tick modulus.
        // This runs during the statement's `exists` in OCaml, i.e. BEFORE the
        // which_branch / branch_data logic of the circuit body.
        {
            let forbidden = crate::shifted_value::forbidden_shifted_values_fq();
            // OCaml applies `Other_field.check` to the fq slots in REVERSE
            // order (perm, zds, zsl, b, cip) — the spec/typ processes the
            // `[cip; b; zsl; zds; perm]` vector back-to-front. Match that so
            // the per-slot forbidden blocks land on the same rows/wiring.
            for slot in stmt[0..5].iter().rev() {
                let mut eqs = Vec::with_capacity(forbidden.len());
                for &value in &forbidden {
                    eqs.push(slot.equal(sys, loc!(), &FieldVar::constant(value))?);
                }
                let eq_refs: Vec<&snarky::Boolean<Fq>> = eqs.iter().collect();
                let any = snarky::Boolean::any(&eq_refs, sys, loc!())?;
                any.not()
                    .to_field_var()
                    .assert_equals(sys, loc!(), &FieldVar::constant(Fq::from(1u64)))?;
            }
        }
        // OCaml always witnesses `which_branch`, builds a one-hot vector, and
        // selects the branch width/domain through `Pseudo.choose`, even for a
        // single-branch o1js program.  Mirror that shape instead of folding the
        // branch data to a pure constant.
        let which_branch: FieldVar<Fq> = sys.compute(loc!(), |_| Fq::from(0u64))?;
        let branch0 = which_branch.equal(sys, loc!(), &FieldVar::constant(Fq::from(0u64)))?;
        branch0
            .to_field_var()
            .assert_equals(sys, loc!(), &FieldVar::constant(Fq::from(1u64)))?;
        let proofs_verified = branch0.to_field_var().mul(
            &FieldVar::constant(Fq::from(w.unfinalized.len() as u64)),
            Some("choose proofs_verified".into()),
            loc!(),
            sys,
        )?;
        let domain_log2 = branch0.to_field_var().mul(
            &FieldVar::constant(Fq::from(u64::from(w.step_domain_log2))),
            Some("choose domain_log2".into()),
            loc!(),
            sys,
        )?;
        let expected_branch_data = &domain_log2.scale(Fq::from(4u64)) + &proofs_verified;
        branch_data.assert_equals(
            sys,
            loc!(),
            &expected_branch_data,
        )?;
        let check_other_field_packed = |sys: &mut RunState<Fq>,
                                        value: &FieldVar<Fq>|
         -> SnarkyResult<()> {
            let forbidden = crate::shifted_value::forbidden_shifted_values_fq();
            let mut eqs = Vec::with_capacity(forbidden.len());
            for forbidden_value in forbidden {
                eqs.push(value.equal(sys, loc!(), &FieldVar::constant(forbidden_value))?);
            }
            let eq_refs: Vec<&Boolean<Fq>> = eqs.iter().collect();
            let any = Boolean::any(&eq_refs, sys, loc!())?;
            any.not()
                .to_field_var()
                .assert_equals(sys, loc!(), &FieldVar::constant(Fq::from(1u64)))
        };
        // OCaml 40-slot tail: 8 feature-flag booleans + the optional joint
        // combiner (flag boolean + scalar). o1js compiles with Maybe flags,
        // so they are public boolean slots; our programs use none of them.
        for flag in &stmt[14 + ROUNDS..22 + ROUNDS] {
            sys.assert_r1cs(
                Some("feature flag bit".into()),
                loc!(),
                flag.clone(),
                flag.clone(),
                flag.clone(),
            )?;
        }
        sys.assert_r1cs(
            Some("joint combiner flag bit".into()),
            loc!(),
            stmt[22 + ROUNDS].clone(),
            stmt[22 + ROUNDS].clone(),
            stmt[22 + ROUNDS].clone(),
        )?;

        // OCaml also checks that the statement feature flags are consistent
        // with the optional verifier-index commitments. Our current native
        // verifier index only carries the always-present commitments, so all
        // optional commitment flags are false; still, the derived feature
        // expansion and equality assertions must be present for wrap-circuit
        // parity.
        {
            let feature_flags: Vec<Boolean<Fq>> = stmt[14 + ROUNDS..22 + ROUNDS]
                .iter()
                .cloned()
                .map(Boolean::create_unsafe)
                .collect();
            let range_check0 = feature_flags[0].clone();
            let range_check1 = feature_flags[1].clone();
            let foreign_field_add = feature_flags[2].clone();
            let foreign_field_mul = feature_flags[3].clone();
            let xor = feature_flags[4].clone();
            let rot = feature_flags[5].clone();
            let lookup = feature_flags[6].clone();
            let runtime_tables = feature_flags[7].clone();

            let lookup_pattern_range_check = Boolean::any(
                &[&range_check0, &range_check1, &rot],
                sys,
                loc!(),
            )?;
            let lookup_pattern_xor = xor.clone();
            let table_width_3 = lookup_pattern_xor.clone();
            let table_width_at_least_2 = table_width_3.or(&lookup, loc!(), sys);
            let table_width_at_least_1 = Boolean::any(
                &[
                    &table_width_at_least_2,
                    &lookup_pattern_range_check,
                    &foreign_field_mul,
                ],
                sys,
                loc!(),
            )?;
            // OCaml `Features.to_full` also derives lookups_per_row_4 and
            // lookups_per_row_3 (forced by the sponge's `uses_lookups`), in
            // this order — omitting them shifted the subsequent gate pairing.
            let lookups_per_row_4 = Boolean::any(
                &[&lookup_pattern_xor, &lookup_pattern_range_check, &foreign_field_mul],
                sys,
                loc!(),
            )?;
            let _lookups_per_row_3 = lookups_per_row_4.or(&lookup, loc!(), sys);

            let false_ = Boolean::<Fq>::false_().to_field_var();
            for flag in [
                xor,
                range_check0,
                range_check1,
                foreign_field_add,
                foreign_field_mul.clone(),
                rot,
                table_width_at_least_1,
                table_width_at_least_2,
                table_width_3,
                runtime_tables,
                lookup,
                lookup_pattern_xor,
                lookup_pattern_range_check,
                foreign_field_mul,
            ] {
                flag.to_field_var()
                    .assert_equals(sys, loc!(), &false_)?;
            }
        }

        // OCaml's wrap rule selects the step verification key from the compiled
        // key vector with `Inner_curve.constant`; only the proof payload itself
        // is witnessed through `Inner_curve.typ`.  Keep these commitments as
        // constants here as well, otherwise the circuit gets extra
        // assert-on-curve rows before the index digest.
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
        let assert_vk_point = |sys: &mut RunState<Fq>,
                               point: &Point<Fq>,
                               expected: (Fq, Fq)|
         -> SnarkyResult<()> {
            point
                .x
                .assert_equals(sys, loc!(), &FieldVar::constant(expected.0))?;
            point
                .y
                .assert_equals(sys, loc!(), &FieldVar::constant(expected.1))
        };
        assert_vk_point(sys, &vk.generic, w.generic)?;
        assert_vk_point(sys, &vk.psm, w.psm)?;
        assert_vk_point(sys, &vk.complete_add, w.complete_add)?;
        assert_vk_point(sys, &vk.mul, w.mul)?;
        assert_vk_point(sys, &vk.emul, w.emul)?;
        assert_vk_point(sys, &vk.endomul_scalar, w.endomul_scalar)?;
        for (point, &expected) in vk.coefficients.iter().zip(&w.coefficients) {
            assert_vk_point(sys, point, expected)?;
        }
        for (point, &expected) in vk.sigma_init.iter().zip(&w.sigma_init) {
            assert_vk_point(sys, point, expected)?;
        }
        for (point, &expected) in vk.sigma_last.iter().zip(&w.sigma_last) {
            assert_vk_point(sys, point, expected)?;
        }
        // IVC step 1 (OCaml `absorb verifier index`): recompute the step
        // VK's Fiat-Shamir digest in-circuit from its 28 commitments, in
        // kimchi's `VerifierIndex::digest` order — instead of witnessing it.
        // OCaml emits this index sponge right after selecting the VK, BEFORE
        // witnessing the proof payload points, so the first Poseidon lands
        // before the message/opening on-curve checks (jsoo wrap row ~231).
        let vk_digest: FieldVar<Fq> = {
            let mut index_sponge = crate::sponge::PoseidonSponge::new();
            let mut coords = Vec::with_capacity(56);
            for pt in vk
                .sigma_init
                .iter()
                .chain(vk.sigma_last.iter())
                .chain(vk.coefficients.iter())
                .chain([
                    &vk.generic,
                    &vk.psm,
                    &vk.complete_add,
                    &vk.mul,
                    &vk.emul,
                    &vk.endomul_scalar,
                ])
            {
                coords.push(pt.x.clone());
                coords.push(pt.y.clone());
            }
            index_sponge.absorb(sys, loc!(), &coords);
            index_sponge.squeeze(sys, loc!())
        };
        // OCaml's wrap rule receives the proof through Snarky `Typ`s`; keep
        // proof payload points witnessed (and checked on curve), unlike the
        // constant verifier-index commitments above.
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
        let h = mkpt(sys, w.h)?;
        let sg_olds = mkpts(sys, &w.sg_olds)?;
        let t1 = ShiftedScalar::Type1;
        let z1_repr = w1(sys, w.z1_repr)?;
        let z2_repr = w1(sys, w.z2_repr)?;
        check_other_field_packed(sys, &z1_repr)?;
        check_other_field_packed(sys, &z2_repr)?;
        let openings = OpeningProof {
            lr,
            delta: mkpt(sys, w.delta)?,
            z1: t1(z1_repr),
            z2: t1(z2_repr),
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

        let mds: Vec<Vec<Fq>> = Pallas::sponge_params()
            .mds
            .iter()
            .map(|r| r.to_vec())
            .collect();
        let mut unfinalized = Vec::with_capacity(w.unfinalized.len());
        for u in &w.unfinalized {
            let mut fe = u.evals_flat.iter();
            let mut next_pe =
                |sys: &mut RunState<Fq>| -> SnarkyResult<crate::fr_sponge::PointEvalVar<Fq>> {
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
                ft_eval1: w1(sys, u.ft_eval1)?,
                public_evals: [
                    wvec(sys, &u.public_evals[0])?,
                    wvec(sys, &u.public_evals[1])?,
                ],
                evals,
            };
            let finalize_params = FinalizeParams {
                tokens: &u.finalize_tokens,
                domain: u.finalize_domain,
                srs_log2: u.finalize_srs_log2,
                endo: u.finalize_endo,
                shifts: &u.finalize_shifts,
                endo_r: u.finalize_endo_r,
                mds: &mds,
                shift: ShiftKind::Type2,
            };
            let old_bulletproof_challenges = u
                .old_bulletproof_challenges
                .iter()
                .map(|chals| wvec(sys, chals))
                .collect::<SnarkyResult<Vec<_>>>()?;
            let should_finalize: snarky::Boolean<Fq> =
                sys.compute(loc!(), |_| u.should_finalize)?;
            unfinalized.push(PerUnfinalized {
                finalize_params,
                finalize_evals,
                alpha: w1(sys, u.alpha)?,
                beta: w1(sys, u.beta)?,
                gamma: w1(sys, u.gamma)?,
                zeta: w1(sys, u.zeta)?,
                xi: w1(sys, u.xi)?,
                cip_repr: w1(sys, u.cip_repr)?,
                b_repr: w1(sys, u.b_repr)?,
                perm_repr: w1(sys, u.perm_repr)?,
                bulletproof_challenges: wvec(sys, &u.bulletproof_challenges)?,
                sponge_digest_before_evaluations: w1(sys, u.sponge_digest_before_evaluations)?,
                should_finalize,
                old_bulletproof_challenges,
                prev_step_acc: mkpt(sys, u.prev_step_acc)?,
                hash_dummy_challenges: u.hash_dummy_challenges.clone(),
                hash_old_bulletproof_challenges: u
                    .hash_old_bulletproof_challenges
                    .iter()
                    .map(|chals| wvec(sys, chals))
                    .collect::<SnarkyResult<Vec<_>>>()?,
            });
        }

        let expanded_step_statement_len: usize = w
            .step_statement
            .iter()
            .map(|slot| match slot {
                WrapStepStatementSlot::Field(_) => 2,
                WrapStepStatementSlot::Packed { .. } | WrapStepStatementSlot::Bool(_) => 1,
            })
            .sum();
        assert_eq!(
            expanded_step_statement_len,
            w.step_statement_lagranges.len(),
            "one Lagrange slot per expanded step statement element"
        );
        let mut elements = Vec::with_capacity(w.step_statement.len());
        for slot in &w.step_statement {
            match *slot {
                WrapStepStatementSlot::Field(value) => {
                    let var = sys.compute(loc!(), move |_| value)?;
                    elements.push(StepStatementElement::Split(var));
                }
                WrapStepStatementSlot::Packed { value, num_bits } => {
                    let var = sys.compute(loc!(), move |_| value)?;
                    elements.push(StepStatementElement::Packed {
                        value: var,
                        num_bits,
                    });
                }
                WrapStepStatementSlot::Bool(value) => {
                    let bit = sys.compute(loc!(), move |_| value)?;
                    elements.push(StepStatementElement::Bool(bit));
                }
            }
        }
        let lagranges: Vec<(Point<Fq>, Point<Fq>)> = w
            .step_statement_lagranges
            .iter()
            .map(|&(l, c)| (cpt(l), cpt(c)))
            .collect();

        let params = groupmap::BWParameters::<VestaParameters>::setup();
        let _out = wrap_main::<Fq, VestaParameters>(
            sys,
            loc!(),
            &unfinalized,
            &sg_olds,
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
    pub stable_statement: crate::mina_bin_prot::WrapStatementMinimalV1,
    pub proof: kimchi::proof::ProverProof<Pallas, IpaProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS>,
    pub step_proof: kimchi::proof::ProverProof<Vesta, IpaProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS>,
    pub step_verifier: snarky::api::VerifierIndexWrapper<StepCircuit<A>>,
    pub wrap_verifier: snarky::api::VerifierIndexWrapper<WrapCircuit<ROUNDS, STMT_LEN>>,
    /// The actual wrap verification-key commitments hashed by the step proof.
    pub wrap_vk_pts: Vec<(Fp, Fp)>,
}

/// Network-facing Mina encoding for a base-case Pickles proof.
///
/// The native proof remains available for local verification; this artifact
/// carries the stable Mina bytes needed at API boundaries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinaWrapProof {
    pub statement: Vec<Fq>,
    pub wrap_wire_proof: Vec<u8>,
    pub side_loaded_verification_key: String,
}

/// JSON-safe envelope intended for JS/o1js consumers.
///
/// Field elements are decimal strings to preserve full Pasta precision in
/// JavaScript. The wrapped Mina bin_prot proof bytes are base64 encoded, and
/// the side-loaded verification key remains Mina Base58Check.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct O1jsWrapProofJson {
    pub version: u8,
    pub statement: Vec<String>,
    pub wrap_wire_proof_base64: String,
    pub side_loaded_verification_key_base58: String,
}

#[deprecated(note = "use MinaWrapProof; this wrap proof envelope is no longer base-case specific")]
pub type MinaBaseCaseProof = MinaWrapProof;

#[deprecated(note = "use O1jsWrapProofJson; this JSON envelope is no longer base-case specific")]
pub type O1jsBaseCaseProofJson = O1jsWrapProofJson;

impl MinaWrapProof {
    pub const O1JS_JSON_VERSION: u8 = 1;

    pub fn to_o1js_json_value(&self) -> O1jsWrapProofJson {
        O1jsWrapProofJson {
            version: Self::O1JS_JSON_VERSION,
            statement: self
                .statement
                .iter()
                .map(|field| field.to_string())
                .collect(),
            wrap_wire_proof_base64: BASE64_STANDARD.encode(&self.wrap_wire_proof),
            side_loaded_verification_key_base58: self.side_loaded_verification_key.clone(),
        }
    }

    pub fn from_o1js_json_value(value: O1jsWrapProofJson) -> Result<Self, BaseCaseBackendError> {
        if value.version != Self::O1JS_JSON_VERSION {
            return Err(BaseCaseBackendError::O1jsJsonVersion(value.version));
        }
        let statement = value
            .statement
            .iter()
            .map(|field| {
                field
                    .parse::<Fq>()
                    .map_err(|_| BaseCaseBackendError::O1jsJsonField)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let wrap_wire_proof = BASE64_STANDARD
            .decode(value.wrap_wire_proof_base64)
            .map_err(|_| BaseCaseBackendError::O1jsJsonProofBytes)?;
        Ok(Self {
            statement,
            wrap_wire_proof,
            side_loaded_verification_key: value.side_loaded_verification_key_base58,
        })
    }

    pub fn to_o1js_json_string(&self) -> Result<String, BaseCaseBackendError> {
        serde_json::to_string(&self.to_o1js_json_value())
            .map_err(|_| BaseCaseBackendError::O1jsJsonSerialization)
    }

    pub fn from_o1js_json_string(value: &str) -> Result<Self, BaseCaseBackendError> {
        let value =
            serde_json::from_str(value).map_err(|_| BaseCaseBackendError::O1jsJsonSerialization)?;
        Self::from_o1js_json_value(value)
    }
}

impl<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize> BaseCaseProof<A, ROUNDS, STMT_LEN> {
    pub fn to_mina_network_proof(&self) -> Result<MinaWrapProof, BaseCaseBackendError> {
        let wrap_wire_proof = crate::mina_bin_prot::WrapWireProofV1::from_prover_proof(&self.proof)
            .and_then(|proof| proof.to_bin_prot())
            .map_err(|_| BaseCaseBackendError::MinaProofEncoding)?;
        let step_domain_log2 = self.step_verifier.index.domain.log_size_of_group as u8;
        let side_loaded_verification_key =
            SideLoadedVerificationKey::from_wrap_verifier(step_domain_log2, &self.wrap_verifier)
                .map_err(|_| BaseCaseBackendError::MinaVerificationKeyEncoding)?
                .to_stable_v2_base58()
                .map_err(|_| BaseCaseBackendError::MinaVerificationKeyEncoding)?;
        Ok(MinaWrapProof {
            statement: self.statement.clone(),
            wrap_wire_proof,
            side_loaded_verification_key,
        })
    }

    pub fn ensure_mina_network_proof_matches(
        &self,
        encoded: &MinaWrapProof,
    ) -> Result<(), BaseCaseBackendError> {
        if encoded != &self.to_mina_network_proof()? {
            return Err(BaseCaseBackendError::MinaEncodingMismatch);
        }
        crate::mina_bin_prot::WrapWireProofV1::from_bin_prot(&encoded.wrap_wire_proof)
            .map_err(|_| BaseCaseBackendError::MinaProofEncoding)?;
        SideLoadedVerificationKey::from_stable_v2_base58(
            self.step_verifier.index.domain.log_size_of_group as u8,
            &encoded.side_loaded_verification_key,
        )
        .map_err(|_| BaseCaseBackendError::MinaVerificationKeyEncoding)?;
        Ok(())
    }

    pub fn to_mina_stable_v3(
        &self,
    ) -> Result<crate::mina_bin_prot::WrapProofBaseV3, BaseCaseBackendError> {
        crate::mina_bin_prot::WrapProofBaseV3::from_proofs_with_statement(
            self.stable_statement.clone(),
            &self.step_proof,
            &self.proof,
        )
        .map_err(|_| BaseCaseBackendError::MinaProofEncoding)
    }
}

/// Returns a wrap verifier index's 28 commitments in Pickles' canonical
/// sigma, coefficients, selector order.
pub fn wrap_verification_key_points<const ROUNDS: usize, const STMT_LEN: usize>(
    verifier: &snarky::api::VerifierIndexWrapper<WrapCircuit<ROUNDS, STMT_LEN>>,
) -> Vec<(Fp, Fp)> {
    let index = &verifier.index;
    let point = |p: &Pallas| (p.x, p.y);
    let mut points = Vec::with_capacity(28);
    points.extend(
        index
            .sigma_comm
            .iter()
            .map(|commitment| point(&commitment.chunks[0])),
    );
    points.extend(
        index
            .coefficients_comm
            .iter()
            .map(|commitment| point(&commitment.chunks[0])),
    );
    points.push(point(&index.generic_comm.chunks[0]));
    points.push(point(&index.psm_comm.chunks[0]));
    points.push(point(&index.complete_add_comm.chunks[0]));
    points.push(point(&index.mul_comm.chunks[0]));
    points.push(point(&index.emul_comm.chunks[0]));
    points.push(point(&index.endomul_scalar_comm.chunks[0]));
    assert_eq!(points.len(), 28);
    points
}

/// Compiles the wrap circuit in two passes to break the Pickles VK cycle.
///
/// The bootstrap pass determines the wrap index from the circuit shape. The
/// final pass rebuilds the step proof with those real 28 commitments in its
/// accumulator digest, recompiles the wrap, asserts index stability, and
/// returns only the final proof.
pub fn prove_base_case_two_pass<A: StepApp + Clone, const ROUNDS: usize, const STMT_LEN: usize>(
    app: A,
    witness: A::Witness,
) -> BaseCaseProof<A, ROUNDS, STMT_LEN>
where
    A::Witness: Clone,
{
    // The bootstrap key must satisfy the step circuit's on-curve checks, so
    // use distinct multiples of the Pallas generator as placeholder points.
    let bootstrap_points = {
        use ark_ec::{AffineRepr, CurveGroup};
        let g = Pallas::generator().into_group();
        (1..=28u64)
            .map(|i| {
                let p = (g * mina_curves::pasta::Fq::from(i)).into_affine();
                (p.x, p.y)
            })
            .collect()
    };
    let bootstrap =
        prove_base_case::<A, ROUNDS, STMT_LEN>(app.clone(), witness.clone(), bootstrap_points);
    let actual_points = wrap_verification_key_points(&bootstrap.wrap_verifier);
    let final_proof = prove_base_case::<A, ROUNDS, STMT_LEN>(app, witness, actual_points.clone());
    assert_eq!(
        wrap_verification_key_points(&final_proof.wrap_verifier),
        actual_points,
        "wrap verification key changed between compilation passes"
    );
    final_proof
}

/// Concrete [`CompiledRuleBackend`] for a Pickles base (`N0`) rule.
///
/// Proof creation uses the two-pass real-wrap-VK pipeline. Verification checks
/// both the Kimchi wrap proof and the binding between the caller's public
/// application state and the accumulator digest in the wrap statement.
pub struct BaseCaseRuleBackend<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize> {
    rule_id: RuleId,
    app: A,
}

impl<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize>
    BaseCaseRuleBackend<A, ROUNDS, STMT_LEN>
{
    pub fn compile(rule: &InductiveRule, app: A) -> Result<Self, BaseCaseBackendError> {
        if rule.proofs_verified != ProofsVerified::N0 {
            return Err(BaseCaseBackendError::ExpectedBaseRule(rule.id));
        }
        Ok(Self {
            rule_id: rule.id,
            app,
        })
    }

    pub fn rule_id(&self) -> RuleId {
        self.rule_id
    }

    pub fn prove_with_mina_encoding(
        &mut self,
        public_input: &Vec<Fp>,
        witness: A::Witness,
    ) -> Result<(BaseCaseProof<A, ROUNDS, STMT_LEN>, MinaWrapProof), BaseCaseBackendError>
    where
        A: Clone,
        A::Witness: Clone,
    {
        let proof = <Self as CompiledRuleBackend>::prove(self, public_input, witness)?;
        let encoded = proof.to_mina_network_proof()?;
        Ok((proof, encoded))
    }

    pub fn verify_with_mina_encoding(
        &self,
        public_input: &Vec<Fp>,
        proof: &BaseCaseProof<A, ROUNDS, STMT_LEN>,
        encoded: &MinaWrapProof,
    ) -> Result<(), BaseCaseBackendError>
    where
        A: Clone,
        A::Witness: Clone,
    {
        <Self as CompiledRuleBackend>::verify(self, public_input, proof)?;
        proof.ensure_mina_network_proof_matches(encoded)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BaseCaseBackendError {
    ExpectedBaseRule(RuleId),
    PublicStateMismatch,
    WrapKeyMismatch,
    InvalidStatementLength(usize),
    InvalidWrapProof,
    MinaProofEncoding,
    MinaVerificationKeyEncoding,
    MinaEncodingMismatch,
    O1jsJsonSerialization,
    O1jsJsonVersion(u8),
    O1jsJsonField,
    O1jsJsonProofBytes,
}

impl<A: StepApp + Clone, const ROUNDS: usize, const STMT_LEN: usize> CompiledRuleBackend
    for BaseCaseRuleBackend<A, ROUNDS, STMT_LEN>
where
    A::Witness: Clone,
{
    type PublicInput = Vec<Fp>;
    type Witness = A::Witness;
    type Proof = BaseCaseProof<A, ROUNDS, STMT_LEN>;
    type Error = BaseCaseBackendError;

    fn prove(
        &mut self,
        public_input: &Self::PublicInput,
        witness: Self::Witness,
    ) -> Result<Self::Proof, Self::Error> {
        if self.app.state(&witness) != *public_input {
            return Err(BaseCaseBackendError::PublicStateMismatch);
        }
        Ok(prove_base_case_two_pass::<A, ROUNDS, STMT_LEN>(
            self.app.clone(),
            witness,
        ))
    }

    fn verify(
        &self,
        public_input: &Self::PublicInput,
        proof: &Self::Proof,
    ) -> Result<(), Self::Error> {
        let actual_vk = wrap_verification_key_points(&proof.wrap_verifier);
        if actual_vk != proof.wrap_vk_pts {
            return Err(BaseCaseBackendError::WrapKeyMismatch);
        }
        let digest = crate::hash_messages::hash_messages_for_next_step_proof_ref(
            Vesta::sponge_params(),
            &actual_vk,
            public_input,
            &[],
            &[],
        );
        if proof.statement.len() != STMT_LEN {
            return Err(BaseCaseBackendError::InvalidStatementLength(
                proof.statement.len(),
            ));
        }
        // Wrap.Statement.to_data stores the next-step message digest at slot
        // 12, before bulletproof challenges, branch data and feature flags.
        if proof.statement[12] != fp_to_fq(digest) {
            return Err(BaseCaseBackendError::PublicStateMismatch);
        }
        let statement: [Fq; STMT_LEN] =
            proof
                .statement
                .clone()
                .try_into()
                .map_err(|statement: Vec<Fq>| {
                    BaseCaseBackendError::InvalidStatementLength(statement.len())
                })?;
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            proof.wrap_verifier.verify::<PallasBase, PallasScalar>(
                proof.proof.clone(),
                statement,
                (),
            );
        }))
        .map_err(|_| BaseCaseBackendError::InvalidWrapProof)
    }
}

/// Proves one application execution through the full base-case pipeline and
/// verifies the resulting wrap proof. `ROUNDS` must match the step circuit's
/// IPA round count (log2 of its compiled domain).
pub fn prove_base_case<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize>(
    app: A,
    witness: A::Witness,
    wrap_vk_pts: Vec<(Fp, Fp)>,
) -> BaseCaseProof<A, ROUNDS, STMT_LEN> {
    prove_base_case_with_wrap_dump(app, witness, wrap_vk_pts).0
}

/// The wrap circuit of a base-case proof, in the `{ public_input_size,
/// gates }` shape shared with the jsoo `prover_to_json` dumps — the Fq half
/// of the gate-level parity diff against OCaml Pickles.
#[derive(serde::Serialize)]
pub struct WrapCircuitDump {
    pub public_input_size: usize,
    pub gates: Vec<kimchi::circuits::gate::CircuitGate<Fq>>,
}

/// [`prove_base_case`], additionally returning the compiled wrap circuit's
/// gates for parity tooling.
pub fn prove_base_case_with_wrap_dump<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize>(
    app: A,
    witness: A::Witness,
    wrap_vk_pts: Vec<(Fp, Fp)>,
) -> (BaseCaseProof<A, ROUNDS, STMT_LEN>, WrapCircuitDump) {
    assert_eq!(STMT_LEN, 13 + ROUNDS + 11, "STMT_LEN mismatch (OCaml 40-slot layout)");
    // ---- step proof ----
    let app_state = app.state(&witness);
    let step = StepCircuit { app };
    // Mina proves over the full Tick SRS (2^16) regardless of the circuit's
    // domain, so step IPA proofs always have 16 rounds.
    let (mut step_pi, step_ver) = step
        .compile_to_indexes_with_domain_and_srs(0, Some(crate::common::TICK_ROUNDS as u32))
        .unwrap();
    let svi = &step_ver.index;

    let digest = crate::hash_messages::hash_messages_for_next_step_proof_ref(
        Vesta::sponge_params(),
        &wrap_vk_pts,
        &app_state,
        &[],
        &[],
    );
    // Base-case step proofs carry two dummy accumulators
    // (`Wrap_hack.pad_accumulator`): dummy step-side IPA challenges and
    // their challenge-polynomial commitment over the full Tick SRS.
    let dummy_recursion = {
        let endo_wrap = <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1;
        let endo_step = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1;
        let (_, step_dummy) = crate::dummy::ipa_wrap_and_step::<Fq, Fp>(endo_wrap, endo_step);
        let sg = crate::dummy::compute_sg(svi.srs().as_ref(), &step_dummy.challenges_computed);
        kimchi::proof::RecursionChallenge::new(
            step_dummy.challenges_computed,
            PolyComm { chunks: vec![sg] },
        )
    };
    let (step_proof, _) = step_pi
        .prove_with_recursion_mask::<VestaBase, VestaScalar>(
            digest,
            (witness, wrap_vk_pts.clone()),
            true,
            vec![dummy_recursion.clone(), dummy_recursion.clone()],
            Some(&[false, false]),
        )
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
        .oracles_with_recursion_mask::<VestaBase, VestaScalar, _>(
            svi,
            &public_comm,
            Some(&public_input),
            Some(&[false, false]),
        )
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

    let sg_old_points: Vec<Vesta> = step_proof
        .prev_challenges
        .iter()
        .map(|rc| rc.comm.chunks[0])
        .collect();
    let ww = crate::wrap::wrap_witness(
        svi.max_poly_size as u64,
        svi.domain.size,
        svi.domain.group_gen,
        &step_proof,
        &public_comm,
        svi.digest::<VestaBase>(),
        &sg_old_points,
        Some(&[false, false]),
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
            let mut prev_sponge = VestaScalar::from(params);
            for (keep, rc) in [false, false].iter().zip(&step_proof.prev_challenges) {
                if *keep {
                    prev_sponge.absorb_multiple(&rc.chals);
                }
            }
            prev_sponge.digest()
        };
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
    let dummy_wrap_raw_chals: Vec<Vec<Fq>> = {
        let endo_wrap = <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1;
        let endo_step = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1;
        let (wrap, _) = crate::dummy::ipa_wrap_and_step::<Fq, Fp>(endo_wrap, endo_step);
        vec![wrap.prechallenges.clone(); crate::common::MAX_PROOFS_VERIFIED]
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
    let statement = crate::composition_types::wrap::wrap_statement_to_field_elements_ocaml(
        &plonk_vals,
        fp_to_fq(ww.cip_repr),
        fp_to_fq(ww.b_repr),
        &ScalarChallenge(fp_to_fq(claimed_xi_raw)),
        &bp_chals,
        &ScalarChallenge(Fq::from(0u64)),
        &branch,
        fp_to_fq(ww.sponge_digest),
        msgs_wrap_digest,
        fp_to_fq(digest),
    );
    assert_eq!(statement.len(), STMT_LEN, "statement length");
    let stable_statement = crate::mina_bin_prot::WrapStatementMinimalV1::from_flattened(
        statement.clone(),
        crate::mina_bin_prot::WrapMessagesForNextWrapProofV1 {
            challenge_polynomial_commitment: (sg_pt.x, sg_pt.y),
            old_bulletproof_challenges: dummy_wrap_raw_chals,
        },
        crate::mina_bin_prot::StepMessagesForNextProofV1 {
            challenge_polynomial_commitments: Vec::new(),
            old_bulletproof_challenges: Vec::new(),
        },
    )
    .unwrap();

    // ---- wrap proof ----
    let co = |p: &Vesta| (p.x, p.y);
    let l0 = lgr[0].chunks[0];
    let correction = crate::public_input::lagrange_correction(&l0, 255);
    drop(lgr); // release the SRS cache guard so step_ver can move below
    let srs_h = svi.srs().h;
    let physical_sg_olds: Vec<(Fq, Fq)> = {
        let mut sg_olds: Vec<_> = step_proof
            .prev_challenges
            .iter()
            .map(|rc| co(&rc.comm.chunks[0]))
            .collect();
        if sg_olds.is_empty() {
            let dummy = co(&dummy_recursion.comm.chunks[0]);
            sg_olds.resize(crate::common::MAX_PROOFS_VERIFIED, dummy);
        }
        sg_olds
    };
    let wdata = WrapWitnessData {
        step_domain_log2: svi.domain.log_size_of_group as u8,
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
        sg_olds: physical_sg_olds,
        unfinalized: vec![],
        step_statement: vec![WrapStepStatementSlot::Packed {
            value: fp_to_fq(digest),
            num_bits: 255,
        }],
        step_statement_lagranges: vec![(co(&l0), co(&correction))],
        h: (srs_h.x, srs_h.y),
        new_acc_dummies: dummy_wrap_chals,
    };

    let stmt_arr: [Fq; STMT_LEN] = statement
        .clone()
        .try_into()
        .unwrap_or_else(|_| unreachable!());
    // Full Tock SRS (2^15): wrap IPA proofs always have 15 rounds.
    let (mut wrap_pi, wrap_ver) = WrapCircuit::<ROUNDS, STMT_LEN> { w: wdata }
        .compile_to_indexes_with_domain_and_srs(0, Some(crate::common::TOCK_ROUNDS as u32))
        .unwrap();
    let wrap_dump = WrapCircuitDump {
        public_input_size: wrap_pi.index.cs.public,
        gates: wrap_pi.index.cs.gates.to_vec(),
    };
    let (wrap_proof, _) = wrap_pi
        .prove::<PallasBase, PallasScalar>(stmt_arr, (), true)
        .unwrap();
    wrap_ver.verify::<PallasBase, PallasScalar>(wrap_proof.clone(), stmt_arr, ());

    (
        BaseCaseProof {
            statement,
            stable_statement,
            proof: wrap_proof,
            step_proof,
            step_verifier: step_ver,
            wrap_verifier: wrap_ver,
            wrap_vk_pts,
        },
        wrap_dump,
    )
}

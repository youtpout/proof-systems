//! Dummy proof data for unverified (base-case / padding) proofs — port of
//! pickles' `dummy.ml`.
//!
//! A base-case step proof carries `should_finalize = false` unfinalized
//! entries and padding accumulators; their values are deterministic
//! ([`crate::ro`]) so the prover and every circuit agree on them. `sg` is the
//! commitment to the challenge polynomial of the dummy challenges
//! (`compute_sg` = a non-hiding commitment to `b_poly_coefficients`).

use ark_ff::PrimeField;
use kimchi::proof::{PointEvaluations, ProofEvaluations};
use mina_curves::pasta::{Fp, Fq, Pallas, Vesta};
use std::sync::OnceLock;

use crate::{all_evals::AllEvals, ro::Ro};

/// The dummy IPA challenges of one side: raw 128-bit prechallenges and their
/// endo field images (`Dummy.Ipa.{Step,Wrap}.challenges[_computed]`).
#[derive(Clone)]
pub struct DummyIpa<F: PrimeField> {
    pub prechallenges: Vec<F>,
    pub challenges_computed: Vec<F>,
}

/// Protocol-fixed Pasta dummy challenges, initialized once per process.
pub fn pasta_ipa_wrap_and_step() -> &'static (DummyIpa<Fq>, DummyIpa<Fp>) {
    static DUMMY: OnceLock<(DummyIpa<Fq>, DummyIpa<Fp>)> = OnceLock::new();
    DUMMY.get_or_init(|| {
        use kimchi::curve::KimchiCurve;
        ipa_wrap_and_step::<Fq, Fp>(
            <Pallas as KimchiCurve<{ crate::common::FULL_ROUNDS }>>::endos().1,
            <Vesta as KimchiCurve<{ crate::common::FULL_ROUNDS }>>::endos().1,
        )
    })
}

/// Commitment to the protocol-fixed dummy Wrap challenge polynomial.
pub fn pasta_dummy_wrap_sg() -> Pallas {
    static SG: OnceLock<Pallas> = OnceLock::new();
    *SG.get_or_init(|| {
        compute_sg(
            crate::common::tock_srs(1 << crate::common::TOCK_ROUNDS).as_ref(),
            &pasta_ipa_wrap_and_step().0.challenges_computed,
        )
    })
}

/// One challenge-polynomial accumulator entry: the commitment to `b_poly` and
/// the field-form IPA challenges it commits to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChallengePolynomial<G>
where
    G: poly_commitment::commitment::CommitmentCurve,
{
    pub commitment: G,
    pub challenges: Vec<G::ScalarField>,
}

/// `rounds` dummy challenges from the shared 128-bit stream, with their
/// `to_field` images under `endo` (`Ipa.compute_challenge`).
pub fn ipa_challenges<F: PrimeField>(chal_stream: &mut Ro, rounds: usize, endo: F) -> DummyIpa<F> {
    // `Pickles_types.Vector.init` enumerates its resulting vector in the
    // opposite order from the calls to its initializer. Consume the random
    // oracle forwards, then reverse the stored vector to match OCaml.
    let mut prechallenges: Vec<F> = (0..rounds).map(|_| chal_stream.next_field()).collect();
    prechallenges.reverse();
    let challenges_computed = prechallenges
        .iter()
        .map(|&c| crate::scalar_challenge::ScalarChallenge(c).to_field(endo))
        .collect();
    DummyIpa {
        prechallenges,
        challenges_computed,
    }
}

/// The dummy wrap-side (Tock, 15 rounds) and step-side (Tick, 16 rounds)
/// challenges, drawn from a single `"chal"` stream in that order and stored
/// in `Pickles_types.Vector.init` order (matching `dummy.ml`).
pub fn ipa_wrap_and_step<FWrap: PrimeField, FStep: PrimeField>(
    endo_wrap: FWrap,
    endo_step: FStep,
) -> (DummyIpa<FWrap>, DummyIpa<FStep>) {
    let mut chal = Ro::chal();
    let wrap = ipa_challenges(&mut chal, crate::common::TOCK_ROUNDS, endo_wrap);
    let step = ipa_challenges(&mut chal, crate::common::TICK_ROUNDS, endo_step);
    (wrap, step)
}

/// `Dummy.Ipa.Wrap.challenges_computed`: the wrap-side dummy IPA challenges in
/// field form, after the shared wrap-then-step `Ro.chal` initialisation order.
pub fn wrap_challenges_computed<FWrap: PrimeField, FStep: PrimeField>(
    endo_wrap: FWrap,
    endo_step: FStep,
) -> Vec<FWrap> {
    ipa_wrap_and_step::<FWrap, FStep>(endo_wrap, endo_step)
        .0
        .challenges_computed
}

/// `Wrap_hack.pad_challenges`: front-pad the real wrap accumulator challenge
/// vectors to Pickles' fixed padded length 2 using
/// [`wrap_challenges_computed`].
pub fn pad_wrap_challenges<FWrap: PrimeField, FStep: PrimeField>(
    real: &[Vec<FWrap>],
    endo_wrap: FWrap,
    endo_step: FStep,
) -> Vec<Vec<FWrap>> {
    assert!(
        real.len() <= crate::common::MAX_PROOFS_VERIFIED,
        "pad_wrap_challenges: at most two proof accumulators"
    );
    let dummy = wrap_challenges_computed::<FWrap, FStep>(endo_wrap, endo_step);
    let mut out = Vec::with_capacity(crate::common::MAX_PROOFS_VERIFIED);
    for _ in real.len()..crate::common::MAX_PROOFS_VERIFIED {
        out.push(dummy.clone());
    }
    out.extend(real.iter().cloned());
    out
}

/// `Wrap_hack.pad_accumulator`: front-pad challenge-polynomial accumulator
/// entries to Pickles' fixed padded length 2 using `Dummy.Ipa.Wrap.sg` and
/// `Dummy.Ipa.Wrap.challenges_computed`.
pub fn pad_wrap_accumulator<G, FStep>(
    srs: &poly_commitment::ipa::SRS<G>,
    real: &[ChallengePolynomial<G>],
    endo_wrap: G::ScalarField,
    endo_step: FStep,
) -> Vec<ChallengePolynomial<G>>
where
    G: poly_commitment::commitment::CommitmentCurve,
    FStep: PrimeField,
{
    assert!(
        real.len() <= crate::common::MAX_PROOFS_VERIFIED,
        "pad_wrap_accumulator: at most two proof accumulators"
    );
    let challenges = wrap_challenges_computed::<G::ScalarField, FStep>(endo_wrap, endo_step);
    let dummy = ChallengePolynomial {
        commitment: compute_sg(srs, &challenges),
        challenges,
    };
    let mut out = Vec::with_capacity(crate::common::MAX_PROOFS_VERIFIED);
    for _ in real.len()..crate::common::MAX_PROOFS_VERIFIED {
        out.push(dummy.clone());
    }
    out.extend(real.iter().cloned());
    out
}

/// `compute_sg`: the challenge-polynomial commitment of the given (field-form)
/// challenges — a non-hiding SRS commitment to `b_poly_coefficients(chals)`.
pub fn compute_sg<G>(
    srs: &poly_commitment::ipa::SRS<G>,
    challenges_computed: &[G::ScalarField],
) -> G
where
    G: poly_commitment::commitment::CommitmentCurve,
{
    use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial};
    use poly_commitment::{commitment::b_poly_coefficients, SRS as _};

    let coeffs = b_poly_coefficients(challenges_computed);
    let poly = DensePolynomial::from_coefficients_vec(coeffs);
    srs.commit_non_hiding(&poly, 1).chunks[0]
}

/// `Dummy.evals`: deterministic Tock-field evaluations used for padding
/// unverified proofs. This mirrors `dummy.ml`: every mandatory evaluation has
/// one chunk at `zeta` and one at `zeta*omega`, followed by one public-input
/// chunk at each point and `ft_eval1`.
pub fn evals<F: PrimeField>() -> AllEvals<F> {
    let mut ro = Ro::tock();

    let mut pair = || PointEvaluations {
        zeta: vec![ro.next_field()],
        zeta_omega: vec![ro.next_field()],
    };

    // Keep the draw order aligned with `Evaluation_lengths.default` in OCaml:
    // w, coefficients, z, s, then the six mandatory selectors.
    let w = std::array::from_fn(|_| pair());
    let coefficients = std::array::from_fn(|_| pair());
    let z = pair();
    let s = std::array::from_fn(|_| pair());
    let generic_selector = pair();
    let poseidon_selector = pair();
    let complete_add_selector = pair();
    let mul_selector = pair();
    let emul_selector = pair();
    let endomul_scalar_selector = pair();

    let evals = ProofEvaluations {
        public: None,
        w,
        z,
        s,
        coefficients,
        generic_selector,
        poseidon_selector,
        complete_add_selector,
        mul_selector,
        emul_selector,
        endomul_scalar_selector,
        range_check0_selector: None,
        range_check1_selector: None,
        foreign_field_add_selector: None,
        foreign_field_mul_selector: None,
        xor_selector: None,
        rot_selector: None,
        lookup_aggregation: None,
        lookup_table: None,
        lookup_sorted: std::array::from_fn(|_| None),
        runtime_lookup_table: None,
        runtime_lookup_table_selector: None,
        xor_lookup_selector: None,
        lookup_gate_lookup_selector: None,
        range_check_lookup_selector: None,
        foreign_field_mul_lookup_selector: None,
    };
    let public_input = PointEvaluations {
        zeta: vec![ro.next_field()],
        zeta_omega: vec![ro.next_field()],
    };
    let ft_eval1 = ro.next_field();

    AllEvals {
        ft_eval1,
        public_input,
        evals,
    }
}

/// `Dummy.evals_combined`: same dummy evaluations after chunk-combination.
/// With the default single chunk this is an identity, but keeping the helper
/// explicit matches the OCaml API and the places that consume scalar evals.
pub fn evals_combined<F: PrimeField>() -> AllEvals<F> {
    fn combine<F: PrimeField>(xs: &[F]) -> F {
        xs.iter().copied().sum()
    }

    let evals = evals::<F>();
    AllEvals {
        ft_eval1: evals.ft_eval1,
        public_input: evals.public_input.map(&|xs| vec![combine(&xs)]),
        evals: evals.evals.map(&|pe| pe.map(&|xs| vec![combine(&xs)])),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
    use kimchi::{
        circuits::wires::{COLUMNS, PERMUTS},
        curve::KimchiCurve,
    };
    use mina_curves::pasta::{Fp, Fq, Pallas, Vesta};
    use poly_commitment::{commitment::b_poly_coefficients, SRS as _};
    use std::str::FromStr;

    /// Regression vectors from Pickles' `test_common.ml`.
    #[test]
    fn wrap_computed_challenges_match_ocaml() {
        let expected = [
            "7048930911355605315581096707847688535149125545610393399193999502037687877674",
            "5945064094191074331354717685811267396540107129706976521474145740173204364019",
            "20315491820009986698838977727629973056499886675589920515484193128018854963801",
            "375929229548289966749422550601268097380795636681684498450629863247980915833",
            "19682218496321100578766622300447982536359891434050417209656101638029891689955",
            "516598185966802396400068849903674663130928531697254466925429658676832606723",
            "23729760760563685146228624125180554011222918208600079938584869191222807389336",
            "11155777282048225577422475738306432747575091690354122761439079853293714987855",
            "24977767586983413450834833875715786066408803952857478894197349635213480783870",
            "2813347787496113574506936084777563965225649411532015639663405402448028142689",
            "22626141769059119580550800305467929090916842064220293932303261732461616709448",
            "18748107085456859495495117012311103043200881556220793307463332157672741458218",
            "22196219950929618042921320796106738233125483954115679355597636800196070731081",
            "13054421325261400802177761929986025883530654947859503505174678618288142017333",
            "4799483385651443229337780097631636300491234601736019220096005875687579936102",
        ]
        .map(|x| Fq::from_str(x).expect("valid OCaml Fq regression vector"));
        let endo_wrap = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1;
        let endo_step = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1;
        let actual = wrap_challenges_computed::<Fq, Fp>(endo_wrap, endo_step);
        assert_eq!(actual, expected);
    }

    /// The dummy challenge streams are deterministic and correctly sized, and
    /// `compute_sg` equals the direct MSM of the b-poly coefficients.
    #[test]
    fn dummy_challenges_and_sg() {
        let endo_wrap = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1;
        let endo_step = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1;
        let (wrap, step) = ipa_wrap_and_step::<Fq, Fp>(endo_wrap, endo_step);
        assert_eq!(wrap.prechallenges.len(), crate::common::TOCK_ROUNDS);
        assert_eq!(step.prechallenges.len(), crate::common::TICK_ROUNDS);
        let (wrap2, _) = ipa_wrap_and_step::<Fq, Fp>(endo_wrap, endo_step);
        assert_eq!(wrap.prechallenges, wrap2.prechallenges, "deterministic");
        assert_ne!(
            wrap.prechallenges[0], wrap.prechallenges[1],
            "stream advances"
        );

        // sg == MSM of b_poly_coefficients over the SRS basis
        let srs = poly_commitment::ipa::SRS::<Pallas>::create(1 << crate::common::TOCK_ROUNDS);
        let sg = compute_sg(&srs, &wrap.challenges_computed);
        let coeffs = b_poly_coefficients(&wrap.challenges_computed);
        let expected = <Pallas as AffineRepr>::Group::msm(&srs.g[..coeffs.len()], &coeffs).unwrap();
        assert_eq!(sg, expected.into_affine());
        assert!(sg.is_on_curve());
    }

    /// `Wrap_hack.pad_challenges` prepends dummy wrap challenges up to padded
    /// length 2, preserving the real accumulator suffix.
    #[test]
    fn pad_wrap_challenges_prepends_dummy_vectors() {
        let endo_wrap = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1;
        let endo_step = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1;
        let dummy = wrap_challenges_computed::<Fq, Fp>(endo_wrap, endo_step);

        let none = pad_wrap_challenges::<Fq, Fp>(&[], endo_wrap, endo_step);
        assert_eq!(none, vec![dummy.clone(), dummy.clone()]);

        let real = vec![vec![Fq::from(1u64); crate::common::TOCK_ROUNDS]];
        let one = pad_wrap_challenges::<Fq, Fp>(&real, endo_wrap, endo_step);
        assert_eq!(one, vec![dummy, real[0].clone()]);

        let two_real = vec![
            vec![Fq::from(2u64); crate::common::TOCK_ROUNDS],
            vec![Fq::from(3u64); crate::common::TOCK_ROUNDS],
        ];
        let two = pad_wrap_challenges::<Fq, Fp>(&two_real, endo_wrap, endo_step);
        assert_eq!(two, two_real);
    }

    /// `Wrap_hack.pad_accumulator` uses the same dummy challenge vector and
    /// its `sg = compute_sg(dummy_challenges)`.
    #[test]
    fn pad_wrap_accumulator_prepends_dummy_sg() {
        let endo_wrap = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1;
        let endo_step = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1;
        let srs = poly_commitment::ipa::SRS::<Pallas>::create(1 << crate::common::TOCK_ROUNDS);
        let dummy_challenges = wrap_challenges_computed::<Fq, Fp>(endo_wrap, endo_step);
        let dummy_sg = compute_sg(&srs, &dummy_challenges);

        let real = ChallengePolynomial {
            commitment: Pallas::generator(),
            challenges: vec![Fq::from(42u64); crate::common::TOCK_ROUNDS],
        };
        let padded = pad_wrap_accumulator(&srs, std::slice::from_ref(&real), endo_wrap, endo_step);

        assert_eq!(padded.len(), crate::common::MAX_PROOFS_VERIFIED);
        assert_eq!(padded[0].commitment, dummy_sg);
        assert_eq!(padded[0].challenges, dummy_challenges);
        assert_eq!(padded[1], real);
    }

    /// `Dummy.evals` uses the `Ro.tock` stream in the same order as
    /// `dummy.ml`: mandatory column pairs first, then public-input evals, then
    /// `ft_eval1`.
    #[test]
    fn dummy_evals_follow_ocaml_ro_order() {
        let e = evals::<Fq>();
        let mut ro = Ro::tock();

        assert_eq!(e.evals.w[0].zeta[0], ro.next_field::<Fq>());
        assert_eq!(e.evals.w[0].zeta_omega[0], ro.next_field::<Fq>());

        let mandatory = COLUMNS + COLUMNS + 1 + (PERMUTS - 1) + 6;
        let mut all = Ro::tock();
        let expected: Vec<Fq> = (0..(2 * mandatory + 3)).map(|_| all.next_field()).collect();
        assert_eq!(e.public_input.zeta[0], expected[2 * mandatory]);
        assert_eq!(e.public_input.zeta_omega[0], expected[2 * mandatory + 1]);
        assert_eq!(e.ft_eval1, expected[2 * mandatory + 2]);

        assert!(e.evals.public.is_none());
        assert!(e.evals.range_check0_selector.is_none());
        assert!(e.evals.lookup_sorted.iter().all(Option::is_none));
    }

    /// The default evaluation lengths are all one chunk, so combining preserves
    /// every value while exposing the scalar-eval API shape.
    #[test]
    fn dummy_evals_combined_is_single_chunk_identity() {
        let raw = evals::<Fq>();
        let combined = evals_combined::<Fq>();

        assert_eq!(combined.ft_eval1, raw.ft_eval1);
        assert_eq!(combined.public_input, raw.public_input);
        assert_eq!(combined.evals.z, raw.evals.z);
        assert_eq!(combined.evals.w[0], raw.evals.w[0]);
        assert_eq!(
            combined.evals.endomul_scalar_selector,
            raw.evals.endomul_scalar_selector
        );
    }

    use mina_curves::pasta::VestaParameters;
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use snarky::{api::SnarkyCircuit, loc, FieldVar, RunState, SnarkyResult};

    type BaseSponge = DefaultFqSponge<
        VestaParameters,
        PlonkSpongeConstantsKimchi,
        { crate::common::FULL_ROUNDS },
    >;
    type ScalarSponge =
        DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { crate::common::FULL_ROUNDS }>;

    struct SmallCircuit {}
    impl SnarkyCircuit for SmallCircuit {
        type Curve = Vesta;
        const PREV_CHALLENGES: usize = 1;
        type Proof =
            poly_commitment::ipa::OpeningProof<Self::Curve, { crate::common::FULL_ROUNDS }>;
        type PrivateInput = Fp;
        type PublicInput = FieldVar<Fp>;
        type PublicOutput = ();
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            z: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<()> {
            let x: FieldVar<Fp> = sys.compute(loc!(), |_| *private.unwrap())?;
            let xx = x.mul(&x, None, loc!(), sys)?;
            xx.assert_equals(sys, loc!(), &z)?;
            let _ = sys.poseidon(loc!(), (x, z));
            Ok(())
        }
    }

    /// A proof carrying a dummy recursion challenge (Ro challenges + their
    /// challenge-polynomial commitment) proves and verifies — the accumulator
    /// folding pipeline (`prove_with_recursion` -> `create_recursive` ->
    /// kimchi batch verification) works end-to-end.
    #[test]
    fn recursion_challenge_folding_round_trips() {
        use poly_commitment::commitment::PolyComm;

        let (mut pi, ver) = SmallCircuit {}.compile_to_indexes().unwrap();
        let endo_step =
            <Vesta as kimchi::curve::KimchiCurve<{ crate::common::FULL_ROUNDS }>>::endos().1;
        // as many dummy challenges as the prover SRS supports (the challenge
        // polynomial has 2^rounds coefficients and must fit in one chunk)
        let rounds = {
            use poly_commitment::SRS as _;
            (u32::BITS - 1 - (pi.index.srs.size() as u32).leading_zeros()) as usize
        };
        let mut chal = crate::ro::Ro::chal();
        let dummy = ipa_challenges::<Fp>(&mut chal, rounds, endo_step);
        let sg = compute_sg(&pi.index.srs, &dummy.challenges_computed);
        let recursion = kimchi::proof::RecursionChallenge {
            chals: dummy.challenges_computed,
            comm: PolyComm { chunks: vec![sg] },
        };

        let x = Fp::from(3u64);
        let z = x * x;
        let (proof, _) = pi
            .prove_with_recursion::<BaseSponge, ScalarSponge>(z, x, true, vec![recursion])
            .unwrap();
        ver.verify::<BaseSponge, ScalarSponge>(proof, z, ());
    }

    /// Same, but the accumulator comes from a *real* previous proof of the
    /// same circuit: its transcript-replayed IPA challenges and its sg —
    /// exactly the recursive-step scenario.
    #[test]
    fn recursion_challenge_from_real_proof_round_trips() {
        use ark_ff::{BigInteger, One, PrimeField};
        use poly_commitment::{
            commitment::{shift_scalar, PolyComm},
            SRS as _,
        };

        let (mut pi, ver) = SmallCircuit {}.compile_to_indexes().unwrap();
        let vi = &ver.index;
        let endo_step =
            <Vesta as kimchi::curve::KimchiCurve<{ crate::common::FULL_ROUNDS }>>::endos().1;

        // proof #0 (no accumulator)
        let x = Fp::from(5u64);
        let z = x * x;
        let (proof0, _) = pi
            .prove_with_recursion::<BaseSponge, ScalarSponge>(z, x, true, vec![])
            .unwrap();

        // hmm: the index expects 1 prev challenge — proof #0 with zero would
        // fail verification, so give it a dummy accumulator too
        let _ = proof0;
        let rounds = (u32::BITS - 1 - (pi.index.srs.size() as u32).leading_zeros()) as usize;
        let mut chal = crate::ro::Ro::chal();
        let dummy = ipa_challenges::<Fp>(&mut chal, rounds, endo_step);
        let sg0 = compute_sg(&pi.index.srs, &dummy.challenges_computed);
        let rec0 = kimchi::proof::RecursionChallenge {
            chals: dummy.challenges_computed.clone(),
            comm: PolyComm { chunks: vec![sg0] },
        };
        let (proof0, _) = pi
            .prove_with_recursion::<BaseSponge, ScalarSponge>(z, x, true, vec![rec0])
            .unwrap();

        // extract proof #0's real IPA challenges via the kimchi transcript
        let public_input = vec![z];
        let lgr = vi.srs().get_lagrange_basis(vi.domain);
        let com: Vec<_> = lgr.iter().take(vi.public).collect();
        let elm: Vec<_> = public_input.iter().map(|s| -*s).collect();
        let pc = PolyComm::<Vesta>::multi_scalar_mul(&com, &elm);
        let public_comm = vi
            .srs()
            .mask_custom(pc.clone(), &pc.map(|_| Fp::one()))
            .unwrap()
            .commitment;
        let o = proof0
            .oracles::<BaseSponge, ScalarSponge, _>(vi, &public_comm, Some(&public_input))
            .unwrap();
        let chals = {
            use mina_poseidon::FqSponge as _;
            let mut sp = o.fq_sponge.clone();
            sp.absorb_fr(&[shift_scalar::<Vesta>(o.combined_inner_product)]);
            let _t = sp.challenge_fq();
            proof0
                .proof
                .challenges::<BaseSponge>(&endo_step, &mut sp)
                .chal
        };
        // consistency: sg == commit(b_poly(chals))
        assert_eq!(
            compute_sg(&pi.index.srs, &chals),
            proof0.proof.sg,
            "sg0 == commit(b_poly(chals))"
        );
        let recursion = kimchi::proof::RecursionChallenge {
            chals,
            comm: PolyComm {
                chunks: vec![proof0.proof.sg],
            },
        };

        // proof #1 folds proof #0's accumulator
        let (proof1, _) = pi
            .prove_with_recursion::<BaseSponge, ScalarSponge>(z, x, true, vec![recursion])
            .unwrap();
        ver.verify::<BaseSponge, ScalarSponge>(proof1, z, ());
        let _ = Fp::from_le_bytes_mod_order(&Fp::one().into_bigint().to_bytes_le());
    }

    /// Regression test: folding an accumulator whose challenge polynomial is
    /// *smaller* than the host proof's SRS used to fail kimchi's batch
    /// verification — `RecursionChallenge::evals` returned two chunks
    /// `[full, 0]` when `b_len < max_poly_size` (the `(max..b_len)` diff range
    /// is empty) while the prover opened a single chunk, shifting the
    /// polyscale powers. Fixed by returning a single chunk whenever the
    /// polynomial fits (`max_poly_size >= b_len`); mina never hits this case
    /// because its padded domains keep `b_len == max_poly_size`.
    #[test]
    fn recursion_challenge_cross_size_folding() {
        use ark_ff::One;
        use poly_commitment::{commitment::PolyComm, SRS as _};

        let (pi, _ver) = SmallCircuit {}.compile_to_indexes().unwrap();
        let endo_step =
            <Vesta as kimchi::curve::KimchiCurve<{ crate::common::FULL_ROUNDS }>>::endos().1;
        let rounds = (u32::BITS - 1 - (pi.index.srs.size() as u32).leading_zeros()) as usize;
        let mut chal = crate::ro::Ro::chal();
        let dummy = ipa_challenges::<Fp>(&mut chal, rounds, endo_step);
        let sg0 = compute_sg(&pi.index.srs, &dummy.challenges_computed);
        let recursion = kimchi::proof::RecursionChallenge {
            chals: dummy.challenges_computed,
            comm: PolyComm { chunks: vec![sg0] },
        };

        let (mut big_pi, big_ver) = BiggerCircuit {}.compile_to_indexes().unwrap();
        assert!(
            big_pi.index.srs.size() > pi.index.srs.size(),
            "bigger circuit must have a bigger SRS"
        );
        let x = Fp::from(5u64);
        let z = x * x;
        let _ = Fp::one();
        let (big_proof, _) = big_pi
            .prove_with_recursion::<BaseSponge, ScalarSponge>(z, x, true, vec![recursion])
            .unwrap();
        big_ver.verify::<BaseSponge, ScalarSponge>(big_proof, z, ());
    }

    /// Same statement, more rows (a bigger domain/SRS than [`SmallCircuit`]).
    struct BiggerCircuit {}
    impl SnarkyCircuit for BiggerCircuit {
        type Curve = Vesta;
        const PREV_CHALLENGES: usize = 1;
        type Proof =
            poly_commitment::ipa::OpeningProof<Self::Curve, { crate::common::FULL_ROUNDS }>;
        type PrivateInput = Fp;
        type PublicInput = FieldVar<Fp>;
        type PublicOutput = ();
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            z: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<()> {
            let x: FieldVar<Fp> = sys.compute(loc!(), |_| *private.unwrap())?;
            let xx = x.mul(&x, None, loc!(), sys)?;
            xx.assert_equals(sys, loc!(), &z)?;
            let mut acc = (x, z);
            for _ in 0..60 {
                acc = sys.poseidon(loc!(), acc);
            }
            Ok(())
        }
    }
}

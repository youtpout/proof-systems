//! Dummy proof data for unverified (base-case / padding) proofs — port of
//! pickles' `dummy.ml`.
//!
//! A base-case step proof carries `should_finalize = false` unfinalized
//! entries and padding accumulators; their values are deterministic
//! ([`crate::ro`]) so the prover and every circuit agree on them. `sg` is the
//! commitment to the challenge polynomial of the dummy challenges
//! (`compute_sg` = a non-hiding commitment to `b_poly_coefficients`).

use ark_ff::PrimeField;

use crate::ro::Ro;

/// The dummy IPA challenges of one side: raw 128-bit prechallenges and their
/// endo field images (`Dummy.Ipa.{Step,Wrap}.challenges[_computed]`).
pub struct DummyIpa<F: PrimeField> {
    pub prechallenges: Vec<F>,
    pub challenges_computed: Vec<F>,
}

/// `rounds` dummy challenges from the shared 128-bit stream, with their
/// `to_field` images under `endo` (`Ipa.compute_challenge`).
pub fn ipa_challenges<F: PrimeField>(chal_stream: &mut Ro, rounds: usize, endo: F) -> DummyIpa<F> {
    let prechallenges: Vec<F> = (0..rounds).map(|_| chal_stream.next_field()).collect();
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
/// challenges, drawn from a single `"chal"` stream in that order (matching
/// `dummy.ml`'s module-initialisation order).
pub fn ipa_wrap_and_step<FWrap: PrimeField, FStep: PrimeField>(
    endo_wrap: FWrap,
    endo_step: FStep,
) -> (DummyIpa<FWrap>, DummyIpa<FStep>) {
    let mut chal = Ro::chal();
    let wrap = ipa_challenges(&mut chal, crate::common::TOCK_ROUNDS, endo_wrap);
    let step = ipa_challenges(&mut chal, crate::common::TICK_ROUNDS, endo_step);
    (wrap, step)
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
    use poly_commitment::commitment::b_poly_coefficients;
    use poly_commitment::SRS as _;

    let coeffs = b_poly_coefficients(challenges_computed);
    let poly = DensePolynomial::from_coefficients_vec(coeffs);
    srs.commit_non_hiding(&poly, 1).chunks[0]
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Fq, Pallas, Vesta};
    use poly_commitment::commitment::b_poly_coefficients;
    use poly_commitment::SRS as _;

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
        let expected =
            <Pallas as AffineRepr>::Group::msm(&srs.g[..coeffs.len()], &coeffs).unwrap();
        assert_eq!(sg, expected.into_affine());
        assert!(sg.is_on_curve());
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
        type Proof = poly_commitment::ipa::OpeningProof<Self::Curve, { crate::common::FULL_ROUNDS }>;
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
        let endo_step = <Vesta as kimchi::curve::KimchiCurve<
            { crate::common::FULL_ROUNDS },
        >>::endos()
        .1;
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
        use poly_commitment::commitment::{shift_scalar, PolyComm};
        use poly_commitment::SRS as _;

        let (mut pi, ver) = SmallCircuit {}.compile_to_indexes().unwrap();
        let vi = &ver.index;
        let endo_step = <Vesta as kimchi::curve::KimchiCurve<
            { crate::common::FULL_ROUNDS },
        >>::endos()
        .1;

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
            proof0.proof.challenges::<BaseSponge>(&endo_step, &mut sp).chal
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
        use poly_commitment::commitment::PolyComm;
        use poly_commitment::SRS as _;

        let (pi, _ver) = SmallCircuit {}.compile_to_indexes().unwrap();
        let endo_step = <Vesta as kimchi::curve::KimchiCurve<
            { crate::common::FULL_ROUNDS },
        >>::endos()
        .1;
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

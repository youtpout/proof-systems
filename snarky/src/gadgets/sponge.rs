//! Sponge gadget: the port of the OCaml `sponge/sponge.ml` duplex
//! construction.
//!
//! The actual implementation lives in [crate::poseidon] (it was part of the
//! resurrected snarky code): [DuplexState] provides the alternating
//! absorb/squeeze API on top of the in-circuit Poseidon permutation, using
//! the kimchi parameters of the circuit's curve.

pub use crate::poseidon::{poseidon, CircuitAbsorb, DuplexState};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{api::SnarkyCircuit, loc, Boolean, FieldVar, RunState, SnarkyResult};
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        permutation::poseidon_block_cipher,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { crate::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { crate::FULL_ROUNDS }>;

    /// The out-of-circuit equivalent of the in-circuit poseidon gadget:
    /// initial state `[x, y, 0]`, one run of the permutation, keep the first
    /// two elements.
    fn poseidon_out_of_circuit(x: Fp, y: Fp) -> (Fp, Fp) {
        let params = Vesta::sponge_params();
        let mut state = vec![x, y, Fp::from(0u64)];
        poseidon_block_cipher::<Fp, PlonkSpongeConstantsKimchi, { crate::FULL_ROUNDS }>(
            params, &mut state,
        );
        (state[0], state[1])
    }

    struct TestCircuit {}

    impl SnarkyCircuit for TestCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { crate::FULL_ROUNDS }>;

        type PrivateInput = (Fp, Fp);
        type PublicInput = ();
        /// (poseidon(x, y).0, duplex squeeze after absorbing x and y)
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>);

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let x: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0)?;
            let y: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1)?;

            let (hash_left, _hash_right) = sys.poseidon(loc!(), (x.clone(), y.clone()));

            let mut duplex = DuplexState::new();
            duplex.absorb(sys, loc!(), &[x, y]);
            let squeezed = duplex.squeeze(sys, loc!());

            Ok((hash_left, squeezed))
        }
    }

    #[test]
    fn snarky_poseidon_matches_out_of_circuit() {
        let test_circuit = TestCircuit {};
        let (mut prover_index, verifier_index) = test_circuit.compile_to_indexes().unwrap();

        let mut rng = o1_utils::tests::make_test_rng(None);

        for _ in 0..2 {
            use ark_ff::UniformRand;
            let x = Fp::rand(&mut rng);
            let y = Fp::rand(&mut rng);

            let (expected_hash, _) = poseidon_out_of_circuit(x, y);
            // the duplex absorbs x and y into the rate part of a zero state
            // and squeezes the first element of the permuted state
            let (expected_squeezed, _) = poseidon_out_of_circuit(x, y);

            let (proof, public_output) = prover_index
                .prove::<BaseSponge, ScalarSponge>((), (x, y), true)
                .unwrap();

            assert_eq!(public_output.0, expected_hash);
            assert_eq!(public_output.1, expected_squeezed);
            verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
        }
    }

    /// The duplex construction is deterministic: absorbing the same inputs
    /// in two different ways (all at once vs one by one) squeezes the same
    /// output.
    struct DuplexCircuit {}

    impl SnarkyCircuit for DuplexCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { crate::FULL_ROUNDS }>;

        type PrivateInput = (Fp, Fp);
        type PublicInput = ();
        type PublicOutput = Boolean<Fp>;

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let x: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0)?;
            let y: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1)?;

            let mut duplex1 = DuplexState::new();
            duplex1.absorb(sys, loc!(), &[x.clone(), y.clone()]);
            let squeezed1 = duplex1.squeeze(sys, loc!());

            let mut duplex2 = DuplexState::new();
            duplex2.absorb(sys, loc!(), &[x]);
            duplex2.absorb(sys, loc!(), &[y]);
            let squeezed2 = duplex2.squeeze(sys, loc!());

            squeezed1.equal(sys, loc!(), &squeezed2)
        }
    }

    #[test]
    fn snarky_duplex_deterministic() {
        let test_circuit = DuplexCircuit {};
        let (mut prover_index, verifier_index) = test_circuit.compile_to_indexes().unwrap();

        let mut rng = o1_utils::tests::make_test_rng(None);

        use ark_ff::UniformRand;
        let x = Fp::rand(&mut rng);
        let y = Fp::rand(&mut rng);

        let (proof, public_output) = prover_index
            .prove::<BaseSponge, ScalarSponge>((), (x, y), true)
            .unwrap();

        assert!(*public_output);
        verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
    }
}

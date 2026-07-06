//! Challenge extraction from a sponge squeeze
//! (port of pickles' `lowest_128_bits` / `squeeze_challenge`).

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{FieldVar, RunState, SnarkyResult};

/// The bit length of a scalar challenge.
pub const CHALLENGE_BITS: usize = 128;

/// Returns the lowest 128 bits of `x` as a field element, constraining the
/// witnessed decomposition `x = lo + hi * 2^128` with `hi` (and optionally
/// `lo`) range-checked to 128 bits. Port of pickles' `lowest_128_bits`.
pub fn lowest_128_bits<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    x: &FieldVar<F>,
    constrain_low_bits: bool,
) -> SnarkyResult<FieldVar<F>> {
    use snarky::runner::WitnessGeneration;

    let two_128 = {
        let mut acc = F::one();
        for _ in 0..CHALLENGE_BITS {
            acc.double_in_place();
        }
        acc
    };

    let x_lo = x.clone();
    let lo: FieldVar<F> = sys.compute(loc.clone(), move |env: &dyn WitnessGeneration<F>| {
        let bits = env.read_var(&x_lo).into_bigint().to_bits_le();
        recompose(&bits[..CHALLENGE_BITS])
    })?;
    let x_hi = x.clone();
    let hi: FieldVar<F> = sys.compute(loc.clone(), move |env: &dyn WitnessGeneration<F>| {
        let bits = env.read_var(&x_hi).into_bigint().to_bits_le();
        recompose(&bits[CHALLENGE_BITS..])
    })?;

    // range-check hi (and optionally lo) to CHALLENGE_BITS bits: the unpack
    // gadget constrains the value to fit in that many boolean-constrained bits
    let _ = snarky::gadgets::bits::unpack(sys, loc.clone(), &hi, CHALLENGE_BITS)?;
    if constrain_low_bits {
        let _ = snarky::gadgets::bits::unpack(sys, loc.clone(), &lo, CHALLENGE_BITS)?;
    }

    // x = lo + hi * 2^128
    let recomposed = &lo + &hi.scale(two_128);
    recomposed.assert_equals(sys, loc, x)?;

    Ok(lo)
}

/// Squeezes a 128-bit challenge from a duplex sponge (step-8
/// `squeeze_challenge`): the lowest 128 bits of a sponge squeeze.
pub fn squeeze_challenge<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    sponge: &mut snarky::gadgets::sponge::DuplexState<F>,
) -> SnarkyResult<FieldVar<F>> {
    let squeezed = sponge.squeeze(sys, loc.clone());
    lowest_128_bits(sys, loc, &squeezed, true)
}

use ark_ff::BigInteger;
fn recompose<F: PrimeField>(bits: &[bool]) -> F {
    let mut acc = F::zero();
    for &b in bits.iter().rev() {
        acc.double_in_place();
        if b {
            acc += F::one();
        }
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::BigInteger;
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;
    use snarky::{api::SnarkyCircuit, loc};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    struct LowCircuit {}
    impl SnarkyCircuit for LowCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = Fp;
        type PublicInput = ();
        type PublicOutput = FieldVar<Fp>;
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<FieldVar<Fp>> {
            let x: FieldVar<Fp> = sys.compute(loc!(), |_| *private.unwrap())?;
            lowest_128_bits(sys, loc!(), &x, true)
        }
    }

    fn lowest_128_ref(x: Fp) -> Fp {
        let bits = x.into_bigint().to_bits_le();
        super::recompose(&bits[..128])
    }

    struct SqueezeCircuit {
        inputs: Vec<Fp>,
    }
    impl SnarkyCircuit for SqueezeCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = FieldVar<Fp>;
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<FieldVar<Fp>> {
            let mut sponge = snarky::gadgets::sponge::DuplexState::new();
            let mut vars = vec![];
            for &v in &self.inputs {
                vars.push(sys.compute(loc!(), move |_| v)?);
            }
            sponge.absorb(sys, loc!(), &vars);
            squeeze_challenge(sys, loc!(), &mut sponge)
        }
    }

    /// squeeze_challenge produces a 128-bit value and is deterministic.
    /// (NOTE: the exact parity of snarky's DuplexState absorption convention
    /// with mina_poseidon's ArithmeticSponge is a separate finalize_other_proof
    /// concern — the two use different rate/state management. Tracked in
    /// pickles/CLAUDE.md.)
    #[test]
    fn squeeze_challenge_is_128_bits_and_deterministic() {
        let inputs = vec![Fp::from(3u64), Fp::from(5u64), Fp::from(7u64)];
        let circuit = SqueezeCircuit {
            inputs: inputs.clone(),
        };
        let (mut pi, ver) = circuit.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        // the challenge fits in 128 bits
        let bits = out.into_bigint().to_bits_le();
        assert!(bits[128..].iter().all(|b| !b), "challenge exceeds 128 bits");
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);

        // determinism: a second run yields the same challenge
        let (mut pi2, _) = SqueezeCircuit { inputs }.compile_to_indexes().unwrap();
        let (_, out2) = pi2.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(*out, *out2);
    }

    #[test]
    fn lowest_128_bits_matches_reference() {
        let circuit = LowCircuit {};
        let (mut pi, ver) = circuit.compile_to_indexes().unwrap();
        let mut rng = o1_utils::tests::make_test_rng(None);
        for _ in 0..3 {
            use ark_ff::UniformRand;
            let x = Fp::rand(&mut rng);
            let expected = lowest_128_ref(x);
            let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), x, true).unwrap();
            assert_eq!(*out, expected);
            ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
        }
    }
}

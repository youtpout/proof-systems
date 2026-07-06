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

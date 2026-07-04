//! Scalar challenges and their endo-scalar interpretation
//! (port of pickles' `scalar_challenge.ml`).
//!
//! A scalar challenge is a 128-bit value `c` interpreted as a full scalar
//! through the curve endomorphism: `to_field(c) = 2 * (endo-fold of the bits
//! of c)`, matching kimchi's `ScalarChallenge::to_field`.

use ark_ff::{BigInteger, PrimeField};

use crate::common::SCALAR_CHALLENGE_BITS;

/// A 128-bit scalar challenge (out-of-circuit representation).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScalarChallenge<F>(pub F);

impl<F: PrimeField> ScalarChallenge<F> {
    /// Interprets the challenge as a full field element via the
    /// endomorphism, exactly as kimchi's `ScalarChallenge::to_field`
    /// (`endo_coefficient` is the scalar endo of the proof's curve).
    pub fn to_field(&self, endo_coefficient: F) -> F {
        // same algorithm as kimchi::oracles / OCaml `Scalar_challenge.to_field`
        let bits = to_bits(self.0);
        let mut a = F::from(2u64);
        let mut b = F::from(2u64);
        for i in (0..SCALAR_CHALLENGE_BITS / 2).rev() {
            let r_2i = bits[2 * i];
            let s = if r_2i { F::one() } else { -F::one() };
            if bits[2 * i + 1] {
                a = a.double() + s;
                b = b.double();
            } else {
                a = a.double();
                b = b.double() + s;
            }
        }
        a * endo_coefficient + b
    }
}

fn to_bits<F: PrimeField>(x: F) -> Vec<bool> {
    let mut bits = x.into_bigint().to_bits_le();
    bits.truncate(SCALAR_CHALLENGE_BITS);
    bits.resize(SCALAR_CHALLENGE_BITS, false);
    bits
}

#[cfg(test)]
mod tests {
    use super::*;
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Vesta};

    /// Our to_field matches kimchi's ScalarChallenge::to_field.
    #[test]
    fn matches_kimchi_scalar_challenge() {
        use ark_ff::UniformRand;
        let mut rng = o1_utils::tests::make_test_rng(None);
        let (_, endo_r) = Vesta::endos();
        for _ in 0..10 {
            // sample a 128-bit challenge
            let c = Fp::from(u128::rand(&mut rng));
            let ours = ScalarChallenge(c).to_field(*endo_r);
            let kimchi = mina_poseidon::sponge::ScalarChallenge::new(c).to_field(endo_r);
            assert_eq!(ours, kimchi);
        }
    }
}

//! In-circuit bulletproof / inner-product-argument verification pieces
//! (pickles' `check_bulletproof` and `Split_commitments.combine`), the second
//! half of `incrementally_verify_proof`.
//!
//! The commitments are combined with the polyscale challenge `xi` by Horner's
//! rule, scaling by `xi` through the endomorphism gadget
//! ([`crate::scalar_challenge::endo`]) exactly as pickles does — not by a full
//! scalar multiplication.

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{gadgets::curve::Point, FieldVar, RunState, SnarkyResult};

use crate::scalar_challenge::endo;

/// Combines commitments by the polyscale challenge `xi`
/// (`Split_commitments.combine`): returns `Σ_i xi_field^i · C_i`, computed by
/// Horner's rule where each `xi·acc` is the endomorphism scalar multiplication
/// `endo(acc, xi)`.
///
/// `xi` is the 128-bit polyscale challenge (as squeezed); `endo_base` is the
/// curve's base endomorphism coefficient (for the `EndoMul` gate).
pub fn combine_commitments<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    commitments: &[Point<F>],
    xi: &FieldVar<F>,
    endo_base: F,
) -> SnarkyResult<Point<F>> {
    use crate::common::SCALAR_CHALLENGE_BITS;
    use crate::plonk_curve_ops::add_fast;

    let n = commitments.len();
    assert!(n > 0, "combine_commitments: empty commitments");
    // Horner from the highest-index commitment down:
    // acc = C_{n-1}; for i = n-2..0 { acc = C_i + xi·acc }
    let mut acc = commitments[n - 1].clone();
    for c in commitments[..n - 1].iter().rev() {
        let scaled = endo(sys, loc.clone(), &acc, xi, SCALAR_CHALLENGE_BITS, endo_base)?;
        acc = add_fast(sys, loc.clone(), c, &scaled)?;
    }
    Ok(acc)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Fq, Pallas, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;
    use snarky::{api::SnarkyCircuit, loc};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    struct CombineCircuit {
        xi: u128,
        comms: Vec<(Fp, Fp)>,
    }
    impl SnarkyCircuit for CombineCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>);
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let xi: FieldVar<Fp> = sys.compute(loc!(), |_| Fp::from(self.xi))?;
            let mut comms = vec![];
            for &(x, y) in &self.comms {
                comms.push(Point::new(
                    sys.compute(loc!(), move |_| x)?,
                    sys.compute(loc!(), move |_| y)?,
                ));
            }
            let endo_base = crate::endo::tick::base();
            let acc = combine_commitments(sys, loc!(), &comms, &xi, endo_base)?;
            Ok((acc.x, acc.y))
        }
    }

    /// The in-circuit commitment combination equals the out-of-circuit
    /// `Σ xi_field^i · C_i` (Horner with the endo scalar).
    #[test]
    fn combine_commitments_matches_reference() {
        let mut rng = o1_utils::tests::make_test_rng(None);
        let (_, endo_scalar) = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();

        for n in [1usize, 2, 4] {
            let comms: Vec<Pallas> = (0..n)
                .map(|_| (Pallas::generator() * Fq::rand(&mut rng)).into_affine())
                .collect();
            let xi = u128::rand(&mut rng);
            let xi_field = crate::scalar_challenge::ScalarChallenge(Fq::from(xi)).to_field(*endo_scalar);

            // reference: acc = C_{n-1}; for i=n-2..0 { acc = C_i + xi_field*acc }
            let mut acc = comms[n - 1].into_group();
            for c in comms[..n - 1].iter().rev() {
                acc = *c + acc * xi_field;
            }
            let expected = acc.into_affine();

            let circ = CombineCircuit {
                xi,
                comms: comms.iter().map(|c| (c.x, c.y)).collect(),
            };
            let (mut pi, ver) = circ.compile_to_indexes().unwrap();
            let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
            assert_eq!(*out, (expected.x, expected.y), "n = {n}");
            ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
        }
    }
}

//! In-circuit public-input commitment (`x_hat`) — IVC steps 3–4 of pickles'
//! `incrementally_verify_proof` (`wrap_verifier.ml`, lines ~879–968).
//!
//! The verifier commits to the proof's public input using the SRS Lagrange
//! basis: `x_hat = -(Σ_i input_i · L_i) + H` (the negation and the blinding
//! by the generator `H` match kimchi's public commitment
//! `mask_custom(multi_scalar_mul(L, -input), 1)`).
//!
//! Each variable input of `n > 1` bits is scaled by
//! [`scale_fast2_prime`], which computes `(input + 2^k)·L` with
//! `k = scale_fast2_shift_bits(n)`; the extra `2^k·L` is cancelled by a
//! constant *correction* term `-(2^k)·L` folded into the initial accumulator
//! (pickles' `lagrange_with_correction`). Single-bit inputs are handled by a
//! conditional add instead.

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{gadgets::curve::Point, Boolean, FieldVar, RunState, SnarkyResult};

use crate::plonk_curve_ops::{add_fast, scale_fast2_prime};

/// One public-input element, as consumed by [`public_input_commitment`].
/// The `lagrange` (and `correction`) points are circuit constants taken from
/// the SRS ([`lagrange_correction`] computes the correction out-of-circuit).
pub enum Term<F: PrimeField> {
    /// A packed variable of `num_bits > 1` bits (`Add_with_correction`):
    /// contributes `value · lagrange` after the correction cancels the shift.
    Packed {
        value: FieldVar<F>,
        num_bits: usize,
        lagrange: Point<F>,
        /// `-(2^scale_fast2_shift_bits(num_bits)) · lagrange`, as a constant.
        correction: Point<F>,
    },
    /// A single-bit variable (`Cond_add`): contributes `bit · lagrange`.
    Cond {
        bit: Boolean<F>,
        lagrange: Point<F>,
    },
}

/// Computes the correction point `-(2^scale_fast2_shift_bits(num_bits)) · L`
/// for a `num_bits`-bit input whose Lagrange commitment is `lagrange`
/// (out-of-circuit; the result is embedded as a circuit constant).
pub fn lagrange_correction<C>(
    lagrange: &ark_ec::short_weierstrass::Affine<C>,
    num_bits: usize,
) -> ark_ec::short_weierstrass::Affine<C>
where
    C: ark_ec::short_weierstrass::SWCurveConfig,
{
    use ark_ec::CurveGroup;
    use ark_ff::Field;

    let shift = crate::plonk_curve_ops::scale_fast2_shift_bits(num_bits);
    let two_to_shift = C::ScalarField::from(2u64).pow([shift as u64]);
    (-(*lagrange * two_to_shift)).into_affine()
}

/// The in-circuit public-input commitment:
/// `x_hat = -(Σ_i input_i · L_i) + H`.
///
/// Follows the OCaml fold order: the constant corrections are summed first
/// (the initial accumulator), then every term is folded in input order —
/// `Cond` as a conditional add, `Packed` as `acc + scale_fast2_prime(L, x)` —
/// and the result is negated and blinded by `h` (the SRS blinding generator).
///
/// At least one `Packed` term is required (pickles' statements always have
/// field-sized elements, and the OCaml `List.reduce_exn` of the corrections
/// makes the same assumption).
pub fn public_input_commitment<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    terms: &[Term<F>],
    h: &Point<F>,
) -> SnarkyResult<Point<F>> {
    // init = Σ corrections of the Packed terms
    let mut acc: Option<Point<F>> = None;
    for t in terms {
        if let Term::Packed { correction, .. } = t {
            acc = Some(match acc {
                None => correction.clone(),
                Some(a) => add_fast(sys, loc.clone(), &a, correction)?,
            });
        }
    }
    let mut acc = acc.expect("public_input_commitment: at least one Packed term required");

    // fold the terms in input order
    for t in terms {
        match t {
            Term::Cond { bit, lagrange } => {
                let added = add_fast(sys, loc.clone(), lagrange, &acc)?;
                acc = Point::select(sys, loc.clone(), bit, &added, &acc)?;
            }
            Term::Packed {
                value,
                num_bits,
                lagrange,
                ..
            } => {
                let scaled = scale_fast2_prime(sys, loc.clone(), lagrange, value, *num_bits)?;
                acc = add_fast(sys, loc.clone(), &acc, &scaled)?;
            }
        }
    }

    // x_hat = -(acc) + H (blinding)
    add_fast(sys, loc, &acc.negate(), h)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;
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

    /// A statement-shaped input mix: two 128-bit packed values (challenges),
    /// one full-width 255-bit packed value (a field element / digest), and two
    /// single-bit values (booleans), each with its own Lagrange "commitment".
    struct XHatCircuit {
        values_128: [u128; 2],
        value_255: Fq,
        bits: [bool; 2],
        lagranges: Vec<(Fp, Fp)>,
        corrections: Vec<(Fp, Fp)>,
        h: (Fp, Fp),
    }

    impl SnarkyCircuit for XHatCircuit {
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
            let cpt = |p: (Fp, Fp)| Point::new(FieldVar::constant(p.0), FieldVar::constant(p.1));

            // embed the 255-bit Fq value into Fp (integer-preserving)
            let v255 = crate::shifted_value::embed_repr::<Fq, Fp>(self.value_255);

            let mut terms = vec![];
            for (i, &v) in self.values_128.iter().enumerate() {
                let value: FieldVar<Fp> = sys.compute(loc!(), move |_| Fp::from(v))?;
                terms.push(Term::Packed {
                    value,
                    num_bits: 128,
                    lagrange: cpt(self.lagranges[i]),
                    correction: cpt(self.corrections[i]),
                });
            }
            let value: FieldVar<Fp> = sys.compute(loc!(), move |_| v255)?;
            terms.push(Term::Packed {
                value,
                num_bits: 255,
                lagrange: cpt(self.lagranges[2]),
                correction: cpt(self.corrections[2]),
            });
            for (i, &b) in self.bits.iter().enumerate() {
                let bit: Boolean<Fp> = sys.compute(loc!(), move |_| b)?;
                terms.push(Term::Cond {
                    bit,
                    lagrange: cpt(self.lagranges[3 + i]),
                });
            }

            let h = cpt(self.h);
            let x_hat = public_input_commitment(sys, loc!(), &terms, &h)?;
            Ok((x_hat.x, x_hat.y))
        }
    }

    /// `public_input_commitment` == `-(Σ input_i · L_i) + H` computed
    /// out-of-circuit, on a statement-shaped mix of 128-bit, 255-bit and
    /// boolean inputs.
    #[test]
    fn x_hat_matches_reference() {
        let mut rng = o1_utils::tests::make_test_rng(None);
        let rand_pt = |rng: &mut _| (Pallas::generator() * Fq::rand(rng)).into_affine();

        let lagranges: Vec<Pallas> = (0..5).map(|_| rand_pt(&mut rng)).collect();
        let values_128 = [u128::rand(&mut rng), u128::rand(&mut rng)];
        let value_255 = Fq::rand(&mut rng);
        let bits = [true, false];
        let h = rand_pt(&mut rng);

        // corrections for the three Packed terms
        let corrections: Vec<Pallas> = vec![
            lagrange_correction(&lagranges[0], 128),
            lagrange_correction(&lagranges[1], 128),
            lagrange_correction(&lagranges[2], 255),
        ];

        // reference: x_hat = -(Σ input_i · L_i) + H
        let mut sum = lagranges[0] * Fq::from(values_128[0])
            + lagranges[1] * Fq::from(values_128[1])
            + lagranges[2] * value_255;
        for (i, &b) in bits.iter().enumerate() {
            if b {
                sum += lagranges[3 + i].into_group();
            }
        }
        let expected = (-sum + h).into_affine();

        let circ = XHatCircuit {
            values_128,
            value_255,
            bits,
            lagranges: lagranges.iter().map(|p| (p.x, p.y)).collect(),
            corrections: corrections.iter().map(|p| (p.x, p.y)).collect(),
            h: (h.x, h.y),
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(*out, (expected.x, expected.y));
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }
}

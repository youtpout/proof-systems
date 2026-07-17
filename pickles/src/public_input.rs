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
use snarky::{gadgets::curve::Point, Boolean, FieldVar, RunState, SnarkyResult, SnarkyType};

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
    Cond { bit: Boolean<F>, lagrange: Point<F> },
}

/// One element of a Pickles statement before commitment packing: either a
/// packed value, a full-field element that must be split into `(x / 2, odd)`,
/// or a single boolean.
pub enum StatementElement<F: PrimeField> {
    Packed { value: FieldVar<F>, num_bits: usize },
    Split(FieldVar<F>),
    Bool(Boolean<F>),
}

/// Builds x_hat [`Term`]s from Pickles statement elements. Full-field elements
/// expand per OCaml `Spec.pack`/`wrap_main.split_field`: `Split(x)` becomes
/// `[Packed(x_div_2, 255), Cond(x_odd)]`.
/// Where the x_hat Lagrange constants come from, per statement slot.
pub enum StatementLagranges<'a, F: PrimeField> {
    /// Pre-built (constant or already-selected) `(L_i, correction_i)` points.
    Prepared(&'a [(Point<F>, Point<F>)]),
    /// Heterogeneous branch step-domains: per-branch constant sets combined
    /// through the `which_branch` one-hot ON DEMAND, slot by slot — OCaml's
    /// wrap-side `lagrange`/`lagrange_with_correction` (wrap_verifier.ml:334,
    /// :382) build each slot's masked sum inside the x_hat term loop, so the
    /// materialization rows land there, not at the circuit head.
    OneHot {
        sets: &'a [Vec<((F, F), (F, F))>],
        branches: &'a [Boolean<F>],
    },
}

pub fn statement_terms<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    elements: &[StatementElement<F>],
    lagranges: &StatementLagranges<'_, F>,
) -> SnarkyResult<Vec<Term<F>>> {
    let mut terms = Vec::new();
    let mut slot = 0usize;
    let slot_count = match lagranges {
        StatementLagranges::Prepared(l) => l.len(),
        StatementLagranges::OneHot { sets, .. } => sets[0].len(),
    };
    // `want_correction`: OCaml only builds a correction for
    // `Add_with_correction` terms (`x, n`); a `Cond_add` term (`b, 1`) takes
    // ONLY the lagrange (wrap_verifier.ml:911-922). Selecting + sealing a
    // correction for every boolean slot costs rows jsoo does not have.
    let next = |sys: &mut RunState<F>,
                slot: &mut usize,
                want_correction: bool|
     -> SnarkyResult<(Point<F>, Option<Point<F>>)> {
        let index = *slot;
        *slot += 1;
        Ok(match lagranges {
            StatementLagranges::Prepared(l) => {
                let (lag, corr) = l[index].clone();
                (lag, want_correction.then_some(corr))
            }
            StatementLagranges::OneHot { sets, branches } => {
                let mut select =
                    |pick: &dyn Fn(&((F, F), (F, F))) -> (F, F),
                     sys: &mut RunState<F>|
                     -> SnarkyResult<Point<F>> {
                        let mut x = FieldVar::zero();
                        let mut y = FieldVar::zero();
                        for (branch, set) in branches.iter().zip(*sets) {
                            let (px, py) = pick(&set[index]);
                            x = x + branch.to_field_var().scale(px);
                            y = y + branch.to_field_var().scale(py);
                        }
                        // OCaml `lagrange` (wrap_verifier.ml:334) ends with a
                        // plain `Vector.reduce_exn ~f:Field.(+)` and does NOT
                        // seal. We seal anyway: our consumers re-reduce the
                        // lincom at EVERY use, so leaving it lazy costs ~58
                        // MORE rows (measured: net +26 -> +84). Matching
                        // OCaml here requires matching its consumption
                        // pattern too — until then the seal is the closer
                        // approximation.
                        Ok(Point::new(x.seal(sys, loc.clone())?, y.seal(sys, loc.clone())?))
                    };
                let l = select(&|e| e.0, sys)?;
                let c = if want_correction {
                    Some(select(&|e| e.1, sys)?)
                } else {
                    None
                };
                (l, c)
            }
        })
    };
    for e in elements {
        match e {
            StatementElement::Packed { value, num_bits } => {
                let (lagrange, correction) = next(sys, &mut slot, true)?;
                terms.push(Term::Packed {
                    value: value.clone(),
                    num_bits: *num_bits,
                    lagrange,
                    correction: correction.expect("packed term needs a correction"),
                });
            }
            StatementElement::Split(x) => {
                let (y, odd) = split_field(sys, loc.clone(), x)?;
                let (lagrange, correction) = next(sys, &mut slot, true)?;
                terms.push(Term::Packed {
                    value: y,
                    num_bits: 255,
                    lagrange,
                    correction: correction.expect("packed term needs a correction"),
                });
                let (lagrange, _) = next(sys, &mut slot, false)?;
                terms.push(Term::Cond { bit: odd, lagrange });
            }
            StatementElement::Bool(b) => {
                b.check(sys, loc.clone())?;
                let (lagrange, _) = next(sys, &mut slot, false)?;
                terms.push(Term::Cond {
                    bit: b.clone(),
                    lagrange,
                });
            }
        }
    }
    assert_eq!(slot, slot_count, "statement_terms: slot count");
    Ok(terms)
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

/// One input of [`multiscale_known`]: a (possibly constant) statement value,
/// its packed bit width, and the CONSTANT Lagrange commitment it scales.
pub struct KnownTerm<F: PrimeField> {
    pub value: FieldVar<F>,
    pub num_bits: usize,
    /// The slot's Lagrange commitment, as raw affine coordinates.
    pub lagrange: (F, F),
}

/// OCaml `Step_verifier.multiscale_known` (step_verifier.ml:115) — the
/// step-side public-input commitment over a KNOWN wrap domain:
///
/// 1. Constant values contribute `c · L_i` entirely OUT of circuit.
/// 2. Every variable value is scaled first (`Ops.scale_fast2'`, all scales
///    emitted back to back), collecting the `2^shift · L_i` correction
///    constants out of circuit.
/// 3. The scaled points are reduced left-to-right with `add_fast`.
/// 4. One final `add_fast` folds in the single constant point
///    `Σ constant_part − Σ corrections`.
///
/// Returns the UN-negated, UN-blinded sum: the caller negates and adds `H`
/// exactly as `incrementally_verify_proof` does (step_verifier.ml:554-577).
pub fn multiscale_known<F, C>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    terms: &[KnownTerm<F>],
) -> SnarkyResult<Point<F>>
where
    F: PrimeField,
    C: ark_ec::short_weierstrass::SWCurveConfig<BaseField = F>,
{
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{BigInteger, Field as _};

    type Affine<C> = ark_ec::short_weierstrass::Affine<C>;

    // out-of-circuit accumulator: Σ constant-valued terms − Σ corrections
    let mut constant_acc: Option<ark_ec::short_weierstrass::Projective<C>> = None;
    let mut add_constant = |p: ark_ec::short_weierstrass::Projective<C>| {
        constant_acc = Some(match constant_acc.take() {
            None => p,
            Some(acc) => acc + p,
        });
    };

    // pass 1: emit every scale, in statement order (OCaml `List.map` over
    // `non_constant_part` completes before the reduce)
    let mut scaled: Vec<Point<F>> = Vec::new();
    for term in terms {
        let g = Affine::<C>::new_unchecked(term.lagrange.0, term.lagrange.1);
        match &term.value {
            FieldVar::Constant(c) => {
                if c.is_zero() {
                    continue;
                }
                // `c · L_i`, out of circuit (`scaled_lagrange` for c ∉ {0,1})
                if c.is_one() {
                    add_constant(g.into_group());
                } else {
                    let scalar = C::ScalarField::from_bigint(
                        <<C::ScalarField as PrimeField>::BigInt as ark_ff::BigInteger>::from_bits_le(
                            &c.into_bigint().to_bits_le(),
                        ),
                    )
                    .expect("field element fits the scalar field");
                    add_constant(g * scalar);
                }
            }
            value => {
                let lagrange_pt = Point::new(
                    FieldVar::constant(term.lagrange.0),
                    FieldVar::constant(term.lagrange.1),
                );
                scaled.push(crate::plonk_curve_ops::scale_fast2_prime(
                    sys,
                    loc.clone(),
                    &lagrange_pt,
                    value,
                    term.num_bits,
                )?);
                // correction −2^shift · L_i, out of circuit
                let shift = crate::plonk_curve_ops::scale_fast2_shift_bits(term.num_bits);
                let two_to_shift = C::ScalarField::from(2u64).pow([shift as u64]);
                add_constant(-(g * two_to_shift));
            }
        }
    }

    // pass 2: reduce the scaled points left-to-right
    let mut scaled = scaled.into_iter();
    let mut acc = scaled
        .next()
        .expect("multiscale_known: at least one variable term");
    for rr in scaled {
        acc = add_fast(
            sys,
            Cow::Owned(format!("{loc} | multiscale_known reduce")),
            &acc,
            &rr,
        )?;
    }

    // final constant fold
    let constant_point = constant_acc
        .expect("multiscale_known: at least one correction")
        .into_affine();
    add_fast(
        sys,
        Cow::Owned(format!("{loc} | multiscale_known constant add")),
        &acc,
        &Point::new(
            FieldVar::constant(constant_point.x),
            FieldVar::constant(constant_point.y),
        ),
    )
}

/// Splitting a field variable into `(x_div_2, x_odd)` — used on the wrap side
/// where a step statement element lives in the *bigger* Tick field: the halved
/// value fits the Tock circuit's Lagrange scaling, and the odd bit becomes a
/// separate 1-bit (conditional) public-input term.
pub use crate::plonk_curve_ops::split_field;

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
                Some(a) => add_fast(
                    sys,
                    Cow::Owned(format!("{loc} | public_input correction add")),
                    &a,
                    correction,
                )?,
            });
        }
    }
    let mut acc = acc.expect("public_input_commitment: at least one Packed term required");

    // fold the terms in input order
    for t in terms {
        match t {
            Term::Cond { bit, lagrange } => {
                let added = add_fast(
                    sys,
                    Cow::Owned(format!("{loc} | public_input conditional add")),
                    lagrange,
                    &acc,
                )?;
                acc = Point::select(sys, loc.clone(), bit, &added, &acc)?;
            }
            Term::Packed {
                value,
                num_bits,
                lagrange,
                ..
            } => {
                let scaled = scale_fast2_prime(sys, loc.clone(), lagrange, value, *num_bits)?;
                acc = add_fast(
                    sys,
                    Cow::Owned(format!("{loc} | public_input packed add")),
                    &acc,
                    &scaled,
                )?;
            }
        }
    }

    // x_hat = -(acc) + H (blinding). OCaml's `add_fast` seals the negated
    // y-coordinate before allocating the CompleteAdd witness.
    let neg_acc = acc.negate();
    let neg_acc = Point::new(neg_acc.x, neg_acc.y.seal(sys, loc.clone())?);
    add_fast(
        sys,
        Cow::Owned(format!("{loc} | public_input blinding add")),
        &neg_acc,
        h,
    )
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

    struct SplitCircuit {
        x: Fp,
    }

    impl SnarkyCircuit for SplitCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = (FieldVar<Fp>, Boolean<Fp>);

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let x: FieldVar<Fp> = sys.compute(loc!(), |_| self.x)?;
            split_field(sys, loc!(), &x)
        }
    }

    /// `split_field(x)` == the integer halving `(x - odd) / 2` with the low
    /// bit, on odd and even inputs.
    #[test]
    fn split_field_matches_reference() {
        use ark_ff::{BigInteger, PrimeField as _};
        let mut rng = o1_utils::tests::make_test_rng(None);
        for _ in 0..2 {
            let x = Fp::rand(&mut rng);
            let bits = x.into_bigint().to_bits_le();
            let odd = bits[0];
            let y_ref = {
                let mut half = Fp::from(0u64);
                for &b in bits[1..].iter().rev() {
                    half = half + half;
                    if b {
                        half += Fp::from(1u64);
                    }
                }
                half
            };

            let circ = SplitCircuit { x };
            let (mut pi, ver) = circ.compile_to_indexes().unwrap();
            let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
            let (y, b) = *out.clone();
            assert_eq!(y, y_ref, "halved value");
            assert_eq!(b, odd, "odd bit");
            ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
        }
    }
}

//! Elliptic curve gadgets, the port of the OCaml `snarky_curve` library.
//!
//! Points are represented in affine coordinates over the circuit's field —
//! e.g. Pallas points inside a Vesta-proved circuit (whose scalar field is
//! Pallas' base field). The addition uses kimchi's native `CompleteAdd` gate.
//!
//! Limitation (also documented in `snarky/CLAUDE.md`): the affine
//! representation cannot encode the point at infinity, so [scale] returns
//! garbage coordinates when the scalar maps the point to the identity. The
//! `CompleteAdd` gate itself handles those cases soundly via its `inf` flag.

use std::borrow::Cow;

use ark_ff::PrimeField;

use crate::{
    constraint_system::{EcAddCompleteInput, KimchiConstraint},
    runner::Constraint,
    Boolean, FieldVar, RunState, SnarkyResult,
};

/// An affine, non-infinity point with coordinates in the circuit field.
#[derive(Debug, Clone)]
pub struct Point<F: PrimeField> {
    pub x: FieldVar<F>,
    pub y: FieldVar<F>,
}

impl<F: PrimeField> Point<F> {
    pub fn new(x: FieldVar<F>, y: FieldVar<F>) -> Self {
        Self { x, y }
    }

    /// A constant point from out-of-circuit affine coordinates.
    pub fn constant((x, y): (F, F)) -> Self {
        Self {
            x: FieldVar::constant(x),
            y: FieldVar::constant(y),
        }
    }

    /// Witnesses a point from a prover-supplied value, and constrains it to
    /// be on the curve `y² = x³ + a·x + b`.
    pub fn compute_checked(
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        a: F,
        b: F,
        value: impl FnOnce() -> (F, F) + 'static,
    ) -> SnarkyResult<Self> {
        let (x, y): (FieldVar<F>, FieldVar<F>) = sys.compute(loc.clone(), |_| value())?;
        let point = Self::new(x, y);
        point.assert_on_curve(sys, loc, a, b)?;
        Ok(point)
    }

    /// Constrains `y² = x³ + a·x + b`.
    pub fn assert_on_curve(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        a: F,
        b: F,
    ) -> SnarkyResult<()> {
        // Mirrors OCaml snarky_curve's `assert_on_curve` gate for gate:
        // x² via a Square constraint (Field.square, not a mul's R1CS),
        // x³ = x²·x via R1CS, then y² = x³ + a·x + b via a Square constraint.
        let x2: FieldVar<F> = sys.compute(loc.clone(), {
            let x = self.x.clone();
            move |env| {
                let v: F = env.read_var(&x);
                v * v
            }
        })?;
        sys.add_constraint(
            Constraint::BasicSnarkyConstraint(
                crate::constraint_system::BasicSnarkyConstraint::Square(
                    self.x.clone(),
                    x2.clone(),
                ),
            ),
            Some("on-curve x^2".into()),
            loc.clone(),
        )?;
        let x3 = x2.mul(&self.x, None, loc.clone(), sys)?;
        let rhs = &(&x3 + &self.x.scale(a)) + &FieldVar::constant(b);
        sys.add_constraint(
            Constraint::BasicSnarkyConstraint(
                crate::constraint_system::BasicSnarkyConstraint::Square(self.y.clone(), rhs),
            ),
            Some("on-curve check".into()),
            loc,
        )
    }

    /// `if b { then_ } else { else_ }`, coordinate-wise.
    pub fn select(
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        b: &Boolean<F>,
        then_: &Self,
        else_: &Self,
    ) -> SnarkyResult<Self> {
        let y = sys.if_(loc.clone(), b.clone(), then_.y.clone(), else_.y.clone())?;
        let x = sys.if_(loc, b.clone(), then_.x.clone(), else_.x.clone())?;
        Ok(Self { x, y })
    }

    /// `-self`.
    pub fn negate(&self) -> Self {
        Self {
            x: self.x.clone(),
            y: -&self.y,
        }
    }
}

/// The witness values of the `CompleteAdd` gate for `(x1, y1) + (x2, y2)`:
/// `[x3, y3, inf, same_x, slope, inf_z, x21_inv]`.
fn complete_add_witness<F: PrimeField>(x1: F, y1: F, x2: F, y2: F) -> [F; 7] {
    let same_x = x1 == x2;
    let x21 = x2 - x1;
    let x21_inv = if same_x {
        F::zero()
    } else {
        x21.inverse().unwrap()
    };
    let slope = if same_x {
        // doubling: (3 x1²) / (2 y1)
        let three_x1_squared = x1 * x1 * F::from(3u64);
        three_x1_squared * (y1 + y1).inverse().unwrap_or_else(F::zero)
    } else {
        (y2 - y1) * x21_inv
    };
    let inf = if same_x && y1 != y2 {
        F::one()
    } else {
        F::zero()
    };
    let inf_z = if y1 == y2 {
        F::zero()
    } else if same_x {
        (y1 - y2).inverse().unwrap()
    } else {
        F::zero()
    };
    let x3 = slope * slope - x1 - x2;
    let y3 = slope * (x1 - x3) - y1;
    [x3, y3, inf, same_x.into(), slope, inf_z, x21_inv]
}

/// Complete addition `p1 + p2` using kimchi's `CompleteAdd` gate.
/// Doubling (`p1 = p2`) is handled by the gate; if the result is the point
/// at infinity (`p1 = -p2`) the gate's `inf` flag is set and the returned
/// coordinates are meaningless.
pub fn add_complete<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    p1: &Point<F>,
    p2: &Point<F>,
) -> SnarkyResult<Point<F>> {
    // Witness the gate's auxiliary values one by one, in OCaml add_fast's
    // exists order (same_x, inf_z, x21_inv, s, x3, y3), with `inf` the
    // constant zero (`check_finite = true`): points at infinity cannot occur
    // in the pickles gadgets, and the constant wires the cell into the
    // cached-zero permutation class exactly like OCaml.
    let aux = |sys: &mut RunState<F>, loc: Cow<'static, str>, k: usize| -> SnarkyResult<FieldVar<F>> {
        let (x1, y1) = (p1.x.clone(), p1.y.clone());
        let (x2, y2) = (p2.x.clone(), p2.y.clone());
        sys.compute(loc, move |env| {
            complete_add_witness(
                env.read_var(&x1),
                env.read_var(&y1),
                env.read_var(&x2),
                env.read_var(&y2),
            )[k]
        })
    };
    // complete_add_witness order: [x3, y3, inf, same_x, slope, inf_z, x21_inv]
    let same_x = aux(sys, loc.clone(), 3)?;
    let inf = FieldVar::zero();
    let inf_z = aux(sys, loc.clone(), 5)?;
    let x21_inv = aux(sys, loc.clone(), 6)?;
    let slope = aux(sys, loc.clone(), 4)?;
    let x3 = aux(sys, loc.clone(), 0)?;
    let y3 = aux(sys, loc.clone(), 1)?;

    let constraint =
        Constraint::KimchiConstraint(KimchiConstraint::EcAddComplete(EcAddCompleteInput {
            p1: (p1.x.clone(), p1.y.clone()),
            p2: (p2.x.clone(), p2.y.clone()),
            p3: (x3.clone(), y3.clone()),
            inf,
            same_x,
            slope,
            inf_z,
            x21_inv,
        }));
    sys.add_constraint(constraint, Some("EC complete add".into()), loc)?;

    Ok(Point::new(x3, y3))
}

/// Doubling, as a complete addition of the point with itself.
pub fn double<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    p: &Point<F>,
) -> SnarkyResult<Point<F>> {
    add_complete(sys, loc, p, p)
}

/// Scalar multiplication by double-and-add over the little-endian `bits`,
/// with a constant `shift` point to avoid representing the identity in
/// affine coordinates: computes `shift + sum_i bits[i] * 2^i * p`, then
/// subtracts `shift`.
///
/// First-pass implementation: kimchi's `VarBaseMul`/endomorphism gates would
/// be much cheaper (tracked in the backlog).
pub fn scale<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    p: &Point<F>,
    bits: &[Boolean<F>],
    shift: (F, F),
) -> SnarkyResult<Point<F>> {
    let mut acc = Point::constant(shift);
    let mut pow = p.clone();
    for (i, bit) in bits.iter().enumerate() {
        let sum = add_complete(sys, loc.clone(), &acc, &pow)?;
        acc = Point::select(sys, loc.clone(), bit, &sum, &acc)?;
        if i + 1 < bits.len() {
            pow = double(sys, loc.clone(), &pow)?;
        }
    }
    let neg_shift = Point::constant(shift).negate();
    add_complete(sys, loc, &acc, &neg_shift)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{api::SnarkyCircuit, loc};
    use ark_ec::{AffineRepr, CurveGroup};
    use mina_curves::pasta::{Fp, Fq, Pallas, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { crate::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { crate::FULL_ROUNDS }>;

    fn pallas_coords(p: Pallas) -> (Fp, Fp) {
        (p.x, p.y)
    }

    /// Number of bits of the test scalar.
    const SCALAR_BITS: usize = 8;

    struct TestCircuit {
        shift: (Fp, Fp),
    }

    impl SnarkyCircuit for TestCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { crate::FULL_ROUNDS }>;

        /// Two Pallas points and a small scalar: ((x1, y1, x2), (y2, k))
        type PrivateInput = ((Fp, Fp, Fp), (Fp, Fp));
        type PublicInput = ();
        /// (p1 + p2, 2 * p1, k * p1) as ((x, y, x), (y, x), y)
        type PublicOutput = (
            (FieldVar<Fp>, FieldVar<Fp>, FieldVar<Fp>),
            (FieldVar<Fp>, FieldVar<Fp>),
            FieldVar<Fp>,
        );

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let x1: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0 .0)?;
            let y1: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0 .1)?;
            let x2: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0 .2)?;
            let y2: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1 .0)?;
            let k: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1 .1)?;

            let p1 = Point::new(x1, y1);
            let p2 = Point::new(x2, y2);

            // Pallas: y² = x³ + 5
            p1.assert_on_curve(sys, loc!(), Fp::from(0u64), Fp::from(5u64))?;

            let sum = add_complete(sys, loc!(), &p1, &p2)?;
            let doubled = double(sys, loc!(), &p1)?;

            let bits = crate::gadgets::bits::unpack(sys, loc!(), &k, SCALAR_BITS)?;
            let scaled = scale(sys, loc!(), &p1, &bits, self.shift)?;

            Ok(((sum.x, sum.y, doubled.x), (doubled.y, scaled.x), scaled.y))
        }
    }

    #[test]
    fn snarky_curve_ops() {
        let generator = Pallas::generator();
        let shift = pallas_coords((generator * Fq::from(0x1234u64)).into_affine());

        let test_circuit = TestCircuit { shift };
        let (mut prover_index, verifier_index) = test_circuit.compile_to_indexes().unwrap();

        let k = 141u64; // fits in SCALAR_BITS bits
        let p1 = (generator * Fq::from(7u64)).into_affine();
        let p2 = (generator * Fq::from(11u64)).into_affine();

        let expected_sum = pallas_coords((p1 + p2).into_affine());
        let expected_double = pallas_coords((p1 + p1).into_affine());
        let expected_scaled = pallas_coords((p1 * Fq::from(k)).into_affine());

        let (p1x, p1y) = pallas_coords(p1);
        let (p2x, p2y) = pallas_coords(p2);
        let private_input = ((p1x, p1y, p2x), (p2y, Fp::from(k)));

        let (proof, public_output) = prover_index
            .prove::<BaseSponge, ScalarSponge>((), private_input, true)
            .unwrap();

        let ((sum_x, sum_y, double_x), (double_y, scaled_x), scaled_y) = *public_output;
        assert_eq!((sum_x, sum_y), expected_sum);
        assert_eq!((double_x, double_y), expected_double);
        assert_eq!((scaled_x, scaled_y), expected_scaled);

        verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
    }
}

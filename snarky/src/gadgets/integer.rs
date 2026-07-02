//! Integers with interval-tracked bounds.
//!
//! Port of the OCaml `snarky_integer/integer.ml`: an [Integer] is a field
//! variable together with an [Interval] tracking either its exact (constant)
//! value or a strict upper bound, plus a cached bit decomposition.

use std::borrow::Cow;

use ark_ff::PrimeField;
use num_bigint::BigUint;

use super::bits::{assert_lt, bits_needed, compare, field_to_biguint, pack, unpack};
use crate::{Boolean, FieldVar, RunState, SnarkyResult};

/// Returns the field size as a [BigUint].
fn field_size<F: PrimeField>() -> BigUint {
    F::MODULUS.into()
}

fn one() -> BigUint {
    BigUint::from(1u32)
}

/// Bounds on an [Integer]: either an exact constant, or a strict upper bound.
#[derive(Debug, Clone)]
pub enum Interval {
    Constant(BigUint),
    LessThan(BigUint),
}

impl Interval {
    fn check<F: PrimeField>(self) -> Self {
        let bound = match &self {
            Interval::Constant(x) => x,
            Interval::LessThan(x) => x,
        };
        assert!(
            *bound < field_size::<F>(),
            "Integer interval exceeds the field size"
        );
        self
    }

    fn scale<F: PrimeField>(&self, x: &BigUint) -> Self {
        match self {
            Interval::Constant(t) => Interval::Constant(t * x),
            Interval::LessThan(t) => Interval::LessThan(t * x),
        }
        .check::<F>()
    }

    fn succ<F: PrimeField>(&self) -> Self {
        match self {
            Interval::Constant(x) => Interval::Constant(x + one()),
            Interval::LessThan(x) => Interval::LessThan(x + one()),
        }
        .check::<F>()
    }

    fn add<F: PrimeField>(&self, other: &Self) -> Self {
        use Interval::{Constant, LessThan};
        match (self, other) {
            (Constant(a), Constant(b)) => Constant(a + b),
            (LessThan(a), LessThan(b)) => LessThan(a + b),
            (Constant(c), LessThan(bound)) | (LessThan(bound), Constant(c)) => {
                LessThan(c + one() + bound)
            }
        }
        .check::<F>()
    }

    fn mul<F: PrimeField>(&self, other: &Self) -> Self {
        use Interval::{Constant, LessThan};
        match (self, other) {
            (Constant(a), Constant(b)) => Constant(a * b),
            (LessThan(a), LessThan(b)) => LessThan(a * b),
            (Constant(c), LessThan(bound)) | (LessThan(bound), Constant(c)) => {
                LessThan((c + one()) * bound)
            }
        }
        .check::<F>()
    }

    /// The number of bits needed to represent any value within the interval.
    pub fn bits_needed(&self) -> usize {
        match self {
            Interval::Constant(x) => bits_needed(&(x + one())),
            Interval::LessThan(x) => bits_needed(x),
        }
    }

    fn min(&self, other: &Self) -> Self {
        use Interval::{Constant, LessThan};
        match (self, other) {
            (Constant(a), Constant(b)) => Constant(std::cmp::min(a, b).clone()),
            (LessThan(a), LessThan(b)) => LessThan(std::cmp::min(a, b).clone()),
            (Constant(c), LessThan(bound)) | (LessThan(bound), Constant(c)) => {
                LessThan(std::cmp::min(&(c + one()), bound).clone())
            }
        }
    }

    /// Least upper bound.
    fn lub(&self, other: &Self) -> Self {
        use Interval::{Constant, LessThan};
        match (self, other) {
            (Constant(a), Constant(b)) => {
                if a == b {
                    Constant(a.clone())
                } else {
                    LessThan(std::cmp::max(a, b) + one())
                }
            }
            (LessThan(a), LessThan(b)) => LessThan(std::cmp::max(a, b).clone()),
            (Constant(c), LessThan(bound)) | (LessThan(bound), Constant(c)) => {
                LessThan(std::cmp::max(&(c + one()), bound).clone())
            }
        }
    }

    fn quotient(&self, other: &Self) -> Self {
        use Interval::{Constant, LessThan};
        match (self, other) {
            (Constant(a), Constant(b)) => Constant(a / b),
            (LessThan(a), Constant(b)) => LessThan((a / b) + one()),
            (Constant(a), LessThan(_)) => LessThan(a + one()),
            (LessThan(a), LessThan(_)) => LessThan(a.clone()),
        }
    }

    fn gte(&self, other: &Self) -> bool {
        use Interval::{Constant, LessThan};
        match (self, other) {
            (Constant(a), Constant(b)) | (LessThan(a), LessThan(b)) => a >= b,
            (LessThan(a), Constant(b)) => *a >= b + one(),
            (Constant(a), LessThan(b)) => a + one() >= *b,
        }
    }
}

/// A field variable with a tracked interval and a cached bit decomposition.
#[derive(Debug, Clone)]
pub struct Integer<F: PrimeField> {
    value: FieldVar<F>,
    pub interval: Interval,
    bits: Option<Vec<Boolean<F>>>,
}

impl<F: PrimeField> Integer<F> {
    /// Creates an integer from a variable known (by the caller) to be
    /// strictly less than `upper_bound`. No constraint is added; use
    /// [Self::of_bits] or check the range yourself when the variable comes
    /// from an untrusted witness.
    pub fn create_unsafe(value: FieldVar<F>, upper_bound: BigUint) -> Self {
        Self {
            value,
            interval: Interval::LessThan(upper_bound).check::<F>(),
            bits: None,
        }
    }

    /// Creates a constant integer.
    pub fn constant(x: &BigUint) -> Self {
        assert!(*x < field_size::<F>());
        let length = bits_needed(&(x + one()));
        let bits = (0..length)
            .map(|i| {
                if x.bit(i as u64) {
                    Boolean::true_()
                } else {
                    Boolean::false_()
                }
            })
            .collect();
        Self {
            value: FieldVar::constant(F::from(x.clone())),
            interval: Interval::Constant(x.clone()),
            bits: Some(bits),
        }
    }

    /// Creates an integer from a little-endian list of bits.
    pub fn of_bits(bits: &[Boolean<F>]) -> Self {
        Self {
            value: pack(bits),
            interval: Interval::LessThan(one() << bits.len()),
            bits: Some(bits.to_vec()),
        }
    }

    /// The underlying field variable.
    pub fn to_field(&self) -> &FieldVar<F> {
        &self.value
    }

    /// Multiplies by `2^k`.
    pub fn shift_left(&self, k: usize) -> Self {
        let two_to_k = one() << k;
        Self {
            value: self.value.scale(F::from(two_to_k.clone())),
            interval: self.interval.scale::<F>(&two_to_k),
            bits: self.bits.as_ref().map(|bs| {
                std::iter::repeat_with(Boolean::false_)
                    .take(k)
                    .chain(bs.iter().cloned())
                    .collect()
            }),
        }
    }

    /// Addition. No constraint is added (the result is a linear combination).
    pub fn add(&self, other: &Self) -> Self {
        Self {
            value: &self.value + &other.value,
            interval: self.interval.add::<F>(&other.interval),
            bits: None,
        }
    }

    /// Multiplication.
    pub fn mul(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Self> {
        let value = self
            .value
            .mul(&other.value, Some("Integer::mul".into()), loc, sys)?;
        Ok(Self {
            value,
            interval: self.interval.mul::<F>(&other.interval),
            bits: None,
        })
    }

    /// `self + 1`.
    pub fn succ(&self) -> Self {
        Self {
            value: &self.value + &FieldVar::constant(F::one()),
            interval: self.interval.succ::<F>(),
            bits: None,
        }
    }

    /// `self + if cond { 1 } else { 0 }`.
    pub fn succ_if(&self, cond: &Boolean<F>) -> Self {
        Self {
            value: &self.value + &cond.to_field_var(),
            interval: self.interval.lub(&self.interval.succ::<F>()),
            bits: None,
        }
    }

    /// Given `self` and `b`, returns `(q, r)` such that `self = q * b + r`
    /// and `r < b`. The quotient and remainder are witnessed and constrained.
    pub fn div_mod(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<(Self, Self)> {
        // guess (q, r)
        let a_value = self.value.clone();
        let b_value = other.value.clone();
        let (q, r): (FieldVar<F>, FieldVar<F>) = sys.compute(loc.clone(), move |env| {
            let a = field_to_biguint(env.read_var(&a_value));
            let b = field_to_biguint(env.read_var(&b_value));
            (F::from(&a / &b), F::from(a % b))
        })?;

        // check:
        //   r < b
        //   a = q * b + r
        //   q has at most as many bits as a
        let q_bit_length = self.interval.bits_needed();
        let q_bits = unpack(sys, loc.clone(), &q, q_bit_length)?;
        let b_bit_length = other.interval.bits_needed();
        let r_bits = unpack(sys, loc.clone(), &r, b_bit_length)?;
        assert_lt(sys, loc.clone(), b_bit_length, &r, &other.value)?;
        // this assertion checks that the multiplication q * b is safe
        assert!(q_bit_length + b_bit_length + 1 < F::MODULUS_BIT_SIZE as usize);
        sys.assert_r1cs(
            Some("Integer::div_mod".into()),
            loc,
            q.clone(),
            other.value.clone(),
            &self.value - &r,
        )?;

        Ok((
            Self {
                value: q,
                interval: self.interval.quotient(&other.interval),
                bits: Some(q_bits),
            },
            Self {
                value: r,
                interval: other.interval.clone(),
                bits: Some(r_bits),
            },
        ))
    }

    /// Subtraction, proven non-negative by unpacking the result.
    ///
    /// # Panics
    ///
    /// Panics if the intervals do not guarantee `self >= other`.
    pub fn subtract_unpacking(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Self> {
        assert!(
            self.interval.gte(&other.interval),
            "Integer::subtract_unpacking: potential underflow"
        );
        let value = &self.value - &other.value;
        let length = self.interval.bits_needed();
        // the constraints added in [unpack] ensure that 0 <= value <= self
        let bits = unpack(sys, loc, &value, length)?;
        Ok(Self {
            value,
            interval: self.interval.clone(),
            bits: Some(bits),
        })
    }

    /// `(underflow, if underflow { 0 } else { self - other })`.
    pub fn subtract_unpacking_or_zero(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<(Boolean<F>, Self)> {
        let underflow = self.lt(sys, loc.clone(), other)?;
        let value = (&self.value - &other.value).mul(
            &underflow.not().to_field_var(),
            Some("Integer::subtract_unpacking_or_zero".into()),
            loc,
            sys,
        )?;
        Ok((
            underflow,
            Self {
                value,
                interval: self.interval.clone(),
                bits: None,
            },
        ))
    }

    /// The little-endian bit decomposition (cached after the first call).
    pub fn to_bits(
        &mut self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
    ) -> SnarkyResult<Vec<Boolean<F>>> {
        match &self.bits {
            Some(bs) => Ok(bs.clone()),
            None => {
                let bits = unpack(sys, loc, &self.value, self.interval.bits_needed())?;
                self.bits = Some(bits.clone());
                Ok(bits)
            }
        }
    }

    fn max_bits(a: &Self, b: &Self) -> usize {
        std::cmp::max(a.interval.bits_needed(), b.interval.bits_needed())
    }

    /// `self == other`.
    pub fn equal(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Boolean<F>> {
        self.value.equal(sys, loc, &other.value)
    }

    /// `self < other`.
    pub fn lt(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Boolean<F>> {
        let res = compare(
            sys,
            loc,
            Self::max_bits(self, other),
            &self.value,
            &other.value,
        )?;
        Ok(res.less)
    }

    /// `self <= other`.
    pub fn lte(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Boolean<F>> {
        let res = compare(
            sys,
            loc,
            Self::max_bits(self, other),
            &self.value,
            &other.value,
        )?;
        Ok(res.less_or_equal)
    }

    /// `self >= other`.
    pub fn gte(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Boolean<F>> {
        Ok(self.lt(sys, loc, other)?.not())
    }

    /// `self > other`.
    pub fn gt(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Boolean<F>> {
        Ok(self.lte(sys, loc, other)?.not())
    }

    /// `min(self, other)`.
    pub fn min(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Self> {
        let res = compare(
            sys,
            loc.clone(),
            Self::max_bits(self, other),
            &self.value,
            &other.value,
        )?;
        let value = sys.if_(
            loc,
            res.less_or_equal,
            self.value.clone(),
            other.value.clone(),
        )?;
        Ok(Self {
            value,
            interval: self.interval.min(&other.interval),
            bits: None,
        })
    }

    /// `if cond { then_ } else { else_ }`.
    pub fn if_(
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        cond: &Boolean<F>,
        then_: &Self,
        else_: &Self,
    ) -> SnarkyResult<Self> {
        let value = sys.if_(loc, cond.clone(), then_.value.clone(), else_.value.clone())?;
        Ok(Self {
            value,
            interval: then_.interval.lub(&else_.interval),
            bits: None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{api::SnarkyCircuit, loc};
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { crate::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { crate::FULL_ROUNDS }>;

    struct TestCircuit {}

    impl SnarkyCircuit for TestCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { crate::FULL_ROUNDS }>;

        /// (a, b), both < 2^32, b != 0
        type PrivateInput = (Fp, Fp);
        type PublicInput = ();
        /// (a / b, a mod b, a - b or zero)
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>, FieldVar<Fp>);

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let a: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0)?;
            let b: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1)?;

            let bound = BigUint::from(1u64 << 32);
            let a = Integer::create_unsafe(a, bound.clone());
            let b = Integer::create_unsafe(b, bound);

            let (q, r) = a.div_mod(sys, loc!(), &b)?;
            let (_underflow, diff) = a.subtract_unpacking_or_zero(sys, loc!(), &b)?;

            Ok((
                q.to_field().clone(),
                r.to_field().clone(),
                diff.to_field().clone(),
            ))
        }
    }

    #[test]
    fn snarky_integer_div_mod() {
        let test_circuit = TestCircuit {};
        let (mut prover_index, verifier_index) = test_circuit.compile_to_indexes().unwrap();

        for (a, b) in [(42u64, 5u64), (5, 42), (1234567, 89), (100, 100)] {
            let private_input = (Fp::from(a), Fp::from(b));
            let expected = (
                Fp::from(a / b),
                Fp::from(a % b),
                Fp::from(a.saturating_sub(b)),
            );
            let (proof, public_output) = prover_index
                .prove::<BaseSponge, ScalarSponge>((), private_input, true)
                .unwrap();
            assert_eq!(*public_output, expected, "{a} div_mod {b}");
            verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
        }
    }
}

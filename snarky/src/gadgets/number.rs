//! Checked numbers with interval tracking.
//!
//! Port of the OCaml snarky `src/base/number.ml`: a [Number] is a field
//! variable together with out-of-circuit lower/upper bounds, which are used
//! to pick minimal bit lengths for comparisons and to short-circuit
//! comparisons whose result is implied by the bounds.

use std::borrow::Cow;

use ark_ff::PrimeField;
use num_bigint::BigUint;

use super::bits::{bits_needed, compare, field_to_biguint, pack, two_to_the, unpack};
use crate::{Boolean, FieldVar, RunState, SnarkyResult};

/// Returns `2^n` as a [BigUint].
fn pow2(n: usize) -> BigUint {
    BigUint::from(1u32) << n
}

/// Returns the field size as a [BigUint].
fn field_size<F: PrimeField>() -> BigUint {
    F::MODULUS.into()
}

/// A field variable together with bounds on the value it can take.
#[derive(Debug, Clone)]
pub struct Number<F: PrimeField> {
    pub upper_bound: BigUint,
    pub lower_bound: BigUint,
    var: FieldVar<F>,
    bits: Option<Vec<Boolean<F>>>,
}

impl<F: PrimeField> Number<F> {
    /// Creates a constant number.
    pub fn constant(x: F) -> Self {
        let n = field_to_biguint(x);
        let num_bits = bits_needed(&n);
        let bits = (0..num_bits)
            .map(|i| {
                if n.bit(i as u64) {
                    Boolean::true_()
                } else {
                    Boolean::false_()
                }
            })
            .collect();
        Self {
            upper_bound: n.clone(),
            lower_bound: n,
            var: FieldVar::constant(x),
            bits: Some(bits),
        }
    }

    pub fn zero() -> Self {
        Self::constant(F::zero())
    }

    pub fn one() -> Self {
        Self::constant(F::one())
    }

    /// Creates a number from a little-endian list of bits.
    ///
    /// # Panics
    ///
    /// Panics if the number of bits doesn't fit in a field element.
    pub fn of_bits(bits: &[Boolean<F>]) -> Self {
        let n = bits.len();
        assert!(n < F::MODULUS_BIT_SIZE as usize);
        Self {
            upper_bound: pow2(n) - BigUint::from(1u32),
            lower_bound: BigUint::from(0u32),
            var: pack(bits),
            bits: Some(bits.to_vec()),
        }
    }

    /// Creates a number from a variable known (by the caller) to be strictly
    /// less than `2^num_bits`. The decomposition in `num_bits` bits is
    /// constrained, proving the bound.
    pub fn of_var_checked(
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        var: FieldVar<F>,
        num_bits: usize,
    ) -> SnarkyResult<Self> {
        let bits = unpack(sys, loc, &var, num_bits)?;
        Ok(Self {
            upper_bound: pow2(num_bits) - BigUint::from(1u32),
            lower_bound: BigUint::from(0u32),
            var,
            bits: Some(bits),
        })
    }

    /// The underlying field variable.
    pub fn to_var(&self) -> &FieldVar<F> {
        &self.var
    }

    /// The little-endian bit decomposition of the number.
    pub fn to_bits(
        &mut self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
    ) -> SnarkyResult<Vec<Boolean<F>>> {
        let length = bits_needed(&self.upper_bound);
        match &self.bits {
            Some(bs) => Ok(bs.iter().take(length).cloned().collect()),
            None => {
                let bits = unpack(sys, loc, &self.var, length)?;
                self.bits = Some(bits.clone());
                Ok(bits)
            }
        }
    }

    /// Multiplies by `2^k` (a shift left of `k` bits).
    ///
    /// # Panics
    ///
    /// Panics if the result may overflow the field.
    pub fn mul_pow_2(
        &mut self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        k: usize,
    ) -> SnarkyResult<Self> {
        let bits = self.to_bits(sys, loc)?;
        let multiplied: Vec<Boolean<F>> = std::iter::repeat_with(Boolean::false_)
            .take(k)
            .chain(bits)
            .collect();
        let upper_bound = &self.upper_bound * pow2(k);
        assert!(
            upper_bound < field_size::<F>(),
            "Number::mul_pow_2: potential overflow"
        );
        Ok(Self {
            upper_bound,
            lower_bound: &self.lower_bound * pow2(k),
            var: pack(&multiplied),
            bits: Some(multiplied),
        })
    }

    /// Divides by `2^k`, rounding towards zero (a shift right of `k` bits).
    pub fn div_pow_2(
        &mut self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        k: usize,
    ) -> SnarkyResult<Self> {
        let bits = self.to_bits(sys, loc)?;
        let divided: Vec<Boolean<F>> = bits.into_iter().skip(k).collect();
        let of_bits = Self::of_bits(&divided);
        // Note: the bounds diverge from the OCaml original, which divides the
        // upper bound of the truncated decomposition by 2^k a second time and
        // thus under-estimates it (a bug: comparisons could then short-circuit
        // incorrectly). `floor(self / 2^k)` is bounded by `bound(self) >> k`.
        Ok(Self {
            upper_bound: &self.upper_bound >> k,
            lower_bound: &self.lower_bound >> k,
            var: of_bits.var,
            bits: of_bits.bits,
        })
    }

    /// `ceil(self / 2^k)`, using `ceil(n/m) = if m * floor(n/m) = n then floor(n/m) else floor(n/m) + 1`.
    pub fn ceil_div_pow_2(
        &mut self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        k: usize,
    ) -> SnarkyResult<Self> {
        let mut floor_div = self.div_pow_2(sys, loc.clone(), k)?;
        let mul_back = floor_div.mul_pow_2(sys, loc.clone(), k)?;
        let divides = mul_back.equal(sys, loc.clone(), self)?;
        let plus_one = floor_div.add(&Self::one());
        Self::if_(sys, loc, &divides, &floor_div, &plus_one)
    }

    /// `self mod 2^k`, i.e. the `k` low-order bits of `self`.
    ///
    /// Note: the OCaml original computes `self - 2^k * floor(self / 2^k)`,
    /// whose interval-checked subtraction spuriously reports a potential
    /// underflow whenever `self.lower_bound` is small. Packing the low `k`
    /// bits of the (constrained) decomposition is equivalent and cheaper.
    pub fn mod_pow_2(
        &mut self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        k: usize,
    ) -> SnarkyResult<Self> {
        let bits = self.to_bits(sys, loc)?;
        let low: Vec<Boolean<F>> = bits.into_iter().take(k).collect();
        Ok(Self::of_bits(&low))
    }

    /// Clamps the number to `n` bits: the result is `self` if it fits in `n`
    /// bits, and `2^n - 1` otherwise.
    ///
    /// # Panics
    ///
    /// Panics if `n` doesn't fit in a field element.
    pub fn clamp_to_n_bits(
        &mut self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        n: usize,
    ) -> SnarkyResult<Self> {
        assert!(n < F::MODULUS_BIT_SIZE as usize);
        let k = pow2(n);
        if self.upper_bound < k {
            return Ok(self.clone());
        }
        let bits = self.to_bits(sys, loc.clone())?;
        let truncated: Vec<Boolean<F>> = bits.into_iter().take(n).collect();
        let g = pack(&truncated);
        let fits = self.var.equal(sys, loc.clone(), &g)?;
        let max = FieldVar::constant(two_to_the::<F>(n) - F::one());
        let r = sys.if_(loc, fits, g, max)?;
        Ok(Self {
            upper_bound: k - BigUint::from(1u32),
            lower_bound: self.lower_bound.clone(),
            var: r,
            bits: None,
        })
    }

    /// The bit length needed to compare `x` and `y`.
    fn compare_bit_length(x: &Self, y: &Self) -> usize {
        std::cmp::max(bits_needed(&x.upper_bound), bits_needed(&y.upper_bound))
    }

    /// `self < other`. Short-circuits when the bounds already decide the result.
    pub fn lt(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Boolean<F>> {
        if self.upper_bound < other.lower_bound {
            Ok(Boolean::true_())
        } else if self.lower_bound >= other.upper_bound {
            Ok(Boolean::false_())
        } else {
            let bit_length = Self::compare_bit_length(self, other);
            let res = compare(sys, loc, bit_length, &self.var, &other.var)?;
            Ok(res.less)
        }
    }

    /// `self <= other`. Short-circuits when the bounds already decide the result.
    pub fn lte(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Boolean<F>> {
        if self.upper_bound <= other.lower_bound {
            Ok(Boolean::true_())
        } else if self.lower_bound > other.upper_bound {
            Ok(Boolean::false_())
        } else {
            let bit_length = Self::compare_bit_length(self, other);
            let res = compare(sys, loc, bit_length, &self.var, &other.var)?;
            Ok(res.less_or_equal)
        }
    }

    /// `self > other`.
    pub fn gt(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Boolean<F>> {
        other.lt(sys, loc, self)
    }

    /// `self >= other`.
    pub fn gte(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Boolean<F>> {
        other.lte(sys, loc, self)
    }

    /// `self == other`.
    pub fn equal(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Boolean<F>> {
        self.var.equal(sys, loc, &other.var)
    }

    /// `if b { then_ } else { else_ }`.
    pub fn if_(
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        b: &Boolean<F>,
        then_: &Self,
        else_: &Self,
    ) -> SnarkyResult<Self> {
        let var = sys.if_(loc, b.clone(), then_.var.clone(), else_.var.clone())?;
        Ok(Self {
            upper_bound: std::cmp::max(&then_.upper_bound, &else_.upper_bound).clone(),
            lower_bound: std::cmp::min(&then_.lower_bound, &else_.lower_bound).clone(),
            var,
            bits: None,
        })
    }

    /// Addition. No constraint is added (the result is a linear combination).
    ///
    /// # Panics
    ///
    /// Panics if the result may overflow the field.
    pub fn add(&self, other: &Self) -> Self {
        let upper_bound = &self.upper_bound + &other.upper_bound;
        assert!(
            upper_bound < field_size::<F>(),
            "Number::add: potential overflow ({} + {} > field size)",
            self.upper_bound,
            other.upper_bound,
        );
        Self {
            upper_bound,
            lower_bound: &self.lower_bound + &other.lower_bound,
            var: &self.var + &other.var,
            bits: None,
        }
    }

    /// Subtraction. No constraint is added (the result is a linear combination).
    ///
    /// # Panics
    ///
    /// Panics if the result may underflow.
    pub fn sub(&self, other: &Self) -> Self {
        assert!(
            self.lower_bound >= other.upper_bound,
            "Number::sub: potential underflow ({} < {})",
            self.lower_bound,
            other.upper_bound,
        );
        Self {
            upper_bound: &self.upper_bound - &other.lower_bound,
            lower_bound: &self.lower_bound - &other.upper_bound,
            var: &self.var - &other.var,
            bits: None,
        }
    }

    /// Multiplication.
    ///
    /// # Panics
    ///
    /// Panics if the result may overflow the field.
    pub fn mul(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Self> {
        let upper_bound = &self.upper_bound * &other.upper_bound;
        assert!(
            upper_bound < field_size::<F>(),
            "Number::mul: potential overflow ({} * {} > field size)",
            self.upper_bound,
            other.upper_bound,
        );
        let var = self
            .var
            .mul(&other.var, Some("Number::mul".into()), loc, sys)?;
        Ok(Self {
            upper_bound,
            lower_bound: &self.lower_bound * &other.lower_bound,
            var,
            bits: None,
        })
    }

    /// `min(self, other)`.
    pub fn min(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Self> {
        let less = self.lt(sys, loc.clone(), other)?;
        Self::if_(sys, loc, &less, self, other)
    }

    /// `max(self, other)`.
    pub fn max(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        other: &Self,
    ) -> SnarkyResult<Self> {
        let less = self.lt(sys, loc.clone(), other)?;
        Self::if_(sys, loc, &less, other, self)
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

        /// (a, b), both < 2^32
        type PrivateInput = (Fp, Fp);
        type PublicInput = ();
        /// (a < b, min(a, b), (a + b) * a mod 2^16)
        type PublicOutput = (Boolean<Fp>, FieldVar<Fp>, FieldVar<Fp>);

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let a: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0)?;
            let b: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1)?;

            let a = Number::of_var_checked(sys, loc!(), a, 32)?;
            let b = Number::of_var_checked(sys, loc!(), b, 32)?;

            let less = a.lt(sys, loc!(), &b)?;
            let min = a.min(sys, loc!(), &b)?;
            let mut product = a.add(&b).mul(sys, loc!(), &a)?;
            let modulo = product.mod_pow_2(sys, loc!(), 16)?;

            Ok((less, min.to_var().clone(), modulo.to_var().clone()))
        }
    }

    #[test]
    fn snarky_number_ops() {
        let test_circuit = TestCircuit {};
        let (mut prover_index, verifier_index) = test_circuit.compile_to_indexes().unwrap();

        for (a, b) in [(42u64, 43u64), (43, 42), (1234567, 89), (0, 0)] {
            let private_input = (Fp::from(a), Fp::from(b));
            let expected = (
                a < b,
                Fp::from(std::cmp::min(a, b)),
                Fp::from(((a + b) * a) % (1 << 16)),
            );
            let (proof, public_output) = prover_index
                .prove::<BaseSponge, ScalarSponge>((), private_input, true)
                .unwrap();
            assert_eq!(*public_output, expected, "{a} vs {b}");
            verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
        }
    }
}

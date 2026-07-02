//! Bit (de)composition gadgets.
//!
//! Port of the OCaml snarky primitives `Field.Var.pack`/`project`,
//! `Field.Checked.unpack`/`choose_preimage` (`src/base/snark0.ml`) and
//! `Field.Checked.compare` (`src/base/utils.ml`).

use std::borrow::Cow;

use ark_ff::{BigInteger, PrimeField};
use num_bigint::BigUint;

use crate::{Boolean, FieldVar, RunState, SnarkyResult};

/// Returns `2^n` as a field element.
pub fn two_to_the<F: PrimeField>(n: usize) -> F {
    let mut acc = F::one();
    for _ in 0..n {
        acc = acc + acc;
    }
    acc
}

/// The number of bits needed to represent the given number.
pub fn bits_needed(x: &BigUint) -> usize {
    x.bits() as usize
}

/// Converts a field element to a [BigUint].
pub fn field_to_biguint<F: PrimeField>(x: F) -> BigUint {
    x.into_bigint().into()
}

/// Packs a little-endian list of bits into a single field variable:
/// `sum_i 2^i * bits[i]`.
/// No constraint is added: the result is a linear combination of the inputs.
///
/// # Panics
///
/// Panics if the number of bits doesn't fit in a field element.
pub fn pack<F: PrimeField>(bits: &[Boolean<F>]) -> FieldVar<F> {
    assert!(
        bits.len() < F::MODULUS_BIT_SIZE as usize,
        "pack: too many bits ({}) for the field",
        bits.len()
    );
    let terms: Vec<_> = bits
        .iter()
        .enumerate()
        .map(|(i, b)| (two_to_the::<F>(i), b.to_field_var()))
        .collect();
    FieldVar::linear_combination(&terms)
}

/// Witnesses the `length` low-order bits of `var` without constraining
/// them to actually recompose to `var`.
/// Each bit is still constrained to be boolean.
pub fn unpack_unchecked<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    var: &FieldVar<F>,
    length: usize,
) -> SnarkyResult<Vec<Boolean<F>>> {
    let mut bits = Vec::with_capacity(length);
    for i in 0..length {
        let var = var.clone();
        let bit: Boolean<F> = sys.compute(loc.clone(), move |env| {
            let x = env.read_var(&var);
            x.into_bigint().get_bit(i)
        })?;
        bits.push(bit);
    }
    Ok(bits)
}

/// Decomposes `var` into its `length` low-order bits (little-endian), and
/// constrains the decomposition (this is the OCaml `choose_preimage`).
///
/// # Panics
///
/// Panics if `length` doesn't fit in a field element.
pub fn unpack<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    var: &FieldVar<F>,
    length: usize,
) -> SnarkyResult<Vec<Boolean<F>>> {
    assert!(
        length < F::MODULUS_BIT_SIZE as usize,
        "unpack: too many bits ({length}) for the field"
    );
    let bits = unpack_unchecked(sys, loc.clone(), var, length)?;
    // constrain sum_i 2^i b_i == var
    let lc = pack(&bits);
    sys.assert_r1cs(
        Some("unpack".into()),
        loc,
        lc,
        FieldVar::constant(F::one()),
        var.clone(),
    )?;
    Ok(bits)
}

/// The result of [compare].
#[derive(Debug)]
pub struct ComparisonResult<F: PrimeField> {
    pub less: Boolean<F>,
    pub less_or_equal: Boolean<F>,
}

/// Compares `a` and `b`, both assumed to fit in `bit_length` bits.
///
/// The logic (from the OCaml `Field.Checked.compare`): let `n = bit_length`;
/// then `-2^n < b - a < 2^n`, so the `n`-th bit of `2^n + b - a` is set iff
/// `b - a >= 0`, i.e. iff `a <= b`. Strictness is decided by whether the low
/// `n` bits of `2^n + b - a` are all zero (which happens iff `a = b`).
///
/// # Panics
///
/// Panics if `bit_length` exceeds `size_in_bits - 2`, as `2^(n+1) - 1` must
/// fit in the field.
pub fn compare<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    bit_length: usize,
    a: &FieldVar<F>,
    b: &FieldVar<F>,
) -> SnarkyResult<ComparisonResult<F>> {
    assert!(
        bit_length <= F::MODULUS_BIT_SIZE as usize - 2,
        "compare: bit_length ({bit_length}) too large for the field"
    );

    let alpha_packed = FieldVar::constant(two_to_the::<F>(bit_length)) + b - a;
    let alpha = unpack(sys, loc.clone(), &alpha_packed, bit_length + 1)?;

    let (prefix, less_or_equal) = alpha.split_at(bit_length);
    let less_or_equal = less_or_equal[0].clone();

    let prefix: Vec<&Boolean<F>> = prefix.iter().collect();
    let not_all_zeros = Boolean::any(&prefix, sys, loc.clone())?;

    let less = less_or_equal.and(&not_all_zeros, sys, loc);

    Ok(ComparisonResult {
        less,
        less_or_equal,
    })
}

/// Asserts that `a < b`, both assumed to fit in `bit_length` bits.
pub fn assert_lt<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    bit_length: usize,
    a: &FieldVar<F>,
    b: &FieldVar<F>,
) -> SnarkyResult<()> {
    let res = compare(sys, loc.clone(), bit_length, a, b)?;
    res.less
        .to_field_var()
        .assert_equals(sys, loc, &FieldVar::constant(F::one()))
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

        type PrivateInput = (Fp, Fp);
        type PublicInput = ();
        /// (a < b, a <= b)
        type PublicOutput = (Boolean<Fp>, Boolean<Fp>);

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let a: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0)?;
            let b: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1)?;

            // unpack/pack roundtrip on a
            let bits = unpack(sys, loc!(), &a, 64)?;
            let repacked = pack(&bits);
            repacked.assert_equals(sys, loc!(), &a)?;

            let res = compare(sys, loc!(), 64, &a, &b)?;
            Ok((res.less, res.less_or_equal))
        }
    }

    #[test]
    fn snarky_bits_compare() {
        let test_circuit = TestCircuit {};
        let (mut prover_index, verifier_index) = test_circuit.compile_to_indexes().unwrap();

        for (a, b, less, less_or_equal) in [
            (42u64, 43u64, true, true),
            (43, 42, false, false),
            (42, 42, false, true),
            (0, u64::MAX, true, true),
        ] {
            let private_input = (Fp::from(a), Fp::from(b));
            let (proof, public_output) = prover_index
                .prove::<BaseSponge, ScalarSponge>((), private_input, true)
                .unwrap();
            assert_eq!(*public_output, (less, less_or_equal), "{a} vs {b}");
            verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
        }
    }
}

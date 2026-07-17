//! Curve operations for the pickles verifier circuits
//! (port of pickles' `plonk_curve_ops.ml`).

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{
    constraint_system::{KimchiConstraint, ScaleRound},
    gadgets::curve::{add_complete, Point},
    runner::{Constraint, WitnessGeneration},
    Boolean, FieldVar, RunState, SnarkyResult,
};

/// Bits handled by one VarBaseMul row.
pub const BITS_PER_CHUNK: usize = 5;

/// Field division `a / b`: witnesses `q = a / b` and constrains `q * b = a`.
pub fn div_var<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    a: &FieldVar<F>,
    b: &FieldVar<F>,
) -> SnarkyResult<FieldVar<F>> {
    use snarky::runner::WitnessGeneration;
    let (a2, b2) = (a.clone(), b.clone());
    let q: FieldVar<F> = sys.compute(loc.clone(), move |env: &dyn WitnessGeneration<F>| {
        env.read_var(&a2) * env.read_var(&b2).inverse().unwrap()
    })?;
    sys.assert_r1cs(Some("div_var".into()), loc, q.clone(), b.clone(), a.clone())?;
    Ok(q)
}

/// Complete addition (one `CompleteAdd` row); pickles' `add_fast`.
pub fn add_fast<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    p1: &Point<F>,
    p2: &Point<F>,
) -> SnarkyResult<Point<F>> {
    // OCaml `add_fast` (plonk_curve_ops.ml:12) SEALS both points first:
    // `let p1 = seal p1 in let p2 = seal p2 in`. A coordinate that is a
    // scaled lincom (e.g. the `-y` of `G.negate g`) therefore becomes its
    // own variable through `exists + Field.Assert.equal` — gate form
    // `[c,c,0,0,0]` — instead of being reduced inside the gate's own input
    // handling (`reduce_to_v`, form `[c,0,c,0,0]`).
    let p1 = Point::new(
        p1.x.seal(sys, loc.clone())?,
        p1.y.seal(sys, loc.clone())?,
    );
    let p2 = Point::new(
        p2.x.seal(sys, loc.clone())?,
        p2.y.seal(sys, loc.clone())?,
    );
    add_complete(sys, loc, &p1, &p2)
}

/// Scalar multiplication by MSB-first bits, using the VarBaseMul gate
/// (5 bits per row): computes `(2·n + 2^num_bits + 1) · base`, where `n` is
/// the integer packed from `bits_msb` — the `Shifted_value.Type1` convention.
/// This is the port of pickles' `scale_fast_msb_bits`.
pub fn scale_fast_msb_bits<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    base: &Point<F>,
    bits_msb: &[Boolean<F>],
) -> SnarkyResult<Point<F>> {
    let bit_vars: Vec<FieldVar<F>> = bits_msb.iter().map(|b| b.to_field_var()).collect();
    let (acc, _n_acc) = scale_fast_core(sys, loc, base, &bit_vars)?;
    Ok(acc)
}

/// Scalar multiplication by a packed `num_bits`-bit scalar, unpacking it on
/// the fly: the bits are witnessed (MSB-first) and constrained boolean *by
/// the VarBaseMul gate itself*, and the recomposition is asserted equal to
/// `scalar`. Returns the product `(2·scalar + 2^num_bits + 1) · base` and
/// the LSB-first bits. Port of pickles' `scale_fast_unpack`.
pub fn scale_fast_unpack<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    base: &Point<F>,
    scalar: &FieldVar<F>,
    num_bits: usize,
) -> SnarkyResult<(Point<F>, Vec<Boolean<F>>)> {
    use ark_ff::BigInteger;

    // witness the MSB-first bits of the scalar
    let mut bit_vars = Vec::with_capacity(num_bits);
    for i in 0..num_bits {
        let scalar = scalar.clone();
        let bit: FieldVar<F> =
            sys.compute(loc.clone(), move |env: &dyn WitnessGeneration<F>| {
                let bits = env.read_var(&scalar).into_bigint().to_bits_le();
                if bits[num_bits - 1 - i] {
                    F::one()
                } else {
                    F::zero()
                }
            })?;
        bit_vars.push(bit);
    }

    let (acc, n_acc) = scale_fast_core(sys, loc.clone(), base, &bit_vars)?;
    n_acc.assert_equals(sys, loc, scalar)?;

    let bits_lsb = bit_vars
        .into_iter()
        .rev()
        .map(Boolean::create_unsafe)
        .collect();
    Ok((acc, bits_lsb))
}

/// [scale_fast_unpack], discarding the bits.
pub fn scale_fast<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    base: &Point<F>,
    scalar: &FieldVar<F>,
    num_bits: usize,
) -> SnarkyResult<Point<F>> {
    let (acc, _bits) = scale_fast_unpack(sys, loc, base, scalar, num_bits)?;
    Ok(acc)
}

/// The shared VarBaseMul chunk loop; `bit_vars` are the MSB-first bits as
/// field variables (0/1). Returns the accumulated point and the bit
/// recomposition `n_acc`.
fn scale_fast_core<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    base: &Point<F>,
    bit_vars: &[FieldVar<F>],
) -> SnarkyResult<(Point<F>, FieldVar<F>)> {
    let num_bits = bit_vars.len();
    assert_eq!(
        num_bits % BITS_PER_CHUNK,
        0,
        "scale_fast: num_bits must be a multiple of {BITS_PER_CHUNK}"
    );
    let chunks = num_bits / BITS_PER_CHUNK;

    let y_base = base.y.seal(sys, loc.clone())?;
    let x_base = base.x.seal(sys, loc.clone())?;
    let base = Point::new(x_base.clone(), y_base.clone());

    let mut acc = add_fast(sys, loc.clone(), &base, &base)?;
    let mut n_acc = FieldVar::zero();
    let mut state = Vec::with_capacity(chunks);

    for chunk in 0..chunks {
        let bs: Vec<FieldVar<F>> = (0..BITS_PER_CHUNK)
            .map(|i| bit_vars[chunk * BITS_PER_CHUNK + i].clone())
            .collect();

        let n_acc_prev = n_acc.clone();
        // n_acc = fold (2*acc + b) over the chunk's bits
        n_acc = {
            let (prev, bs) = (n_acc_prev.clone(), bs.clone());
            sys.compute(loc.clone(), move |env: &dyn WitnessGeneration<F>| {
                let mut n = env.read_var(&prev);
                for b in &bs {
                    n = n.double() + env.read_var(b);
                }
                n
            })?
        };

        let mut accs = vec![(acc.x.clone(), acc.y.clone())];
        let mut slopes = Vec::with_capacity(BITS_PER_CHUNK);

        for b in &bs {
            let (x_acc, y_acc) = (acc.x.clone(), acc.y.clone());

            macro_rules! w {
                (|$env:ident| $body:expr, [$($v:ident),*]) => {{
                    $(let $v = $v.clone();)*
                    let value: FieldVar<F> = sys.compute(loc.clone(), move |$env: &dyn WitnessGeneration<F>| {
                        $(let $v = $env.read_var(&$v);)*
                        $body
                    })?;
                    value
                }};
            }
            let two = F::from(2u64);

            // acc' = 2*acc + (2b - 1)*base, via two slopes as in the gate
            let s1 = w!(
                |env| (y_acc - (y_base * (two * b - F::one())))
                    * (x_acc - x_base).inverse().unwrap(),
                [y_acc, y_base, b, x_acc, x_base]
            );
            let s1_squared = w!(|env| s1.square(), [s1]);
            let s2 = w!(
                |env| (y_acc.double() * (x_acc.double() + x_base - s1_squared).inverse().unwrap())
                    - s1,
                [y_acc, x_acc, x_base, s1_squared, s1]
            );
            let x_res = w!(
                |env| x_base + s2.square() - s1_squared,
                [x_base, s2, s1_squared]
            );
            let y_res = w!(
                |env| ((x_acc - x_res) * s2) - y_acc,
                [x_acc, x_res, s2, y_acc]
            );

            acc = Point::new(x_res, y_res);
            accs.push((acc.x.clone(), acc.y.clone()));
            slopes.push(s1);
        }

        state.push(ScaleRound {
            accs,
            bits: bs,
            ss: slopes,
            base: (x_base.clone(), y_base.clone()),
            n_prev: n_acc_prev,
            n_next: n_acc.clone(),
        });
    }

    sys.add_constraint(
        Constraint::KimchiConstraint(KimchiConstraint::EcScale(state)),
        Some("scale_fast".into()),
        loc,
    )?;

    Ok((acc, n_acc))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
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

    const NUM_BITS: usize = 10;

    struct ScaleCircuit {}

    impl SnarkyCircuit for ScaleCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;

        /// (scalar bits packed in an Fp, (g.x, g.y))
        type PrivateInput = (Fp, (Fp, Fp));
        type PublicInput = ();
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>);

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let n: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0)?;
            let gx: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1 .0)?;
            let gy: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1 .1)?;

            // MSB-first bits of n
            let bits_lsb = snarky::gadgets::bits::unpack(sys, loc!(), &n, NUM_BITS)?;
            let bits_msb: Vec<_> = bits_lsb.into_iter().rev().collect();

            let g = Point::new(gx, gy);
            let res = scale_fast_msb_bits(sys, loc!(), &g, &bits_msb)?;
            Ok((res.x, res.y))
        }
    }

    /// `scale_fast_msb_bits(g, bits(n))` == `(2n + 2^num_bits + 1) · g`.
    #[test]
    fn scale_fast_matches_scalar_mul() {
        let circuit = ScaleCircuit {};
        let (mut prover_index, verifier_index) = circuit.compile_to_indexes().unwrap();

        let mut rng = o1_utils::tests::make_test_rng(None);

        for _ in 0..2 {
            use ark_ff::UniformRand;
            let n = u64::rand(&mut rng) % (1 << NUM_BITS);
            let g = (Pallas::generator() * Fq::rand(&mut rng)).into_affine();

            let scalar = Fq::from(2 * n + (1 << NUM_BITS) + 1);
            let expected = (g * scalar).into_affine();

            let private_input = (Fp::from(n), (g.x, g.y));
            let (proof, public_output) = prover_index
                .prove::<BaseSponge, ScalarSponge>((), private_input, true)
                .unwrap();

            assert_eq!(*public_output, (expected.x, expected.y));
            verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
        }
    }
}

#[cfg(test)]
mod unpack_tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
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

    const NUM_BITS: usize = 10;

    struct UnpackCircuit {}

    impl SnarkyCircuit for UnpackCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;

        /// (packed scalar, (g.x, g.y))
        type PrivateInput = (Fp, (Fp, Fp));
        type PublicInput = ();
        /// (scale result, recomposed low bit as sanity)
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>, Boolean<Fp>);

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let n: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0)?;
            let gx: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1 .0)?;
            let gy: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1 .1)?;

            let g = Point::new(gx, gy);
            let (res, bits_lsb) = scale_fast_unpack(sys, loc!(), &g, &n, NUM_BITS)?;
            Ok((res.x, res.y, bits_lsb[0].clone()))
        }
    }

    /// `scale_fast_unpack` scales like `scale_fast_msb_bits` and returns the
    /// scalar's bits, all constrained in-circuit.
    #[test]
    fn scale_fast_unpack_matches_scalar_mul() {
        let circuit = UnpackCircuit {};
        let (mut prover_index, verifier_index) = circuit.compile_to_indexes().unwrap();

        let mut rng = o1_utils::tests::make_test_rng(None);

        for _ in 0..2 {
            use ark_ff::UniformRand;
            let n = u64::rand(&mut rng) % (1 << NUM_BITS);
            let g = (Pallas::generator() * Fq::rand(&mut rng)).into_affine();

            let scalar = Fq::from(2 * n + (1 << NUM_BITS) + 1);
            let expected = (g * scalar).into_affine();

            let private_input = (Fp::from(n), (g.x, g.y));
            let (proof, public_output) = prover_index
                .prove::<BaseSponge, ScalarSponge>((), private_input, true)
                .unwrap();

            let (x, y, low_bit) = &*public_output;
            assert_eq!((*x, *y), (expected.x, expected.y));
            assert_eq!(*low_bit, (n & 1) == 1);
            verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
        }
    }
}

/// Number of VarBaseMul chunks needed to scale by a `num_bits`-bit scalar.
pub fn chunks_needed(num_bits: usize) -> usize {
    num_bits.div_ceil(BITS_PER_CHUNK)
}

/// Scalar multiplication in the `Shifted_value.Type2` convention: the scalar
/// is given as `(s_div_2, s_odd)` with `s = 2·s_div_2 + s_odd`, and the
/// result is `(s + 2^actual_bits) · g`, where `actual_bits` is `num_bits - 1`
/// rounded up to a whole number of VarBaseMul chunks.
/// Port of pickles' `scale_fast2`.
pub fn scale_fast2<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    g: &Point<F>,
    s_div_2: &FieldVar<F>,
    s_odd: &Boolean<F>,
    num_bits: usize,
) -> SnarkyResult<Point<F>> {
    let s_div_2_bits = num_bits - 1;
    let actual_bits_used = chunks_needed(s_div_2_bits) * BITS_PER_CHUNK;

    let (h, bits_lsb) = scale_fast_unpack(sys, loc.clone(), g, s_div_2, actual_bits_used)?;

    // constrain the top bits of s_div_2 to be 0
    for bit in &bits_lsb[s_div_2_bits..] {
        bit.to_field_var()
            .assert_equals(sys, loc.clone(), &FieldVar::zero())?;
    }

    // if s_odd { h } else { h - g }
    let previous_flush = sys
        .system
        .as_ref()
        .map(|system| system.flush_generic_before_custom());
    if let Some(system) = &mut sys.system {
        system.set_flush_generic_before_custom(false);
    }
    let h_minus_g_result = add_fast(
        sys,
        Cow::Owned(format!("{loc} | scale_fast2 h_minus_g add")),
        &h,
        &g.negate(),
    );
    if let (Some(previous_flush), Some(system)) = (previous_flush, &mut sys.system) {
        system.set_flush_generic_before_custom(previous_flush);
    }
    let h_minus_g = h_minus_g_result?;
    Point::select(sys, loc, s_odd, &h, &h_minus_g)
}

/// The `2^k` shift picked up by [`scale_fast2`] for a `num_bits`-bit scalar:
/// `k = BITS_PER_CHUNK · chunks_needed(num_bits - 1)` (the whole-chunk width
/// used to scale `s_div_2`). The Lagrange correction terms of the public-input
/// commitment must be `-(2^k)·L` with this same `k`.
pub fn scale_fast2_shift_bits(num_bits: usize) -> usize {
    chunks_needed(num_bits - 1) * BITS_PER_CHUNK
}

/// Splits a field variable into `(x_div_2, x_odd)` with `x = 2·x_div_2 +
/// x_odd` and the booleanity of `x_odd` asserted (pickles'
/// `wrap_main.ml::split_field`, also the witness step of `scale_fast2'`).
///
/// The split is on the *integer representative* of `x`, so it is valid for a
/// cross-field value embedded losslessly in the circuit field.
pub fn split_field<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    x: &FieldVar<F>,
) -> SnarkyResult<(FieldVar<F>, Boolean<F>)> {
    use ark_ff::BigInteger;

    let x_clone = x.clone();
    let (y, odd): (FieldVar<F>, FieldVar<F>) =
        sys.compute(loc.clone(), move |env: &dyn WitnessGeneration<F>| {
            let bits = env.read_var(&x_clone).into_bigint().to_bits_le();
            let mut half = F::zero();
            for &b in bits[1..].iter().rev() {
                half = half + half;
                if b {
                    half += F::one();
                }
            }
            (half, if bits[0] { F::one() } else { F::zero() })
        })?;
    // booleanity of the odd bit, and 2·y + odd == x
    sys.add_constraint(
        Constraint::BasicSnarkyConstraint(
            snarky::constraint_system::BasicSnarkyConstraint::Boolean(odd.clone()),
        ),
        Some("split_field: odd bit".into()),
        loc.clone(),
    )?;
    let recomposed = &(&y + &y) + &odd;
    recomposed.assert_equals(sys, loc, x)?;
    Ok((y, Boolean::create_unsafe(odd)))
}

/// An in-circuit `Shifted_value` representative of a cross-field scalar,
/// following kimchi's `shift_scalar` conventions (`commitment.rs`):
///
/// - [`ShiftedScalar::Type1`] when the scalar field is *smaller* than the
///   circuit field (wrap side, Tick scalars): a single representative `t` with
///   `value = 2t + 2^size + 1`, scaled by [`scale_fast`] and absorbed as one
///   element.
/// - [`ShiftedScalar::Type2`] when the scalar field is *bigger* (step side,
///   Tock scalars — Fq > Fp): the split pair `(s_div_2, s_odd)` of
///   `t = value - 2^size` (which does not fit the circuit field), scaled by
///   [`scale_fast2`] and absorbed as two elements (`absorb_fr`'s split).
#[derive(Clone)]
pub enum ShiftedScalar<F: PrimeField> {
    Type1(FieldVar<F>),
    Type2(FieldVar<F>, Boolean<F>),
}

impl<F: PrimeField> ShiftedScalar<F> {
    /// Absorbs the representative into the transcript sponge exactly as
    /// kimchi's `absorb_fr(shift_scalar(value))`: one element for Type1, the
    /// `(s_div_2, s_odd)` pair for Type2.
    pub fn absorb(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        sponge: &mut crate::sponge::PoseidonSponge<F>,
    ) {
        match self {
            ShiftedScalar::Type1(t) => sponge.absorb(sys, loc, std::slice::from_ref(t)),
            ShiftedScalar::Type2(s_div_2, s_odd) => {
                sponge.absorb(sys, loc.clone(), std::slice::from_ref(s_div_2));
                sponge.absorb(sys, loc, &[s_odd.to_field_var()]);
            }
        }
    }

    /// `value · g` through the matching scale gadget ([`scale_fast`] /
    /// [`scale_fast2`]); `num_bits` is the scalar field's size in bits.
    pub fn scale(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        g: &Point<F>,
        num_bits: usize,
    ) -> SnarkyResult<Point<F>> {
        match self {
            ShiftedScalar::Type1(t) => scale_fast(sys, loc, g, t, num_bits),
            ShiftedScalar::Type2(s_div_2, s_odd) => {
                scale_fast2(sys, loc, g, s_div_2, s_odd, num_bits)
            }
        }
    }
}

/// Scalar multiplication by a packed `num_bits`-bit scalar in the
/// `Shifted_value.Type2` convention (pickles' `scale_fast2'`): witnesses the
/// split `(s_div_2, s_odd)` via [`split_field`] and runs [`scale_fast2`].
/// Returns `(s + 2^scale_fast2_shift_bits(num_bits)) · g`.
pub fn scale_fast2_prime<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    g: &Point<F>,
    s: &FieldVar<F>,
    num_bits: usize,
) -> SnarkyResult<Point<F>> {
    let (s_div_2, s_odd) = split_field(sys, loc.clone(), s)?;
    scale_fast2(sys, loc, g, &s_div_2, &s_odd, num_bits)
}

#[cfg(test)]
mod scale_fast2_tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use mina_curves::pasta::{Fp, Fq, Pallas, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;
    use snarky::{api::SnarkyCircuit, loc, Boolean};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    const NUM_BITS: usize = 11;

    struct Scale2Circuit {}

    impl SnarkyCircuit for Scale2Circuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;

        /// ((s_div_2, s_odd), (g.x, g.y))
        type PrivateInput = ((Fp, bool), (Fp, Fp));
        type PublicInput = ();
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>);

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let s_div_2: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0 .0)?;
            let s_odd: Boolean<Fp> = sys.compute(loc!(), |_| private.unwrap().0 .1)?;
            let gx: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1 .0)?;
            let gy: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1 .1)?;

            let g = Point::new(gx, gy);
            let res = scale_fast2(sys, loc!(), &g, &s_div_2, &s_odd, NUM_BITS)?;
            Ok((res.x, res.y))
        }
    }

    /// `scale_fast2(g, (s_div_2, s_odd))` == `(s + 2^actual_bits) · g`
    /// with `s = 2·s_div_2 + s_odd`.
    #[test]
    fn scale_fast2_matches_scalar_mul() {
        let circuit = Scale2Circuit {};
        let (mut prover_index, verifier_index) = circuit.compile_to_indexes().unwrap();

        let mut rng = o1_utils::tests::make_test_rng(None);
        let actual_bits = chunks_needed(NUM_BITS - 1) * BITS_PER_CHUNK;

        for s_odd in [false, true] {
            use ark_ff::UniformRand;
            let s_div_2 = u64::rand(&mut rng) % (1 << (NUM_BITS - 1));
            let g = (Pallas::generator() * Fq::rand(&mut rng)).into_affine();

            let s = 2 * s_div_2 + u64::from(s_odd);
            let scalar = Fq::from(s + (1 << actual_bits));
            let expected = (g * scalar).into_affine();

            let private_input = ((Fp::from(s_div_2), s_odd), (g.x, g.y));
            let (proof, public_output) = prover_index
                .prove::<BaseSponge, ScalarSponge>((), private_input, true)
                .unwrap();

            assert_eq!(*public_output, (expected.x, expected.y), "s_odd = {s_odd}");
            verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
        }
    }

    struct Scale2PrimeCircuit {}

    impl SnarkyCircuit for Scale2PrimeCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;

        /// (s packed, (g.x, g.y))
        type PrivateInput = (Fp, (Fp, Fp));
        type PublicInput = ();
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>);

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let s: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0)?;
            let gx: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1 .0)?;
            let gy: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1 .1)?;

            let g = Point::new(gx, gy);
            let res = scale_fast2_prime(sys, loc!(), &g, &s, NUM_BITS)?;
            Ok((res.x, res.y))
        }
    }

    /// `scale_fast2_prime(g, s)` == `(s + 2^scale_fast2_shift_bits) · g`, with
    /// the `(s_div_2, s_odd)` split witnessed in-circuit.
    #[test]
    fn scale_fast2_prime_matches_scalar_mul() {
        let circuit = Scale2PrimeCircuit {};
        let (mut prover_index, verifier_index) = circuit.compile_to_indexes().unwrap();

        let mut rng = o1_utils::tests::make_test_rng(None);
        let shift = scale_fast2_shift_bits(NUM_BITS);

        for _ in 0..2 {
            use ark_ff::UniformRand;
            let s = u64::rand(&mut rng) % (1 << NUM_BITS);
            let g = (Pallas::generator() * Fq::rand(&mut rng)).into_affine();

            let scalar = Fq::from(s + (1 << shift));
            let expected = (g * scalar).into_affine();

            let private_input = (Fp::from(s), (g.x, g.y));
            let (proof, public_output) = prover_index
                .prove::<BaseSponge, ScalarSponge>((), private_input, true)
                .unwrap();

            assert_eq!(*public_output, (expected.x, expected.y), "s = {s}");
            verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
        }
    }
}

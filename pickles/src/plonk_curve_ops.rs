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

/// Complete addition (one `CompleteAdd` row); pickles' `add_fast`.
pub fn add_fast<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    p1: &Point<F>,
    p2: &Point<F>,
) -> SnarkyResult<Point<F>> {
    add_complete(sys, loc, p1, p2)
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
    let num_bits = bits_msb.len();
    assert_eq!(
        num_bits % BITS_PER_CHUNK,
        0,
        "scale_fast_msb_bits: num_bits must be a multiple of {BITS_PER_CHUNK}"
    );
    let chunks = num_bits / BITS_PER_CHUNK;

    let x_base = base.x.seal(sys, loc.clone())?;
    let y_base = base.y.seal(sys, loc.clone())?;
    let base = Point::new(x_base.clone(), y_base.clone());

    let mut acc = add_fast(sys, loc.clone(), &base, &base)?;
    let mut n_acc = FieldVar::zero();
    let mut state = Vec::with_capacity(chunks);

    for chunk in 0..chunks {
        let bs: Vec<FieldVar<F>> = (0..BITS_PER_CHUNK)
            .map(|i| bits_msb[chunk * BITS_PER_CHUNK + i].to_field_var())
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

    Ok(acc)
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

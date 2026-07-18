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
use snarky::{gadgets::curve::Point, Boolean, FieldVar, RunState, SnarkyResult};

use crate::scalar_challenge::{endo, endo_inv};

/// One entry of the polyscale combination — pickles'
/// `(Point.t array, Boolean.var) Opt.t` (wrap_verifier.ml:509). Points are
/// single-chunk and always `Finite` in the base subset (the wrap verifier
/// maps everything to `\`Finite` at wrap_verifier.ml:1413-1416).
pub enum CommitmentOpt<F: PrimeField> {
    /// Always present (`Opt.Just`).
    Just(Point<F>),
    /// Present iff the boolean is true (`Opt.Maybe` — the masked sg_old
    /// accumulators, wrap_verifier.ml:1369-1370).
    Maybe(Boolean<F>, Point<F>),
    /// Absent (`Opt.Nothing` — unused optional gate commitments).
    Nothing,
}

/// Combines commitments by the polyscale challenge `xi` — the faithful port
/// of `Split_commitments.combine` (wrap_verifier.ml:496-566) over
/// `Pcs_batch.combine_split_commitments` (pcs_batch.ml:18-40): the flat list
/// is processed in REVERSE (the last entry seeds the accumulator, `Nothing`s
/// are skipped), each `scale_and_add` step computes
/// `if acc.non_zero then p + endo(acc, xi) else p`, then
/// `if keep then that else acc.point`, and tracks
/// `non_zero = keep ||| acc.non_zero`; the final `non_zero` is asserted true.
///
/// `xi` is the 128-bit polyscale challenge (as squeezed); `endo_base` is the
/// curve's base endomorphism coefficient (for the `EndoMul` gate).
pub fn combine_commitments<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    commitments: &[CommitmentOpt<F>],
    xi: &FieldVar<F>,
    endo_base: F,
) -> SnarkyResult<Point<F>> {
    use crate::{common::SCALAR_CHALLENGE_BITS, plonk_curve_ops::add_fast};

    struct CurveOpt<F: PrimeField> {
        point: Point<F>,
        non_zero: Boolean<F>,
    }

    let mut acc: Option<CurveOpt<F>> = None;
    for entry in commitments.iter().rev() {
        let (keep, p) = match entry {
            CommitmentOpt::Nothing => continue,
            CommitmentOpt::Just(p) => (Boolean::true_(), p),
            CommitmentOpt::Maybe(keep, p) => (keep.clone(), p),
        };
        acc = Some(match acc {
            // `init` (pcs_batch.ml:33): seed from the last non-Nothing entry.
            None => CurveOpt {
                non_zero: keep,
                point: p.clone(),
            },
            // `scale_and_add` (wrap_verifier.ml:508-545).
            Some(a) => {
                let scaled = endo(
                    sys,
                    loc.clone(),
                    &a.point,
                    xi,
                    SCALAR_CHALLENGE_BITS,
                    endo_base,
                )?;
                let added = add_fast(
                    sys,
                    Cow::Owned(format!("{loc} | combine_commitments add")),
                    p,
                    &scaled,
                )?;
                // base = if acc.non_zero then p + xi·acc else p
                let base_y = sys.if_(loc.clone(), a.non_zero.clone(), added.y, p.y.clone())?;
                let base_x = sys.if_(loc.clone(), a.non_zero.clone(), added.x, p.x.clone())?;
                // point = if keep then base else acc.point
                let point_y = sys.if_(loc.clone(), keep.clone(), base_y, a.point.y.clone())?;
                let point_x = sys.if_(loc.clone(), keep.clone(), base_x, a.point.x.clone())?;
                let non_zero = keep.or(&a.non_zero, loc.clone(), sys);
                CurveOpt {
                    non_zero,
                    point: Point::new(point_x, point_y),
                }
            }
        });
    }
    let acc = acc.expect("combine_commitments: empty commitments");
    // Boolean.Assert.is_true non_zero (wrap_verifier.ml:564)
    acc.non_zero
        .to_field_var()
        .assert_equals(sys, loc, &FieldVar::constant(F::one()))?;
    Ok(acc.point)
}

/// The bulletproof reduction term sum (pickles' `bullet_reduce`, EC part):
/// given the per-round `(L, R)` points and the round prechallenges `pre`
/// (128-bit), returns `Σ_round (endo_inv(L, pre) + endo(R, pre))`
/// = `Σ_round (pre_field⁻¹·L + pre_field·R)`.
///
/// The sponge-driven derivation of the prechallenges is handled by the caller;
/// this is the pure elliptic-curve fold.
pub fn bullet_reduce_terms<F, C>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    lr: &[(Point<F>, Point<F>)],
    prechallenges: &[FieldVar<F>],
    endo_base: F,
    endo_scalar: <ark_ec::short_weierstrass::Affine<C> as ark_ec::AffineRepr>::ScalarField,
) -> SnarkyResult<Point<F>>
where
    F: PrimeField,
    C: ark_ec::short_weierstrass::SWCurveConfig<BaseField = F>,
{
    use crate::{common::SCALAR_CHALLENGE_BITS, plonk_curve_ops::add_fast};

    assert_eq!(lr.len(), prechallenges.len());
    assert!(!lr.is_empty(), "bullet_reduce_terms: no rounds");

    // OCaml first maps `term_and_challenge` over every (L, R) pair, producing
    // all `endo_inv(L) + endo(R)` terms, and only then runs `Array.reduce` on
    // that array.  Reducing eagerly inside this loop interleaves the running
    // sum's CompleteAdd with the next round's EndoMul block, yielding the same
    // point but a different gate order for every round after the first.
    let mut terms = Vec::with_capacity(lr.len());
    for ((l, r), pre) in lr.iter().zip(prechallenges) {
        let left = endo_inv::<F, C>(
            sys,
            loc.clone(),
            l,
            pre,
            SCALAR_CHALLENGE_BITS,
            endo_base,
            endo_scalar,
        )?;
        let right = endo(sys, loc.clone(), r, pre, SCALAR_CHALLENGE_BITS, endo_base)?;
        terms.push(add_fast(sys, loc.clone(), &left, &right)?);
    }

    let mut terms = terms.into_iter();
    let mut acc = terms.next().expect("bullet_reduce_terms: no rounds");
    for term in terms {
        acc = add_fast(sys, loc.clone(), &acc, &term)?;
    }
    Ok(acc)
}

/// The sponge-driven prechallenge derivation of pickles' `bullet_reduce`
/// (`wrap_verifier.ml`, lines ~168–174): for each IPA round, absorb the round's
/// `L` then `R` commitment into the (base-field) transcript sponge and squeeze a
/// raw 128-bit challenge. These prechallenges are then fed to
/// [`bullet_reduce_terms`] (as the endomorphism scalars) and recorded as the
/// deferred bulletproof challenges.
pub fn bullet_reduce_challenges<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    sponge: &mut crate::sponge::PoseidonSponge<F>,
    lr: &[(crate::oracles::PointVar<F>, crate::oracles::PointVar<F>)],
) -> SnarkyResult<Vec<FieldVar<F>>> {
    use crate::{challenge::squeeze_scalar, oracles::absorb_commitment};

    let mut prechallenges = Vec::with_capacity(lr.len());
    for (l, r) in lr {
        absorb_commitment(sys, loc.clone(), sponge, std::slice::from_ref(l));
        absorb_commitment(sys, loc.clone(), sponge, std::slice::from_ref(r));
        prechallenges.push(squeeze_scalar(sys, loc.clone(), sponge)?);
    }
    Ok(prechallenges)
}

/// The IPA challenge inputs produced by [`ipa_challenges_transcript`]:
/// `(u, prechallenges, c)`.
pub type IpaChallenges<F> = (Point<F>, Vec<FieldVar<F>>, FieldVar<F>);

/// The transcript-driven derivation of the IPA challenge inputs, threading a
/// single base-field sponge exactly as kimchi's `OpeningProof::verify`
/// (`poly-commitment/src/ipa.rs`, lines ~371–383) and pickles'
/// `check_bulletproof`:
///
/// ```text
/// absorb_shifted(sponge, combined_inner_product);      // absorb_fr(shift(cip))
/// u = group_map(squeeze_field sponge);                 // challenge_fq -> group_map
/// prechallenges = bullet_reduce(sponge, lr);           // per round: absorb L,R; squeeze
/// absorb(sponge, delta);                               // absorb_g(delta)
/// c = squeeze_scalar sponge;                           // raw 128-bit challenge
/// ```
///
/// Returns `(u, prechallenges, c)`, ready for [`check_bulletproof_equation`]
/// (`c` is the raw challenge fed to the [`endo`] gadget). `cip` is the
/// `Shifted_value.Type1` representative of the combined inner product.
#[allow(clippy::too_many_arguments)]
pub fn ipa_challenges_transcript<F, C>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    sponge: &mut crate::sponge::PoseidonSponge<F>,
    cip: &crate::plonk_curve_ops::ShiftedScalar<F>,
    lr: &[(crate::oracles::PointVar<F>, crate::oracles::PointVar<F>)],
    delta: &crate::oracles::PointVar<F>,
    group_map_params: &groupmap::BWParameters<C>,
) -> SnarkyResult<IpaChallenges<F>>
where
    F: PrimeField,
    C: ark_ec::short_weierstrass::SWCurveConfig<BaseField = F>,
{
    use crate::{challenge::squeeze_scalar, oracles::absorb_commitment};
    use snarky::gadgets::group_map::to_group;

    // absorb_shifted(combined_inner_product) — 1 or 2 elements per convention
    cip.absorb(sys, loc.clone(), sponge);

    // u = group_map(squeeze_field)
    let t = sponge.squeeze(sys, loc.clone());
    let (ux, uy) = to_group(sys, loc.clone(), group_map_params, &t)?;
    let u = Point::new(ux, uy);

    // prechallenges = bullet_reduce(sponge, lr)
    let prechallenges = bullet_reduce_challenges(sys, loc.clone(), sponge, lr)?;

    // absorb(delta); c = squeeze_scalar (raw 128-bit)
    absorb_commitment(sys, loc.clone(), sponge, std::slice::from_ref(delta));
    let c = squeeze_scalar(sys, loc, sponge)?;

    Ok((u, prechallenges, c))
}

/// The final inner-product-argument equation of pickles' `check_bulletproof`
/// (`wrap_verifier.ml`, lines ~603–622):
///
/// ```text
/// q   = combined_polynomial + scale_fast(u, cip) + lr_prod
/// lhs = endo(q, c) + delta
/// rhs = scale_fast(challenge_polynomial_commitment + scale_fast(u, b), z1)
///       + scale_fast(H, z2)
/// Success (equal_g lhs rhs)
/// ```
///
/// Returns the `equal_g` boolean asserting `c·Q + δ == z1·(G + b·U) + z2·H`.
///
/// The scalar advice values `cip` (combined inner product), `b`, `z1`, `z2` are
/// the `Shifted_value.Type1` representatives, scaled through [`scale_fast`]
/// (which computes `(2·repr + 2^num_bits + 1)·base`); `num_bits` is the other
/// field's `size_in_bits`. `c` is the 128-bit squeezed scalar challenge scaled
/// through the endomorphism gadget ([`endo`]). The sponge-driven derivation of
/// `u`, the prechallenges and `c` is handled by the caller.
#[allow(clippy::too_many_arguments)]
pub fn prepare_bulletproof_q<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    combined_polynomial: &Point<F>,
    lr_prod: &Point<F>,
    u: &Point<F>,
    cip: &crate::plonk_curve_ops::ShiftedScalar<F>,
    num_bits: usize,
) -> SnarkyResult<Point<F>> {
    use crate::plonk_curve_ops::add_fast;

    let uc = cip.scale(sys, loc.clone(), u, num_bits)?;
    let p_prime = add_fast(
        sys,
        Cow::Owned(format!("{loc} | bulletproof p_prime add")),
        combined_polynomial,
        &uc,
    )?;
    add_fast(
        sys,
        Cow::Owned(format!("{loc} | bulletproof q add")),
        &p_prime,
        lr_prod,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn check_bulletproof_equation_from_q<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    q: &Point<F>,
    u: &Point<F>,
    b: &crate::plonk_curve_ops::ShiftedScalar<F>,
    z1: &crate::plonk_curve_ops::ShiftedScalar<F>,
    z2: &crate::plonk_curve_ops::ShiftedScalar<F>,
    c: &FieldVar<F>,
    delta: &Point<F>,
    challenge_polynomial_commitment: &Point<F>,
    h_generator: &Point<F>,
    endo_base: F,
    num_bits: usize,
) -> SnarkyResult<snarky::Boolean<F>> {
    use crate::{common::SCALAR_CHALLENGE_BITS, plonk_curve_ops::add_fast};

    let cq = endo(sys, loc.clone(), q, c, SCALAR_CHALLENGE_BITS, endo_base)?;
    let lhs = add_fast(
        sys,
        Cow::Owned(format!("{loc} | bulletproof lhs add")),
        &cq,
        delta,
    )?;

    let b_u = b.scale(sys, loc.clone(), u, num_bits)?;
    let g_plus_b_u = add_fast(
        sys,
        Cow::Owned(format!("{loc} | bulletproof g_plus_b_u add")),
        challenge_polynomial_commitment,
        &b_u,
    )?;
    let z1_g_plus_b_u = z1.scale(sys, loc.clone(), &g_plus_b_u, num_bits)?;
    let z2_h = z2.scale(sys, loc.clone(), h_generator, num_bits)?;
    let rhs = add_fast(
        sys,
        Cow::Owned(format!("{loc} | bulletproof rhs add")),
        &z1_g_plus_b_u,
        &z2_h,
    )?;

    let equal = |sys: &mut RunState<F>,
                 lhs: &FieldVar<F>,
                 rhs: &FieldVar<F>|
     -> SnarkyResult<snarky::Boolean<F>> {
        let z = lhs - rhs;
        let z_for_witness = z.clone();
        let (result, z_inv): (FieldVar<F>, FieldVar<F>) = sys.compute(loc.clone(), move |env| {
            let z = env.read_var(&z_for_witness);
            match z.inverse() {
                Some(inv) => (F::zero(), inv),
                None => (F::one(), F::zero()),
            }
        })?;
        sys.assert_r1cs(
            Some("equals_2".into()),
            loc.clone(),
            result.clone(),
            z.clone(),
            FieldVar::zero(),
        )?;
        sys.assert_r1cs(
            Some("equals_1".into()),
            loc.clone(),
            z_inv,
            z,
            FieldVar::constant(F::one()) - &result,
        )?;
        Ok(snarky::Boolean::create_unsafe(result))
    };
    let x_eq = equal(sys, &lhs.x, &rhs.x)?;
    let y_eq = equal(sys, &lhs.y, &rhs.y)?;
    snarky::Boolean::all(&[x_eq, y_eq], sys, loc)
}

#[allow(clippy::too_many_arguments)]
pub fn check_bulletproof_equation<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    combined_polynomial: &Point<F>,
    lr_prod: &Point<F>,
    u: &Point<F>,
    cip: &crate::plonk_curve_ops::ShiftedScalar<F>,
    b: &crate::plonk_curve_ops::ShiftedScalar<F>,
    z1: &crate::plonk_curve_ops::ShiftedScalar<F>,
    z2: &crate::plonk_curve_ops::ShiftedScalar<F>,
    c: &FieldVar<F>,
    delta: &Point<F>,
    challenge_polynomial_commitment: &Point<F>,
    h_generator: &Point<F>,
    endo_base: F,
    num_bits: usize,
) -> SnarkyResult<snarky::Boolean<F>> {
    let q = prepare_bulletproof_q(
        sys,
        loc.clone(),
        combined_polynomial,
        lr_prod,
        u,
        cip,
        num_bits,
    )?;
    check_bulletproof_equation_from_q(
        sys,
        loc,
        &q,
        u,
        b,
        z1,
        z2,
        c,
        delta,
        challenge_polynomial_commitment,
        h_generator,
        endo_base,
        num_bits,
    )
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
                comms.push(CommitmentOpt::Just(Point::new(
                    sys.compute(loc!(), move |_| x)?,
                    sys.compute(loc!(), move |_| y)?,
                )));
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
            let xi_field =
                crate::scalar_challenge::ScalarChallenge(Fq::from(xi)).to_field(*endo_scalar);

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

    struct BulletReduceCircuit {
        prechallenges: Vec<u128>,
        lr: Vec<((Fp, Fp), (Fp, Fp))>,
    }
    impl SnarkyCircuit for BulletReduceCircuit {
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
            let mkpt = |sys: &mut RunState<Fp>, p: (Fp, Fp)| -> SnarkyResult<Point<Fp>> {
                Ok(Point::new(
                    sys.compute(loc!(), move |_| p.0)?,
                    sys.compute(loc!(), move |_| p.1)?,
                ))
            };
            let mut lr = vec![];
            for &(l, r) in &self.lr {
                lr.push((mkpt(sys, l)?, mkpt(sys, r)?));
            }
            let mut pres = vec![];
            for &c in &self.prechallenges {
                pres.push(sys.compute(loc!(), move |_| Fp::from(c))?);
            }
            let acc = bullet_reduce_terms::<Fp, mina_curves::pasta::PallasParameters>(
                sys,
                loc!(),
                &lr,
                &pres,
                crate::endo::tick::base(),
                <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1,
            )?;
            Ok((acc.x, acc.y))
        }
    }

    /// bullet_reduce_terms equals Σ (pre_field⁻¹·L + pre_field·R).
    #[test]
    fn bullet_reduce_matches_reference() {
        let mut rng = o1_utils::tests::make_test_rng(None);
        let (_, endo_scalar) = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();
        let rounds = 3;
        let lr_pts: Vec<(Pallas, Pallas)> = (0..rounds)
            .map(|_| {
                (
                    (Pallas::generator() * Fq::rand(&mut rng)).into_affine(),
                    (Pallas::generator() * Fq::rand(&mut rng)).into_affine(),
                )
            })
            .collect();
        let pres: Vec<u128> = (0..rounds).map(|_| u128::rand(&mut rng)).collect();

        // reference
        use ark_ff::Field;
        let mut acc = Pallas::zero().into_group();
        for (&(l, r), &pre) in lr_pts.iter().zip(&pres) {
            let pf = crate::scalar_challenge::ScalarChallenge(Fq::from(pre)).to_field(*endo_scalar);
            acc += l.into_group() * pf.inverse().unwrap() + r.into_group() * pf;
        }
        let expected = acc.into_affine();

        let circ = BulletReduceCircuit {
            prechallenges: pres,
            lr: lr_pts
                .iter()
                .map(|(l, r)| ((l.x, l.y), (r.x, r.y)))
                .collect(),
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(*out, (expected.x, expected.y));
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }

    use mina_poseidon::poseidon::{ArithmeticSponge, Sponge as _};
    type RefSponge = ArithmeticSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    fn lowest_128(x: Fp) -> Fp {
        use ark_ff::{AdditiveGroup, BigInteger, One, Zero};
        let bits = x.into_bigint().to_bits_le();
        let mut acc = Fp::zero();
        for &b in bits[..128].iter().rev() {
            acc.double_in_place();
            if b {
                acc += Fp::one();
            }
        }
        acc
    }

    struct BulletChalCircuit {
        lr: Vec<((Fp, Fp), (Fp, Fp))>,
    }
    impl SnarkyCircuit for BulletChalCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>, FieldVar<Fp>);
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let mkpt = |sys: &mut RunState<Fp>,
                        p: (Fp, Fp)|
             -> SnarkyResult<crate::oracles::PointVar<Fp>> {
                Ok((
                    sys.compute(loc!(), move |_| p.0)?,
                    sys.compute(loc!(), move |_| p.1)?,
                ))
            };
            let mut lr = vec![];
            for &(l, r) in &self.lr {
                lr.push((mkpt(sys, l)?, mkpt(sys, r)?));
            }
            let mut sponge = crate::sponge::PoseidonSponge::new();
            let chals = bullet_reduce_challenges(sys, loc!(), &mut sponge, &lr)?;
            Ok((chals[0].clone(), chals[1].clone(), chals[2].clone()))
        }
    }

    /// `bullet_reduce_challenges` reproduces the out-of-circuit transcript:
    /// absorb `L`, `R` per round, squeeze a raw 128-bit challenge.
    #[test]
    fn bullet_reduce_challenges_match_reference() {
        let mut rng = o1_utils::tests::make_test_rng(None);
        let rounds = 3;
        let lr_pts: Vec<(Pallas, Pallas)> = (0..rounds)
            .map(|_| {
                (
                    (Pallas::generator() * Fq::rand(&mut rng)).into_affine(),
                    (Pallas::generator() * Fq::rand(&mut rng)).into_affine(),
                )
            })
            .collect();

        // reference: ArithmeticSponge<Fp>, absorb l.x,l.y,r.x,r.y then squeeze
        let mut s = RefSponge::new(Vesta::sponge_params());
        let expected: Vec<Fp> = lr_pts
            .iter()
            .map(|(l, r)| {
                s.absorb(&[l.x]);
                s.absorb(&[l.y]);
                s.absorb(&[r.x]);
                s.absorb(&[r.y]);
                lowest_128(s.squeeze())
            })
            .collect();

        let circ = BulletChalCircuit {
            lr: lr_pts
                .iter()
                .map(|(l, r)| ((l.x, l.y), (r.x, r.y)))
                .collect(),
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        let (c0, c1, c2) = *out.clone();
        assert_eq!(c0, expected[0], "round 0");
        assert_eq!(c1, expected[1], "round 1");
        assert_eq!(c2, expected[2], "round 2");
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }

    struct IpaTranscriptCircuit {
        cip: u128,
        lr: Vec<((Fp, Fp), (Fp, Fp))>,
        delta: (Fp, Fp),
    }
    impl SnarkyCircuit for IpaTranscriptCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        // ((u.x, u.y), c, (pre0, pre1))
        type PublicOutput = (
            (FieldVar<Fp>, FieldVar<Fp>),
            FieldVar<Fp>,
            (FieldVar<Fp>, FieldVar<Fp>),
        );
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let mkpt = |sys: &mut RunState<Fp>,
                        p: (Fp, Fp)|
             -> SnarkyResult<crate::oracles::PointVar<Fp>> {
                Ok((
                    sys.compute(loc!(), move |_| p.0)?,
                    sys.compute(loc!(), move |_| p.1)?,
                ))
            };
            let cip = crate::plonk_curve_ops::ShiftedScalar::Type1(
                sys.compute(loc!(), |_| Fp::from(self.cip))?,
            );
            let mut lr = vec![];
            for &(l, r) in &self.lr {
                lr.push((mkpt(sys, l)?, mkpt(sys, r)?));
            }
            let delta = mkpt(sys, self.delta)?;
            use groupmap::GroupMap;
            let params = groupmap::BWParameters::<mina_curves::pasta::PallasParameters>::setup();
            let mut sponge = crate::sponge::PoseidonSponge::new();
            let (u, pre, c) = ipa_challenges_transcript::<Fp, mina_curves::pasta::PallasParameters>(
                sys,
                loc!(),
                &mut sponge,
                &cip,
                &lr,
                &delta,
                &params,
            )?;
            Ok(((u.x, u.y), c, (pre[0].clone(), pre[1].clone())))
        }
    }

    /// `ipa_challenges_transcript` threads the sponge exactly as kimchi's IPA
    /// verifier: absorb(cip) -> group_map(squeeze) -> per-round absorb(L,R)+
    /// squeeze -> absorb(delta) -> squeeze(c). Matches an out-of-circuit mirror.
    #[test]
    fn ipa_challenges_transcript_match_reference() {
        use groupmap::GroupMap;
        let mut rng = o1_utils::tests::make_test_rng(None);
        let rounds = 2;
        let lr_pts: Vec<(Pallas, Pallas)> = (0..rounds)
            .map(|_| {
                (
                    (Pallas::generator() * Fq::rand(&mut rng)).into_affine(),
                    (Pallas::generator() * Fq::rand(&mut rng)).into_affine(),
                )
            })
            .collect();
        let cip = u128::rand(&mut rng);
        let delta = (Pallas::generator() * Fq::rand(&mut rng)).into_affine();

        // out-of-circuit mirror over ArithmeticSponge<Fp>
        let params = groupmap::BWParameters::<mina_curves::pasta::PallasParameters>::setup();
        let mut s = RefSponge::new(Vesta::sponge_params());
        s.absorb(&[Fp::from(cip)]);
        let (ux, uy) = params.to_group(s.squeeze());
        let pre_ref: Vec<Fp> = lr_pts
            .iter()
            .map(|(l, r)| {
                s.absorb(&[l.x]);
                s.absorb(&[l.y]);
                s.absorb(&[r.x]);
                s.absorb(&[r.y]);
                lowest_128(s.squeeze())
            })
            .collect();
        s.absorb(&[delta.x]);
        s.absorb(&[delta.y]);
        let c_ref = lowest_128(s.squeeze());

        let circ = IpaTranscriptCircuit {
            cip,
            lr: lr_pts
                .iter()
                .map(|(l, r)| ((l.x, l.y), (r.x, r.y)))
                .collect(),
            delta: (delta.x, delta.y),
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        let ((ux_c, uy_c), c_c, (p0, p1)) = *out.clone();
        assert_eq!((ux_c, uy_c), (ux, uy), "u = group_map(squeeze)");
        assert_eq!(p0, pre_ref[0], "prechallenge 0");
        assert_eq!(p1, pre_ref[1], "prechallenge 1");
        assert_eq!(c_c, c_ref, "c");
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }

    /// The other field's `size_in_bits` (Fp, the step field); a multiple of the
    /// 5-bit VarBaseMul chunk width.
    const OTHER_FIELD_BITS: usize = 255;

    /// Out-of-circuit `scale_fast`: `(2·n + 2^num_bits + 1) · base`, matching
    /// the `Shifted_value.Type1` convention.
    fn scale_fast_ref(base: Pallas, repr: u128, num_bits: usize) -> Pallas {
        use ark_ff::{Field, One};
        let shift = Fq::from(2u64).pow([num_bits as u64]);
        let k = Fq::from(2u64) * Fq::from(repr) + shift + Fq::one();
        (base * k).into_affine()
    }

    struct BulletproofEqCircuit {
        combined_polynomial: (Fp, Fp),
        lr_prod: (Fp, Fp),
        u: (Fp, Fp),
        cip: u128,
        b: u128,
        z1: u128,
        z2: u128,
        c: u128,
        delta: (Fp, Fp),
        cpc: (Fp, Fp),
        h: (Fp, Fp),
    }
    impl SnarkyCircuit for BulletproofEqCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = snarky::Boolean<Fp>;
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let mkpt = |sys: &mut RunState<Fp>, p: (Fp, Fp)| -> SnarkyResult<Point<Fp>> {
                Ok(Point::new(
                    sys.compute(loc!(), move |_| p.0)?,
                    sys.compute(loc!(), move |_| p.1)?,
                ))
            };
            let mksc = |sys: &mut RunState<Fp>, s: u128| -> SnarkyResult<FieldVar<Fp>> {
                sys.compute(loc!(), move |_| Fp::from(s))
            };
            let combined_polynomial = mkpt(sys, self.combined_polynomial)?;
            let lr_prod = mkpt(sys, self.lr_prod)?;
            let u = mkpt(sys, self.u)?;
            let delta = mkpt(sys, self.delta)?;
            let cpc = mkpt(sys, self.cpc)?;
            let h = mkpt(sys, self.h)?;
            let t1 = |x| crate::plonk_curve_ops::ShiftedScalar::Type1(x);
            let cip = t1(mksc(sys, self.cip)?);
            let b = t1(mksc(sys, self.b)?);
            let z1 = t1(mksc(sys, self.z1)?);
            let z2 = t1(mksc(sys, self.z2)?);
            let c = mksc(sys, self.c)?;
            check_bulletproof_equation(
                sys,
                loc!(),
                &combined_polynomial,
                &lr_prod,
                &u,
                &cip,
                &b,
                &z1,
                &z2,
                &c,
                &delta,
                &cpc,
                &h,
                crate::endo::tick::base(),
                OTHER_FIELD_BITS,
            )
        }
    }

    /// `check_bulletproof_equation` returns `true` when `δ` is chosen so that
    /// `c·Q + δ == z1·(G + b·U) + z2·H`, and `false` when `δ` is perturbed.
    #[test]
    fn check_bulletproof_equation_accepts_and_rejects() {
        let mut rng = o1_utils::tests::make_test_rng(None);
        let (_, endo_scalar) = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();

        let rand_pt = |rng: &mut _| (Pallas::generator() * Fq::rand(rng)).into_affine();
        let combined_polynomial = rand_pt(&mut rng);
        let lr_prod = rand_pt(&mut rng);
        let u = rand_pt(&mut rng);
        let cpc = rand_pt(&mut rng);
        let h = rand_pt(&mut rng);
        let cip = u128::rand(&mut rng);
        let b = u128::rand(&mut rng);
        let z1 = u128::rand(&mut rng);
        let z2 = u128::rand(&mut rng);
        let c = u128::rand(&mut rng);

        // reference rhs = z1·(cpc + b·u) + z2·h
        let b_u = scale_fast_ref(u, b, OTHER_FIELD_BITS);
        let g_plus_b_u = (cpc + b_u).into_affine();
        let z1_term = scale_fast_ref(g_plus_b_u, z1, OTHER_FIELD_BITS);
        let z2_h = scale_fast_ref(h, z2, OTHER_FIELD_BITS);
        let rhs = (z1_term + z2_h).into_affine();

        // reference cq = endo(q, c), with q = combined_polynomial + u·cip + lr_prod
        let uc = scale_fast_ref(u, cip, OTHER_FIELD_BITS);
        let q = (combined_polynomial + uc + lr_prod).into_affine();
        let c_field = crate::scalar_challenge::ScalarChallenge(Fq::from(c)).to_field(*endo_scalar);
        let cq = (q * c_field).into_affine();

        // δ chosen so that lhs = cq + δ == rhs
        let delta_ok = (rhs.into_group() - cq.into_group()).into_affine();
        // perturbed δ so that lhs != rhs
        let delta_bad = (delta_ok + Pallas::generator()).into_affine();

        for (delta, expected) in [(delta_ok, true), (delta_bad, false)] {
            let circ = BulletproofEqCircuit {
                combined_polynomial: (combined_polynomial.x, combined_polynomial.y),
                lr_prod: (lr_prod.x, lr_prod.y),
                u: (u.x, u.y),
                cip,
                b,
                z1,
                z2,
                c,
                delta: (delta.x, delta.y),
                cpc: (cpc.x, cpc.y),
                h: (h.x, h.y),
            };
            let (mut pi, ver) = circ.compile_to_indexes().unwrap();
            let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
            assert_eq!(*out, expected, "equal_g mismatch (expected {expected})");
            ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
        }
    }
}

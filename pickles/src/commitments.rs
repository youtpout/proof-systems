//! Verifier commitment combinations for `incrementally_verify_proof`.
//!
//! `ft_comm` (pickles' `Common.ft_comm`, IVC step 14) builds the commitment to
//! the linearization polynomial `ft` from the verification key's last
//! permutation commitment and the quotient commitment `t_comm`, using the
//! deferred PlonK scalars `perm`, `zeta_to_srs_length` and
//! `zeta_to_domain_size` (`Shifted_value.Type1` field elements scaled through
//! [`scale_fast`]).

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{gadgets::curve::Point, RunState, SnarkyResult};

use crate::plonk_curve_ops::{add_fast, ShiftedScalar};

/// Combines a chunked commitment by the SRS-length challenge, Horner-style
/// (pickles' `reduce_chunks`): `res = comm[n-1]; for i=n-2..0 { res = comm[i] +
/// scale·res }`, where `scale·res` scales by `zeta_to_srs_length`.
fn reduce_chunks<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    comm: &[Point<F>],
    zeta_to_srs_length: &ShiftedScalar<F>,
    num_bits: usize,
) -> SnarkyResult<Point<F>> {
    let n = comm.len();
    assert!(n > 0, "reduce_chunks: empty commitment");
    let mut res = comm[n - 1].clone();
    for c in comm[..n - 1].iter().rev() {
        let scaled = zeta_to_srs_length.scale(sys, loc.clone(), &res, num_bits)?;
        res = add_fast(sys, loc.clone(), c, &scaled)?;
    }
    Ok(res)
}

/// Commitment to the linearization polynomial `ft` (pickles' `Common.ft_comm`):
///
/// ```text
/// sigma      = reduce_chunks(sigma_comm_last, zeta_to_srs_length)
/// f_comm     = perm · sigma
/// t          = reduce_chunks(t_comm, zeta_to_srs_length)
/// ft_comm    = f_comm + t - zeta_to_domain_size · t
/// ```
///
/// `sigma_comm_last` is the *last* permutation commitment of the verification
/// key (index `PERMUTS-1`), given as its chunks; `t_comm` is the quotient
/// commitment chunks. The scalars are `Shifted_value.Type1` representatives
/// scaled through [`scale_fast`] with `num_bits` = the other field's
/// `size_in_bits`.
#[allow(clippy::too_many_arguments)]
pub fn ft_comm<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    sigma_comm_last: &[Point<F>],
    t_comm: &[Point<F>],
    perm: &ShiftedScalar<F>,
    zeta_to_srs_length: &ShiftedScalar<F>,
    zeta_to_domain_size: &ShiftedScalar<F>,
    num_bits: usize,
) -> SnarkyResult<Point<F>> {
    // f_comm = perm · reduce_chunks(sigma_comm_last)
    let sigma = reduce_chunks(sys, loc.clone(), sigma_comm_last, zeta_to_srs_length, num_bits)?;
    let f_comm = perm.scale(sys, loc.clone(), &sigma, num_bits)?;

    // chunked_t_comm = reduce_chunks(t_comm)
    let chunked_t = reduce_chunks(sys, loc.clone(), t_comm, zeta_to_srs_length, num_bits)?;

    // OCaml evaluates the right-hand argument of
    // `f_comm + chunked_t + negate (scale chunked_t zeta_to_domain_size)`
    // before the two additions.  Preserve that order: `scale_fast` emits a
    // long VarBaseMul block, so computing `sum` first moves one CompleteAdd
    // across that block even though the resulting point is identical.
    let t_scaled = zeta_to_domain_size.scale(sys, loc.clone(), &chunked_t, num_bits)?;

    // ft_comm = f_comm + chunked_t - zeta_to_domain_size · chunked_t
    let sum = add_fast(
        sys,
        Cow::Owned(format!("{loc} | ft_comm sum add")),
        &f_comm,
        &chunked_t,
    )?;
    let neg_t_scaled = t_scaled.negate();
    let neg_t_scaled = Point::new(
        neg_t_scaled.x,
        neg_t_scaled.y.seal(sys, loc.clone())?,
    );
    add_fast(
        sys,
        Cow::Owned(format!("{loc} | ft_comm final add")),
        &sum,
        &neg_t_scaled,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{Field, One, UniformRand};
    use mina_curves::pasta::{Fp, Fq, Pallas, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;
    use snarky::{api::SnarkyCircuit, loc, FieldVar};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    const OTHER_FIELD_BITS: usize = 255;

    /// Out-of-circuit `scale_fast`: `(2·n + 2^num_bits + 1) · base`.
    fn scale_fast_ref(base: Pallas, repr: u128) -> Pallas {
        let shift = Fq::from(2u64).pow([OTHER_FIELD_BITS as u64]);
        let k = Fq::from(2u64) * Fq::from(repr) + shift + Fq::one();
        (base * k).into_affine()
    }

    fn reduce_chunks_ref(comm: &[Pallas], scale: u128) -> Pallas {
        let n = comm.len();
        let mut res = comm[n - 1].into_group();
        for c in comm[..n - 1].iter().rev() {
            res = *c + scale_fast_ref(res.into_affine(), scale);
        }
        res.into_affine()
    }

    struct FtCommCircuit {
        sigma_comm_last: Vec<(Fp, Fp)>,
        t_comm: Vec<(Fp, Fp)>,
        perm: u128,
        zeta_to_srs_length: u128,
        zeta_to_domain_size: u128,
    }
    impl SnarkyCircuit for FtCommCircuit {
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
            let mkpts = |sys: &mut RunState<Fp>, ps: &[(Fp, Fp)]| -> SnarkyResult<Vec<Point<Fp>>> {
                let mut out = vec![];
                for &(x, y) in ps {
                    out.push(Point::new(
                        sys.compute(loc!(), move |_| x)?,
                        sys.compute(loc!(), move |_| y)?,
                    ));
                }
                Ok(out)
            };
            let mksc = |sys: &mut RunState<Fp>, s: u128| sys.compute(loc!(), move |_| Fp::from(s));
            let sigma_comm_last = mkpts(sys, &self.sigma_comm_last)?;
            let t_comm = mkpts(sys, &self.t_comm)?;
            let perm = ShiftedScalar::Type1(mksc(sys, self.perm)?);
            let zsl = ShiftedScalar::Type1(mksc(sys, self.zeta_to_srs_length)?);
            let zds = ShiftedScalar::Type1(mksc(sys, self.zeta_to_domain_size)?);
            let ft = ft_comm(
                sys,
                loc!(),
                &sigma_comm_last,
                &t_comm,
                &perm,
                &zsl,
                &zds,
                OTHER_FIELD_BITS,
            )?;
            Ok((ft.x, ft.y))
        }
    }

    /// In-circuit `ft_comm` equals the out-of-circuit reference computing the
    /// same `f_comm + chunked_t - zeta_to_domain_size·chunked_t`.
    #[test]
    fn ft_comm_matches_reference() {
        let mut rng = o1_utils::tests::make_test_rng(None);
        let rand_pt = |rng: &mut _| (Pallas::generator() * Fq::rand(rng)).into_affine();

        // sigma_comm_last is a single chunk; t_comm is split into 7 (quotient).
        let sigma_comm_last: Vec<Pallas> = (0..1).map(|_| rand_pt(&mut rng)).collect();
        let t_comm: Vec<Pallas> = (0..7).map(|_| rand_pt(&mut rng)).collect();
        let perm = u128::rand(&mut rng);
        let zeta_to_srs_length = u128::rand(&mut rng);
        let zeta_to_domain_size = u128::rand(&mut rng);

        // reference
        let sigma = reduce_chunks_ref(&sigma_comm_last, zeta_to_srs_length);
        let f_comm = scale_fast_ref(sigma, perm);
        let chunked_t = reduce_chunks_ref(&t_comm, zeta_to_srs_length);
        let t_scaled = scale_fast_ref(chunked_t, zeta_to_domain_size);
        let expected = (f_comm + chunked_t - t_scaled).into_affine();

        let circ = FtCommCircuit {
            sigma_comm_last: sigma_comm_last.iter().map(|c| (c.x, c.y)).collect(),
            t_comm: t_comm.iter().map(|c| (c.x, c.y)).collect(),
            perm,
            zeta_to_srs_length,
            zeta_to_domain_size,
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(*out, (expected.x, expected.y));
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }
}

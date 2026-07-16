//! In-circuit reconstruction of the kimchi Fr-sponge Fiat-Shamir transcript
//! used by `finalize_other_proof` to resample the polyscale `xi` (v) and the
//! evalscale `r` (u).
//!
//! This mirrors, gate-for-gate, the sequence in `kimchi/src/verifier.rs`
//! (the `to_batch` oracle computation), lines ~283–402:
//!
//! ```text
//! let digest = fq_sponge.clone().digest();
//! fr_sponge.absorb(&digest);
//! let prev_challenge_digest = { fresh; for chals { absorb_multiple(chals) }; digest() };
//! fr_sponge.absorb(&prev_challenge_digest);
//! fr_sponge.absorb(&ft_eval1);
//! fr_sponge.absorb_multiple(&public_evals[0]);
//! fr_sponge.absorb_multiple(&public_evals[1]);
//! fr_sponge.absorb_evaluations(&evals);
//! let v_chal = fr_sponge.challenge();   // xi / polyscale
//! let u_chal = fr_sponge.challenge();   // r  / evalscale
//! ```
//!
//! The Fr-sponge is a plain [`mina_poseidon::poseidon::ArithmeticSponge`] over
//! the scalar field, so its in-circuit analogue is exactly
//! [`crate::sponge::PoseidonSponge`] (the fixed `DuplexState`). Each
//! `challenge()` in kimchi squeezes one field element and keeps its lowest two
//! 64-bit limbs (128 bits) — precisely what [`crate::challenge::squeeze_challenge`]
//! reproduces.
//!
//! The squeezed values here are the **128-bit scalar challenges**
//! (`o.oracles.v_chal` / `o.oracles.u_chal`); the endomorphism conversion to
//! the full field elements `v` / `u` (`o.oracles.v` / `o.oracles.u`) is a
//! separate, already-ported step (see [`crate::scalar_challenge`]).

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{Boolean, FieldVar, RunState, SnarkyResult};

use crate::{challenge::squeeze_challenge, sponge::PoseidonSponge};

/// A single polynomial's evaluations at `zeta` and `zeta * omega`, each a list
/// of chunks (length 1 in the single-chunk / base-step case).
pub type PointEvalVar<F> = (Vec<FieldVar<F>>, Vec<FieldVar<F>>);

/// The proof column evaluations absorbed by the Fr-sponge, in kimchi's exact
/// `absorb_evaluations` order (mandatory columns only — the no-optional-gate,
/// no-lookup subset used by a base step circuit).
#[derive(Clone)]
pub struct AbsorbEvalsVar<F: PrimeField> {
    pub z: PointEvalVar<F>,
    pub generic_selector: PointEvalVar<F>,
    pub poseidon_selector: PointEvalVar<F>,
    pub complete_add_selector: PointEvalVar<F>,
    pub mul_selector: PointEvalVar<F>,
    pub emul_selector: PointEvalVar<F>,
    pub endomul_scalar_selector: PointEvalVar<F>,
    /// the 15 witness columns
    pub w: Vec<PointEvalVar<F>>,
    /// the 15 coefficient columns
    pub coefficients: Vec<PointEvalVar<F>>,
    /// the 6 evaluated permutation columns (`PERMUTS - 1`)
    pub s: Vec<PointEvalVar<F>>,
}

impl<F: PrimeField> AbsorbEvalsVar<F> {
    /// The columns in the exact order kimchi's `FrSponge::absorb_evaluations`
    /// pushes them: `z`, the seven fixed selectors, then `w`, `coefficients`,
    /// `s`.
    fn ordered_points(&self) -> Vec<&PointEvalVar<F>> {
        let mut points = vec![
            &self.z,
            &self.generic_selector,
            &self.poseidon_selector,
            &self.complete_add_selector,
            &self.mul_selector,
            &self.emul_selector,
            &self.endomul_scalar_selector,
        ];
        points.extend(self.w.iter());
        points.extend(self.coefficients.iter());
        points.extend(self.s.iter());
        points
    }
}

/// All the field elements fed to the Fr-sponge before squeezing `xi` and `r`.
pub struct FrSpongeInputs<F: PrimeField> {
    /// `fq_sponge.digest()` — the base-field sponge digest that seeds the
    /// Fr-sponge (threaded in from the proof transcript).
    pub digest: FieldVar<F>,
    /// The previous recursion challenges, one inner-list per prior proof
    /// (empty for a base proof). Each inner list is absorbed with
    /// `absorb_multiple` into a *fresh* sponge whose digest is then folded in.
    pub prev_challenges: Vec<Vec<FieldVar<F>>>,
    /// When present, conditionally absorbs the fixed-width previous
    /// challenges exactly like `step_verifier.ml`'s `Opt_sponge`. Padding is
    /// at the front, so this mask is aligned with `prev_challenges`.
    pub prev_challenge_mask: Option<Vec<Boolean<F>>>,
    /// `ft(zeta * omega)`.
    pub ft_eval1: FieldVar<F>,
    /// The negated public-input polynomial evaluations at `zeta` and `zeta*w`.
    pub public_evals: [Vec<FieldVar<F>>; 2],
    /// The proof column evaluations.
    pub evals: AbsorbEvalsVar<F>,
    /// How `xi` is squeezed: the OCaml STEP side uses `squeeze_challenge`
    /// (both 128-bit halves range-checked, step_verifier.ml:990); the WRAP
    /// side uses `squeeze_scalar` (high half only, wrap_verifier.ml:1606).
    pub xi_constrain_low_bits: bool,
}

/// Absorbs `xs` into the sponge one element at a time (matching kimchi's
/// per-element `FrSponge::absorb`; the duplex state machine makes this
/// equivalent to a single `absorb_multiple`).
fn absorb_all<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    sponge: &mut PoseidonSponge<F>,
    xs: &[FieldVar<F>],
) {
    for x in xs {
        sponge.absorb(sys, loc.clone(), std::slice::from_ref(x));
    }
}

/// Runs the Fr-sponge transcript in-circuit and returns the two squeezed
/// 128-bit scalar challenges `(xi_chal, r_chal)` — the circuit counterparts of
/// `o.oracles.v_chal` and `o.oracles.u_chal`.
pub fn squeeze_xi_r<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    inputs: &FrSpongeInputs<F>,
) -> SnarkyResult<(FieldVar<F>, FieldVar<F>)> {
    let mut sponge = PoseidonSponge::new();

    // 1. absorb the fq-sponge digest
    absorb_all(
        sys,
        loc.clone(),
        &mut sponge,
        std::slice::from_ref(&inputs.digest),
    );

    // 2. absorb the previous-recursion-challenges digest (computed in a fresh
    //    sponge to keep the optional-sponge scope small, exactly as kimchi does)
    let prev_challenge_digest = match &inputs.prev_challenge_mask {
        None => {
            let mut inner = PoseidonSponge::new();
            for chals in &inputs.prev_challenges {
                absorb_all(sys, loc.clone(), &mut inner, chals);
            }
            inner.squeeze(sys, loc.clone())
        }
        Some(mask) => {
            assert_eq!(mask.len(), inputs.prev_challenges.len());
            let mut inner = crate::opt_sponge::OptSponge::new();
            for (keep, chals) in mask.iter().zip(&inputs.prev_challenges) {
                for challenge in chals {
                    inner.absorb((keep.clone(), challenge.clone()));
                }
            }
            inner.squeeze(sys, loc.clone())?
        }
    };
    absorb_all(
        sys,
        loc.clone(),
        &mut sponge,
        std::slice::from_ref(&prev_challenge_digest),
    );

    // 3. absorb ft(zeta*omega)
    absorb_all(
        sys,
        loc.clone(),
        &mut sponge,
        std::slice::from_ref(&inputs.ft_eval1),
    );

    // 4. absorb the public-input polynomial evaluations
    absorb_all(sys, loc.clone(), &mut sponge, &inputs.public_evals[0]);
    absorb_all(sys, loc.clone(), &mut sponge, &inputs.public_evals[1]);

    // 5. absorb all the column evaluations, zeta then zeta*omega per column
    for (zeta, zeta_omega) in inputs.evals.ordered_points() {
        absorb_all(sys, loc.clone(), &mut sponge, zeta);
        absorb_all(sys, loc.clone(), &mut sponge, zeta_omega);
    }

    // 6. squeeze xi (polyscale) then r (evalscale)
    // OCaml wrap side: `xi_actual = squeeze_scalar` (high half checked only,
    // wrap_verifier.ml:1606); step side: `squeeze_challenge` for both
    // (step_verifier.ml:990-992). `r` is `squeeze_challenge` on both sides.
    let xi = if inputs.xi_constrain_low_bits {
        squeeze_challenge(sys, loc.clone(), &mut sponge)?
    } else {
        crate::challenge::squeeze_scalar(sys, loc.clone(), &mut sponge)?
    };
    let r = squeeze_challenge(sys, loc, &mut sponge)?;
    Ok((xi, r))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::One;
    use kimchi::{
        circuits::wires::{COLUMNS, PERMUTS},
        curve::KimchiCurve,
    };
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::{commitment::PolyComm, ipa::OpeningProof, SRS};
    use snarky::{api::SnarkyCircuit, loc};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    /// The circuit whose proof we will feed to the Fr-sponge reconstruction.
    struct SmallCircuit {}
    impl SnarkyCircuit for SmallCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = Fp;
        type PublicInput = FieldVar<Fp>;
        type PublicOutput = ();
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            z: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<()> {
            let x: FieldVar<Fp> = sys.compute(loc!(), |_| *private.unwrap())?;
            let xx = x.mul(&x, None, loc!(), sys)?;
            xx.assert_equals(sys, loc!(), &z)?;
            let _ = sys.poseidon(loc!(), (x, z));
            Ok(())
        }
    }

    /// Captured Fr-sponge inputs of a real proof, replayed in the circuit.
    struct FrSpongeCircuit {
        digest: Fp,
        ft_eval1: Fp,
        public_evals: [Vec<Fp>; 2],
        z: (Vec<Fp>, Vec<Fp>),
        generic: (Vec<Fp>, Vec<Fp>),
        poseidon: (Vec<Fp>, Vec<Fp>),
        complete_add: (Vec<Fp>, Vec<Fp>),
        mul: (Vec<Fp>, Vec<Fp>),
        emul: (Vec<Fp>, Vec<Fp>),
        endomul_scalar: (Vec<Fp>, Vec<Fp>),
        w: Vec<(Vec<Fp>, Vec<Fp>)>,
        coefficients: Vec<(Vec<Fp>, Vec<Fp>)>,
        s: Vec<(Vec<Fp>, Vec<Fp>)>,
    }

    impl SnarkyCircuit for FrSpongeCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>);

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            _private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let w1 = |sys: &mut RunState<Fp>, v: Fp| sys.compute(loc!(), move |_| v);
            let wvec = |sys: &mut RunState<Fp>, vs: &[Fp]| -> SnarkyResult<Vec<FieldVar<Fp>>> {
                let mut out = vec![];
                for &v in vs {
                    out.push(sys.compute(loc!(), move |_| v)?);
                }
                Ok(out)
            };
            let wpair = |sys: &mut RunState<Fp>,
                         p: &(Vec<Fp>, Vec<Fp>)|
             -> SnarkyResult<PointEvalVar<Fp>> {
                Ok((wvec(sys, &p.0)?, wvec(sys, &p.1)?))
            };

            let digest = w1(sys, self.digest)?;
            let ft_eval1 = w1(sys, self.ft_eval1)?;
            let public_evals = [
                wvec(sys, &self.public_evals[0])?,
                wvec(sys, &self.public_evals[1])?,
            ];

            let z = wpair(sys, &self.z)?;
            let generic_selector = wpair(sys, &self.generic)?;
            let poseidon_selector = wpair(sys, &self.poseidon)?;
            let complete_add_selector = wpair(sys, &self.complete_add)?;
            let mul_selector = wpair(sys, &self.mul)?;
            let emul_selector = wpair(sys, &self.emul)?;
            let endomul_scalar_selector = wpair(sys, &self.endomul_scalar)?;
            let mut wcols = vec![];
            for p in &self.w {
                wcols.push(wpair(sys, p)?);
            }
            let mut coeffs = vec![];
            for p in &self.coefficients {
                coeffs.push(wpair(sys, p)?);
            }
            let mut scols = vec![];
            for p in &self.s {
                scols.push(wpair(sys, p)?);
            }

            let evals = AbsorbEvalsVar {
                z,
                generic_selector,
                poseidon_selector,
                complete_add_selector,
                mul_selector,
                emul_selector,
                endomul_scalar_selector,
                w: wcols,
                coefficients: coeffs,
                s: scols,
            };
            let inputs = FrSpongeInputs {
                digest,
                prev_challenges: vec![],
                prev_challenge_mask: None,
                ft_eval1,
                public_evals,
                evals,
                xi_constrain_low_bits: true,
            };
            squeeze_xi_r(sys, loc!(), &inputs)
        }
    }

    /// The in-circuit Fr-sponge reproduces kimchi's `v_chal` / `u_chal`
    /// (the 128-bit scalar challenges) on a real proof.
    #[test]
    fn fr_sponge_matches_kimchi() {
        let mut pi = SmallCircuit {}.compile_to_indexes().unwrap().0;
        let vi = SmallCircuit {}.compile_to_indexes().unwrap().1;
        let vi = &vi.index;
        let x = Fp::from(7u64);
        let z = x * x;
        let (proof, _) = pi.prove::<BaseSponge, ScalarSponge>(z, x, true).unwrap();

        let public_input = vec![z];
        let lgr = vi.srs().get_lagrange_basis(vi.domain);
        let com: Vec<_> = lgr.iter().take(vi.public).collect();
        let elm: Vec<_> = public_input.iter().map(|s| -*s).collect();
        let pc = PolyComm::<Vesta>::multi_scalar_mul(&com, &elm);
        let public_comm = vi
            .srs()
            .mask_custom(pc.clone(), &pc.map(|_| Fp::one()))
            .unwrap()
            .commitment;
        let o = proof
            .oracles::<BaseSponge, ScalarSponge, _>(vi, &public_comm, Some(&public_input))
            .unwrap();

        // capture the column evaluations as chunked vecs, in kimchi order
        let e = &proof.evals;
        let pair =
            |p: &kimchi::proof::PointEvaluations<Vec<Fp>>| (p.zeta.clone(), p.zeta_omega.clone());
        assert_eq!(e.w.len(), COLUMNS);
        assert_eq!(e.coefficients.len(), COLUMNS);
        assert_eq!(e.s.len(), PERMUTS - 1);

        let circ = FrSpongeCircuit {
            digest: o.digest,
            ft_eval1: proof.ft_eval1,
            public_evals: o.public_evals.clone(),
            z: pair(&e.z),
            generic: pair(&e.generic_selector),
            poseidon: pair(&e.poseidon_selector),
            complete_add: pair(&e.complete_add_selector),
            mul: pair(&e.mul_selector),
            emul: pair(&e.emul_selector),
            endomul_scalar: pair(&e.endomul_scalar_selector),
            w: e.w.iter().map(pair).collect(),
            coefficients: e.coefficients.iter().map(pair).collect(),
            s: e.s.iter().map(pair).collect(),
        };

        let (mut fpi, fver) = circ.compile_to_indexes().unwrap();
        let (fproof, out) = fpi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        let (xi_chal, r_chal) = (out.0, out.1);

        // The Fr-sponge inner field (`ScalarChallenge`) is opaque, so compare
        // via the endomorphism conversion (`v = v_chal.to_field(endo_r)`) — the
        // exact value consumed downstream. `to_field` is injective on 128-bit
        // challenges, so equality here proves the raw challenges match too.
        use mina_poseidon::sponge::ScalarChallenge;
        let (_, endo_r) = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();
        let xi_field = ScalarChallenge::new(xi_chal).to_field(endo_r);
        let r_field = ScalarChallenge::new(r_chal).to_field(endo_r);
        assert_eq!(xi_field, o.oracles.v, "xi (polyscale) matches kimchi");
        assert_eq!(r_field, o.oracles.u, "r (evalscale) matches kimchi");

        fver.verify::<BaseSponge, ScalarSponge>(fproof, (), (xi_chal, r_chal));
    }
}

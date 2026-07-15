//! `All_evals` (port of `plonk_types.ml`'s `All_evals`): the bundle of
//! evaluations carried in a proof statement and consumed by
//! `finalize_other_proof` — `ft(zeta*omega)`, the public-input polynomial
//! evaluated at both points, and every column evaluated at both points (each a
//! chunked array).
//!
//! We reuse kimchi's [`ProofEvaluations`] / [`PointEvaluations`] as the
//! underlying `Evals` type instead of re-porting the (large) OCaml `Evals`
//! record.

use kimchi::proof::{PointEvaluations, ProofEvaluations};

/// The public-input and column evaluations at a single evaluation point.
pub struct PointEvals<F> {
    /// The public-input polynomial evaluated at this point (chunked).
    pub public_input: Vec<F>,
    /// Every column evaluated at this point (chunked).
    pub evals: ProofEvaluations<Vec<F>>,
}

/// `All_evals`: `ft_eval1`, plus the public-input and column evaluations at
/// `zeta` and `zeta*omega` (each chunked).
pub struct AllEvals<F> {
    /// `ft(zeta * omega)`.
    pub ft_eval1: F,
    /// The public-input polynomial at `zeta` and `zeta*omega` (chunked).
    pub public_input: PointEvaluations<Vec<F>>,
    /// Every column's `PointEvaluations` (at `zeta` and `zeta*omega`, chunked).
    pub evals: ProofEvaluations<PointEvaluations<Vec<F>>>,
}

impl<F: Clone> AllEvals<F> {
    /// Splits the paired evaluations into the two evaluation points
    /// (`All_evals.With_public_input.In_circuit.factor`): the first component
    /// holds everything evaluated at `zeta`, the second at `zeta*omega`.
    pub fn factor(&self) -> (PointEvals<F>, PointEvals<F>) {
        let at_zeta = PointEvals {
            public_input: self.public_input.zeta.clone(),
            evals: self.evals.map_ref(&|pe| pe.zeta.clone()),
        };
        let at_zetaw = PointEvals {
            public_input: self.public_input.zeta_omega.clone(),
            evals: self.evals.map_ref(&|pe| pe.zeta_omega.clone()),
        };
        (at_zeta, at_zetaw)
    }
}

impl<F: Clone> AllEvals<F> {
    /// Builds an [`AllEvals`] from a kimchi proof's column evaluations, the
    /// public-input evaluations (`o.public_evals`, in `[at_zeta, at_zetaw]`
    /// order) and `ft_eval1`.
    pub fn from_parts(
        evals: ProofEvaluations<PointEvaluations<Vec<F>>>,
        public_evals: [Vec<F>; 2],
        ft_eval1: F,
    ) -> Self {
        let [zeta, zeta_omega] = public_evals;
        Self {
            ft_eval1,
            public_input: PointEvaluations { zeta, zeta_omega },
            evals,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::{commitment::PolyComm, ipa::OpeningProof, SRS};
    use snarky::{api::SnarkyCircuit, loc, FieldVar, RunState, SnarkyResult};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

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

    /// `factor` on a real proof splits into the per-point evaluations that match
    /// the raw proof column values at zeta / zeta*omega.
    #[test]
    fn factor_matches_proof_evals() {
        use ark_ff::One;
        let mut pi = SmallCircuit {}.compile_to_indexes().unwrap().0;
        let vi = SmallCircuit {}.compile_to_indexes().unwrap().1;
        let vi = &vi.index;
        let x = Fp::from(3u64);
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

        let all = AllEvals::from_parts(proof.evals.clone(), o.public_evals.clone(), proof.ft_eval1);
        let (at_zeta, at_zetaw) = all.factor();

        // public input split
        assert_eq!(at_zeta.public_input, o.public_evals[0]);
        assert_eq!(at_zetaw.public_input, o.public_evals[1]);

        // a couple of columns: the factored zeta/zetaw evals equal the proof's
        assert_eq!(at_zeta.evals.z, proof.evals.z.zeta);
        assert_eq!(at_zetaw.evals.z, proof.evals.z.zeta_omega);
        assert_eq!(at_zeta.evals.w[0], proof.evals.w[0].zeta);
        assert_eq!(at_zetaw.evals.w[0], proof.evals.w[0].zeta_omega);
        assert_eq!(
            at_zeta.evals.generic_selector,
            proof.evals.generic_selector.zeta
        );
        assert_eq!(all.ft_eval1, proof.ft_eval1);
    }
}

//! Merkle tree gadgets, the port of the checked part of the OCaml
//! `src/base/merkle_tree.ml`.
//!
//! The in-circuit hash is the Poseidon gadget (`hash(l, r)` is the first
//! component of the permutation of `[l, r, 0]`), so the out-of-circuit
//! counterpart of these gadgets is `mina_poseidon`'s block cipher with the
//! kimchi parameters.

use std::borrow::Cow;

use ark_ff::PrimeField;

use crate::{Boolean, FieldVar, RunState, SnarkyResult};

/// Hashes two children into their parent node.
pub fn hash_node<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    left: FieldVar<F>,
    right: FieldVar<F>,
) -> FieldVar<F> {
    let (hash, _) = sys.poseidon(loc, (left, right));
    hash
}

/// Computes the root implied by a leaf, its position (as little-endian
/// address bits: `address[0]` decides at the leaf level) and the sibling
/// hashes along the path (leaf level first).
///
/// # Panics
///
/// Panics if `address` and `path` have different lengths.
pub fn implied_root<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    leaf: &FieldVar<F>,
    address: &[Boolean<F>],
    path: &[FieldVar<F>],
) -> SnarkyResult<FieldVar<F>> {
    assert_eq!(
        address.len(),
        path.len(),
        "implied_root: address and path must have the same depth"
    );
    let mut acc = leaf.clone();
    for (is_right, sibling) in address.iter().zip(path) {
        // if the node is the right child, the sibling is on the left
        let left = sys.if_(loc.clone(), is_right.clone(), sibling.clone(), acc.clone())?;
        let right = sys.if_(loc.clone(), is_right.clone(), acc, sibling.clone())?;
        acc = hash_node(sys, loc.clone(), left, right);
    }
    Ok(acc)
}

/// Asserts that a leaf belongs to the Merkle tree with the given root.
pub fn check_membership<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    root: &FieldVar<F>,
    leaf: &FieldVar<F>,
    address: &[Boolean<F>],
    path: &[FieldVar<F>],
) -> SnarkyResult<()> {
    let implied = implied_root(sys, loc.clone(), leaf, address, path)?;
    implied.assert_equals(sys, loc, root)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{api::SnarkyCircuit, loc};
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        permutation::poseidon_block_cipher,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { crate::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { crate::FULL_ROUNDS }>;

    const DEPTH: usize = 3;

    /// The out-of-circuit hash matching [hash_node].
    fn hash(l: Fp, r: Fp) -> Fp {
        let params = Vesta::sponge_params();
        let mut state = vec![l, r, Fp::from(0u64)];
        poseidon_block_cipher::<Fp, PlonkSpongeConstantsKimchi, { crate::FULL_ROUNDS }>(
            params, &mut state,
        );
        state[0]
    }

    /// A reference Merkle tree over 2^DEPTH leaves.
    /// Returns (root, per-leaf authentication paths).
    fn build_tree(leaves: &[Fp]) -> (Fp, Vec<Vec<Fp>>) {
        assert_eq!(leaves.len(), 1 << DEPTH);
        let mut levels = vec![leaves.to_vec()];
        while levels.last().unwrap().len() > 1 {
            let prev = levels.last().unwrap();
            let next: Vec<Fp> = prev.chunks(2).map(|lr| hash(lr[0], lr[1])).collect();
            levels.push(next);
        }
        let root = levels.last().unwrap()[0];

        let paths = (0..leaves.len())
            .map(|leaf_idx| {
                let mut idx = leaf_idx;
                let mut path = Vec::with_capacity(DEPTH);
                for level in &levels[..DEPTH] {
                    path.push(level[idx ^ 1]);
                    idx /= 2;
                }
                path
            })
            .collect();
        (root, paths)
    }

    struct TestCircuit {}

    impl SnarkyCircuit for TestCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { crate::FULL_ROUNDS }>;

        /// (leaf, address bits (little-endian), path)
        type PrivateInput = (Fp, [bool; DEPTH], [Fp; DEPTH]);
        /// The root.
        type PublicInput = FieldVar<Fp>;
        type PublicOutput = ();

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            root: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let leaf: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0)?;
            let address: [Boolean<Fp>; DEPTH] = sys.compute(loc!(), |_| private.unwrap().1)?;
            let path: [FieldVar<Fp>; DEPTH] = sys.compute(loc!(), |_| private.unwrap().2)?;

            check_membership(sys, loc!(), &root, &leaf, &address, &path)
        }
    }

    #[test]
    fn snarky_merkle_membership() {
        let leaves: Vec<Fp> = (0..1 << DEPTH).map(|i| Fp::from(100 + i as u64)).collect();
        let (root, paths) = build_tree(&leaves);

        let test_circuit = TestCircuit {};
        let (mut prover_index, verifier_index) = test_circuit.compile_to_indexes().unwrap();

        for leaf_idx in [0usize, 3, 7] {
            let address = std::array::from_fn(|i| (leaf_idx >> i) & 1 == 1);
            let path: [Fp; DEPTH] = paths[leaf_idx].clone().try_into().unwrap();

            let private_input = (leaves[leaf_idx], address, path);
            let (proof, _) = prover_index
                .prove::<BaseSponge, ScalarSponge>(root, private_input, true)
                .unwrap();

            verifier_index.verify::<BaseSponge, ScalarSponge>(proof, root, ());
        }
    }

    #[test]
    #[should_panic]
    fn snarky_merkle_wrong_leaf_panics() {
        let leaves: Vec<Fp> = (0..1 << DEPTH).map(|i| Fp::from(100 + i as u64)).collect();
        let (root, paths) = build_tree(&leaves);

        let test_circuit = TestCircuit {};
        let (mut prover_index, _) = test_circuit.compile_to_indexes().unwrap();

        let leaf_idx = 2usize;
        let address = std::array::from_fn(|i| (leaf_idx >> i) & 1 == 1);
        let path: [Fp; DEPTH] = paths[leaf_idx].clone().try_into().unwrap();

        // wrong leaf value
        let private_input = (Fp::from(999u64), address, path);
        let _ = prover_index
            .prove::<BaseSponge, ScalarSponge>(root, private_input, true)
            .unwrap();
    }
}

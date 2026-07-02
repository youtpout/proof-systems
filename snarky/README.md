# Snarky (Rust)

Snarky is a DSL for writing zero-knowledge circuits, used as the front end to
the [kimchi](../kimchi) proof system. It is the Rust port of the OCaml
[snarky](https://github.com/o1-labs/snarky) library (only the non-legacy parts:
the `src/base` core and the gadget libraries — the libsnark-era backends were
not ported).

## Usage

Implement the [`SnarkyCircuit`] trait to describe your circuit, then compile it
to a prover and verifier index:

```rust,ignore
use snarky::prelude::*;

struct MyCircuit {}

impl SnarkyCircuit for MyCircuit {
    type Curve = Vesta;
    type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;

    type PrivateInput = Fp;
    type PublicInput = FieldVar<Fp>;
    type PublicOutput = ();

    fn circuit(
        &self,
        sys: &mut RunState<Fp>,
        public: Self::PublicInput,
        private: Option<&Self::PrivateInput>,
    ) -> SnarkyResult<Self::PublicOutput> {
        // witness a value
        let x: FieldVar<Fp> = sys.compute(loc!(), |_| *private.unwrap())?;
        // constrain it: x * x = public
        sys.assert_r1cs(None, loc!(), x.clone(), x, public)?;
        Ok(())
    }
}

let (mut prover_index, verifier_index) = MyCircuit {}.compile_to_indexes()?;
let (proof, output) = prover_index.prove::<BaseSponge, ScalarSponge>(pub_in, priv_in, false)?;
verifier_index.verify::<BaseSponge, ScalarSponge>(proof, pub_in, *output);
```

See `src/tests.rs` and the `tests/` directory (including a port of the OCaml
`fermat.ml` example) for complete examples.

## Contents

- `FieldVar` (the OCaml `Cvar`): circuit variables as linear combinations;
- `SnarkyType` (the OCaml `Typ`): maps Rust types to circuit variables, with a
  `#[derive(SnarkyType)]` macro in [`snarky-deriver`](./deriver);
- `Boolean`: boolean variables and logic;
- `RunState`: circuit compilation and witness generation
  (the OCaml `Checked` runner, imperative `Snark.Run` style);
- `gadgets/`: ports of the OCaml gadget libraries —
  `bits` (un/packing, comparison), `number` & `integer` (bounded arithmetic),
  `sponge` (Poseidon duplex), `curve` (complete EC ops on kimchi gates),
  `group_map` (hash-to-curve), `merkle_tree` (membership proofs);
- in-circuit Poseidon and 3x88-bit range checks using kimchi's custom gates.

The port status, the differences with the OCaml API and the backlog are
tracked in [CLAUDE.md](./CLAUDE.md).

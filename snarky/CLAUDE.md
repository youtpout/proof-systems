# snarky (Rust) — Integration progress tracker

Rust port of the OCaml [snarky](https://github.com/o1-labs/snarky) circuit-writing
DSL, integrated into the proof-systems workspace as the `snarky` crate (plus the
`snarky-deriver` proc-macro crate in `snarky/deriver`).

## Audit principle — fidelity to OCaml

This code will be audited and must correspond as closely as possible to the
base OCaml source (`~/Projects/snarky`, `src/base` + `src/intf`; and the mina
`plonk_constraint_system.ml`). **Any change that brings the code closer to the
OCaml structure and is NEUTRAL (no test regression, no change in gate counts)
should still be committed** — fidelity to the OCaml source is a value in
itself for auditability, not only gate-parity optimisation. Do not reject a
"faithful but gate-neutral" refactor: commit it with a message stating it
aligns the structure on the OCaml without gate effect. Always confirm no
regression (`cargo test -p snarky`, and downstream `pickles` recorded 9/9:
N0/N1/N2). This is especially important for the constraint-emission order,
reductions and the double-generic pairing, where matching OCaml exactly is
what closes gate-parity gaps downstream (pickles wrap circuit).

## Origin

- The core of this crate is the snarky DSL that used to live in
  `kimchi/src/snarky/` and was deleted in commit `cb7484542c`
  ("Kimchi: Remove snarky", May 2025). Files were restored with
  `git show cb7484542c^:kimchi/src/snarky/<file>`.
- `runner.rs` and `constraint_system.rs` were still on disk (dead code,
  no longer compiled by kimchi) and were `git mv`ed here.
- `kimchi/snarky-deriver` (orphaned, not in the workspace) was moved to
  `snarky/deriver` and re-pointed from `::kimchi` to `::snarky`.
- OCaml reference: `~/Projects/snarky` (see its README: everything under
  `src/` is legacy libsnark-era code EXCEPT `src/intf` and `src/base`).
- Mina usage reference: `~/Projects/mina` (`Pickles.Impls.Step`,
  `transaction_snark`) — Mina consumes snarky through the imperative
  `Snark.Run` API, which is what this crate reproduces.

## Port status

| OCaml source | Rust module | Status | Test |
|---|---|---|---|
| `src/base/cvar.ml` | `src/cvar.rs` (`FieldVar`) | resurrected | via all circuit tests |
| `src/base/checked*.ml`, `run_state.ml`, `runners.ml` | `src/runner.rs` (`RunState`) | moved (dead file) + FULL_ROUNDS fix | `tests::test_simple_circuit` |
| `src/base/constraint_system.ml` + mina `plonk_constraint_system.ml` | `src/constraint_system.rs` | moved (dead file) + 2 bug fixes (see below) | `constraint_system::tests` |
| `src/base/typ.ml` | `src/snarky_type.rs` (`SnarkyType`) + `deriver/` | resurrected; 3-tuple impl added | `tests/derive.rs` |
| `src/base/boolean.ml` | `src/boolean.rs` | resurrected (already had xor/any/all) | via circuit tests |
| `src/base/as_prover.ml`, `request.ml`, `handle.ml` | — | **by design**: replaced by witness closures (`RunState::compute`) + `PrivateInput` | — |
| `src/base/snark0.ml`, `snark_intf.ml` (Run API) | `src/api.rs` (`SnarkyCircuit`) | resurrected + kimchi API drift fixes | all `compile_to_indexes` tests |
| `Field.Checked.unpack/choose_preimage/compare`, `Field.Var.pack/project` | `src/gadgets/bits.rs` | **new** | `gadgets::bits::tests` |
| `src/base/number.ml` | `src/gadgets/number.rs` | **new** (2 upstream bugs fixed, see notes) | `gadgets::number::tests` |
| `snarky_integer/integer.ml` | `src/gadgets/integer.rs` | **new** | `gadgets::integer::tests` |
| `sponge/sponge.ml` | `src/poseidon.rs` (`DuplexState`) re-exported by `src/gadgets/sponge.rs` | resurrected + successors bug fix | `gadgets::sponge::tests` (matches `mina_poseidon` out-of-circuit) |
| `snarky_curve/snarky_curve.ml` | `src/gadgets/curve.rs` | **new** (uses kimchi `CompleteAdd` gate) | `gadgets::curve::tests` (matches ark-ec) |
| `group_map/` + mina `snarky_group_map/checked_map.ml` | `src/gadgets/group_map.rs` | **new** (mirrors the Rust `groupmap` crate SvdW formulas) | `gadgets::group_map::tests` (matches `groupmap::to_group`) |
| `src/base/merkle_tree.ml` (checked part) | `src/gadgets/merkle_tree.rs` | **new** | `gadgets::merkle_tree::tests` |
| `src/tests/fermat.ml` | `tests/fermat.rs` | ported (cube-root trick adapted: Pasta has p ≡ 1 mod 3, p ≡ 4 mod 9 → cbrt = `c^((2p+1)/9)`) | `tests/fermat.rs` |
| kimchi range checks (no OCaml equivalent) | `src/range_checks.rs` | resurrected, made `pub` | `range_checks::test` |
| `src/base/pedersen.ml` | — | **skipped** (obsolete; Mina hashes with Poseidon) | — |
| `snarky_signature/` | — | **deferred** (needs scalar-field arithmetic gadgets; backlog) | — |
| `snarkette/`, `src/` C++ libsnark bindings, monadic `Checked` | — | **skipped** (replaced by arkworks / mina-curves / kimchi) | — |
| deleted `folding.rs` | — | **skipped** (depended on the removed `folding` crate) | — |

## API deltas vs OCaml

- Imperative Run-style only (`&mut RunState<F>` + `loc!()`), no `Checked` monad.
- `As_prover`/`Request` are subsumed by `RunState::compute` closures and the
  `SnarkyCircuit::PrivateInput` associated type.
- `FULL_ROUNDS` is fixed crate-wide to the kimchi sponge
  (`snarky::FULL_ROUNDS = mina_poseidon::pasta::FULL_ROUNDS = 55`) instead of
  threading kimchi's const generic through every type — the OCaml snarky is
  kimchi-only anyway.
- std-only for now (backtraces in errors.rs); no attempt to follow kimchi's
  no_std support.

## Bitrot fixed during resurrection (kimchi API drift)

- `ArithmeticSpongeParams`, `KimchiCurve`, `FqSponge`, `OpenProof`,
  `ProverIndex`/`VerifierIndex`/`ProverProof`, `verifier::verify` all gained a
  `FULL_ROUNDS` const generic → fixed to `crate::FULL_ROUNDS`.
- `ProverIndex` third type param is now the SRS (not the OpenProof);
  `ProverIndex::create` takes a new `lazy_mode: bool` arg (passed `false`).
- `mina_poseidon::permutation::full_round` was made `pub` again (was
  `pub(crate)`), needed by the round-by-round poseidon gadget.
- `Circuit::generate_asm` could no longer be an inherent impl (foreign type) →
  extension trait `asm::Asm`.
- kimchi's `loc!` now expands to `::alloc::…` → snarky defines its own std
  `loc!`.

## Genuine bugs found and fixed (were in the resurrected/orphaned code)

1. `constraint_system.rs reduce_to_var`: the `constant`/`lincom` arguments of
   `create_internal` were crossed between the two branches (scaled-var passed
   `Some(s)`, constant passed `None`), producing witness values `s + s*x` and
   `0` instead of `s*x` and `s`. Verified against mina's
   `plonk_constraint_system.ml`.
2. `poseidon.rs`: `iter::successors` computes one successor past the last item
   taken → applied an out-of-bounds 56th round (masked by `Vec` params before
   the arrays refactor). Rewritten as an explicit loop.
3. `deriver`: generated `to_cvars` never pushed the field cvars into the
   result vector; generated `check` used a pre-`loc` trait signature.
4. `number.ml` upstream bugs not reproduced: `div_pow_2` under-estimated the
   upper bound (division applied twice), and `mod_pow_2`'s interval-checked
   subtraction spuriously underflowed — `mod_pow_2` now packs the low bits
   directly.

## Backlog

- No current snarky blocker for the Pickles base-case and first recursive-step
  path: Poseidon, field vars, booleans, curve/group-map gadgets, typ derivation
  and kimchi proving API are sufficient for the validated Pickles tests.
- Pickles-driven leftovers in snarky are mostly quality/coverage work: broader
  `SnarkyType` shapes if the generic Pickles API needs them, better doc tests,
  and keeping the low-level gadgets layout-stable as Pickles moves from the
  harness to a public compile/prove API.
- Signature verification gadget (`snarky_signature`) — needs curve scalar ops.
- Efficient scalar multiplication using kimchi's `VarBaseMul`/endomorphism
  gates (current `gadgets::curve::scale` is naive double-and-add with a
  constant shift, and cannot represent an identity result in affine coords).
- `no_std` support.
- Wire `snarky/deriver` doc examples into rustdoc tests.
- Consider exposing `ocaml_types` conversions end-to-end (feature exists,
  never compiled in CI).

## Verification

```sh
cargo build -p snarky
cargo test -p snarky            # 15 lib tests + 3 derive + 3 fermat
cargo clippy -p snarky -p snarky-deriver --all-targets -- -D warnings
cargo build --workspace         # make sure kimchi & friends still build
```

# Kimchi

[![codecov](https://codecov.io/gh/o1-labs/proof-systems/graph/badge.svg?token=pl6W1FDfV0)](https://codecov.io/gh/o1-labs/proof-systems)

[![CI](https://github.com/o1-labs/proof-systems/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/o1-labs/proof-systems/actions/workflows/ci.yml)
[![CI nightly](https://github.com/o1-labs/proof-systems/actions/workflows/ci-nightly.yml/badge.svg?branch=master)](https://github.com/o1-labs/proof-systems/actions/workflows/ci-nightly.yml)
[![GitHub page](https://github.com/o1-labs/proof-systems/actions/workflows/gh-page.yml/badge.svg?branch=master)](https://github.com/o1-labs/proof-systems/actions/workflows/gh-page.yml)
[![o1vm CI](https://github.com/o1-labs/proof-systems/actions/workflows/o1vm-ci.yml/badge.svg?branch=master)](https://github.com/o1-labs/proof-systems/actions/workflows/o1vm-ci.yml)

[![dependency status](https://deps.rs/repo/github/o1-labs/proof-systems/status.svg?style=flat-square)](https://deps.rs/repo/github/o1-labs/proof-systems)

This repository contains **kimchi**, a general-purpose zero-knowledge proof
system for proving the correct execution of programs.

You can read more about this project on the
[Kimchi book](https://o1-labs.github.io/proof-systems), or for a lighter
introduction in this
[blogpost](https://minaprotocol.com/blog/kimchi-the-latest-update-to-minas-proof-system).

[See here for the rust documentation](https://o1-labs.github.io/proof-systems/rustdoc).

## User Warning

This project comes as is. We provide no guarantee of stability or support, as
the crates closely follow the needs of the
[Mina](<[https://](https://github.com/minaprotocol/mina)>) project.

If you use this project in a production environment, it is your responsibility
to perform a security audit to ensure that the software meets your requirements.

## Performance

At the time of this writing:

### Proving time

| number of gates | seconds |
| :-------------: | :-----: |
|      2^11       |  0.6s   |
|      2^15       |  3.3s   |
|      2^16       |  6.3s   |

### Verification time

| number of gates | seconds |
| :-------------: | :-----: |
|      2^15       |  0.1s   |
|      2^16       |  0.1s   |

### Proof size

| number of gates | bytes |
| :-------------: | :---: |
|      2^15       | 4947  |
|      2^16       | 5018  |

## Organization

The project is organized in the following way:

- [book/](book/). The mina book, RFCs, and specifications.
  [Available here in HTML](https://o1-labs.github.io/proof-systems).
- [curves/](curves/). The elliptic curves we use (for now just the pasta
  curves).
- [groupmap/](groupmap/). Used to convert elliptic curve elements to field
  elements.
- [hasher/](hasher/). Interfaces for mina hashing.
- [kimchi/](kimchi/). Our proof system based on PLONK.
- [poly-commitment/](poly-commitment/). Polynomial commitment code.
- [poseidon/](poseidon/). Implementation of the poseidon hash function.
- [signer/](signer/). Interfaces for mina signature schemes.
- [tools/](tools/). Various tooling to help us work on kimchi.
- [utils/](utils/). Collection of useful functions and traits.

This fork additionally hosts the pure-Rust recursion stack that replaces the
OCaml/`js_of_ocaml` proving backend in o1js:

- [snarky/](snarky/). The Rust constraint-system DSL (`SnarkyCircuit`,
  `RunState`) and gadgets (Poseidon/sponge, curve, group map, bits, Merkle),
  gate-for-gate compatible with Mina's `plonk_constraint_system.ml`.
- [pickles/](pickles/). The Rust port of Pickles (step/wrap circuits,
  incremental verification, side-loaded keys). This is the crate under active
  gate-level parity work against the jsoo reference.
- [kimchi-napi/](kimchi-napi/). Node N-API bindings that expose the prover and
  the constraint system to JavaScript.
- [kimchi-wasm/](kimchi-wasm/). WebAssembly bindings for the browser.

## Building the Rust proof-system backend

These crates are the bottom layer of the new o1js proving stack:

```text
o1js  ->  mina-runtime (mina-rust)  ->  proof-systems (this repo)
```

### Toolchain

The workspace pins its Rust version in [`rust-toolchain.toml`](rust-toolchain.toml)
(currently stable `1.92`); `rustup` selects it automatically. The WebAssembly
targets additionally require the nightly toolchain declared in the
[`Makefile`](Makefile) (`NIGHTLY_RUST_VERSION`, currently
`nightly-2025-12-11`) with the `wasm32-unknown-unknown` target.

### Prover crates (native)

Build and test the recursion crates directly:

```sh
# Constraint system DSL and gadgets
cargo build -p snarky --release
cargo test  -p snarky --release

# Pickles (step/wrap recursion)
cargo build -p pickles --release
cargo test  -p pickles --release --lib            # unit tests (101)
cargo test  -p pickles --release --test recorded  # end-to-end N0/N1/N2 (9)
```

### Node bindings (`kimchi-napi`)

o1js drives this build through its own `build:native` script (see the
"Building the Rust proof-system backend" section of the o1js `README-dev.md`),
which invokes:

```sh
napi build --manifest-path Cargo.toml --package kimchi-napi \
  --output-dir <out> --release --esm
```

You can also build the crate on its own with
`cargo build -p kimchi-napi --release`. Node ≥ 22 is required for
`@napi-rs/cli` 3.x.

### Browser bindings (`kimchi-wasm`)

```sh
make build-nodejs   # WebAssembly for Node   -> target/nodejs
make build-web      # WebAssembly for the browser -> target/web
```

Both targets shell out to the nightly toolchain and `wasm-bindgen`; run
`rustup target add wasm32-unknown-unknown` first if it is not installed.

## Contributing

Check [CONTRIBUTING.md](CONTRIBUTING.md) if you are interested in contributing
to this project.

## Generate rustdoc locally

An effort is made to have the documentation being self-contained, referring to
the mina book for more details when necessary. You can build the rust
documentation with

<!-- This must be the same than the content in .github/workflows/gh-page.yml -->

```shell
rustup install nightly
RUSTDOCFLAGS="--enable-index-page -Zunstable-options" cargo +nightly doc --all --no-deps
```

You can visualize the documentation by opening the file `target/doc/index.html`.

## CI

<!-- Please update this section if you add more workflows -->

- [CI](.github/workflows/ci.yml). This workflow ensures that the entire project
  builds correctly, adheres to guidelines, and passes all necessary tests.
- [Nightly tests with the code coverage](.github/workflows/ci-nightly.yml). This
  workflow runs all the tests per scheduler or on-demand, generates and attaches
  the code coverage report to the job's execution results.
- [Benchmarks](.github/workflows/benches.yml). This workflow runs benchmarks
  when a pull request is labeled with "benchmark." It sets up the Rust and OCaml
  environments, installs necessary tools, and executes cargo criterion
  benchmarks on the kimchi crate. The benchmark results are then posted as a
  comment on the pull request for review.
- [Deploy Specifications & Docs to GitHub Pages](.github/workflows/gh-page.yml).
  When CI passes on master, the documentation built from the rust code will be
  available by this [link](https://o1-labs.github.io/proof-systems/rustdoc) and
  the book will be available by this
  [link](https://o1-labs.github.io/proof-systems).
- [MIPS Build and Package](.github/workflows/o1vm-upload-mips-build.yml) This
  workflow runs the assembler and linker on the programs from the OpenMips test
  suite, and provides a link where you can download the artifacts (recommended
  if you don't have / can't install the required MIPS tooling). This workflow
  also runs the o1vm ELF parser on the artifacts to check that our parsing is
  working. Currently it is run via manual trigger only -- you can find the
  trigger in the
  [GitHub actions tab](https://github.com/o1-labs/proof-systems/actions/workflows/mips-build.yml)
  and the link to the artifacts will appear in logs of the `Upload Artifacts`
  stage.

## Nix for Dependencies (WIP)

If you have `nix` installed and in particular, `flakes` enabled, you can install
the dependencies for these projects using nix. Simply `nix develop .` inside
this directory to bring into scope `rustup`, `opam`, and `go` (along with a few
other tools). You will have to manage the toolchains yourself using `rustup` and
`opam`, in the current iteration.

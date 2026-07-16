//! The main interface to using Snarky.
//!
//! To use Snarky, simply implements the [SnarkyCircuit] trait.

use core::marker::PhantomData;

use groupmap::GroupMap;
use kimchi::{
    circuits::{
        constraints::{ConstraintSystem, ZK_ROWS_BY_DEFAULT},
        gate::CircuitGate,
        polynomial::COLUMNS,
        wires::{Wire, WIRES},
    },
    curve::KimchiCurve,
    plonk_sponge::FrSponge,
    proof::ProverProof,
    prover_index::ProverIndex,
    verifier::verify,
    verifier_index::VerifierIndex,
};
use mina_poseidon::{poseidon::ArithmeticSpongeParams, FqSponge};

use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use log::debug;
use poly_commitment::{commitment::CommitmentCurve, OpenProof, SRS};

use super::{asm::Asm, errors::SnarkyResult, runner::RunState, snarky_type::SnarkyType};
use crate::FULL_ROUNDS;

#[derive(Debug, Clone, Copy, Default)]
pub struct CompileProfile {
    pub lowering_micros: u64,
    pub constraint_system_micros: u64,
    pub lagrange_micros: u64,
    pub prover_index_micros: u64,
}

static LAST_COMPILE_PROFILE: std::sync::Mutex<CompileProfile> =
    std::sync::Mutex::new(CompileProfile {
        lowering_micros: 0,
        constraint_system_micros: 0,
        lagrange_micros: 0,
        prover_index_micros: 0,
    });
static COMPILE_PROFILE_HOOK: std::sync::Mutex<Option<fn(CompileProfile)>> =
    std::sync::Mutex::new(None);

pub fn last_compile_profile() -> CompileProfile {
    *LAST_COMPILE_PROFILE.lock().unwrap()
}

pub fn set_compile_profile_hook(hook: Option<fn(CompileProfile)>) {
    *COMPILE_PROFILE_HOOK.lock().unwrap() = hook;
}

fn record_compile_profile(profile: CompileProfile) {
    *LAST_COMPILE_PROFILE.lock().unwrap() = profile;
    if let Some(hook) = *COMPILE_PROFILE_HOOK.lock().unwrap() {
        hook(profile);
    }
}

/// A witness represents the execution trace of a circuit.
#[derive(Debug)]
pub struct Witness<F>(pub [Vec<F>; COLUMNS]);

//
// aliases
//

type ScalarField<C> = <C as AffineRepr>::ScalarField;
type BaseField<C> = <C as AffineRepr>::BaseField;

/// The SRS type associated to a circuit's proof.
type SrsOf<C> =
    <<C as SnarkyCircuit>::Proof as OpenProof<<C as SnarkyCircuit>::Curve, FULL_ROUNDS>>::SRS;

/// A prover index.
pub struct ProverIndexWrapper<Circuit>
where
    Circuit: SnarkyCircuit,
{
    compiled_circuit: CompiledCircuit<Circuit>,
    /// The underlying kimchi prover index.
    pub index: ProverIndex<FULL_ROUNDS, Circuit::Curve, SrsOf<Circuit>>,
}

type Proof<C> = ProverProof<<C as SnarkyCircuit>::Curve, <C as SnarkyCircuit>::Proof, FULL_ROUNDS>;
type Output<C> = <<C as SnarkyCircuit>::PublicOutput as SnarkyType<
    ScalarField<<C as SnarkyCircuit>::Curve>,
>>::OutOfCircuit;

impl<Circuit> ProverIndexWrapper<Circuit>
where
    Circuit: SnarkyCircuit,
{
    /// Reattaches a previously serialized Kimchi index to a freshly compiled
    /// Snarky witness generator. The exact constraint system is checked before
    /// the cached commitments are accepted, so cache data cannot substitute a
    /// different circuit.
    pub fn from_cached_index(
        circuit: Circuit,
        minimum_domain_log2: u32,
        index: ProverIndex<FULL_ROUNDS, Circuit::Curve, SrsOf<Circuit>>,
    ) -> Result<(Self, VerifierIndexWrapper<Circuit>), String>
    where
        <Circuit::Curve as AffineRepr>::BaseField: PrimeField,
    {
        let mut compiled_circuit = compile(circuit).map_err(|err| err.to_string())?;
        if minimum_domain_log2 > 0 {
            let target_domain_size = 1usize << minimum_domain_log2;
            let target_gate_count =
                target_domain_size - usize::try_from(ZK_ROWS_BY_DEFAULT).unwrap();
            if compiled_circuit.gates.len() < target_gate_count {
                let pad = target_gate_count - compiled_circuit.gates.len();
                compiled_circuit.gates.extend(
                    (compiled_circuit.gates.len()..target_gate_count).map(|row| {
                        CircuitGate::zero(std::array::from_fn(|column| Wire {
                            row,
                            col: WIRES[column],
                        }))
                    }),
                );
                compiled_circuit
                    .gate_labels
                    .extend(std::iter::repeat_with(String::new).take(pad));
            }
        }
        let expected_cs = ConstraintSystem::create(compiled_circuit.gates.clone())
            .public(compiled_circuit.public_input_size)
            .prev_challenges(Circuit::PREV_CHALLENGES)
            .build()
            .map_err(|err| format!("failed to rebuild cached constraint system: {err}"))?;
        if index.cs.public != expected_cs.public
            || index.cs.prev_challenges != expected_cs.prev_challenges
            || index.cs.domain.d1.log_size_of_group != expected_cs.domain.d1.log_size_of_group
            || index.cs.domain.d1.group_gen != expected_cs.domain.d1.group_gen
            || index.cs.gates != expected_cs.gates
        {
            return Err("cached prover index does not match the compiled circuit".into());
        }
        if minimum_domain_log2 > 0 && index.cs.domain.d1.log_size_of_group < minimum_domain_log2 {
            return Err("cached prover index has a smaller domain than requested".into());
        }
        let verifier_index = index.verifier_index();
        Ok((
            Self {
                compiled_circuit,
                index,
            },
            VerifierIndexWrapper {
                index: verifier_index,
            },
        ))
    }

    /// Debug-only: per-gate emission labels aligned 1:1 with the compiled
    /// gates (and hence with `self.index.cs.gates`), for parity tooling.
    pub fn gate_labels(&self) -> &[String] {
        &self.compiled_circuit.gate_labels
    }

    /// Produces an assembly-like encoding of the circuit.
    pub fn asm(&self) -> String {
        kimchi::circuits::gate::Circuit::new(
            self.compiled_circuit.public_input_size,
            &self.compiled_circuit.gates,
        )
        .generate_asm()
    }

    /// Produces a proof for the given public input.
    /// Like [`Self::prove`], but with previous recursion challenges — the
    /// polynomial commitments and challenges of accumulated proofs, which the
    /// prover folds into the opening (pickles' `sg_old`).
    pub fn prove_with_recursion<EFqSponge, EFrSponge>(
        // TODO: this should not be mutable ideally
        &mut self,
        public_input: <Circuit::PublicInput as SnarkyType<ScalarField<Circuit::Curve>>>::OutOfCircuit,
        private_input: Circuit::PrivateInput,
        // TODO: rename to verify_witness?
        debug: bool,
        prev_challenges: Vec<kimchi::proof::RecursionChallenge<Circuit::Curve>>,
    ) -> SnarkyResult<(Proof<Circuit>, Box<Output<Circuit>>)>
    where
        <Circuit::Curve as AffineRepr>::BaseField: PrimeField,
        EFqSponge: Clone
            + FqSponge<
                BaseField<Circuit::Curve>,
                Circuit::Curve,
                ScalarField<Circuit::Curve>,
                FULL_ROUNDS,
            >,
        EFrSponge: FrSponge<ScalarField<Circuit::Curve>>,
        EFrSponge: From<&'static ArithmeticSpongeParams<ScalarField<Circuit::Curve>, FULL_ROUNDS>>,
    {
        self.prove_with_recursion_mask::<EFqSponge, EFrSponge>(
            public_input,
            private_input,
            debug,
            prev_challenges,
            None,
        )
    }

    /// Like [`Self::prove_with_recursion`], but with Pickles' optional
    /// accumulator mask for previous recursion challenges.
    pub fn prove_with_recursion_mask<EFqSponge, EFrSponge>(
        // TODO: this should not be mutable ideally
        &mut self,
        public_input: <Circuit::PublicInput as SnarkyType<ScalarField<Circuit::Curve>>>::OutOfCircuit,
        private_input: Circuit::PrivateInput,
        // TODO: rename to verify_witness?
        debug: bool,
        prev_challenges: Vec<kimchi::proof::RecursionChallenge<Circuit::Curve>>,
        prev_challenges_mask: Option<&[bool]>,
    ) -> SnarkyResult<(Proof<Circuit>, Box<Output<Circuit>>)>
    where
        <Circuit::Curve as AffineRepr>::BaseField: PrimeField,
        EFqSponge: Clone
            + FqSponge<
                BaseField<Circuit::Curve>,
                Circuit::Curve,
                ScalarField<Circuit::Curve>,
                FULL_ROUNDS,
            >,
        EFrSponge: FrSponge<ScalarField<Circuit::Curve>>,
        EFrSponge: From<&'static ArithmeticSpongeParams<ScalarField<Circuit::Curve>, FULL_ROUNDS>>,
    {
        kimchi::live_trace::checkpoint("snarky: prove begin");
        // create public input
        let public_input_without_output =
            Circuit::PublicInput::value_to_field_elements(&public_input).0;

        // init
        self.compiled_circuit
            .sys
            .generate_witness_init(public_input_without_output.clone())?;

        // run circuit and get return var
        let public_input_var: Circuit::PublicInput = self.compiled_circuit.sys.public_input();
        let return_var = self.compiled_circuit.circuit.circuit(
            &mut self.compiled_circuit.sys,
            public_input_var,
            Some(&private_input),
        )?;

        // get values from private input vec
        let (return_cvars, aux) = return_var.to_cvars();
        let mut public_output_values = vec![];
        for cvar in &return_cvars {
            public_output_values.push(cvar.eval(&self.compiled_circuit.sys));
        }

        // create constraint between public output var and return var
        {
            // Note: since the values of the public output part are set to zero at this point,
            // let's also avoid checking the wiring (which would fail)
            let eval_constraints = self.compiled_circuit.sys.eval_constraints;
            self.compiled_circuit.sys.eval_constraints = false;

            self.compiled_circuit.sys.wire_public_output(return_var)?;

            self.compiled_circuit.sys.eval_constraints = eval_constraints;
        }

        // finalize
        let mut witness = self.compiled_circuit.sys.generate_witness();

        // replace public output part of witness
        let start = Circuit::PublicInput::SIZE_IN_FIELD_ELEMENTS;
        let end = start + Circuit::PublicOutput::SIZE_IN_FIELD_ELEMENTS;
        for (cell, val) in &mut witness.0[0][start..end]
            .iter_mut()
            .zip(&public_output_values)
        {
            *cell = *val;
        }

        // same but with the full public input
        let mut public_input_and_output = public_input_without_output;
        public_input_and_output.extend(public_output_values.clone());

        // reconstruct public output
        let public_output =
            Circuit::PublicOutput::value_of_field_elements(public_output_values, aux);

        kimchi::live_trace::checkpoint("snarky: witness generated");
        // verify the witness
        // TODO: return error instead of panicking
        if debug {
            if std::env::var("SNARKY_DEBUG_WITNESS").is_ok() {
                witness.debug();
            }
            if let Err(err) = self.index.verify(&witness.0, &public_input_and_output) {
                eprintln!("[witness-debug] verify failed: {err:?}");
                let labels = self.gate_labels();
                let gates = &self.index.cs.gates;
                let dump = |row: usize| {
                    let typ = gates.get(row).map(|g| format!("{:?}", g.typ));
                    let coeffs = gates
                        .get(row)
                        .map(|g| g.coeffs.iter().map(ToString::to_string).collect::<Vec<_>>());
                    eprintln!(
                        "[witness-debug] row {row}: typ={typ:?} label={:?} coeffs={coeffs:?}",
                        labels.get(row)
                    );
                    for col in 0..15 {
                        eprintln!(
                            "[witness-debug]   w[{col}][{row}] = {}",
                            witness.0[col][row]
                        );
                    }
                };
                if let Ok(spec) = std::env::var("SNARKY_DEBUG_ROWS") {
                    for part in spec.split(',') {
                        if let Ok(row) = part.trim().parse::<usize>() {
                            dump(row);
                        }
                    }
                }
                panic!("witness verification failed: {err:?}");
            }
        }

        kimchi::live_trace::checkpoint("snarky: witness verified");
        // produce a proof
        let group_map = <Circuit::Curve as CommitmentCurve>::Map::setup();

        // TODO: return error instead of panicking
        let proof: Proof<Circuit> =
            ProverProof::create_recursive_with_recursion_mask::<EFqSponge, EFrSponge, _>(
                &group_map,
                witness.0,
                &[],
                &self.index,
                prev_challenges,
                prev_challenges_mask,
                None,
                &mut rand::rngs::OsRng,
            )
            .unwrap();

        // return proof + public output
        Ok((proof, Box::new(public_output)))
    }

    /// Produces a proof for the given public and private inputs.
    pub fn prove<EFqSponge, EFrSponge>(
        &mut self,
        public_input: <Circuit::PublicInput as SnarkyType<ScalarField<Circuit::Curve>>>::OutOfCircuit,
        private_input: Circuit::PrivateInput,
        debug: bool,
    ) -> SnarkyResult<(Proof<Circuit>, Box<Output<Circuit>>)>
    where
        <Circuit::Curve as AffineRepr>::BaseField: PrimeField,
        EFqSponge: Clone
            + FqSponge<
                BaseField<Circuit::Curve>,
                Circuit::Curve,
                ScalarField<Circuit::Curve>,
                FULL_ROUNDS,
            >,
        EFrSponge: FrSponge<ScalarField<Circuit::Curve>>,
        EFrSponge: From<&'static ArithmeticSpongeParams<ScalarField<Circuit::Curve>, FULL_ROUNDS>>,
    {
        self.prove_with_recursion::<EFqSponge, EFrSponge>(
            public_input,
            private_input,
            debug,
            vec![],
        )
    }
}

/// A verifier index.
pub struct VerifierIndexWrapper<Circuit>
where
    Circuit: SnarkyCircuit,
{
    /// The underlying kimchi verifier index.
    pub index: VerifierIndex<FULL_ROUNDS, Circuit::Curve, SrsOf<Circuit>>,
}

impl<Circuit> Clone for VerifierIndexWrapper<Circuit>
where
    Circuit: SnarkyCircuit,
{
    fn clone(&self) -> Self {
        Self {
            index: self.index.clone(),
        }
    }
}

impl<Circuit> VerifierIndexWrapper<Circuit>
where
    Circuit: SnarkyCircuit,
{
    /// Verify a proof for a given public input and public output.
    pub fn verify<EFqSponge, EFrSponge>(
        &self,
        proof: Proof<Circuit>,
        public_input: <Circuit::PublicInput as SnarkyType<ScalarField<Circuit::Curve>>>::OutOfCircuit,
        public_output: <Circuit::PublicOutput as SnarkyType<ScalarField<Circuit::Curve>>>::OutOfCircuit,
    ) where
        <Circuit::Curve as AffineRepr>::BaseField: PrimeField,
        EFqSponge: Clone
            + FqSponge<
                BaseField<Circuit::Curve>,
                Circuit::Curve,
                ScalarField<Circuit::Curve>,
                FULL_ROUNDS,
            >,
        EFrSponge: FrSponge<ScalarField<Circuit::Curve>>,
        EFrSponge: From<&'static ArithmeticSpongeParams<ScalarField<Circuit::Curve>, FULL_ROUNDS>>,
    {
        let mut public_input = Circuit::PublicInput::value_to_field_elements(&public_input).0;
        public_input.extend(Circuit::PublicOutput::value_to_field_elements(&public_output).0);

        // verify the proof
        let group_map = <Circuit::Curve as CommitmentCurve>::Map::setup();

        verify::<FULL_ROUNDS, Circuit::Curve, EFqSponge, EFrSponge, Circuit::Proof>(
            &group_map,
            &self.index,
            &proof,
            &public_input,
        )
        .unwrap()
    }
}

//
// Compilation
//

/// A compiled circuit.
// TODO: implement digest function
pub struct CompiledCircuit<Circuit>
where
    Circuit: SnarkyCircuit,
{
    /// The snarky circuit itself.
    circuit: Circuit,

    //// The state after compilation
    sys: RunState<ScalarField<Circuit::Curve>>,

    /// The public input size.
    // TODO: can't we get this from `circuit.public_input_size()`? (easy to implement). Or better, this could be a `Circuit` type that contains the gates as well (or the kimchi ConstraintSystem type)
    public_input_size: usize,

    /// The gates obtained after compilation.
    pub gates: Vec<CircuitGate<ScalarField<Circuit::Curve>>>,
    /// Debug-only: per-gate emission labels, aligned 1:1 with [`Self::gates`]
    /// (for parity tooling / dumps). Padding gates get an empty label.
    pub gate_labels: Vec<String>,
    phantom: PhantomData<Circuit>,
}

/// Compiles a circuit to a [CompiledCircuit].
fn compile<Circuit: SnarkyCircuit>(circuit: Circuit) -> SnarkyResult<CompiledCircuit<Circuit>> {
    // calculate public input size
    let public_input_size = Circuit::PublicInput::SIZE_IN_FIELD_ELEMENTS
        + Circuit::PublicOutput::SIZE_IN_FIELD_ELEMENTS;

    // create snarky constraint system
    let mut sys = RunState::new::<Circuit::Curve>(
        Circuit::PublicInput::SIZE_IN_FIELD_ELEMENTS,
        Circuit::PublicOutput::SIZE_IN_FIELD_ELEMENTS,
        true,
    );

    // run circuit and get return var
    let public_input: Circuit::PublicInput = sys.public_input();
    let return_var = circuit.circuit(&mut sys, public_input, None)?;

    // create constraint between public output var and return var
    // compile to gates
    // TODO: don't panic here, return an error

    let gates = sys.wire_output_and_compile(return_var).unwrap();
    let gates = gates.to_vec();
    let gate_labels = sys
        .system
        .as_ref()
        .map(|s| s.gate_labels.clone())
        .unwrap_or_default();
    sys.compact_for_witness();

    // return compiled circuit
    let compiled_circuit = CompiledCircuit {
        circuit,
        sys,
        public_input_size,
        gates,
        gate_labels,
        phantom: PhantomData,
    };
    Ok(compiled_circuit)
}

//
// The main user-facing trait for constructing circuits.
//

/// The main trait. Implement this on your circuit to get access to more functions (specifically [Self::compile_to_indexes]).
pub trait SnarkyCircuit: Sized {
    /// A circuit must be defined for a specific field,
    /// as it might be incorrect to use a different field.
    /// Currently we specify the field by the curve,
    /// which is more strict and needed due to implementation details in kimchi.
    // TODO: if we remove `sponge_params` from KimchiCurve and move it to the Field then we could specify a field here instead.
    type Curve: KimchiCurve<FULL_ROUNDS>;
    type Proof: OpenProof<Self::Curve, FULL_ROUNDS>;

    /// The number of recursion challenges (accumulated challenge-polynomial
    /// commitments) every proof of this circuit carries — baked into the
    /// verifier index. Proofs must pass exactly this many to
    /// [`ProverIndexWrapper::prove_with_recursion`].
    const PREV_CHALLENGES: usize = 0;

    /// The private input used by the circuit.
    type PrivateInput;

    /// The public input used by the circuit.
    type PublicInput: SnarkyType<ScalarField<Self::Curve>>;

    /// The public output returned by the circuit.
    type PublicOutput: SnarkyType<ScalarField<Self::Curve>>;

    /// The circuit. It takes:
    ///
    /// - `self`: to parameterize it at compile time.
    /// - `sys`: to construct the circuit or generate the witness (dpeending on mode)
    /// - `public_input`: the public input (as defined above)
    /// - `private_input`: the private input as an option, set to `None` for compilation.
    ///
    /// It returns a [SnarkyResult] containing the public output.
    fn circuit(
        &self,
        // TODO: change to an enum that is either the state for compilation or the state for proving ([WitnessGeneration])
        // TODO: change the name to `runner` everywhere?
        sys: &mut RunState<ScalarField<Self::Curve>>,
        public_input: Self::PublicInput,
        private_input: Option<&Self::PrivateInput>,
    ) -> SnarkyResult<Self::PublicOutput>;

    /// Returns the SRS used to compile this circuit. Implementations that
    /// repeatedly compile circuits over a protocol-fixed SRS can override
    /// this to share the immutable setup instead of regenerating it.
    fn srs(size: usize) -> std::sync::Arc<SrsOf<Self>>
    where
        <Self::Curve as AffineRepr>::BaseField: PrimeField,
    {
        std::sync::Arc::new(<SrsOf<Self> as SRS<Self::Curve>>::create(size))
    }

    /// Compile only far enough to determine the Kimchi evaluation domain.
    /// Unlike [`Self::compile_to_indexes`], this does not create an SRS or
    /// polynomial commitments and is suitable for dispatching on domain size.
    fn domain_log2(self) -> SnarkyResult<u32> {
        let compiled_circuit = compile(self)?;
        let cs = ConstraintSystem::create(compiled_circuit.gates)
            .public(compiled_circuit.public_input_size)
            .prev_challenges(Self::PREV_CHALLENGES)
            .build()
            .unwrap();
        Ok(cs.domain.d1.log_size_of_group)
    }

    /// Compiles the circuit to a prover index ([ProverIndexWrapper]) and a verifier index ([VerifierIndexWrapper]).
    fn compile_to_indexes(
        self,
    ) -> SnarkyResult<(ProverIndexWrapper<Self>, VerifierIndexWrapper<Self>)>
    where
        <Self::Curve as AffineRepr>::BaseField: PrimeField,
    {
        self.compile_to_indexes_with_minimum_domain_log2(0)
    }

    /// Compiles the circuit while padding it with zero gates to at least the
    /// requested power-of-two domain. This is required by recursive proof
    /// systems whose dummy accumulators have a protocol-fixed challenge count.
    fn compile_to_indexes_with_minimum_domain_log2(
        self,
        minimum_domain_log2: u32,
    ) -> SnarkyResult<(ProverIndexWrapper<Self>, VerifierIndexWrapper<Self>)>
    where
        <Self::Curve as AffineRepr>::BaseField: PrimeField,
    {
        self.compile_to_indexes_with_domain_and_srs(minimum_domain_log2, None)
    }

    /// Compiles like [`Self::compile_to_indexes_with_minimum_domain_log2`],
    /// but with an explicit SRS size. Mina uses full-size SRSes (2^16 on the
    /// step/Vesta side, 2^15 on the wrap/Pallas side) regardless of the
    /// circuit's domain, so its IPA proofs always have 16/15 rounds; the
    /// default (`None`) sizes the SRS to the domain, which is smaller and
    /// faster but network-incompatible.
    fn compile_to_indexes_with_domain_and_srs(
        self,
        minimum_domain_log2: u32,
        srs_log2: Option<u32>,
    ) -> SnarkyResult<(ProverIndexWrapper<Self>, VerifierIndexWrapper<Self>)>
    where
        <Self::Curve as AffineRepr>::BaseField: PrimeField,
    {
        let started = crate::wasm_instant::Instant::now();
        let mut compiled_circuit = compile(self)?;
        if std::env::var_os("SNARKY_PROFILE_INDEX").is_some() {
            eprintln!(
                "  [index detail] raw gates={} (pre-padding)",
                compiled_circuit.gates.len()
            );
        }
        if minimum_domain_log2 > 0 {
            let target_domain_size = 1usize << minimum_domain_log2;
            let target_gate_count =
                target_domain_size - usize::try_from(ZK_ROWS_BY_DEFAULT).unwrap();
            if compiled_circuit.gates.len() < target_gate_count {
                let pad = target_gate_count - compiled_circuit.gates.len();
                compiled_circuit.gates.extend(
                    (compiled_circuit.gates.len()..target_gate_count).map(|row| {
                        CircuitGate::zero(std::array::from_fn(|column| Wire {
                            row,
                            col: WIRES[column],
                        }))
                    }),
                );
                compiled_circuit
                    .gate_labels
                    .extend(std::iter::repeat_with(String::new).take(pad));
            }
        }
        let lowered_at = crate::wasm_instant::Instant::now();
        let mut profile = CompileProfile {
            lowering_micros: (lowered_at - started).as_micros() as u64,
            ..CompileProfile::default()
        };
        record_compile_profile(profile);

        // create constraint system
        let cs = ConstraintSystem::create(compiled_circuit.gates.clone())
            .public(compiled_circuit.public_input_size)
            .prev_challenges(Self::PREV_CHALLENGES)
            .build()
            .unwrap();
        let constraint_system_at = crate::wasm_instant::Instant::now();
        profile.constraint_system_micros = (constraint_system_at - lowered_at).as_micros() as u64;
        record_compile_profile(profile);
        if minimum_domain_log2 > 0 {
            assert!(
                cs.domain.d1.log_size_of_group >= minimum_domain_log2,
                "minimum domain padding must select at least the requested domain"
            );
        }

        // create SRS (for vesta, as the circuit is in Fp)
        let srs_size = match srs_log2 {
            Some(log2) => {
                assert!(
                    (1usize << log2) >= cs.domain.d1.size as usize,
                    "requested SRS smaller than the circuit domain"
                );
                1usize << log2
            }
            None => cs.domain.d1.size as usize,
        };
        let srs = Self::srs(srs_size);
        srs.get_lagrange_basis(cs.domain.d1);
        let lagrange_at = crate::wasm_instant::Instant::now();
        profile.lagrange_micros = (lagrange_at - constraint_system_at).as_micros() as u64;
        record_compile_profile(profile);

        debug!("using an SRS of size {}", srs.size());

        // create indexes
        let endo_q =
            <<Self as SnarkyCircuit>::Curve as KimchiCurve<FULL_ROUNDS>>::other_curve_endo();

        let t_create = crate::wasm_instant::Instant::now();
        let prover_index =
            kimchi::prover_index::ProverIndex::<FULL_ROUNDS, Self::Curve, SrsOf<Self>>::create(
                cs, *endo_q, srs, false,
            );
        let t_vi = crate::wasm_instant::Instant::now();
        let verifier_index = prover_index.verifier_index();
        if std::env::var_os("SNARKY_PROFILE_INDEX").is_some() {
            eprintln!(
                "  [index detail] create={:.0?} verifier_index={:.0?} domain=2^{} ",
                t_vi - t_create,
                t_vi.elapsed(),
                prover_index.cs.domain.d1.log_size_of_group,
            );
        }
        let prover_index_at = crate::wasm_instant::Instant::now();
        profile.prover_index_micros = (prover_index_at - lagrange_at).as_micros() as u64;
        record_compile_profile(profile);

        let prover_index = ProverIndexWrapper {
            compiled_circuit,
            index: prover_index,
        };

        let verifier_index = VerifierIndexWrapper {
            index: verifier_index,
        };

        Ok((prover_index, verifier_index))
    }
}

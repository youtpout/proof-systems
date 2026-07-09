//! Typed branch metadata for a Pickles inductive program.
//!
//! This is the Rust-side foundation for `inductive_rule.ml`/`compile.ml`: it
//! gives every branch a stable identity and validates the recursion width and
//! domains before expensive circuit compilation starts.

use std::collections::HashSet;

use ark_ff::PrimeField;

use crate::{
    common::{wrap_domain_log2, TICK_ROUNDS},
    composition_types::{BranchData, ProofSlot, ProofsVerified},
};

/// Stable identifier used to route a prover request to one compiled branch.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RuleId(pub u32);

/// Static recursion metadata for one inductive rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductiveRule {
    pub id: RuleId,
    pub name: String,
    pub proofs_verified: ProofsVerified,
    /// Domain of the step circuit implementing this branch.
    pub step_domain_log2: u8,
}

impl InductiveRule {
    pub fn new(
        id: RuleId,
        name: impl Into<String>,
        proofs_verified: ProofsVerified,
        step_domain_log2: u8,
    ) -> Self {
        Self {
            id,
            name: name.into(),
            proofs_verified,
            step_domain_log2,
        }
    }

    pub fn branch_data(&self) -> BranchData {
        BranchData {
            proofs_verified: self.proofs_verified,
            domain_log2: self.step_domain_log2,
        }
    }

    pub fn wrap_domain_log2(&self) -> u32 {
        wrap_domain_log2(self.proofs_verified.to_usize())
    }

    pub fn proof_slots<T>(&self, proofs: Vec<T>) -> Result<[ProofSlot<T>; 2], ProgramError> {
        if proofs.len() != self.proofs_verified.to_usize() {
            return Err(ProgramError::WrongProofCount {
                rule: self.id,
                expected: self.proofs_verified.to_usize(),
                actual: proofs.len(),
            });
        }
        Ok(crate::composition_types::front_pad_proof_slots(proofs))
    }

    /// Stable field representation used at the compiler/protocol boundary.
    /// Human-readable rule names are intentionally excluded.
    pub fn to_mina_field_elements<F: PrimeField>(&self) -> [F; 3] {
        [
            F::from(u64::from(self.id.0)),
            F::from(self.proofs_verified.to_usize() as u64),
            F::from(u64::from(self.step_domain_log2)),
        ]
    }
}

/// Validated collection of branches, ready for a compiler/prover backend.
#[derive(Clone, Debug)]
pub struct PicklesProgram {
    name: String,
    rules: Vec<InductiveRule>,
}

/// A compiled branch backend. Implementations own the concrete step/wrap
/// indexes and know how to create and verify that branch's proof type.
pub trait CompiledRuleBackend {
    type PublicInput;
    type Witness;
    type Proof;
    type Error;

    fn prove(
        &mut self,
        public_input: &Self::PublicInput,
        witness: Self::Witness,
    ) -> Result<Self::Proof, Self::Error>;

    fn verify(
        &self,
        public_input: &Self::PublicInput,
        proof: &Self::Proof,
    ) -> Result<(), Self::Error>;
}

/// Proof tagged with the branch that created it. Verification routes using
/// this tag and never accepts an unlabelled proof against an arbitrary index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuleProof<P> {
    pub rule_id: RuleId,
    pub proof: P,
}

/// A metadata-validated program whose branches have concrete compiled
/// backends attached.
pub struct CompiledPicklesProgram<B: CompiledRuleBackend> {
    metadata: PicklesProgram,
    backends: Vec<(RuleId, B)>,
}

impl<B: CompiledRuleBackend> CompiledPicklesProgram<B> {
    pub fn metadata(&self) -> &PicklesProgram {
        &self.metadata
    }

    pub fn prove(
        &mut self,
        rule_id: RuleId,
        public_input: &B::PublicInput,
        witness: B::Witness,
    ) -> Result<RuleProof<B::Proof>, ProgramExecutionError<B::Error>> {
        let backend = self
            .backends
            .iter_mut()
            .find(|(id, _)| *id == rule_id)
            .map(|(_, backend)| backend)
            .ok_or(ProgramExecutionError::UnknownRule(rule_id))?;
        let proof = backend
            .prove(public_input, witness)
            .map_err(ProgramExecutionError::Backend)?;
        Ok(RuleProof { rule_id, proof })
    }

    pub fn verify(
        &self,
        public_input: &B::PublicInput,
        proof: &RuleProof<B::Proof>,
    ) -> Result<(), ProgramExecutionError<B::Error>> {
        let backend = self
            .backends
            .iter()
            .find(|(id, _)| *id == proof.rule_id)
            .map(|(_, backend)| backend)
            .ok_or(ProgramExecutionError::UnknownRule(proof.rule_id))?;
        backend
            .verify(public_input, &proof.proof)
            .map_err(ProgramExecutionError::Backend)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProgramExecutionError<E> {
    UnknownRule(RuleId),
    Backend(E),
}

/// Witness of a recursive rule: application witness plus the previous proofs
/// consumed by the rule.
pub struct RecursiveRuleWitness<W, P, const ARITY: usize> {
    pub witness: W,
    pub previous_proofs: [P; ARITY],
}

/// Typed backend adapter for a recursive `N1` or `N2` branch. It validates the
/// rule arity at compilation and front-pads previous proofs before invoking
/// the concrete Pickles prover.
pub struct RecursiveRuleBackend<
    const ARITY: usize,
    I,
    W,
    PreviousProof,
    Proof,
    E,
    Prove,
    Verify,
> {
    rule: InductiveRule,
    prove: Prove,
    verify: Verify,
    _types: std::marker::PhantomData<(I, W, PreviousProof, Proof, E)>,
}

pub type N1RuleBackend<I, W, PreviousProof, Proof, E, Prove, Verify> =
    RecursiveRuleBackend<1, I, W, PreviousProof, Proof, E, Prove, Verify>;
pub type N2RuleBackend<I, W, PreviousProof, Proof, E, Prove, Verify> =
    RecursiveRuleBackend<2, I, W, PreviousProof, Proof, E, Prove, Verify>;

impl<
        const ARITY: usize,
        I,
        W,
        PreviousProof,
        Proof,
        E,
        Prove,
        Verify,
    > RecursiveRuleBackend<ARITY, I, W, PreviousProof, Proof, E, Prove, Verify>
{
    pub fn compile(
        rule: &InductiveRule,
        prove: Prove,
        verify: Verify,
    ) -> Result<Self, ProgramError> {
        if rule.proofs_verified.to_usize() != ARITY || !(1..=2).contains(&ARITY) {
            return Err(ProgramError::WrongProofCount {
                rule: rule.id,
                expected: rule.proofs_verified.to_usize(),
                actual: ARITY,
            });
        }
        Ok(Self {
            rule: rule.clone(),
            prove,
            verify,
            _types: std::marker::PhantomData,
        })
    }

    pub fn rule(&self) -> &InductiveRule {
        &self.rule
    }
}

impl<
        const ARITY: usize,
        I,
        W,
        PreviousProof,
        Proof,
        E,
        Prove,
        Verify,
    > CompiledRuleBackend
    for RecursiveRuleBackend<ARITY, I, W, PreviousProof, Proof, E, Prove, Verify>
where
    Prove: FnMut(&I, W, [ProofSlot<PreviousProof>; 2]) -> Result<Proof, E>,
    Verify: Fn(&I, &Proof) -> Result<(), E>,
{
    type PublicInput = I;
    type Witness = RecursiveRuleWitness<W, PreviousProof, ARITY>;
    type Proof = Proof;
    type Error = E;

    fn prove(
        &mut self,
        public_input: &I,
        witness: Self::Witness,
    ) -> Result<Proof, E> {
        let slots = self
            .rule
            .proof_slots(witness.previous_proofs.into_iter().collect())
            .expect("backend arity was checked at compile time");
        (self.prove)(public_input, witness.witness, slots)
    }

    fn verify(&self, public_input: &I, proof: &Proof) -> Result<(), E> {
        (self.verify)(public_input, proof)
    }
}

impl PicklesProgram {
    pub fn compile_metadata(
        name: impl Into<String>,
        rules: Vec<InductiveRule>,
    ) -> Result<Self, ProgramError> {
        let name = name.into();
        if name.is_empty() {
            return Err(ProgramError::EmptyProgramName);
        }
        if rules.is_empty() {
            return Err(ProgramError::NoRules);
        }

        let mut ids = HashSet::with_capacity(rules.len());
        let mut names = HashSet::with_capacity(rules.len());
        for rule in &rules {
            if rule.name.is_empty() {
                return Err(ProgramError::EmptyRuleName(rule.id));
            }
            if !ids.insert(rule.id) {
                return Err(ProgramError::DuplicateRuleId(rule.id));
            }
            if !names.insert(rule.name.clone()) {
                return Err(ProgramError::DuplicateRuleName(rule.name.clone()));
            }
            if usize::from(rule.step_domain_log2) > TICK_ROUNDS {
                return Err(ProgramError::StepDomainTooLarge {
                    rule: rule.id,
                    domain_log2: rule.step_domain_log2,
                });
            }
        }
        Ok(Self { name, rules })
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn rules(&self) -> &[InductiveRule] {
        &self.rules
    }

    pub fn rule(&self, id: RuleId) -> Result<&InductiveRule, ProgramError> {
        self.rules
            .iter()
            .find(|rule| rule.id == id)
            .ok_or(ProgramError::UnknownRule(id))
    }

    /// Compiles every validated branch exactly once and binds the resulting
    /// backend/index to its stable [`RuleId`].
    pub fn compile<B, E>(
        self,
        mut compile_rule: impl FnMut(&InductiveRule) -> Result<B, E>,
    ) -> Result<CompiledPicklesProgram<B>, ProgramExecutionError<E>>
    where
        B: CompiledRuleBackend,
    {
        let mut backends = Vec::with_capacity(self.rules.len());
        for rule in &self.rules {
            let backend = compile_rule(rule).map_err(ProgramExecutionError::Backend)?;
            backends.push((rule.id, backend));
        }
        Ok(CompiledPicklesProgram {
            metadata: self,
            backends,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProgramError {
    EmptyProgramName,
    NoRules,
    EmptyRuleName(RuleId),
    DuplicateRuleId(RuleId),
    DuplicateRuleName(String),
    StepDomainTooLarge {
        rule: RuleId,
        domain_log2: u8,
    },
    UnknownRule(RuleId),
    WrongProofCount {
        rule: RuleId,
        expected: usize,
        actual: usize,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compiles_and_routes_multi_branch_metadata() {
        let base = InductiveRule::new(RuleId(0), "base", ProofsVerified::N0, 9);
        let unary = InductiveRule::new(RuleId(1), "unary", ProofsVerified::N1, 16);
        let binary = InductiveRule::new(RuleId(2), "binary", ProofsVerified::N2, 16);
        let program =
            PicklesProgram::compile_metadata("ledger", vec![base, unary, binary]).unwrap();

        assert_eq!(program.rule(RuleId(1)).unwrap().wrap_domain_log2(), 14);
        assert_eq!(
            program.rule(RuleId(1)).unwrap().proof_slots(vec![7]).unwrap(),
            [ProofSlot::Dummy, ProofSlot::Proof(7)]
        );
        assert_eq!(
            program
                .rule(RuleId(2))
                .unwrap()
                .branch_data()
                .proofs_verified,
            ProofsVerified::N2
        );
    }

    #[test]
    fn rejects_ambiguous_or_inconsistent_rules() {
        let duplicate = vec![
            InductiveRule::new(RuleId(0), "base", ProofsVerified::N0, 9),
            InductiveRule::new(RuleId(0), "again", ProofsVerified::N1, 16),
        ];
        assert_eq!(
            PicklesProgram::compile_metadata("bad", duplicate).unwrap_err(),
            ProgramError::DuplicateRuleId(RuleId(0))
        );

        let rule = InductiveRule::new(RuleId(3), "too-wide", ProofsVerified::N1, 17);
        assert!(matches!(
            PicklesProgram::compile_metadata("bad", vec![rule]),
            Err(ProgramError::StepDomainTooLarge { .. })
        ));
    }

    #[test]
    fn enforces_each_rules_recursion_arity() {
        let rule = InductiveRule::new(RuleId(4), "unary", ProofsVerified::N1, 16);
        assert_eq!(
            rule.proof_slots::<u8>(vec![]).unwrap_err(),
            ProgramError::WrongProofCount {
                rule: RuleId(4),
                expected: 1,
                actual: 0,
            }
        );
    }

    #[derive(Clone)]
    struct ArithmeticBackend {
        rule: RuleId,
    }

    impl CompiledRuleBackend for ArithmeticBackend {
        type PublicInput = u64;
        type Witness = u64;
        type Proof = u64;
        type Error = &'static str;

        fn prove(&mut self, public_input: &u64, witness: u64) -> Result<u64, Self::Error> {
            let result = match self.rule {
                RuleId(0) => witness,
                RuleId(1) => witness + 1,
                _ => return Err("unsupported rule"),
            };
            (result == *public_input)
                .then_some(result)
                .ok_or("invalid witness")
        }

        fn verify(&self, public_input: &u64, proof: &u64) -> Result<(), Self::Error> {
            (proof == public_input).then_some(()).ok_or("invalid proof")
        }
    }

    #[test]
    fn compile_prove_verify_routes_to_the_bound_branch() {
        let metadata = PicklesProgram::compile_metadata(
            "arithmetic",
            vec![
                InductiveRule::new(RuleId(0), "base", ProofsVerified::N0, 9),
                InductiveRule::new(RuleId(1), "successor", ProofsVerified::N1, 16),
            ],
        )
        .unwrap();
        let mut program = metadata
            .compile(|rule| Ok::<_, &'static str>(ArithmeticBackend { rule: rule.id }))
            .unwrap();

        let base = program.prove(RuleId(0), &7, 7).unwrap();
        let successor = program.prove(RuleId(1), &8, 7).unwrap();
        program.verify(&7, &base).unwrap();
        program.verify(&8, &successor).unwrap();

        let wrongly_tagged = RuleProof {
            rule_id: RuleId(99),
            proof: 7,
        };
        assert_eq!(
            program.verify(&7, &wrongly_tagged),
            Err(ProgramExecutionError::UnknownRule(RuleId(99)))
        );
        assert_eq!(
            program.prove(RuleId(1), &9, 7),
            Err(ProgramExecutionError::Backend("invalid witness"))
        );
    }

    #[test]
    fn rule_field_encoding_is_stable() {
        use mina_curves::pasta::Fp;

        let rule = InductiveRule::new(RuleId(7), "ignored-on-wire", ProofsVerified::N2, 16);
        assert_eq!(
            rule.to_mina_field_elements::<Fp>(),
            [Fp::from(7u64), Fp::from(2u64), Fp::from(16u64)]
        );
        assert_eq!(
            rule.branch_data().pack::<Fp>(),
            Fp::from(16u64 * 4 + 2)
        );
    }

    #[test]
    fn recursive_backends_enforce_n1_and_n2_padding() {
        fn verify(input: &u64, proof: &u64) -> Result<(), &'static str> {
            (input == proof).then_some(()).ok_or("bad proof")
        }
        let unary_rule = InductiveRule::new(RuleId(1), "unary", ProofsVerified::N1, 16);
        let mut unary = N1RuleBackend::compile(
            &unary_rule,
            |input: &u64, witness: u64, slots: [ProofSlot<u64>; 2]| {
                assert_eq!(slots, [ProofSlot::Dummy, ProofSlot::Proof(4)]);
                Ok::<_, &'static str>(*input + witness)
            },
            verify,
        )
        .unwrap();
        let proof = unary
            .prove(
                &5,
                RecursiveRuleWitness {
                    witness: 2,
                    previous_proofs: [4],
                },
            )
            .unwrap();
        assert_eq!(proof, 7);

        let binary_rule = InductiveRule::new(RuleId(2), "binary", ProofsVerified::N2, 16);
        let mut binary = N2RuleBackend::compile(
            &binary_rule,
            |input: &u64, _: (), slots: [ProofSlot<u64>; 2]| {
                assert_eq!(
                    slots,
                    [ProofSlot::Proof(3), ProofSlot::Proof(4)]
                );
                Ok::<_, &'static str>(*input)
            },
            verify,
        )
        .unwrap();
        assert_eq!(
            binary
                .prove(
                    &9,
                    RecursiveRuleWitness {
                        witness: (),
                        previous_proofs: [3, 4],
                    },
                )
                .unwrap(),
            9
        );
    }
}

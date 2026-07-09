//! Typed branch metadata for a Pickles inductive program.
//!
//! This is the Rust-side foundation for `inductive_rule.ml`/`compile.ml`: it
//! gives every branch a stable identity and validates the recursion width and
//! domains before expensive circuit compilation starts.

use std::collections::HashSet;

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
}

/// Validated collection of branches, ready for a compiler/prover backend.
#[derive(Clone, Debug)]
pub struct PicklesProgram {
    name: String,
    rules: Vec<InductiveRule>,
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
}

//! OCaml bindings for the snarky crate's constraint system.
//!
//! This is the FFI surface that lets an OCaml snarky front end delegate the
//! constraint-system construction and witness generation to the Rust
//! implementation (`snarky::constraint_system::SnarkyConstraintSystem`),
//! replacing Mina's OCaml `plonk_constraint_system.ml`.
//!
//! Circuit variables cross the boundary as flattened linear combinations
//! `(constant, [(coefficient, var_index); ...])` — the OCaml side linearizes
//! its `Cvar.t` tree before each call, which keeps the FFI free of recursive
//! types and lets the Rust side own reduction and gate layout.

use kimchi::circuits::gate::caml::CamlCircuitGate;
use snarky::constraint_system::{BasicSnarkyConstraint, SnarkyConstraintSystem, SnarkyCvar};

/// A circuit variable, as a flattened linear combination.
#[derive(Clone, Debug)]
pub struct LinComCvar<F>(pub Option<F>, pub Vec<(F, usize)>);

impl<F: Clone> SnarkyCvar for LinComCvar<F> {
    type Field = F;

    fn to_constant_and_terms(&self) -> (Option<F>, Vec<(F, usize)>) {
        (self.0.clone(), self.1.clone())
    }
}

macro_rules! impl_snarky_cs {
    ($mod_name:ident, $field:ty, $caml_field:ty, $curve:ty, $cs:ident, $cs_ptr:ident, $finalizer:ident, $prefix:ident) => {
        pub mod $mod_name {
            use super::*;
            use paste::paste;
            use snarky::constants::Constants;

            type Field = $field;
            type CamlField = $caml_field;

            /// The OCaml-facing flattened cvar: `(constant, terms)`.
            type CamlLinCom = (Option<CamlField>, Vec<(CamlField, ocaml::Int)>);

            fn conv(cvar: CamlLinCom) -> LinComCvar<Field> {
                let (constant, terms) = cvar;
                LinComCvar(
                    constant.map(Into::into),
                    terms
                        .into_iter()
                        .map(|(c, idx)| (c.into(), idx as usize))
                        .collect(),
                )
            }

            #[derive(ocaml_gen::CustomType)]
            pub struct $cs(pub SnarkyConstraintSystem<Field>);
            pub type $cs_ptr<'a> = ocaml::Pointer<'a, $cs>;

            extern "C" fn $finalizer(v: ocaml::Raw) {
                unsafe {
                    let v: $cs_ptr = v.as_pointer();
                    v.drop_in_place()
                };
            }

            ocaml::custom!($cs {
                finalize: $finalizer,
            });

            paste! {
                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _create>]() -> $cs {
                    let constants = Constants::new::<$curve>();
                    $cs(SnarkyConstraintSystem::create(constants))
                }

                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _set_primary_input_size>](mut cs: $cs_ptr, n: ocaml::Int) {
                    cs.as_mut().0.set_primary_input_size(n as usize);
                }

                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _get_primary_input_size>](cs: $cs_ptr) -> ocaml::Int {
                    cs.as_ref().0.get_primary_input_size() as ocaml::Int
                }

                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _set_prev_challenges>](mut cs: $cs_ptr, n: ocaml::Int) {
                    cs.as_mut().0.set_prev_challenges(n as usize);
                }

                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _get_rows_len>](cs: $cs_ptr) -> ocaml::Int {
                    cs.as_ref().0.get_rows_len() as ocaml::Int
                }

                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _add_boolean>](mut cs: $cs_ptr, x: CamlLinCom) {
                    cs.as_mut().0.add_basic_snarky_constraint(
                        &[],
                        &"ocaml".into(),
                        BasicSnarkyConstraint::Boolean(conv(x)),
                    );
                }

                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _add_equal>](mut cs: $cs_ptr, x: CamlLinCom, y: CamlLinCom) {
                    cs.as_mut().0.add_basic_snarky_constraint(
                        &[],
                        &"ocaml".into(),
                        BasicSnarkyConstraint::Equal(conv(x), conv(y)),
                    );
                }

                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _add_square>](mut cs: $cs_ptr, x: CamlLinCom, y: CamlLinCom) {
                    cs.as_mut().0.add_basic_snarky_constraint(
                        &[],
                        &"ocaml".into(),
                        BasicSnarkyConstraint::Square(conv(x), conv(y)),
                    );
                }

                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _add_r1cs>](
                    mut cs: $cs_ptr,
                    a: CamlLinCom,
                    b: CamlLinCom,
                    c: CamlLinCom,
                ) {
                    cs.as_mut().0.add_basic_snarky_constraint(
                        &[],
                        &"ocaml".into(),
                        BasicSnarkyConstraint::R1CS(conv(a), conv(b), conv(c)),
                    );
                }

                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _finalize>](mut cs: $cs_ptr) {
                    cs.as_mut().0.finalize();
                }

                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _digest>](mut cs: $cs_ptr) -> [u8; 32] {
                    cs.as_mut().0.digest()
                }

                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _get_gates>](mut cs: $cs_ptr) -> Vec<CamlCircuitGate<CamlField>> {
                    cs.as_mut()
                        .0
                        .finalize_and_get_gates()
                        .iter()
                        .map(Into::into)
                        .collect()
                }

                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _compute_witness>](
                    mut cs: $cs_ptr,
                    public_inputs: Vec<CamlField>,
                    private_inputs: Vec<CamlField>,
                ) -> Vec<Vec<CamlField>> {
                    let public_inputs: Vec<Field> =
                        public_inputs.into_iter().map(Into::into).collect();
                    let private_inputs: Vec<Field> =
                        private_inputs.into_iter().map(Into::into).collect();
                    let witness = cs
                        .as_mut()
                        .0
                        .compute_witness_for_ocaml(&public_inputs, &private_inputs);
                    witness
                        .into_iter()
                        .map(|col| col.into_iter().map(Into::into).collect())
                        .collect()
                }
            }
        }
    };
}

impl_snarky_cs!(
    fp,
    mina_curves::pasta::Fp,
    crate::arkworks::CamlFp,
    mina_curves::pasta::Vesta,
    CamlFpSnarkyConstraintSystem,
    CamlFpSnarkyConstraintSystemPtr,
    caml_fp_snarky_cs_finalize_gc,
    caml_fp_snarky_cs
);

impl_snarky_cs!(
    fq,
    mina_curves::pasta::Fq,
    crate::arkworks::CamlFq,
    mina_curves::pasta::Pallas,
    CamlFqSnarkyConstraintSystem,
    CamlFqSnarkyConstraintSystemPtr,
    caml_fq_snarky_cs_finalize_gc,
    caml_fq_snarky_cs
);

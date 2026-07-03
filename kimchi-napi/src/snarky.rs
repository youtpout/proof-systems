//! NAPI bindings for the snarky crate's constraint system, for o1js.
//!
//! This is the Node-facing counterpart of the OCaml FFI in
//! `kimchi-stubs/src/snarky_constraint_system.rs`: it lets o1js build
//! circuits on the Rust constraint system directly, without going through
//! the js_of_ocaml Snarky layer.
//!
//! Circuit variables cross the boundary as flattened linear combinations:
//! an optional constant plus parallel arrays of coefficients (compressed
//! field bytes) and variable indices.

use napi::bindgen_prelude::*;
use napi_derive::napi;
use paste::paste;
use std::sync::{Arc, Mutex};

use snarky::constraint_system::{BasicSnarkyConstraint, SnarkyConstraintSystem, SnarkyCvar};

use crate::gate_vector::{CoreGateVector, NapiFpGateVector, NapiFqGateVector};
use crate::wrappers::field::{NapiPastaFp, NapiPastaFq};
use wasm_types::FlatVectorElem;

/// A circuit variable, as a flattened linear combination.
#[derive(Clone, Debug)]
pub struct LinComCvar<F>(pub Option<F>, pub Vec<(F, usize)>);

impl<F: Clone> SnarkyCvar for LinComCvar<F> {
    type Field = F;

    fn to_constant_and_terms(&self) -> (Option<F>, Vec<(F, usize)>) {
        (self.0.clone(), self.1.clone())
    }
}

macro_rules! impl_snarky_napi {
    ($field_name:ident, $F:ty, $NapiF:ty, $curve:ty, $gate_vector:ty) => {
        paste! {
            #[napi(js_name = [<"Wasm" $field_name:camel "SnarkyConstraintSystem">])]
            #[derive(Clone)]
            pub struct [<Napi $field_name:camel SnarkyCs>](
                #[napi(skip)] pub Arc<Mutex<SnarkyConstraintSystem<$F>>>,
            );

            impl FromNapiValue for [<Napi $field_name:camel SnarkyCs>] {
                unsafe fn from_napi_value(
                    env: sys::napi_env,
                    napi_val: sys::napi_value,
                ) -> Result<Self> {
                    let instance = <ClassInstance<[<Napi $field_name:camel SnarkyCs>]> as FromNapiValue>::from_napi_value(env, napi_val)?;
                    Ok((*instance).clone())
                }
            }

            /// Decodes a flattened linear combination from its JS encoding.
            fn [<$field_name _lincom>](
                constant: Option<Uint8Array>,
                coeffs: Vec<Uint8Array>,
                indices: Vec<u32>,
            ) -> LinComCvar<$F> {
                assert_eq!(coeffs.len(), indices.len(), "lincom: length mismatch");
                let constant = constant.map(|b| <$NapiF as FlatVectorElem>::unflatten(b.to_vec()).0);
                let terms = coeffs
                    .into_iter()
                    .zip(indices)
                    .map(|(c, i)| (<$NapiF as FlatVectorElem>::unflatten(c.to_vec()).0, i as usize))
                    .collect();
                LinComCvar(constant, terms)
            }

            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_create">])]
            pub fn [<caml_ $field_name _snarky_cs_create>]() -> [<Napi $field_name:camel SnarkyCs>] {
                let constants = snarky::constants::Constants::new::<$curve>();
                [<Napi $field_name:camel SnarkyCs>](Arc::new(Mutex::new(
                    SnarkyConstraintSystem::create(constants),
                )))
            }

            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_set_primary_input_size">])]
            pub fn [<caml_ $field_name _snarky_cs_set_primary_input_size>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                n: u32,
            ) {
                cs.0.lock().unwrap().set_primary_input_size(n as usize);
            }

            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_get_rows_len">])]
            pub fn [<caml_ $field_name _snarky_cs_get_rows_len>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
            ) -> u32 {
                cs.0.lock().unwrap().get_rows_len() as u32
            }

            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_add_boolean">])]
            pub fn [<caml_ $field_name _snarky_cs_add_boolean>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                constant: Option<Uint8Array>,
                coeffs: Vec<Uint8Array>,
                indices: Vec<u32>,
            ) {
                cs.0.lock().unwrap().add_basic_snarky_constraint(
                    &[],
                    &"o1js".into(),
                    BasicSnarkyConstraint::Boolean([<$field_name _lincom>](constant, coeffs, indices)),
                );
            }

            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_add_equal">])]
            #[allow(clippy::too_many_arguments)]
            pub fn [<caml_ $field_name _snarky_cs_add_equal>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                c1: Option<Uint8Array>, k1: Vec<Uint8Array>, i1: Vec<u32>,
                c2: Option<Uint8Array>, k2: Vec<Uint8Array>, i2: Vec<u32>,
            ) {
                cs.0.lock().unwrap().add_basic_snarky_constraint(
                    &[],
                    &"o1js".into(),
                    BasicSnarkyConstraint::Equal(
                        [<$field_name _lincom>](c1, k1, i1),
                        [<$field_name _lincom>](c2, k2, i2),
                    ),
                );
            }

            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_add_square">])]
            #[allow(clippy::too_many_arguments)]
            pub fn [<caml_ $field_name _snarky_cs_add_square>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                c1: Option<Uint8Array>, k1: Vec<Uint8Array>, i1: Vec<u32>,
                c2: Option<Uint8Array>, k2: Vec<Uint8Array>, i2: Vec<u32>,
            ) {
                cs.0.lock().unwrap().add_basic_snarky_constraint(
                    &[],
                    &"o1js".into(),
                    BasicSnarkyConstraint::Square(
                        [<$field_name _lincom>](c1, k1, i1),
                        [<$field_name _lincom>](c2, k2, i2),
                    ),
                );
            }

            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_add_r1cs">])]
            #[allow(clippy::too_many_arguments)]
            pub fn [<caml_ $field_name _snarky_cs_add_r1cs>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                c1: Option<Uint8Array>, k1: Vec<Uint8Array>, i1: Vec<u32>,
                c2: Option<Uint8Array>, k2: Vec<Uint8Array>, i2: Vec<u32>,
                c3: Option<Uint8Array>, k3: Vec<Uint8Array>, i3: Vec<u32>,
            ) {
                cs.0.lock().unwrap().add_basic_snarky_constraint(
                    &[],
                    &"o1js".into(),
                    BasicSnarkyConstraint::R1CS(
                        [<$field_name _lincom>](c1, k1, i1),
                        [<$field_name _lincom>](c2, k2, i2),
                        [<$field_name _lincom>](c3, k3, i3),
                    ),
                );
            }

            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_finalize">])]
            pub fn [<caml_ $field_name _snarky_cs_finalize>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
            ) {
                cs.0.lock().unwrap().finalize();
            }

            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_digest">])]
            pub fn [<caml_ $field_name _snarky_cs_digest>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
            ) -> Uint8Array {
                Uint8Array::from(cs.0.lock().unwrap().digest().to_vec())
            }

            /// Hands the finalized gates to the existing prover-index path as
            /// a native gate vector.
            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_to_gate_vector">])]
            pub fn [<caml_ $field_name _snarky_cs_to_gate_vector>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
            ) -> $gate_vector {
                let gates = cs.0.lock().unwrap().finalize_and_get_gates().clone();
                CoreGateVector::from_vec(gates).into()
            }

            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_compute_witness">])]
            pub fn [<caml_ $field_name _snarky_cs_compute_witness>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                public_inputs: Vec<Uint8Array>,
                private_inputs: Vec<Uint8Array>,
            ) -> Vec<Vec<Uint8Array>> {
                let public_inputs: Vec<$F> = public_inputs
                    .into_iter()
                    .map(|b| <$NapiF as FlatVectorElem>::unflatten(b.to_vec()).0)
                    .collect();
                let private_inputs: Vec<$F> = private_inputs
                    .into_iter()
                    .map(|b| <$NapiF as FlatVectorElem>::unflatten(b.to_vec()).0)
                    .collect();
                let witness = cs
                    .0
                    .lock()
                    .unwrap()
                    .compute_witness_for_ocaml(&public_inputs, &private_inputs);
                witness
                    .into_iter()
                    .map(|col| {
                        col.into_iter()
                            .map(|x| Uint8Array::from(<$NapiF>::from(x).flatten()))
                            .collect()
                    })
                    .collect()
            }
        }
    };
}

impl_snarky_napi!(
    fp,
    mina_curves::pasta::Fp,
    NapiPastaFp,
    mina_curves::pasta::Vesta,
    NapiFpGateVector
);
impl_snarky_napi!(
    fq,
    mina_curves::pasta::Fq,
    NapiPastaFq,
    mina_curves::pasta::Pallas,
    NapiFqGateVector
);

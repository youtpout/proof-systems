//! NAPI bindings for the snarky crate's constraint system, for o1js.
//!
//! This is the Node-facing counterpart of the OCaml FFI in
//! `kimchi-stubs/src/snarky_constraint_system.rs`: it lets o1js build
//! circuits on the Rust constraint system directly, without going through
//! the js_of_ocaml Snarky layer.
//!
//! Circuit variables cross the boundary as flattened linear combinations,
//! batched per call into parallel buffers (napi-rs does not support typed
//! arrays inside objects):
//! - `sizes[k]`: number of terms of the k-th linear combination
//! - `has_constant[k]`: 1 if the k-th lincom has a constant
//! - `constants`: the constants of the lincoms that have one, 32 bytes each
//! - `coeffs`: all term coefficients, 32 bytes each, lincoms concatenated
//! - `indices`: all term variable indices, same order as `coeffs`

use napi::bindgen_prelude::*;
use napi_derive::napi;
use paste::paste;
use std::sync::{Arc, Mutex};
use wasm_types::FlatVectorElem;

use snarky::constraint_system::{
    BasicInput, BasicSnarkyConstraint, EcAddCompleteInput, KimchiConstraint,
    SnarkyConstraintSystem, SnarkyCvar,
};

use crate::gate_vector::{CoreGateVector, NapiFpGateVector, NapiFqGateVector};
use crate::wrappers::field::{NapiPastaFp, NapiPastaFq};

/// A circuit variable, as a flattened linear combination.
#[derive(Clone, Debug)]
pub struct LinComCvar<F>(pub Option<F>, pub Vec<(F, usize)>);

impl<F: Clone> SnarkyCvar for LinComCvar<F> {
    type Field = F;

    fn to_constant_and_terms(&self) -> (Option<F>, Vec<(F, usize)>) {
        (self.0.clone(), self.1.clone())
    }
}

/// Maps o1js's numeric gate-type enum (same order as kimchi's `GateType`
/// declaration) to the Rust enum. Only the concrete circuit gates are
/// accepted.
fn gate_type_of_u32(t: u32) -> kimchi::circuits::gate::GateType {
    use kimchi::circuits::gate::GateType::*;
    match t {
        0 => Zero,
        1 => Generic,
        2 => Poseidon,
        3 => CompleteAdd,
        4 => VarBaseMul,
        5 => EndoMul,
        6 => EndoMulScalar,
        7 => Lookup,
        8 => RangeCheck0,
        9 => RangeCheck1,
        10 => ForeignFieldAdd,
        11 => ForeignFieldMul,
        12 => Xor16,
        13 => Rot64,
        _ => panic!("gate_type_of_u32: unsupported gate type {t}"),
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

            const [<$field_name:upper _SIZE>]: usize = <$NapiF as FlatVectorElem>::FLATTENED_SIZE;

            fn [<$field_name _of_bytes>](bytes: &[u8]) -> $F {
                <$NapiF as FlatVectorElem>::unflatten(bytes.to_vec()).0
            }

            /// Decodes a batch of linear combinations from its flat encoding.
            fn [<$field_name _lincoms>](
                sizes: &[u32],
                has_constant: &[u8],
                constants: &[u8],
                coeffs: &[u8],
                indices: &[u32],
            ) -> Vec<LinComCvar<$F>> {
                let sz = [<$field_name:upper _SIZE>];
                assert_eq!(sizes.len(), has_constant.len(), "lincoms: length mismatch");
                let mut consts = constants.chunks_exact(sz);
                let mut coeffs = coeffs.chunks_exact(sz);
                let mut indices = indices.iter();
                sizes
                    .iter()
                    .zip(has_constant)
                    .map(|(&n, &has_c)| {
                        let constant = if has_c != 0 {
                            Some([<$field_name _of_bytes>](consts.next().expect("missing constant")))
                        } else {
                            None
                        };
                        let terms = (0..n)
                            .map(|_| {
                                let c = [<$field_name _of_bytes>](coeffs.next().expect("missing coeff"));
                                let i = *indices.next().expect("missing index") as usize;
                                (c, i)
                            })
                            .collect();
                        LinComCvar(constant, terms)
                    })
                    .collect()
            }

            /// Decodes exactly `n` linear combinations.
            fn [<$field_name _lincoms_n>](
                n: usize,
                sizes: Uint32Array,
                has_constant: Uint8Array,
                constants: Uint8Array,
                coeffs: Uint8Array,
                indices: Uint32Array,
            ) -> Vec<LinComCvar<$F>> {
                let lincoms = [<$field_name _lincoms>](&sizes, &has_constant, &constants, &coeffs, &indices);
                assert_eq!(lincoms.len(), n, "expected {n} linear combinations");
                lincoms
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

            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_get_primary_input_size">])]
            pub fn [<caml_ $field_name _snarky_cs_get_primary_input_size>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
            ) -> u32 {
                cs.0.lock().unwrap().get_primary_input_size() as u32
            }

            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_set_prev_challenges">])]
            pub fn [<caml_ $field_name _snarky_cs_set_prev_challenges>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                n: u32,
            ) {
                cs.0.lock().unwrap().set_prev_challenges(n as usize);
            }

            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_get_rows_len">])]
            pub fn [<caml_ $field_name _snarky_cs_get_rows_len>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
            ) -> u32 {
                cs.0.lock().unwrap().get_rows_len() as u32
            }

            /// Basic snarky constraints. `kind`: 0 = boolean(x), 1 = equal(x, y),
            /// 2 = square(x, y), 3 = r1cs(x, y, z); the batch carries 1, 2 or 3
            /// linear combinations accordingly.
            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_add_basic_constraint">])]
            #[allow(clippy::too_many_arguments)]
            pub fn [<caml_ $field_name _snarky_cs_add_basic_constraint>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                kind: u32,
                sizes: Uint32Array,
                has_constant: Uint8Array,
                constants: Uint8Array,
                coeffs: Uint8Array,
                indices: Uint32Array,
            ) {
                let mut lincoms = [<$field_name _lincoms>](&sizes, &has_constant, &constants, &coeffs, &indices).into_iter();
                let mut n = move || lincoms.next().expect("missing linear combination");
                let constraint = match kind {
                    0 => BasicSnarkyConstraint::Boolean(n()),
                    1 => BasicSnarkyConstraint::Equal(n(), n()),
                    2 => BasicSnarkyConstraint::Square(n(), n()),
                    3 => BasicSnarkyConstraint::R1CS(n(), n(), n()),
                    _ => panic!("add_basic_constraint: unknown kind {kind}"),
                };
                cs.0.lock().unwrap().add_basic_snarky_constraint(
                    &[],
                    &"o1js".into(),
                    constraint,
                );
            }

            /// Generic kimchi gate: `cl*l + cr*r + co*o + m*l*r + c = 0`.
            /// The batch carries the 3 lincoms `[l, r, o]`; `scalars` is the
            /// concatenation of the 5 coefficients `[cl, cr, co, m, c]`.
            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_add_generic">])]
            #[allow(clippy::too_many_arguments)]
            pub fn [<caml_ $field_name _snarky_cs_add_generic>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                scalars: Uint8Array,
                sizes: Uint32Array,
                has_constant: Uint8Array,
                constants: Uint8Array,
                coeffs: Uint8Array,
                indices: Uint32Array,
            ) {
                let sz = [<$field_name:upper _SIZE>];
                assert_eq!(scalars.len(), 5 * sz, "add_generic: expected 5 scalar coefficients");
                let mut scalars_it = scalars.chunks_exact(sz).map([<$field_name _of_bytes>]);
                let mut s = move || scalars_it.next().unwrap();
                let mut lincoms = [<$field_name _lincoms_n>](3, sizes, has_constant, constants, coeffs, indices).into_iter();
                let mut l = move || lincoms.next().unwrap();
                cs.0.lock().unwrap().add_constraint(
                    &[],
                    &"o1js".into(),
                    KimchiConstraint::Basic(BasicInput {
                        l: (s(), l()),
                        r: (s(), l()),
                        o: (s(), l()),
                        m: s(),
                        c: s(),
                    }),
                );
            }

            /// A full poseidon permutation: the batch carries the 56 * 3
            /// state lincoms, row-major.
            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_add_poseidon">])]
            pub fn [<caml_ $field_name _snarky_cs_add_poseidon>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                sizes: Uint32Array,
                has_constant: Uint8Array,
                constants: Uint8Array,
                coeffs: Uint8Array,
                indices: Uint32Array,
            ) {
                let lincoms = [<$field_name _lincoms>](&sizes, &has_constant, &constants, &coeffs, &indices);
                assert_eq!(lincoms.len() % 3, 0, "add_poseidon: state width is 3");
                let state = lincoms
                    .chunks(3)
                    .map(|row| row.to_vec())
                    .collect();
                cs.0.lock().unwrap().add_constraint(
                    &[],
                    &"o1js".into(),
                    KimchiConstraint::Poseidon(state),
                );
            }

            /// Complete EC addition; the batch carries the 11 variables
            /// `[x1, y1, x2, y2, x3, y3, inf, same_x, slope, inf_z, x21_inv]`.
            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_add_ec_add_complete">])]
            pub fn [<caml_ $field_name _snarky_cs_add_ec_add_complete>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                sizes: Uint32Array,
                has_constant: Uint8Array,
                constants: Uint8Array,
                coeffs: Uint8Array,
                indices: Uint32Array,
            ) {
                let mut it = [<$field_name _lincoms_n>](11, sizes, has_constant, constants, coeffs, indices).into_iter();
                let mut n = move || it.next().unwrap();
                cs.0.lock().unwrap().add_constraint(
                    &[],
                    &"o1js".into(),
                    KimchiConstraint::EcAddComplete(EcAddCompleteInput {
                        p1: (n(), n()),
                        p2: (n(), n()),
                        p3: (n(), n()),
                        inf: n(),
                        same_x: n(),
                        slope: n(),
                        inf_z: n(),
                        x21_inv: n(),
                    }),
                );
            }

            /// One row of an 88-bit range check; the batch carries the 15
            /// variables in column order; `compact` is a field element.
            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_add_range_check0">])]
            #[allow(clippy::too_many_arguments)]
            pub fn [<caml_ $field_name _snarky_cs_add_range_check0>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                compact: Uint8Array,
                sizes: Uint32Array,
                has_constant: Uint8Array,
                constants: Uint8Array,
                coeffs: Uint8Array,
                indices: Uint32Array,
            ) {
                let compact = [<$field_name _of_bytes>](&compact);
                let vars = [<$field_name _lincoms_n>](15, sizes, has_constant, constants, coeffs, indices);
                cs.0.lock().unwrap().add_constraint(
                    &[],
                    &"o1js".into(),
                    KimchiConstraint::RangeCheck0(vars, compact),
                );
            }

            /// The two rows of the RangeCheck1 gate; the batch carries
            /// 30 variables (current row then next row, column order).
            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_add_range_check1">])]
            pub fn [<caml_ $field_name _snarky_cs_add_range_check1>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                sizes: Uint32Array,
                has_constant: Uint8Array,
                constants: Uint8Array,
                coeffs: Uint8Array,
                indices: Uint32Array,
            ) {
                let mut vars = [<$field_name _lincoms_n>](30, sizes, has_constant, constants, coeffs, indices);
                let next = vars.split_off(15);
                cs.0.lock().unwrap().add_constraint(
                    &[],
                    &"o1js".into(),
                    KimchiConstraint::RangeCheck1(vars, next),
                );
            }

            /// A lookup row: the batch carries the 7 variables `[w0..w6]`.
            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_add_lookup">])]
            pub fn [<caml_ $field_name _snarky_cs_add_lookup>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                sizes: Uint32Array,
                has_constant: Uint8Array,
                constants: Uint8Array,
                coeffs: Uint8Array,
                indices: Uint32Array,
            ) {
                let vars = [<$field_name _lincoms_n>](7, sizes, has_constant, constants, coeffs, indices);
                cs.0.lock().unwrap().add_constraint(
                    &[],
                    &"o1js".into(),
                    KimchiConstraint::Lookup(vars),
                );
            }

            /// Escape hatch: one row with an arbitrary gate type (numeric,
            /// kimchi `GateType` declaration order). `present` is a 0/1 mask
            /// of the row's 15 cells; the batch carries the present lincoms
            /// in order. `gate_coeffs` is the concatenation of the gate's
            /// coefficients. Covers Xor16, Rot64, foreign field rows, ...
            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_add_row">])]
            #[allow(clippy::too_many_arguments)]
            pub fn [<caml_ $field_name _snarky_cs_add_row>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                gate_type: u32,
                present: Uint8Array,
                gate_coeffs: Uint8Array,
                sizes: Uint32Array,
                has_constant: Uint8Array,
                constants: Uint8Array,
                coeffs: Uint8Array,
                indices: Uint32Array,
            ) {
                let sz = [<$field_name:upper _SIZE>];
                let gate_coeffs = gate_coeffs
                    .chunks_exact(sz)
                    .map([<$field_name _of_bytes>])
                    .collect();
                let mut lincoms = [<$field_name _lincoms>](&sizes, &has_constant, &constants, &coeffs, &indices).into_iter();
                let vars = present
                    .iter()
                    .map(|&p| if p != 0 { Some(lincoms.next().expect("missing cell")) } else { None })
                    .collect();
                cs.0.lock().unwrap().add_kimchi_row(
                    &[],
                    &"o1js".into(),
                    gate_type_of_u32(gate_type),
                    vars,
                    gate_coeffs,
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

            /// Computes the witness columns; field elements cross as
            /// concatenated 32-byte chunks.
            #[napi(js_name = [<"caml_" $field_name "_snarky_cs_compute_witness">])]
            pub fn [<caml_ $field_name _snarky_cs_compute_witness>](
                cs: &[<Napi $field_name:camel SnarkyCs>],
                public_inputs: Uint8Array,
                private_inputs: Uint8Array,
            ) -> Vec<Uint8Array> {
                let sz = [<$field_name:upper _SIZE>];
                let public_inputs: Vec<$F> = public_inputs
                    .chunks_exact(sz)
                    .map([<$field_name _of_bytes>])
                    .collect();
                let private_inputs: Vec<$F> = private_inputs
                    .chunks_exact(sz)
                    .map([<$field_name _of_bytes>])
                    .collect();
                let witness = cs
                    .0
                    .lock()
                    .unwrap()
                    .compute_witness_for_ocaml(&public_inputs, &private_inputs);
                witness
                    .into_iter()
                    .map(|col| {
                        let mut bytes = Vec::with_capacity(col.len() * sz);
                        for x in col {
                            bytes.extend(<$NapiF>::from(x).flatten());
                        }
                        Uint8Array::from(bytes)
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

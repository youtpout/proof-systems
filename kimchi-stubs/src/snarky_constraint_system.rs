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
use snarky::constraint_system::{
    BasicInput, BasicSnarkyConstraint, EcAddCompleteInput, EcEndoscaleInput, EndoscaleRound,
    EndoscaleScalarRound, KimchiConstraint, ScaleRound, SnarkyConstraintSystem, SnarkyCvar,
};

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

                //
                // kimchi custom constraints
                //

                fn conv_scaled((s, x): (CamlField, CamlLinCom)) -> (Field, LinComCvar<Field>) {
                    (s.into(), conv(x))
                }

                fn conv_pair((x, y): (CamlLinCom, CamlLinCom)) -> (LinComCvar<Field>, LinComCvar<Field>) {
                    (conv(x), conv(y))
                }

                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _add_basic>](
                    mut cs: $cs_ptr,
                    l: (CamlField, CamlLinCom),
                    r: (CamlField, CamlLinCom),
                    o: (CamlField, CamlLinCom),
                    m: CamlField,
                    c: CamlField,
                ) {
                    cs.as_mut().0.add_constraint(
                        &[],
                        &"ocaml".into(),
                        KimchiConstraint::Basic(BasicInput {
                            l: conv_scaled(l),
                            r: conv_scaled(r),
                            o: conv_scaled(o),
                            m: m.into(),
                            c: c.into(),
                        }),
                    );
                }

                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _add_poseidon>](mut cs: $cs_ptr, state: Vec<Vec<CamlLinCom>>) {
                    let state = state
                        .into_iter()
                        .map(|row| row.into_iter().map(conv).collect())
                        .collect();
                    cs.as_mut().0.add_constraint(
                        &[],
                        &"ocaml".into(),
                        KimchiConstraint::Poseidon(state),
                    );
                }

                #[allow(clippy::too_many_arguments)]
                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _add_ec_add_complete>](
                    mut cs: $cs_ptr,
                    p1: (CamlLinCom, CamlLinCom),
                    p2: (CamlLinCom, CamlLinCom),
                    p3: (CamlLinCom, CamlLinCom),
                    inf: CamlLinCom,
                    same_x: CamlLinCom,
                    slope: CamlLinCom,
                    inf_z: CamlLinCom,
                    x21_inv: CamlLinCom,
                ) {
                    cs.as_mut().0.add_constraint(
                        &[],
                        &"ocaml".into(),
                        KimchiConstraint::EcAddComplete(EcAddCompleteInput {
                            p1: conv_pair(p1),
                            p2: conv_pair(p2),
                            p3: conv_pair(p3),
                            inf: conv(inf),
                            same_x: conv(same_x),
                            slope: conv(slope),
                            inf_z: conv(inf_z),
                            x21_inv: conv(x21_inv),
                        }),
                    );
                }

                /// Each round is `(accs, bits, ss, base, n_prev, n_next)`.
                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _add_ec_scale>](
                    mut cs: $cs_ptr,
                    state: Vec<(
                        Vec<(CamlLinCom, CamlLinCom)>,
                        Vec<CamlLinCom>,
                        Vec<CamlLinCom>,
                        (CamlLinCom, CamlLinCom),
                        CamlLinCom,
                        CamlLinCom,
                    )>,
                ) {
                    let state = state
                        .into_iter()
                        .map(|(accs, bits, ss, base, n_prev, n_next)| ScaleRound {
                            accs: accs.into_iter().map(conv_pair).collect(),
                            bits: bits.into_iter().map(conv).collect(),
                            ss: ss.into_iter().map(conv).collect(),
                            base: conv_pair(base),
                            n_prev: conv(n_prev),
                            n_next: conv(n_next),
                        })
                        .collect();
                    cs.as_mut().0.add_constraint(
                        &[],
                        &"ocaml".into(),
                        KimchiConstraint::EcScale(state),
                    );
                }

                /// Each round is the 14 variables in declaration order:
                /// `[xt, yt, xp, yp, n_acc, xr, yr, s1, s3, b1, b2, b3, b4, inv]`.
                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _add_ec_endoscale>](
                    mut cs: $cs_ptr,
                    state: Vec<Vec<CamlLinCom>>,
                    xs: CamlLinCom,
                    ys: CamlLinCom,
                    n_acc: CamlLinCom,
                ) {
                    let state = state
                        .into_iter()
                        .map(|round| {
                            let mut it = round.into_iter().map(conv);
                            let mut n = || it.next().expect("endoscale round: 14 variables");
                            EndoscaleRound {
                                xt: n(), yt: n(), xp: n(), yp: n(), n_acc: n(),
                                xr: n(), yr: n(), s1: n(), s3: n(),
                                b1: n(), b2: n(), b3: n(), b4: n(), inv: n(),
                            }
                        })
                        .collect();
                    cs.as_mut().0.add_constraint(
                        &[],
                        &"ocaml".into(),
                        KimchiConstraint::EcEndoscale(EcEndoscaleInput {
                            state,
                            xs: conv(xs),
                            ys: conv(ys),
                            n_acc: conv(n_acc),
                        }),
                    );
                }

                /// Each round is the 14 variables in declaration order:
                /// `[n0, n8, a0, b0, a8, b8, x0, x1, x2, x3, x4, x5, x6, x7]`.
                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _add_ec_endoscalar>](
                    mut cs: $cs_ptr,
                    state: Vec<Vec<CamlLinCom>>,
                ) {
                    let state = state
                        .into_iter()
                        .map(|round| {
                            let mut it = round.into_iter().map(conv);
                            let mut n = || it.next().expect("endoscalar round: 14 variables");
                            EndoscaleScalarRound {
                                n0: n(), n8: n(),
                                a0: n(), b0: n(), a8: n(), b8: n(),
                                x0: n(), x1: n(), x2: n(), x3: n(),
                                x4: n(), x5: n(), x6: n(), x7: n(),
                            }
                        })
                        .collect();
                    cs.as_mut().0.add_constraint(
                        &[],
                        &"ocaml".into(),
                        KimchiConstraint::EcEndoscalar(state),
                    );
                }

                /// The 15 variables in column order `[v, vp0..vp5, vc0..vc7]`.
                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _add_range_check0>](
                    mut cs: $cs_ptr,
                    vars: Vec<CamlLinCom>,
                    compact: CamlField,
                ) {
                    cs.as_mut().0.add_constraint(
                        &[],
                        &"ocaml".into(),
                        KimchiConstraint::RangeCheck0(
                            vars.into_iter().map(conv).collect(),
                            compact.into(),
                        ),
                    );
                }

                /// Current and next rows, 15 variables each, in column order.
                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _add_range_check1>](
                    mut cs: $cs_ptr,
                    curr: Vec<CamlLinCom>,
                    next: Vec<CamlLinCom>,
                ) {
                    cs.as_mut().0.add_constraint(
                        &[],
                        &"ocaml".into(),
                        KimchiConstraint::RangeCheck1(
                            curr.into_iter().map(conv).collect(),
                            next.into_iter().map(conv).collect(),
                        ),
                    );
                }

                /// The 7 variables `[w0..w6]`.
                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _add_lookup>](mut cs: $cs_ptr, vars: Vec<CamlLinCom>) {
                    cs.as_mut().0.add_constraint(
                        &[],
                        &"ocaml".into(),
                        KimchiConstraint::Lookup(vars.into_iter().map(conv).collect()),
                    );
                }

                /// Escape hatch: a single row with an arbitrary gate type,
                /// 15 optional variables and its coefficients.
                #[ocaml_gen::func]
                #[ocaml::func]
                pub fn [<$prefix _add_row>](
                    mut cs: $cs_ptr,
                    gate: kimchi::circuits::gate::GateType,
                    vars: Vec<Option<CamlLinCom>>,
                    coeffs: Vec<CamlField>,
                ) {
                    cs.as_mut().0.add_kimchi_row(
                        &[],
                        &"ocaml".into(),
                        gate,
                        vars.into_iter().map(|v| v.map(conv)).collect(),
                        coeffs.into_iter().map(Into::into).collect(),
                    );
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

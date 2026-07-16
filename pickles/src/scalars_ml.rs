//! In-circuit evaluation of the linearization constant term following the
//! EXACT operation tree of OCaml's generated `scalars.ml` (`Tick.constant_term`
//! / `Tock.constant_term`).
//!
//! Byte-parity with jsoo requires reproducing the generated code's sharing
//! structure (top-level `let x_N` bindings, nested shadowing re-expansions),
//! its `square`/`pow` gadget choices, and OCaml's right-to-left operand
//! evaluation order — kimchi's PolishToken stream evaluates the same
//! polynomial with a different tree, which emits a different gadget sequence.
//!
//! The trees are parsed out of `scalars.ml` (see the session scratchpad's
//! `parse_scalars.py`) into `scalars_tick.json` / `scalars_tock.json`.

use std::borrow::Cow;
use std::collections::HashMap;

use ark_ff::{FftField, PrimeField};
use kimchi::circuits::{
    berkeley_columns::Column,
    gate::{CurrOrNext, GateType},
};
use serde_json::Value;
use snarky::{FieldVar, RunState, SnarkyResult};

use crate::expr_eval::{pow_circuit, square_circuit};

static TICK_JSON: &str = include_str!("scalars_tick.json");
static TOCK_JSON: &str = include_str!("scalars_tock.json");

fn tick_tree() -> &'static Value {
    use std::sync::OnceLock;
    static TREE: OnceLock<Value> = OnceLock::new();
    TREE.get_or_init(|| serde_json::from_str(TICK_JSON).expect("scalars_tick.json"))
}

fn tock_tree() -> &'static Value {
    use std::sync::OnceLock;
    static TREE: OnceLock<Value> = OnceLock::new();
    TREE.get_or_init(|| serde_json::from_str(TOCK_JSON).expect("scalars_tock.json"))
}

/// Which generated constant-term to evaluate.
#[derive(Clone, Copy, Debug)]
pub enum ScalarsKind {
    /// Step-side finalize (Tick field).
    Tick,
    /// Wrap-side finalize (Tock field).
    Tock,
}

/// The environment of the generated code (mirror of `Scalars.Env`), over
/// circuit variables. Feature flags are `Features.none`: every `if_feature`
/// evaluates its else-branch only, and `joint_combiner` is the zero constant.
pub struct ScalarsMlEnv<'a, F: PrimeField> {
    pub column: &'a dyn Fn(Column, CurrOrNext) -> FieldVar<F>,
    pub alpha_pows: &'a [FieldVar<F>],
    pub beta: FieldVar<F>,
    pub gamma: FieldVar<F>,
    pub endo_coefficient: F,
    pub mds: &'a [Vec<F>],
    /// The precomputed `zk_polynomial` (env's
    /// `vanishes_on_zero_knowledge_and_previous_rows`).
    pub zk_polynomial: FieldVar<F>,
    /// The precomputed `ζ^n - 1` used by `unnormalized_lagrange_basis`.
    pub zeta_to_n_minus_1: FieldVar<F>,
    /// The finalize domain, for the lagrange denominators' `ω^offset`.
    pub domain: ScalarsMlDomain<F>,
    /// The evaluation point ζ.
    pub zeta: FieldVar<F>,
    pub zk_rows: u64,
}

/// `ω^offset` source for `unnormalized_lagrange_basis`: constants for a
/// fixed domain; the env's `ω^{-k}` chain for a pseudo domain, with OCaml's
/// LAZY `ω^{-(zk+1)} = ω^{-zk}·ω^{-1}` emitted at first use
/// (plonk_checks.ml:264).
pub enum ScalarsMlDomain<F: PrimeField> {
    Fixed(ark_poly::Radix2EvaluationDomain<F>),
    Selected {
        omegas: crate::ft_eval_circuit::DomainOmegas<F>,
        omega_to_zk_minus_1: std::cell::RefCell<Option<FieldVar<F>>>,
    },
}

impl<F: PrimeField + FftField> ScalarsMlDomain<F> {
    fn omega_pow(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        off: i64,
    ) -> SnarkyResult<FieldVar<F>> {
        match self {
            ScalarsMlDomain::Fixed(d) => {
                let omega_i = if off < 0 {
                    d.group_gen.pow([(-off) as u64]).inverse().unwrap()
                } else {
                    d.group_gen.pow([off as u64])
                };
                Ok(FieldVar::constant(omega_i))
            }
            ScalarsMlDomain::Selected {
                omegas,
                omega_to_zk_minus_1,
            } => match off {
                0 => Ok(FieldVar::constant(F::one())),
                1 => Ok(omegas.generator.clone()),
                -1 => Ok(omegas.omega_to_minus_1.clone()),
                -2 => Ok(omegas.omega_to_zk_plus_1.clone()),
                -3 => Ok(omegas.omega_to_zk.clone()),
                -4 => {
                    if let Some(v) = omega_to_zk_minus_1.borrow().as_ref() {
                        return Ok(v.clone());
                    }
                    let v = omegas
                        .omega_to_zk
                        .mul(&omegas.omega_to_minus_1, None, loc, sys)?;
                    *omega_to_zk_minus_1.borrow_mut() = Some(v.clone());
                    Ok(v)
                }
                other => panic!("scalars_ml: ω^{other} on a pseudo domain"),
            },
        }
    }
}

fn parse_hex_field<F: PrimeField>(s: &str) -> F {
    let hex = s.trim_start_matches("0x").trim_start_matches("0X");
    let mut bytes = Vec::with_capacity(hex.len() / 2);
    let padded = if hex.len() % 2 == 1 {
        format!("0{hex}")
    } else {
        hex.to_string()
    };
    for i in (0..padded.len()).step_by(2) {
        bytes.push(u8::from_str_radix(&padded[i..i + 2], 16).expect("hex literal"));
    }
    bytes.reverse(); // big-endian text -> little-endian bytes
    F::from_le_bytes_mod_order(&bytes)
}

fn gate_type(name: &str) -> GateType {
    match name {
        "Generic" => GateType::Generic,
        "Poseidon" => GateType::Poseidon,
        "CompleteAdd" => GateType::CompleteAdd,
        "VarBaseMul" => GateType::VarBaseMul,
        "EndoMul" => GateType::EndoMul,
        "EndoMulScalar" => GateType::EndoMulScalar,
        "RangeCheck0" => GateType::RangeCheck0,
        "RangeCheck1" => GateType::RangeCheck1,
        "ForeignFieldAdd" => GateType::ForeignFieldAdd,
        "ForeignFieldMul" => GateType::ForeignFieldMul,
        "Xor16" => GateType::Xor16,
        "Rot64" => GateType::Rot64,
        other => panic!("scalars_ml: unknown gate {other}"),
    }
}

struct Eval<'a, 'b, F: PrimeField> {
    env: &'a ScalarsMlEnv<'b, F>,
    loc: Cow<'static, str>,
    /// Top-level and nested `let` bindings currently in scope (shadowing).
    scope: HashMap<String, Vec<FieldVar<F>>>,
}

impl<F: PrimeField + FftField> Eval<'_, '_, F> {
    fn eval(&mut self, sys: &mut RunState<F>, node: &Value) -> SnarkyResult<FieldVar<F>> {
        let arr = node.as_array().expect("expr node");
        let tag = arr[0].as_str().expect("node tag");
        match tag {
            "let" => {
                let bindings = arr[1].as_array().unwrap();
                let mut bound: Vec<String> = Vec::with_capacity(bindings.len());
                for b in bindings {
                    let pair = b.as_array().unwrap();
                    let name = pair[0].as_str().unwrap().to_string();
                    let value = self.eval(sys, &pair[1])?;
                    self.scope.entry(name.clone()).or_default().push(value);
                    bound.push(name);
                }
                let result = self.eval(sys, &arr[2])?;
                for name in bound {
                    self.scope.get_mut(&name).unwrap().pop();
                }
                Ok(result)
            }
            "var" => {
                let name = arr[1].as_str().unwrap();
                Ok(self
                    .scope
                    .get(name)
                    .and_then(|stack| stack.last())
                    .unwrap_or_else(|| panic!("scalars_ml: unbound {name}"))
                    .clone())
            }
            // OCaml evaluates curried arguments right-to-left: the RIGHT
            // operand's gadgets are emitted before the left operand's.
            "add" => {
                let b = self.eval(sys, &arr[2])?;
                let a = self.eval(sys, &arr[1])?;
                Ok(&a + &b)
            }
            "sub" => {
                let b = self.eval(sys, &arr[2])?;
                let a = self.eval(sys, &arr[1])?;
                Ok(&a - &b)
            }
            "mul" => {
                let b = self.eval(sys, &arr[2])?;
                let a = self.eval(sys, &arr[1])?;
                a.mul(&b, None, self.loc.clone(), sys)
            }
            "square" => {
                let a = self.eval(sys, &arr[1])?;
                square_circuit(sys, self.loc.clone(), &a)
            }
            "double" => {
                let a = self.eval(sys, &arr[1])?;
                Ok(a.scale(F::from(2u64)))
            }
            "pow" => {
                let n = arr[2].as_u64().unwrap();
                let a = self.eval(sys, &arr[1])?;
                pow_circuit(sys, self.loc.clone(), &a, n)
            }
            "cell" => {
                let kind = arr[1].as_str().unwrap();
                let row = |s: &str| {
                    if s == "next" {
                        CurrOrNext::Next
                    } else {
                        CurrOrNext::Curr
                    }
                };
                match kind {
                    "witness" => {
                        let i = arr[2].as_u64().unwrap() as usize;
                        Ok((self.env.column)(
                            Column::Witness(i),
                            row(arr[3].as_str().unwrap()),
                        ))
                    }
                    "coefficient" => {
                        let i = arr[2].as_u64().unwrap() as usize;
                        Ok((self.env.column)(
                            Column::Coefficient(i),
                            row(arr[3].as_str().unwrap()),
                        ))
                    }
                    "index" => {
                        let gate = gate_type(arr[2].as_str().unwrap());
                        Ok((self.env.column)(
                            Column::Index(gate),
                            row(arr[3].as_str().unwrap()),
                        ))
                    }
                    other => panic!("scalars_ml: cell {other} outside a disabled feature branch"),
                }
            }
            "alpha_pow" => {
                let n = arr[1].as_u64().unwrap() as usize;
                Ok(self.env.alpha_pows[n].clone())
            }
            "field" => Ok(FieldVar::constant(parse_hex_field::<F>(
                arr[1].as_str().unwrap(),
            ))),
            "mds" => {
                let r = arr[1].as_u64().unwrap() as usize;
                let c = arr[2].as_u64().unwrap() as usize;
                Ok(FieldVar::constant(self.env.mds[r][c]))
            }
            "beta" => Ok(self.env.beta.clone()),
            "gamma" => Ok(self.env.gamma.clone()),
            "endo" => Ok(FieldVar::constant(self.env.endo_coefficient)),
            "joint" => Ok(FieldVar::constant(F::zero())),
            "vanishes" => Ok(self.env.zk_polynomial.clone()),
            "lagrange" => {
                // OCaml env: `(ζ^n - 1) / (ζ - ω^i)` with the SHARED
                // precomputed numerator (plonk_checks.ml:300).
                let zk_rel = arr[1].as_bool().unwrap();
                let i = arr[2].as_i64().unwrap();
                let off = if zk_rel {
                    i - self.env.zk_rows as i64
                } else {
                    i
                };
                let omega_i = self.env.domain.omega_pow(sys, self.loc.clone(), off)?;
                let denominator = &self.env.zeta - &omega_i;
                crate::plonk_curve_ops::div_var(
                    sys,
                    self.loc.clone(),
                    &self.env.zeta_to_n_minus_1,
                    &denominator,
                )
            }
            "if_feature" => {
                // Features are `none` in every o1js pickles circuit: OCaml's
                // env takes the else-thunk (plonk_checks.ml:330).
                self.eval(sys, &arr[3])
            }
            other => panic!("scalars_ml: unknown node {other}"),
        }
    }
}

/// Pure-value evaluation of the generated tree (witness-side mirror of the
/// circuit evaluator; also used to cross-check against kimchi's
/// `PolishToken::evaluate`).
#[allow(clippy::too_many_arguments)]
pub fn eval_constant_term_value<F: PrimeField + FftField>(
    kind: ScalarsKind,
    column: &dyn Fn(Column, CurrOrNext) -> F,
    alpha: F,
    beta: F,
    gamma: F,
    endo_coefficient: F,
    mds: &[Vec<F>],
    domain: ark_poly::Radix2EvaluationDomain<F>,
    zeta: F,
    zk_rows: u64,
) -> F {
    let tree = match kind {
        ScalarsKind::Tick => tick_tree(),
        ScalarsKind::Tock => tock_tree(),
    };
    let mut alpha_pows = vec![F::one(); 71];
    for i in 1..71 {
        alpha_pows[i] = alpha_pows[i - 1] * alpha;
    }
    let zeta_to_n_minus_1 = zeta.pow([domain.size]) - F::one();
    let omega_pow = |off: i64| -> F {
        if off < 0 {
            domain.group_gen.pow([(-off) as u64]).inverse().unwrap()
        } else {
            domain.group_gen.pow([off as u64])
        }
    };
    // (ζ - ω^{-1})(ζ - ω^{-2})...(ζ - ω^{-(zk_rows)}) ... OCaml zk_polynomial
    // is the vanishing polynomial of {ω^{-1}, ω^{-2}, ω^{-3}} at ζ.
    let zk_polynomial = (zeta - omega_pow(-1)) * (zeta - omega_pow(-2)) * (zeta - omega_pow(-3));
    struct VEval<'x, F: PrimeField> {
        column: &'x dyn Fn(Column, CurrOrNext) -> F,
        alpha_pows: Vec<F>,
        beta: F,
        gamma: F,
        endo: F,
        mds: &'x [Vec<F>],
        zk_polynomial: F,
        zeta_to_n_minus_1: F,
        zeta: F,
        zk_rows: u64,
        omega_pow: &'x dyn Fn(i64) -> F,
        scope: HashMap<String, Vec<F>>,
    }
    impl<F: PrimeField> VEval<'_, F> {
        fn eval(&mut self, node: &Value) -> F {
            let arr = node.as_array().unwrap();
            match arr[0].as_str().unwrap() {
                "let" => {
                    let bindings = arr[1].as_array().unwrap();
                    let mut bound = vec![];
                    for b in bindings {
                        let pair = b.as_array().unwrap();
                        let name = pair[0].as_str().unwrap().to_string();
                        let value = self.eval(&pair[1]);
                        self.scope.entry(name.clone()).or_default().push(value);
                        bound.push(name);
                    }
                    let r = self.eval(&arr[2]);
                    for name in bound {
                        self.scope.get_mut(&name).unwrap().pop();
                    }
                    r
                }
                "var" => *self
                    .scope
                    .get(arr[1].as_str().unwrap())
                    .and_then(|s| s.last())
                    .unwrap(),
                "add" => self.eval(&arr[1]) + self.eval(&arr[2]),
                "sub" => self.eval(&arr[1]) - self.eval(&arr[2]),
                "mul" => self.eval(&arr[1]) * self.eval(&arr[2]),
                "square" => self.eval(&arr[1]).square(),
                "double" => self.eval(&arr[1]).double(),
                "pow" => self.eval(&arr[1]).pow([arr[2].as_u64().unwrap()]),
                "cell" => {
                    let row = |s: &str| {
                        if s == "next" {
                            CurrOrNext::Next
                        } else {
                            CurrOrNext::Curr
                        }
                    };
                    match arr[1].as_str().unwrap() {
                        "witness" => (self.column)(
                            Column::Witness(arr[2].as_u64().unwrap() as usize),
                            row(arr[3].as_str().unwrap()),
                        ),
                        "coefficient" => (self.column)(
                            Column::Coefficient(arr[2].as_u64().unwrap() as usize),
                            row(arr[3].as_str().unwrap()),
                        ),
                        "index" => (self.column)(
                            Column::Index(gate_type(arr[2].as_str().unwrap())),
                            row(arr[3].as_str().unwrap()),
                        ),
                        other => panic!("value eval: cell {other} in disabled branch"),
                    }
                }
                "alpha_pow" => self.alpha_pows[arr[1].as_u64().unwrap() as usize],
                "field" => parse_hex_field(arr[1].as_str().unwrap()),
                "mds" => self.mds[arr[1].as_u64().unwrap() as usize][arr[2].as_u64().unwrap() as usize],
                "beta" => self.beta,
                "gamma" => self.gamma,
                "endo" => self.endo,
                "joint" => F::zero(),
                "vanishes" => self.zk_polynomial,
                "lagrange" => {
                    let zk_rel = arr[1].as_bool().unwrap();
                    let i = arr[2].as_i64().unwrap();
                    let off = if zk_rel { i - self.zk_rows as i64 } else { i };
                    self.zeta_to_n_minus_1 * (self.zeta - (self.omega_pow)(off)).inverse().unwrap()
                }
                "if_feature" => self.eval(&arr[3]),
                other => panic!("value eval: {other}"),
            }
        }
    }
    let mut ev = VEval {
        column,
        alpha_pows,
        beta,
        gamma,
        endo: endo_coefficient,
        mds,
        zk_polynomial,
        zeta_to_n_minus_1,
        zeta,
        zk_rows,
        omega_pow: &omega_pow,
        scope: HashMap::new(),
    };
    ev.eval(tree)
}

/// Evaluates the generated `constant_term` over circuit variables.
pub fn eval_constant_term<F: PrimeField + FftField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    kind: ScalarsKind,
    env: &ScalarsMlEnv<'_, F>,
) -> SnarkyResult<FieldVar<F>> {
    let tree = match kind {
        ScalarsKind::Tick => tick_tree(),
        ScalarsKind::Tock => tock_tree(),
    };
    let mut ev = Eval {
        env,
        loc,
        scope: HashMap::new(),
    };
    ev.eval(sys, tree)
}

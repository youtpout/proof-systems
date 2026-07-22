//! Serialization of a Mina Pickles proof to the OCaml S-expression string that
//! `Pickles.Side_loaded.Proof.to_base64` produces
//! (`Base64.encode_exn (Sexp.to_string (sexp_of_t proof))`, proof.ml:322-326).
//! This is the on-chain transaction authorization format (the account-update
//! `authorization.proof` field), distinct from the network bin_prot in
//! [`crate::mina_bin_prot`].
//!
//! Stage 1 (this file): a faithful port of sexplib's machine printer
//! (`Sexp.to_string`) plus a parser, validated by round-tripping a real jsoo
//! proof fixture. Later stages build the structured proof sexp from
//! [`crate::mina_bin_prot::WrapProofBaseV3`].

/// A minimal S-expression tree (atoms and lists), matching OCaml `Sexplib.Sexp.t`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

impl Sexp {
    pub fn atom(s: impl Into<String>) -> Sexp {
        Sexp::Atom(s.into())
    }
    pub fn list(items: Vec<Sexp>) -> Sexp {
        Sexp::List(items)
    }

    /// Renders in sexplib's "machine" format, i.e. exactly `Sexp.to_string`.
    pub fn to_string_mach(&self) -> String {
        let mut out = String::new();
        self.write_mach(&mut out);
        out
    }

    fn write_mach(&self, out: &mut String) {
        match self {
            Sexp::Atom(s) => write_atom(s, out),
            Sexp::List(items) => {
                out.push('(');
                for (i, item) in items.iter().enumerate() {
                    // sexplib inserts a separating space before an element only
                    // when it renders as a bare (unquoted) atom and is not the
                    // first — a preceding '(' , ')' or '"' already delimits.
                    if i > 0 && starts_bare_atom(item) {
                        out.push(' ');
                    }
                    item.write_mach(out);
                }
                out.push(')');
            }
        }
    }
}

/// Whether the element renders starting with a bare-atom character (so it needs
/// a leading space to separate it from a preceding bare atom).
fn starts_bare_atom(s: &Sexp) -> bool {
    match s {
        Sexp::List(_) => false,
        Sexp::Atom(a) => !atom_needs_quote(a),
    }
}

/// sexplib quotes an atom when it is empty or contains a character that would
/// break bare-atom lexing.
fn atom_needs_quote(s: &str) -> bool {
    if s.is_empty() {
        return true;
    }
    s.chars().any(|c| {
        c.is_whitespace()
            || c == '('
            || c == ')'
            || c == '"'
            || c == ';'
            || c == '\\'
            || c == '#'
            || c == '|'
            || c.is_control()
    })
}

fn write_atom(s: &str, out: &mut String) {
    if !atom_needs_quote(s) {
        out.push_str(s);
        return;
    }
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 => {
                // sexplib escapes other control chars as \ddd (3 decimal digits)
                out.push_str(&format!("\\{:03}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

/// Parses a single S-expression from `input` (the whole string must be one sexp).
pub fn parse(input: &str) -> Result<Sexp, String> {
    let bytes = input.as_bytes();
    let mut pos = 0usize;
    skip_ws(bytes, &mut pos);
    let sexp = parse_one(bytes, &mut pos)?;
    skip_ws(bytes, &mut pos);
    if pos != bytes.len() {
        return Err(format!("trailing data at byte {pos}"));
    }
    Ok(sexp)
}

fn skip_ws(bytes: &[u8], pos: &mut usize) {
    while *pos < bytes.len() && bytes[*pos].is_ascii_whitespace() {
        *pos += 1;
    }
}

fn parse_one(bytes: &[u8], pos: &mut usize) -> Result<Sexp, String> {
    if *pos >= bytes.len() {
        return Err("unexpected end of input".into());
    }
    match bytes[*pos] {
        b'(' => {
            *pos += 1;
            let mut items = Vec::new();
            loop {
                skip_ws(bytes, pos);
                if *pos >= bytes.len() {
                    return Err("unterminated list".into());
                }
                if bytes[*pos] == b')' {
                    *pos += 1;
                    break;
                }
                items.push(parse_one(bytes, pos)?);
            }
            Ok(Sexp::List(items))
        }
        b'"' => parse_quoted(bytes, pos),
        b')' => Err(format!("unexpected ')' at byte {pos}")),
        _ => parse_bare(bytes, pos),
    }
}

fn parse_bare(bytes: &[u8], pos: &mut usize) -> Result<Sexp, String> {
    let start = *pos;
    while *pos < bytes.len() {
        let c = bytes[*pos];
        if c.is_ascii_whitespace() || c == b'(' || c == b')' || c == b'"' {
            break;
        }
        *pos += 1;
    }
    let s = std::str::from_utf8(&bytes[start..*pos]).map_err(|e| e.to_string())?;
    Ok(Sexp::Atom(s.to_string()))
}

fn parse_quoted(bytes: &[u8], pos: &mut usize) -> Result<Sexp, String> {
    *pos += 1; // opening quote
    let mut s = String::new();
    while *pos < bytes.len() {
        let c = bytes[*pos];
        match c {
            b'"' => {
                *pos += 1;
                return Ok(Sexp::Atom(s));
            }
            b'\\' => {
                *pos += 1;
                if *pos >= bytes.len() {
                    return Err("bad escape".into());
                }
                match bytes[*pos] {
                    b'"' => s.push('"'),
                    b'\\' => s.push('\\'),
                    b'n' => s.push('\n'),
                    b't' => s.push('\t'),
                    b'r' => s.push('\r'),
                    d if d.is_ascii_digit() => {
                        // \ddd three decimal digits
                        if *pos + 2 >= bytes.len() {
                            return Err("bad decimal escape".into());
                        }
                        let n = std::str::from_utf8(&bytes[*pos..*pos + 3])
                            .ok()
                            .and_then(|t| t.parse::<u32>().ok())
                            .ok_or("bad decimal escape")?;
                        s.push(char::from_u32(n).ok_or("bad decimal escape")?);
                        *pos += 2;
                    }
                    other => return Err(format!("unknown escape \\{}", other as char)),
                }
                *pos += 1;
            }
            _ => {
                s.push(c as char);
                *pos += 1;
            }
        }
    }
    Err("unterminated quoted atom".into())
}

// ---------------------------------------------------------------------------
// Structured proof -> Sexp (the `sexp_of_t (Proofs_verified_2.Repr.V2.t)` port).
// ---------------------------------------------------------------------------

use crate::mina_bin_prot::{
    branch_data_domain_log2, branch_data_proofs_verified, WrapProofBaseV3, WrapProofPrevEvalsV2,
    WrapStatementMinimalV1, WrapWireProofV1,
};
use ark_ff::{BigInteger, PrimeField};
use kimchi::proof::PointEvaluations;
use mina_curves::pasta::{Fp, Fq};

fn a(s: impl Into<String>) -> Sexp {
    Sexp::Atom(s.into())
}
/// `(name value)` key-value pair.
fn kv(name: &str, value: Sexp) -> Sexp {
    Sexp::List(vec![a(name), value])
}

/// A field element as `0x` + 64 uppercase big-endian hex digits (Mina
/// `Field.sexp_of_t`).
fn field_atom<F: PrimeField>(f: &F) -> Sexp {
    let bytes = f.into_bigint().to_bytes_be();
    let mut s = String::with_capacity(2 + bytes.len() * 2);
    s.push_str("0x");
    for b in bytes {
        s.push_str(&format!("{:02X}", b));
    }
    Sexp::Atom(s)
}

/// The four little-endian 64-bit limbs of a field's canonical value.
fn le_limbs<F: PrimeField>(f: &F) -> [u64; 4] {
    let bytes = f.into_bigint().to_bytes_le();
    let mut out = [0u64; 4];
    for (i, slot) in out.iter_mut().enumerate() {
        let mut buf = [0u8; 8];
        for (j, b) in buf.iter_mut().enumerate() {
            if let Some(v) = bytes.get(i * 8 + j) {
                *b = *v;
            }
        }
        *slot = u64::from_le_bytes(buf);
    }
    out
}
/// The low two 64-bit limbs of a field (challenges fit in 128 bits).
fn limbs2<F: PrimeField>(f: &F) -> (u64, u64) {
    let l = le_limbs(f);
    (l[0], l[1])
}
fn hex16(n: u64) -> String {
    format!("{:016x}", n)
}

/// A `Challenge` = `(lo hi)` of two Hex64 limbs (little-endian).
fn plain_challenge<F: PrimeField>(f: &F) -> Sexp {
    let (lo, hi) = limbs2(f);
    Sexp::List(vec![a(hex16(lo)), a(hex16(hi))])
}
/// A `Scalar_challenge` = `((inner (lo hi)))`.
fn scalar_challenge<F: PrimeField>(f: &F) -> Sexp {
    Sexp::List(vec![kv("inner", plain_challenge(f))])
}
/// A `Bulletproof_challenge` = `((prechallenge ((inner (lo hi)))))`.
fn prechallenge<F: PrimeField>(f: &F) -> Sexp {
    Sexp::List(vec![kv("prechallenge", scalar_challenge(f))])
}
fn point_fp(p: &(Fp, Fp)) -> Sexp {
    Sexp::List(vec![field_atom(&p.0), field_atom(&p.1)])
}
fn point_fq(p: &(Fq, Fq)) -> Sexp {
    Sexp::List(vec![field_atom(&p.0), field_atom(&p.1)])
}

fn proofs_verified_atom(v: usize) -> Sexp {
    a(match v {
        0 => "N0",
        1 => "N1",
        _ => "N2",
    })
}

fn statement_sexp(st: &WrapStatementMinimalV1) -> Sexp {
    let fl = &st.flattened;
    let rounds = fl.len() - WrapStatementMinimalV1::FIXED_FLATTENED_LEN_WITHOUT_BP_CHALLENGES;
    let branch_idx = 13 + rounds;

    let feature = |name: &str| kv(name, a("false"));
    let plonk = Sexp::List(vec![
        kv("alpha", scalar_challenge(&fl[7])),
        kv("beta", plain_challenge(&fl[5])),
        kv("gamma", plain_challenge(&fl[6])),
        kv("zeta", scalar_challenge(&fl[8])),
        kv("joint_combiner", Sexp::List(vec![])),
        kv(
            "feature_flags",
            Sexp::List(vec![
                feature("range_check0"),
                feature("range_check1"),
                feature("foreign_field_add"),
                feature("foreign_field_mul"),
                feature("xor"),
                feature("rot"),
                feature("lookup"),
                feature("runtime_tables"),
            ]),
        ),
    ]);
    let bp = Sexp::List(fl[13..branch_idx].iter().map(prechallenge).collect());
    let pv = branch_data_proofs_verified(&fl[branch_idx]).unwrap_or(0);
    let dl = branch_data_domain_log2(&fl[branch_idx]).unwrap_or(0);
    let branch_data = Sexp::List(vec![
        kv("proofs_verified", proofs_verified_atom(pv)),
        kv("domain_log2", a((dl as char).to_string())),
    ]);
    let deferred = Sexp::List(vec![
        kv("plonk", plonk),
        kv("bulletproof_challenges", bp),
        kv("branch_data", branch_data),
    ]);
    let dlimbs = le_limbs(&fl[10]);
    let sponge = Sexp::List((0..4).map(|i| a(hex16(dlimbs[i]))).collect());

    let m = &st.messages_for_next_wrap_proof;
    let old_bp = Sexp::List(
        m.old_bulletproof_challenges
            .iter()
            .map(|v| Sexp::List(v.iter().map(prechallenge).collect()))
            .collect(),
    );
    let mnwp = Sexp::List(vec![
        kv(
            "challenge_polynomial_commitment",
            point_fq(&m.challenge_polynomial_commitment),
        ),
        kv("old_bulletproof_challenges", old_bp),
    ]);
    let proof_state = Sexp::List(vec![
        kv("deferred_values", deferred),
        kv("sponge_digest_before_evaluations", sponge),
        kv("messages_for_next_wrap_proof", mnwp),
    ]);
    let mnsp = Sexp::List(vec![
        kv("app_state", Sexp::List(vec![])),
        kv("challenge_polynomial_commitments", Sexp::List(vec![])),
        kv("old_bulletproof_challenges", Sexp::List(vec![])),
    ]);
    Sexp::List(vec![
        kv("proof_state", proof_state),
        kv("messages_for_next_step_proof", mnsp),
    ])
}

/// PointEvaluations over chunked vectors: `((zeta…)(zeta_omega…))`.
fn point_eval_chunked(pe: &PointEvaluations<Vec<Fp>>) -> Sexp {
    Sexp::List(vec![
        Sexp::List(pe.zeta.iter().map(field_atom).collect()),
        Sexp::List(pe.zeta_omega.iter().map(field_atom).collect()),
    ])
}
fn opt_eval(o: &Option<PointEvaluations<Vec<Fp>>>) -> Sexp {
    match o {
        Some(pe) => point_eval_chunked(pe),
        None => Sexp::List(vec![]),
    }
}

fn prev_evals_sexp(pe: &WrapProofPrevEvalsV2) -> Sexp {
    let e = &pe.evals;
    let public = e.public.as_ref().expect("prev_evals public_input");
    let public_input = Sexp::List(vec![
        field_atom(&public.zeta[0]),
        field_atom(&public.zeta_omega[0]),
    ]);
    let evals = Sexp::List(vec![
        kv("w", Sexp::List(e.w.iter().map(point_eval_chunked).collect())),
        kv(
            "coefficients",
            Sexp::List(e.coefficients.iter().map(point_eval_chunked).collect()),
        ),
        kv("z", point_eval_chunked(&e.z)),
        kv("s", Sexp::List(e.s.iter().map(point_eval_chunked).collect())),
        kv("generic_selector", point_eval_chunked(&e.generic_selector)),
        kv("poseidon_selector", point_eval_chunked(&e.poseidon_selector)),
        kv(
            "complete_add_selector",
            point_eval_chunked(&e.complete_add_selector),
        ),
        kv("mul_selector", point_eval_chunked(&e.mul_selector)),
        kv("emul_selector", point_eval_chunked(&e.emul_selector)),
        kv(
            "endomul_scalar_selector",
            point_eval_chunked(&e.endomul_scalar_selector),
        ),
        kv("range_check0_selector", opt_eval(&e.range_check0_selector)),
        kv("range_check1_selector", opt_eval(&e.range_check1_selector)),
        kv(
            "foreign_field_add_selector",
            opt_eval(&e.foreign_field_add_selector),
        ),
        kv(
            "foreign_field_mul_selector",
            opt_eval(&e.foreign_field_mul_selector),
        ),
        kv("xor_selector", opt_eval(&e.xor_selector)),
        kv("rot_selector", opt_eval(&e.rot_selector)),
        kv("lookup_aggregation", opt_eval(&e.lookup_aggregation)),
        kv("lookup_table", opt_eval(&e.lookup_table)),
        kv(
            "lookup_sorted",
            Sexp::List(e.lookup_sorted.iter().map(opt_eval).collect()),
        ),
        kv("runtime_lookup_table", opt_eval(&e.runtime_lookup_table)),
        kv(
            "runtime_lookup_table_selector",
            opt_eval(&e.runtime_lookup_table_selector),
        ),
        kv("xor_lookup_selector", opt_eval(&e.xor_lookup_selector)),
        kv(
            "lookup_gate_lookup_selector",
            opt_eval(&e.lookup_gate_lookup_selector),
        ),
        kv(
            "range_check_lookup_selector",
            opt_eval(&e.range_check_lookup_selector),
        ),
        kv(
            "foreign_field_mul_lookup_selector",
            opt_eval(&e.foreign_field_mul_lookup_selector),
        ),
    ]);
    Sexp::List(vec![
        kv(
            "evals",
            Sexp::List(vec![kv("public_input", public_input), kv("evals", evals)]),
        ),
        kv("ft_eval1", field_atom(&pe.ft_eval1)),
    ])
}

/// Single-value PointEvaluations in the wire proof: `(zeta zeta_omega)`.
fn eval_pair(p: &(Fq, Fq)) -> Sexp {
    Sexp::List(vec![field_atom(&p.0), field_atom(&p.1)])
}

fn proof_sexp(wp: &WrapWireProofV1) -> Sexp {
    let commitments = Sexp::List(vec![
        kv("w_comm", Sexp::List(wp.w_comm.iter().map(point_fp).collect())),
        kv("z_comm", point_fp(&wp.z_comm)),
        kv("t_comm", Sexp::List(wp.t_comm.iter().map(point_fp).collect())),
    ]);
    let evaluations = Sexp::List(vec![
        kv("w", Sexp::List(wp.w.iter().map(eval_pair).collect())),
        kv(
            "coefficients",
            Sexp::List(wp.coefficients.iter().map(eval_pair).collect()),
        ),
        kv("z", eval_pair(&wp.z)),
        kv("s", Sexp::List(wp.s.iter().map(eval_pair).collect())),
        kv("generic_selector", eval_pair(&wp.generic_selector)),
        kv("poseidon_selector", eval_pair(&wp.poseidon_selector)),
        kv("complete_add_selector", eval_pair(&wp.complete_add_selector)),
        kv("mul_selector", eval_pair(&wp.mul_selector)),
        kv("emul_selector", eval_pair(&wp.emul_selector)),
        kv(
            "endomul_scalar_selector",
            eval_pair(&wp.endomul_scalar_selector),
        ),
    ]);
    let lr = Sexp::List(
        wp.bulletproof_lr
            .iter()
            .map(|(l, r)| Sexp::List(vec![point_fp(l), point_fp(r)]))
            .collect(),
    );
    let bulletproof = Sexp::List(vec![
        kv("lr", lr),
        kv("z_1", field_atom(&wp.z_1)),
        kv("z_2", field_atom(&wp.z_2)),
        kv("delta", point_fp(&wp.delta)),
        kv(
            "challenge_polynomial_commitment",
            point_fp(&wp.challenge_polynomial_commitment),
        ),
    ]);
    Sexp::List(vec![
        kv("commitments", commitments),
        kv("evaluations", evaluations),
        kv("ft_eval1", field_atom(&wp.ft_eval1)),
        kv("bulletproof", bulletproof),
    ])
}

impl WrapProofBaseV3 {
    /// The structured Sexp of this proof, matching `sexp_of_t` for
    /// `Pickles.Proofs_verified_2.Repr.V2.t`.
    pub fn to_transaction_sexp(&self) -> Sexp {
        Sexp::List(vec![
            kv("statement", statement_sexp(&self.stable_statement)),
            kv("prev_evals", prev_evals_sexp(&self.prev_evals)),
            kv("proof", proof_sexp(&self.proof)),
        ])
    }

    /// The transaction authorization proof string: exactly
    /// `Pickles.Side_loaded.Proof.to_base64` = `Base64.encode (Sexp.to_string …)`.
    pub fn to_transaction_base64(&self) -> String {
        use base64::{engine::general_purpose::STANDARD, Engine as _};
        STANDARD.encode(self.to_transaction_sexp().to_string_mach())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const FIXTURE: &str = include_str!("../tests/fixtures/jsoo-zkapp-proof.sexp");

    #[test]
    fn sexp_printer_round_trips_jsoo_fixture() {
        let fixture = FIXTURE.trim_end_matches('\n');
        let parsed = parse(fixture).expect("parse fixture");
        let printed = parsed.to_string_mach();
        assert_eq!(printed, fixture, "sexplib mach printer must match jsoo output");
    }

    /// Compares tree structure only (atom values ignored). Returns the path to
    /// the first mismatch, or None if the shapes match.
    fn shape_diff(a: &Sexp, b: &Sexp, path: &str) -> Option<String> {
        match (a, b) {
            (Sexp::Atom(_), Sexp::Atom(_)) => None,
            (Sexp::List(x), Sexp::List(y)) => {
                if x.len() != y.len() {
                    // Include the first atom name (if any) to locate the node.
                    let name = |v: &[Sexp]| match v.first() {
                        Some(Sexp::Atom(s)) => s.clone(),
                        _ => "?".into(),
                    };
                    return Some(format!(
                        "{path}: len {} != {} (mine='{}' fixture='{}')",
                        x.len(),
                        y.len(),
                        name(x),
                        name(y)
                    ));
                }
                for (i, (xi, yi)) in x.iter().zip(y).enumerate() {
                    let label = match xi {
                        Sexp::List(v) => match v.first() {
                            Some(Sexp::Atom(s)) => s.clone(),
                            _ => i.to_string(),
                        },
                        _ => i.to_string(),
                    };
                    if let Some(d) = shape_diff(xi, yi, &format!("{path}/{label}")) {
                        return Some(d);
                    }
                }
                None
            }
            (Sexp::Atom(x), Sexp::List(_)) => Some(format!("{path}: atom '{x}' vs list")),
            (Sexp::List(_), Sexp::Atom(y)) => Some(format!("{path}: list vs atom '{y}'")),
        }
    }

    #[test]
    fn structured_sexp_shape_matches_fixture() {
        let fixture = parse(FIXTURE.trim_end_matches('\n')).expect("parse");
        let mine = dummy_wrap_proof().to_transaction_sexp();
        if let Some(d) = shape_diff(&mine, &fixture, "") {
            panic!("shape mismatch at {d}");
        }
    }

    // ---- dummy builder (correct shapes, arbitrary values) ----
    use crate::mina_bin_prot::{
        WrapMessagesForNextWrapProofV1, WrapProofBaseV3, WrapProofPrevEvalsV2,
        WrapStatementMinimalV1, WrapWireProofV1,
    };
    use ::kimchi::circuits::wires::{COLUMNS, PERMUTS};
    use kimchi::proof::{PointEvaluations, ProofEvaluations};

    fn pe() -> PointEvaluations<Vec<Fp>> {
        PointEvaluations {
            zeta: vec![Fp::from(1u64)],
            zeta_omega: vec![Fp::from(2u64)],
        }
    }
    fn dummy_evals() -> ProofEvaluations<PointEvaluations<Vec<Fp>>> {
        ProofEvaluations {
            public: Some(pe()),
            w: core::array::from_fn(|_| pe()),
            z: pe(),
            s: core::array::from_fn(|_| pe()),
            coefficients: core::array::from_fn(|_| pe()),
            generic_selector: pe(),
            poseidon_selector: pe(),
            complete_add_selector: pe(),
            mul_selector: pe(),
            emul_selector: pe(),
            endomul_scalar_selector: pe(),
            range_check0_selector: None,
            range_check1_selector: None,
            foreign_field_add_selector: None,
            foreign_field_mul_selector: None,
            xor_selector: None,
            rot_selector: None,
            lookup_aggregation: None,
            lookup_table: None,
            lookup_sorted: core::array::from_fn(|_| None),
            runtime_lookup_table: None,
            runtime_lookup_table_selector: None,
            xor_lookup_selector: None,
            lookup_gate_lookup_selector: None,
            range_check_lookup_selector: None,
            foreign_field_mul_lookup_selector: None,
        }
    }
    fn dummy_wire() -> WrapWireProofV1 {
        let fp = |n: u64| (Fp::from(n), Fp::from(n + 1));
        let fq = |n: u64| (Fq::from(n), Fq::from(n + 1));
        WrapWireProofV1 {
            w_comm: core::array::from_fn(|i| fp(i as u64)),
            z_comm: fp(0),
            t_comm: core::array::from_fn(|i| fp(i as u64)),
            w: core::array::from_fn(|i| fq(i as u64)),
            coefficients: core::array::from_fn(|i| fq(i as u64)),
            z: fq(0),
            s: core::array::from_fn(|i| fq(i as u64)),
            generic_selector: fq(0),
            poseidon_selector: fq(0),
            complete_add_selector: fq(0),
            mul_selector: fq(0),
            emul_selector: fq(0),
            endomul_scalar_selector: fq(0),
            ft_eval1: Fq::from(7u64),
            bulletproof_lr: (0..15).map(|i| (fp(i), fp(i + 100))).collect(),
            z_1: Fq::from(1u64),
            z_2: Fq::from(2u64),
            delta: fp(9),
            challenge_polynomial_commitment: fp(11),
        }
    }
    fn dummy_wrap_proof() -> WrapProofBaseV3 {
        // 40-element flattened statement (24 fixed + 16 bp rounds). Index 29 is
        // branch_data (byte = domain_log2<<2 | proofs_verified_mask).
        let mut flattened: Vec<Fq> = (0..40).map(Fq::from).collect();
        flattened[29] = Fq::from(40u64); // domain_log2=10, proofs_verified=0
        let messages_for_next_wrap_proof = WrapMessagesForNextWrapProofV1 {
            challenge_polynomial_commitment: (Fq::from(3u64), Fq::from(4u64)),
            old_bulletproof_challenges: vec![
                (0..15).map(Fq::from).collect(),
                (0..15).map(Fq::from).collect(),
            ],
        };
        let stable_statement = WrapStatementMinimalV1 {
            flattened: flattened.clone(),
            messages_for_next_wrap_proof,
            messages_for_next_step_proof: crate::mina_bin_prot::StepMessagesForNextProofV1 {
                challenge_polynomial_commitments: Vec::new(),
                old_bulletproof_challenges: Vec::new(),
            },
        };
        let _ = (COLUMNS, PERMUTS);
        WrapProofBaseV3 {
            statement: flattened,
            stable_statement,
            prev_evals: WrapProofPrevEvalsV2 {
                ft_eval1: Fp::from(5u64),
                evals: dummy_evals(),
            },
            proof: dummy_wire(),
        }
    }

    fn dump(s: &Sexp, depth: usize, max_depth: usize, out: &mut String) {
        let pad = "  ".repeat(depth);
        match s {
            Sexp::Atom(a) => {
                let a = if a.len() > 24 { format!("{}…", &a[..24]) } else { a.clone() };
                out.push_str(&format!("{pad}A {a}\n"));
            }
            Sexp::List(items) => {
                // key-value list: (name value)
                if depth >= max_depth {
                    out.push_str(&format!("{pad}L[{}] …\n", items.len()));
                    return;
                }
                out.push_str(&format!("{pad}L[{}]\n", items.len()));
                for it in items.iter().take(6) {
                    dump(it, depth + 1, max_depth, out);
                }
                if items.len() > 6 {
                    out.push_str(&format!("{pad}  …(+{} more)\n", items.len() - 6));
                }
            }
        }
    }

    #[test]
    #[ignore]
    fn dump_structure() {
        let fixture = FIXTURE.trim_end_matches('\n');
        let parsed = parse(fixture).expect("parse");
        let mut out = String::new();
        dump(&parsed, 0, 9, &mut out);
        std::fs::write("/tmp/sexp-structure.txt", &out).unwrap();
        eprintln!("wrote /tmp/sexp-structure.txt ({} lines)", out.lines().count());
    }
}

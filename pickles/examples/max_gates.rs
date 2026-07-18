//! Finds and exercises the largest o1js-compatible step circuit that fits
//! the fixed Tick domain (2^16 rows).
//!
//! This deliberately measures the complete Pickles step circuit, including
//! its public input, dummy selector constraints, accumulator hash, and Kimchi
//! ZK rows. It therefore avoids confusing the 65,536-row domain with 65,536
//! application constraints.
//!
//! Run with:
//!   cargo run -p pickles --release --example max_gates

use ark_ff::Zero;
use mina_curves::pasta::Fp;
use pickles::{
    api::StepCircuit,
    recorded::{LinComb, RecordedApp, RecordedCircuit, RecordedConstraint},
};
use snarky::api::SnarkyCircuit as _;

const DOMAIN_LOG2: u32 = 16;
const DOMAIN_ROWS: usize = 1 << DOMAIN_LOG2;

fn zero_generic() -> RecordedConstraint {
    RecordedConstraint::Generic {
        cl: Fp::zero(),
        l: LinComb::var(0),
        cr: Fp::zero(),
        r: LinComb::var(0),
        co: Fp::zero(),
        o: LinComb::default(),
        m: Fp::zero(),
        c: Fp::zero(),
    }
}

fn domain_log2(application_gates: usize) -> u32 {
    let circuit = RecordedCircuit {
        aux_count: 1,
        output: vec![],
        constraints: vec![zero_generic(); application_gates],
    };
    StepCircuit {
        app: RecordedApp { circuit },
    }
    .domain_log2()
    .expect("constraint-system compilation")
}

fn main() {
    // Find the exact boundary instead of hard-coding Pickles' current
    // framework overhead. This keeps the example valid when that overhead
    // changes while still detecting a regression in the 2^16 capacity.
    let mut fits = 0usize;
    // A Kimchi Generic row carries two independent Generic constraints.
    let mut exceeds = 2 * DOMAIN_ROWS;
    assert!(domain_log2(exceeds) > DOMAIN_LOG2);
    while fits + 1 < exceeds {
        let candidate = fits + (exceeds - fits) / 2;
        if domain_log2(candidate) <= DOMAIN_LOG2 {
            fits = candidate;
        } else {
            exceeds = candidate;
        }
    }

    let full_domain = domain_log2(fits);
    let overflow_domain = domain_log2(fits + 1);
    assert_eq!(full_domain, DOMAIN_LOG2);
    assert!(overflow_domain > DOMAIN_LOG2);

    println!("o1js/Pickles step capacity boundary");
    println!("  domain: 2^{DOMAIN_LOG2} = {DOMAIN_ROWS} rows");
    println!("  maximum Generic half-gates from the application: {fits}");
    println!(
        "  non-application capacity: about {} row-equivalents",
        (2 * DOMAIN_ROWS - fits).div_ceil(2)
    );
    println!("  one more application constraint selects domain 2^{overflow_domain}");
}

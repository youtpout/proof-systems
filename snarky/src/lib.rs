// TODO: uncomment
// #![deny(missing_docs)]

//! Snarky is the front end to kimchi, allowing users to write their own programs and convert them to kimchi circuits.
//!
//! This crate is the Rust port of the OCaml snarky library
//! (<https://github.com/o1-labs/snarky>), resurrected from the DSL that used to
//! live in `kimchi/src/snarky`.
//!
//! See the `tests.rs` file and the `tests/` directory for examples of how to use snarky.

pub mod api;
pub mod asm;
pub mod boolean;
pub mod constants;
pub mod constraint_system;
pub mod cvar;
pub mod errors;
pub mod gadgets;
pub mod poseidon;
pub mod range_checks;
pub mod runner;
pub mod snarky_type;
pub mod union_find;

#[cfg(test)]
mod tests;

/// The number of full rounds of the Poseidon permutation used by kimchi.
/// The OCaml snarky is kimchi-only, so this crate fixes the sponge width
/// instead of threading a const generic through every type.
pub const FULL_ROUNDS: usize = mina_poseidon::pasta::FULL_ROUNDS;

pub use boolean::Boolean;
pub use cvar::FieldVar;
pub use errors::SnarkyResult;
pub use runner::RunState;
pub use snarky_type::{CircuitAndValue, SnarkyType};

/// Handy macro to return the filename and line number of a place in the code.
#[macro_export]
macro_rules! loc {
    () => {{
        ::std::borrow::Cow::Borrowed(concat!(file!(), ":", line!()))
    }};
}

/// A handy module that you can import the content of to easily use snarky.
pub mod prelude {
    use super::*;
    pub use crate::loc;
    pub use api::SnarkyCircuit;
    pub use boolean::Boolean;
    pub use cvar::FieldVar;
    pub use errors::SnarkyResult;
    pub use runner::RunState;
    pub use snarky_type::SnarkyType;
}

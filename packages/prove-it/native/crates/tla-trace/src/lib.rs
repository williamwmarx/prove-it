//! Rebuilds the states of a trace as TLC does, by evaluating them again from the initial
//! predicate along the path the engine found, so that each value prints as TLC built it: a
//! record in the order written until TLC sorts it, an interval as `1..3`, and the lazy sets TLC
//! keeps. The engine's store interns values and keeps none of that (native/DESIGN.md 2.8). The
//! evaluator works on values of its own ([`value`]) and only reads the store, to find the state
//! the search found among the candidates. native/design/trace.md has the plan.
//!
//! The evaluator recurses with the expressions and values it evaluates, so a caller runs it on a
//! thread with a deep stack, as the search runs.

mod action;
mod eval;
mod print;
mod rebuild;
mod sets;
mod value;

pub use print::{format_printed, format_value};
pub use rebuild::Rebuilder;
pub use value::Value;

/// Where the evaluator can't follow TLC yet: the caller reports `not native yet: <reason>`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unsupported(pub String);

/// The states of a trace as TLC prints them.
pub struct Trace {
    pub states: Vec<TraceState>,
}

pub struct TraceState {
    /// Each variable's value, in the IR's order of the variables, as TLC holds it when it prints
    /// the state: sorted where TLC fingerprinted the state.
    pub values: Vec<Value>,
}

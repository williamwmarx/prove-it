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
mod alias;
mod eval;
mod failure;
mod fingerprint;
mod postcondition;
mod pretty;
mod print;
mod random;
mod rebuild;
mod sets;
mod split;
mod value;

pub use alias::Alias;
pub use eval::Registers;
pub use failure::{Failure, FingerprintFailure, Incomplete, Replay, Site, format_call_stack};
pub use postcondition::{Checked, CounterExample, PostconditionInputs, Stats, Verdict};
pub use pretty::pretty_print;
pub use print::{format_printed, format_value};
pub use rebuild::Rebuilder;
pub use split::{Described, SpecDescription, add_actions, add_spec};
pub use value::Value;

/// Where the evaluator can't follow TLC yet: the caller reports `not native yet: <reason>`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unsupported(pub String);

/// What the last state of a trace is to TLC, which decides how TLC finds it and which states it
/// rebuilds (`known` in `toTrace`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ending {
    /// A state the search kept, as a deadlock's: TLC recovers every state.
    Kept,
    /// A state that violates an invariant or an action property, which TLC holds as it found it:
    /// matched by its value, and printed with the one before it as TLC has them.
    Violation,
    /// A lasso's last state: TLC recovers every state, and doesn't rebuild the trace again.
    Lasso,
}

/// The states of a trace as TLC prints them, with what the spec printed as TLC rebuilt them. Each
/// print is the text of each value Print or PrintT printed, which the caller pretty prints and
/// joins as it does a print during the search.
pub struct Trace {
    pub states: Vec<TraceState>,
    /// What TLC prints after the trace, as it rebuilds a violation's trace once more
    /// (`traceOutput`); for a trace of one state, what the initial predicate printed.
    pub trace_output: Vec<Vec<String>>,
}

pub struct TraceState {
    /// Each variable's value, in the IR's order of the variables, as TLC holds it when it prints
    /// the state: sorted where TLC fingerprinted the state.
    pub values: Vec<Value>,
    /// The position in the model's actions of the action that took the step to this state, as
    /// `Tool.getState` finds it: the first whose walk reaches a state TLC takes for this one.
    /// `None` for the first state, a stuttering step, or a model whose IR carries no actions.
    pub action: Option<u32>,
    /// What TLC prints before the state.
    pub printed: Vec<Vec<String>>,
}

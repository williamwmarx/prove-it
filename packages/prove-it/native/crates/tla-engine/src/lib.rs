//! Prove It's native engine. M4 (native/DESIGN.md 11) compiles expressions: [`compile`] turns the
//! expressions of an engine IR into closures over the ids of a tla-values store, as
//! `src/engine/compile.ts` turns the TypeScript AST into closures over its ids, and a
//! [`machine::Machine`] runs them. The search is M5's.

pub mod clock;
pub mod compile;
pub mod context;
pub mod coverage;
pub mod footprint;
pub mod live;
mod log_file;
pub mod machine;
pub mod memo;
pub mod oracle;
pub mod search;
pub mod simulate;
pub mod symmetry;

pub use compile::{CompileError, Compiled, Compiler, Options, Root};
pub use machine::{Continue, Eval, Machine, Printed, Prints, Program, Registers, Step, UNASSIGNED};
pub use tla_values::on_nesting_stack;

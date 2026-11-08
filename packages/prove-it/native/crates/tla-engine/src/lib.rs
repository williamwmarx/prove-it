//! Prove It's native engine. M4 (native/DESIGN.md 11) compiles expressions: [`compile`] turns the
//! expressions of an engine IR into closures over the ids of a tla-values store, as
//! `src/engine/compile.ts` turns the TypeScript AST into closures over its ids, and a
//! [`machine::Machine`] runs them. The search is M5's.

pub mod compile;
pub mod footprint;
pub mod machine;
pub mod memo;

pub use compile::{CompileError, Compiled, Compiler, Options, Root};
pub use machine::{Eval, Machine, Program, UNASSIGNED};
pub use tla_values::on_nesting_stack;

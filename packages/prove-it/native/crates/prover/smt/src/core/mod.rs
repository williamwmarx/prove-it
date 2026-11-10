//! The SMT core, `src/prover/smt/solver/*.ts` (design/smt-core.md): one module per TypeScript
//! file.

pub mod ast;
pub mod case_split_queue;
pub mod cg_table;
pub mod clause;
pub mod enode;
pub mod expr_ref;
pub mod flat_literals;
pub mod goal;
pub mod literal;
pub mod ref_vector;
pub mod smtlib_parser;
pub mod sort;
pub mod sticky_generations;
pub mod var_subst;

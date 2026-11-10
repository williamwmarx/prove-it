//! The SMT core, `src/prover/smt/solver/*.ts` (design/smt-core.md): one module per TypeScript
//! file.

pub mod case_split_queue;
pub mod cg_table;
pub mod clause;
pub mod enode;
pub mod literal;
pub mod sort;
pub mod sticky_generations;

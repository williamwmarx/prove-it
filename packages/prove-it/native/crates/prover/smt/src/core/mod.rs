//! The SMT core, `src/prover/smt/solver/*.ts` (design/smt-core.md): one module per TypeScript
//! file.

pub mod asserted_formulas;
pub mod ast;
pub mod case_split_queue;
pub mod cg_table;
pub mod clause;
pub mod conflict_resolution;
pub mod context;
pub mod dyn_ack;
pub mod enode;
pub mod expr_ref;
pub mod flat_literals;
pub mod internalizer;
pub mod literal;
pub mod model_generator;
pub mod proto_model;
pub mod quantifier_manager;
pub mod ref_vector;
pub mod relevancy;
pub mod rewriter;
pub mod sort;
pub mod sticky_generations;
pub mod theory_lra;

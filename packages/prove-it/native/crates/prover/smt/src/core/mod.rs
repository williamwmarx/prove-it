//! The SMT core, `src/prover/smt/solver/*.ts` (design/smt-core.md): one module per TypeScript
//! file.

pub mod act_cache;
pub mod ast;
pub mod ast_lt;
pub mod ast_util;
pub mod case_split_queue;
pub mod cg_table;
pub mod clause;
pub mod enode;
pub mod expr_ref;
pub mod expr_safe_replace;
pub mod flat_literals;
pub mod literal;
pub mod ref_vector;
pub mod rewriter_tpl;
pub mod sort;
pub mod sticky_generations;
pub mod var_subst;

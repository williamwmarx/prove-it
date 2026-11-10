// STUB: replaced by the real port
//! The name and the signatures a literal port of `theory-lra*.ts` has, for the kernel.
//!
//! `TheoryLra` keeps `protected context: Context`, so (design/smt-core.md, "The context") its state
//! is a struct held by the context as `theory` (an `Option`, as the TypeScript's `theory!` starts
//! unassigned until `setup_context`), and the methods the kernel calls are `impl Context` methods
//! named `theory_<method>`. A theory variable is an `i32`, as `Enode::th_var` is (-1 for none).
//!
//! Methods that hand the theory something to work on (an atom, a term, an equality, an
//! assignment, a variable) are `todo!`. The others are inert, which is what the real theory does
//! while it has nothing: no theory variable, atom or bound can exist without one of the `todo!`
//! methods having run first, so the kernel runs propositional and EUF problems through them. They
//! are marked `STUB: inert`; the real theory also reads the cancel flag in some of them, so step
//! counts differ until it lands.

use crate::core::ast::{AstManager, Expr};
use crate::core::context::{Context, FC_DONE};
use crate::core::enode::EnodeId;
use crate::core::literal::BoolVar;
use crate::util::error::SmtError;

#[derive(Clone, Debug, Default)]
pub struct TheoryLra {}

impl TheoryLra {
    /// `new TheoryLra(context)`: the state, whose lp solver reads the context's resource limit.
    pub fn new(_m: &mut AstManager) -> TheoryLra {
        TheoryLra {}
    }
}

impl Context {
    /// init: register_plugin initializes each theory it registers. STUB: inert.
    pub fn theory_init(&mut self) -> Result<(), SmtError> {
        Ok(())
    }

    pub fn theory_assign_eh(&mut self, _bool_var: BoolVar, _is_true: bool) -> Result<(), SmtError> {
        todo!("theory_lra: not ported yet")
    }

    pub fn theory_relevant_eh(&mut self, _expr: Expr) -> Result<(), SmtError> {
        todo!("theory_lra: not ported yet")
    }

    pub fn theory_new_eq_eh(&mut self, _first: i32, _second: i32) -> Result<(), SmtError> {
        todo!("theory_lra: not ported yet")
    }

    pub fn theory_new_diseq_eh(&mut self, _first: i32, _second: i32) -> Result<(), SmtError> {
        todo!("theory_lra: not ported yet")
    }

    /// STUB: inert.
    pub fn theory_can_propagate(&self) -> bool {
        false
    }

    /// STUB: inert.
    pub fn theory_propagate(&mut self) -> Result<(), SmtError> {
        Ok(())
    }

    /// get_enode: the node of a theory variable.
    pub fn theory_get_enode(&self, _th_var: i32) -> EnodeId {
        todo!("theory_lra: not ported yet")
    }

    pub fn theory_internalize_eq_eh(&mut self, _eq: Expr) -> Result<(), SmtError> {
        todo!("theory_lra: not ported yet")
    }

    /// STUB: inert.
    pub fn theory_push_scope_eh(&mut self) -> Result<(), SmtError> {
        Ok(())
    }

    /// STUB: inert.
    pub fn theory_pop_scope_eh(&mut self, _num_scopes: u32) -> Result<(), SmtError> {
        Ok(())
    }

    /// An `FC_*` status. STUB: inert.
    pub fn theory_final_check_eh(&mut self, _level: u32) -> Result<u8, SmtError> {
        Ok(FC_DONE)
    }

    /// STUB: inert.
    pub fn theory_restart_eh(&mut self) -> Result<(), SmtError> {
        Ok(())
    }

    /// STUB: inert.
    pub fn theory_init_search_eh(&mut self) -> Result<(), SmtError> {
        Ok(())
    }

    /// Whether the theory took the atom.
    pub fn theory_internalize_atom(&mut self, _expr: Expr) -> Result<bool, SmtError> {
        todo!("theory_lra: not ported yet")
    }

    pub fn theory_is_attached_to_var(&self, _node: EnodeId) -> bool {
        todo!("theory_lra: not ported yet")
    }

    /// Whether the theory took the term.
    pub fn theory_internalize_term(&mut self, _expr: Expr) -> Result<bool, SmtError> {
        todo!("theory_lra: not ported yet")
    }
}

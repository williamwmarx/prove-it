// STUB: replaced by the real port
//! The name and the signatures a literal port of `model-finder.ts` has, for the quantifier
//! manager.
//!
//! `ModelFinder` keeps the context, so (design/smt-core.md, "The context") its state is a struct
//! held by the quantifier manager, and its methods that reach the context are `impl Context`
//! methods named `model_finder_<method>`. A quantifier gets in only through
//! `register_quantifier`, which is `todo!`, and a new constraint only through `fix_model`, also
//! `todo!`; the methods that act on those are inert (marked `STUB: inert`), which is what the real
//! finder does without them, so the kernel runs ground problems with MBQI on.

use crate::core::ast::{AstManager, Expr};
use crate::core::context::Context;
use crate::core::proto_model::ProtoModelRef;
use crate::util::error::SmtError;

#[derive(Clone, Debug, Default)]
pub struct ModelFinder {}

impl ModelFinder {
    /// `new ModelFinder(manager, context)`: its rewriters and its AUF solver, whose constructor
    /// takes one step that the stub does not.
    pub fn new(_m: &mut AstManager) -> ModelFinder {
        ModelFinder {}
    }

    /// STUB: inert.
    pub fn push_scope(&mut self) {}

    /// STUB: inert.
    pub fn pop_scope(&mut self, _m: &mut AstManager, _num_scopes: u32) -> Result<(), SmtError> {
        Ok(())
    }
}

impl Context {
    /// registerQuantifier: the quantifier's info, which the quantifier manager does not read.
    pub fn model_finder_register_quantifier(&mut self, _quantifier: Expr) -> Result<(), SmtError> {
        todo!("model_finder: not ported yet")
    }

    /// fix_model: tries to satisfy the relevant quantifiers by changing the model while keeping
    /// the ground formulas satisfied.
    pub fn model_finder_fix_model(&mut self, _model: &ProtoModelRef) -> Result<(), SmtError> {
        todo!("model_finder: not ported yet")
    }

    /// restart_eh: the constraints of the last model become axioms. STUB: inert.
    pub fn model_finder_restart_eh(&mut self) -> Result<(), SmtError> {
        Ok(())
    }
}

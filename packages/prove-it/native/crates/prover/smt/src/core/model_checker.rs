// STUB: replaced by the real port
//! The name and the signatures a literal port of `model-checker.ts` has, for the quantifier
//! manager.
//!
//! `ModelChecker` keeps the context, its model finder and its quantifier manager, so
//! (design/smt-core.md, "The context") its state is a struct held by the quantifier manager, and
//! its methods that reach the context are `impl Context` methods named `model_checker_<method>`.
//! The new instances come only from `check`, which is `todo!`; the methods that act on them are
//! inert (marked `STUB: inert`), which is what the real checker does without them.

use crate::core::ast::{AstManager, Expr};
use crate::core::context::Context;
use crate::core::enode::EnodeId;
use crate::core::proto_model::ProtoModelRef;
use crate::util::error::SmtError;
use crate::util::ordered_map::OrderedMap;

#[derive(Clone, Debug, Default)]
pub struct ModelChecker {}

impl ModelChecker {
    /// `new ModelChecker(context, finder, qmanager)`.
    pub fn new(_m: &mut AstManager) -> ModelChecker {
        ModelChecker {}
    }

    /// STUB: inert (it resets the counters `check` reads).
    pub fn init_search_eh(&mut self) {}

    pub fn has_new_instances(&self) -> bool {
        todo!("model_checker: not ported yet")
    }
}

impl Context {
    /// check(md, root2value): whether the model satisfies every relevant quantifier.
    pub fn model_checker_check(
        &mut self,
        _model: &ProtoModelRef,
        _root2value: &OrderedMap<EnodeId, Expr>,
    ) -> Result<bool, SmtError> {
        todo!("model_checker: not ported yet")
    }

    /// restart_eh: assert_new_instances. STUB: inert.
    pub fn model_checker_restart_eh(&mut self) -> Result<(), SmtError> {
        Ok(())
    }
}

// STUB: replaced by the real port
//! The name and the signatures a literal port of `quantifier-manager.ts` has, for the kernel.
//!
//! `DefaultQuantifierManager` keeps `private context: Context`, so (design/smt-core.md, "The
//! context") its state is a struct held by the context as `qmanager`, the methods that touch only
//! its own fields stay on it, and the methods that reach the context are `impl Context` methods
//! named `qmanager_<method>`.
//!
//! `add` is the only way a quantifier gets in, and it is `todo!`. The methods that only act on the
//! quantifiers there are keep their TypeScript guard, or are inert (marked `STUB: inert`), which is
//! what the real manager does while it has no quantifier, so the kernel runs ground problems
//! through them.

use crate::core::ast::{AstManager, Expr};
use crate::core::context::{Context, FC_CONTINUE, FC_DONE};
use crate::core::enode::EnodeId;
use crate::core::proto_model::ProtoModelRef;
use crate::util::error::SmtError;
use crate::util::ordered_map::OrderedMap;
use std::collections::HashMap;

#[derive(Clone, Debug, Default)]
pub struct DefaultQuantifierManager {
    pub quantifiers: Vec<Expr>,
    generations: HashMap<Expr, u32>,
    /// What the trail closure of `finalCheckEh` restores (`TrailClosure::LazyMatchingIndex`).
    pub lazy_matching_index: u32,
}

impl DefaultQuantifierManager {
    /// `new DefaultQuantifierManager(context, isMbqi)`: its matchers, queue and fingerprints, and
    /// the model finder and checker with MBQI.
    pub fn new(_m: &mut AstManager, _is_mbqi: bool) -> Self {
        DefaultQuantifierManager::default()
    }

    pub fn del(&mut self, quantifier: Expr) {
        self.quantifiers.pop();
        self.generations.remove(&quantifier);
    }

    pub fn has_quantifiers(&self) -> bool {
        !self.quantifiers.is_empty()
    }

    pub fn get_generation(&self, quantifier: Expr) -> u32 {
        self.generations.get(&quantifier).copied().unwrap_or(0)
    }

    pub fn is_model_based(&self) -> bool {
        todo!("quantifier_manager: not ported yet")
    }
}

impl Context {
    /// add: the finder registers the quantifier too.
    pub fn qmanager_add(&mut self, _quantifier: Expr, _generation: u32) -> Result<(), SmtError> {
        todo!("quantifier_manager: not ported yet")
    }

    pub fn qmanager_assign_eh(&mut self, _quantifier: Expr) -> Result<(), SmtError> {
        todo!("quantifier_manager: not ported yet")
    }

    pub fn qmanager_add_eq_eh(
        &mut self,
        _first: EnodeId,
        _second: EnodeId,
    ) -> Result<(), SmtError> {
        if !self.qmanager.quantifiers.is_empty() {
            todo!("quantifier_manager: not ported yet")
        }
        Ok(())
    }

    pub fn qmanager_relevant_eh(&mut self, _node: EnodeId) -> Result<(), SmtError> {
        if self.qmanager.quantifiers.is_empty() {
            return Ok(());
        }
        todo!("quantifier_manager: not ported yet")
    }

    /// STUB: inert.
    pub fn qmanager_push(&mut self) -> Result<(), SmtError> {
        Ok(())
    }

    /// STUB: inert.
    pub fn qmanager_pop(&mut self, _num_scopes: u32) -> Result<(), SmtError> {
        Ok(())
    }

    /// STUB: inert (no instance is queued and no matcher is active).
    pub fn qmanager_can_propagate(&self) -> bool {
        false
    }

    /// STUB: inert (the queue is empty).
    pub fn qmanager_propagate(&mut self) -> Result<(), SmtError> {
        Ok(())
    }

    /// An `FC_*` status. STUB: what it is without a quantifier or a delayed instance.
    pub fn qmanager_final_check_eh(&mut self, is_full: bool) -> Result<u8, SmtError> {
        if !is_full {
            return Ok(FC_DONE);
        }
        if !self.qmanager.quantifiers.is_empty() {
            todo!("quantifier_manager: not ported yet")
        }
        Ok(if self.can_propagate() {
            FC_CONTINUE
        } else {
            FC_DONE
        })
    }

    /// STUB: inert.
    pub fn qmanager_init_search_eh(&mut self) -> Result<(), SmtError> {
        self.qmanager.lazy_matching_index = 0;
        Ok(())
    }

    /// STUB: inert.
    pub fn qmanager_restart_eh(&mut self) -> Result<(), SmtError> {
        Ok(())
    }

    /// adjust_model: the finder fixes the model with MBQI.
    pub fn qmanager_adjust_model(&mut self, _model: &ProtoModelRef) -> Result<(), SmtError> {
        todo!("quantifier_manager: not ported yet")
    }

    /// check_model: a `CHECK_MODEL_*` status.
    pub fn qmanager_check_model(
        &mut self,
        _model: &ProtoModelRef,
        _root2value: &OrderedMap<EnodeId, Expr>,
    ) -> Result<u8, SmtError> {
        todo!("quantifier_manager: not ported yet")
    }
}

// STUB: replaced by the real port
//! The name and the signatures a literal port of `proto-model.ts` has, for the kernel's model
//! state (`context.ts`'s resetModel, mkProtoModel, getModel, validateModel).
//!
//! A `ProtoModel` is shared by its holders (the context's model state, the generated model, the
//! model checker that gets it from `get_model`), which the TypeScript counts with `incRef` and
//! `decRef`; the last `dec_ref` releases what it holds. So the kernel holds it as a
//! `ProtoModelRef`, and keeps the explicit counts at the TypeScript's places.

use std::cell::RefCell;
use std::rc::Rc;

use crate::core::ast::{AstManager, Decl, Expr};
use crate::util::error::SmtError;
use crate::util::hashtable::ObjMap;

pub type ProtoModelRef = Rc<RefCell<ProtoModel>>;

#[derive(Default)]
pub struct ProtoModel {
    /// m_interp: the value of each constant, keyed by declaration, hashed by
    /// `AstManager::get_decl_hash`.
    pub const_interps: ObjMap<Expr>,
}

impl ProtoModel {
    /// model_core::register_decl: the model holds the declaration and the value.
    pub fn register_const(
        &mut self,
        _m: &mut AstManager,
        _decl: Decl,
        _value: Expr,
    ) -> Result<(), SmtError> {
        todo!("proto_model: not ported yet")
    }

    /// The value of a ground expression, which the caller holds a reference to.
    pub fn eval(
        &mut self,
        _m: &mut AstManager,
        _expr: Expr,
        _is_model_completion: bool,
    ) -> Result<Expr, SmtError> {
        todo!("proto_model: not ported yet")
    }

    pub fn complete_partial_funcs(
        &mut self,
        _m: &mut AstManager,
        _is_using_fresh: bool,
    ) -> Result<(), SmtError> {
        todo!("proto_model: not ported yet")
    }

    pub fn cleanup(&mut self, _m: &mut AstManager) -> Result<(), SmtError> {
        todo!("proto_model: not ported yet")
    }

    /// mk_model: the model this proto model makes, with no holder yet.
    pub fn mk_model(&mut self, _m: &mut AstManager) -> Result<ProtoModel, SmtError> {
        todo!("proto_model: not ported yet")
    }

    pub fn inc_ref(&mut self) {
        todo!("proto_model: not ported yet")
    }

    /// The last holder releases the model's references.
    pub fn dec_ref(&mut self, _m: &mut AstManager) -> Result<(), SmtError> {
        todo!("proto_model: not ported yet")
    }
}

// STUB: replaced by the real port
//! The name and the signatures a literal port of `model-generator.ts` has, for
//! `Context::mk_proto_model`.

use crate::core::ast::Expr;
use crate::core::context::Context;
use crate::core::enode::EnodeId;
use crate::core::proto_model::ProtoModelRef;
use crate::util::error::SmtError;
use crate::util::ordered_map::OrderedMap;

pub struct GeneratedModel {
    pub model: ProtoModelRef,
    /// The value of each relevant root, in the order the generator set them.
    pub root2value: OrderedMap<EnodeId, Expr>,
}

/// mkModel: the model of the context's current assignment.
pub fn mk_model(_context: &mut Context) -> Result<GeneratedModel, SmtError> {
    todo!("model_generator: not ported yet")
}

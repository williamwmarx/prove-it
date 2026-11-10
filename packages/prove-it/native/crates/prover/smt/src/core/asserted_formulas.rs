// STUB: replaced by the real port
//! The name and the signatures a literal port of `asserted-formulas.ts` has, for
//! `Context::internalize_assertions`.

use crate::core::ast::{AstManager, Expr};
use crate::util::error::SmtError;

#[derive(Clone, Debug, Default)]
pub struct AssertedFormulas {
    /// m_inconsistent: whether a formula is false, after which no formula is added or
    /// preprocessed.
    pub is_inconsistent: bool,
}

impl AssertedFormulas {
    /// reduce: the formulas asserted since the last call, preprocessed; none once inconsistent.
    /// The asserted formulas keep holding them.
    pub fn reduce(&mut self, _m: &mut AstManager) -> Result<Vec<Expr>, SmtError> {
        todo!("asserted_formulas: not ported yet")
    }
}

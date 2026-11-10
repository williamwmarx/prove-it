// STUB: replaced by the real port on merge
//! Ported from Z3 (src/ast/rewriter/var_subst.cpp), MIT license, through `var-subst.ts`.
//! Substitution and shifting of de Bruijn variables. Only what `smtlib_parser` calls, until the port
//! of `var-subst.ts` lands.

use crate::core::ast::{AstManager, Expr};
use crate::util::error::SmtError;

/// Rebuilds expr with each free variable replaced. replace gets the variable, its de Bruijn index
/// relative to expr, and the number of binders above it.
pub fn replace_free_vars(
    _m: &mut AstManager,
    _expr: Expr,
    _replace: impl FnMut(&mut AstManager, Expr, i32, i32) -> Expr,
) -> Result<Expr, SmtError> {
    todo!("var_subst: ported in core-rewriter-tpl")
}

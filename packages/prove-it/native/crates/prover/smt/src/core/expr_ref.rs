//! Ported from Z3 (src/ast/ast.h), MIT license, through `expr-ref.ts`. The assignments of
//! expr_ref, for code that keeps Z3's reference counts by hand so that expressions are created and
//! deleted in Z3's order. -1 stands for a null expression.

use crate::core::ast::{AstManager, Expr};
use crate::util::error::SmtError;

/// expr_ref's assignment: the new value gains a reference before the old one loses its own.
pub fn assign(manager: &mut AstManager, old: Expr, value: Expr) -> Result<Expr, SmtError> {
    if value != -1 {
        manager.inc_ref(value);
    }
    if old != -1 {
        manager.dec_ref(old)?;
    }
    Ok(value)
}

/// expr_ref's move assignment of a value the caller owns.
pub fn assign_owned(manager: &mut AstManager, old: Expr, value: Expr) -> Result<Expr, SmtError> {
    if old != -1 {
        manager.dec_ref(old)?;
    }
    Ok(value)
}

pub fn release(manager: &mut AstManager, expr: Expr) -> Result<(), SmtError> {
    if expr != -1 {
        manager.dec_ref(expr)?;
    }
    Ok(())
}

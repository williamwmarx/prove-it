//! Ported from Z3 (src/ast/ast_util.cpp), MIT license, through `ast-util.ts`. Flattening of
//! conjunctions and disjunctions in Z3's worklist order, and negation that strips a negation
//! instead of nesting one.

use std::collections::HashSet;

use crate::core::ast::{AstManager, Expr, OP_AND, OP_IMPLIES, OP_NOT, OP_OR};
use crate::core::ref_vector::RefVector;
use crate::core::rewriter_tpl::MAX_RECURSION_DEPTH;
use crate::util::error::SmtError;

/// mk_not.
pub fn mk_not(m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
    if m.is_not(expr) {
        Ok(m.get_arg(expr, 0))
    } else if m.is_true(expr) {
        Ok(m.false_expr)
    } else if m.is_false(expr) {
        Ok(m.true_expr)
    } else {
        m.mk_not(expr)
    }
}

// result.set(index, the last item), then result.pop().
fn replace_by_last(
    m: &mut AstManager,
    result: &mut RefVector,
    index: usize,
) -> Result<(), SmtError> {
    let last = result.items[result.len() - 1];
    result.set(m, index, last)?;
    result.pop(m)
}

// flatten_and and flatten_or on an expr_ref_vector, with Z3's references: the vector holds its
// expressions, and pin holds each visited one until the end. An index that the TypeScript
// decrements to visit again is kept.
fn flatten_vector(
    m: &mut AstManager,
    result: &mut RefVector,
    is_and: bool,
) -> Result<(), SmtError> {
    let mut pin = RefVector::new();
    let mut seen = HashSet::new();
    let junction = if is_and { OP_AND } else { OP_OR };
    let dual = if is_and { OP_OR } else { OP_AND };
    let unit = if is_and { m.true_expr } else { m.false_expr };
    let zero = if is_and { m.false_expr } else { m.true_expr };
    let mut index = 0;
    while index < result.len() {
        let expr = result.items[index];
        if !seen.insert(expr) {
            replace_by_last(m, result, index)?;
            continue;
        }
        pin.push(m, expr);
        let inner = if m.is_not(expr) {
            m.get_arg(expr, 0)
        } else {
            -1
        };
        let inner_op = if inner == -1 { -1 } else { m.get_op(inner) };
        if m.get_op(expr) == junction {
            for arg_index in 0..m.get_num_args(expr) {
                let arg = m.get_arg(expr, arg_index);
                result.push(m, arg);
            }
            replace_by_last(m, result, index)?;
            continue;
        }
        if inner_op == OP_NOT {
            let arg = m.get_arg(inner, 0);
            result.set(m, index, arg)?;
            continue;
        }
        if inner_op == dual {
            for arg_index in 0..m.get_num_args(inner) {
                let arg = m.get_arg(inner, arg_index);
                let negated = mk_not(m, arg)?;
                result.push(m, negated);
            }
            replace_by_last(m, result, index)?;
            continue;
        }
        if is_and && inner_op == OP_IMPLIES {
            let first = m.get_arg(inner, 0);
            result.push(m, first);
            let second = m.get_arg(inner, 1);
            let negated = mk_not(m, second)?;
            result.set(m, index, negated)?;
            continue;
        }
        if !is_and && m.get_op(expr) == OP_IMPLIES {
            let second = m.get_arg(expr, 1);
            result.push(m, second);
            let first = m.get_arg(expr, 0);
            let negated = mk_not(m, first)?;
            result.set(m, index, negated)?;
            continue;
        }
        if expr == unit || inner == zero {
            replace_by_last(m, result, index)?;
            continue;
        }
        if expr == zero || inner == unit {
            result.reset(m)?;
            result.push(m, zero);
            break;
        }
        index += 1;
    }
    pin.reset(m)
}

pub fn flatten_and_vector(m: &mut AstManager, result: &mut RefVector) -> Result<(), SmtError> {
    flatten_vector(m, result, true)
}

pub fn flatten_or_vector(m: &mut AstManager, result: &mut RefVector) -> Result<(), SmtError> {
    flatten_vector(m, result, false)
}

/// push_not with Z3's references: the result comes with a reference, which the caller releases.
pub fn push_not_owned(m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
    push_not_owned_at(m, expr, 0)
}

fn push_not_owned_at(m: &mut AstManager, expr: Expr, depth: usize) -> Result<Expr, SmtError> {
    let op = m.get_op(expr);
    if op != OP_AND && op != OP_OR {
        let result = mk_not(m, expr)?;
        m.inc_ref(result);
        return Ok(result);
    }
    if depth >= MAX_RECURSION_DEPTH {
        return Err(SmtError::Unsupported("push_not nests too deeply".into()));
    }
    let mut args = RefVector::new();
    for index in 0..m.get_num_args(expr) {
        let arg = m.get_arg(expr, index);
        args.push_owned(push_not_owned_at(m, arg, depth + 1)?);
    }
    let result = if op == OP_AND {
        m.mk_or(&args.items)?
    } else {
        m.mk_and(&args.items)?
    };
    m.inc_ref(result);
    args.reset(m)?;
    Ok(result)
}

// Ported from Zenon's prove.ml, as shipped in tlapm. Copyright 2002 INRIA, see LICENSE.
//! Zenon's newnodes: each rule in turn suggests nodes for a formula added to a branch, until one
//! says that the rest don't apply.

use std::rc::Rc;

use crate::ZenonError;
use crate::eqrel::Relations;
use crate::equality_rules::{
    add_congruence, add_matches, add_reflexivity, add_string_equalities, add_symmetric_matches,
    add_transitivity,
};
use crate::expr::{Expr, Expressions};
use crate::index_table::Index;
use crate::node::{Node, Queue, insert_node};
use crate::propositional_rules::{
    add_absurd, add_alpha, add_beta, add_closure, add_delta, add_gamma, add_junction_tree,
    add_unfold, add_useless,
};
use crate::tla::get_extension_nodes;

pub struct SearchContext {
    pub index: Index,
    pub relations: Relations,
    pub exprs: Expressions,
}

/// The queue with the rule's nodes, and whether the rules after it don't apply.
pub type RuleResult = (Queue, bool);

pub type SearchRule = fn(&mut SearchContext, &Queue, &Expr, i64) -> Result<RuleResult, ZenonError>;

pub fn unequal(exprs: &Expressions, left: &Expr, right: &Expr) -> Expr {
    exprs.enot(&exprs.eapp("=", &[left.clone(), right.clone()]))
}

pub fn insert_all(queue: &Queue, nodes: Vec<Rc<Node>>) -> Queue {
    nodes
        .into_iter()
        .fold(queue.clone(), |current, node| insert_node(&current, node))
}

fn add_extensions(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let result = get_extension_nodes(&context.index, &context.exprs, formula, goalness)?;
    Ok((insert_all(queue, result.nodes), result.is_stopped))
}

// Zenon's newnodes_preunif comes after addReflexivity, but it never adds a node: it preunifies a
// formula with its negation, whose heads always differ.
const RULES: [SearchRule; 16] = [
    add_absurd,
    add_closure,
    add_extensions,
    add_junction_tree,
    add_alpha,
    add_beta,
    add_string_equalities,
    add_delta,
    add_gamma,
    add_unfold,
    add_reflexivity,
    add_congruence,
    add_transitivity,
    add_symmetric_matches,
    add_matches,
    add_useless,
];

pub fn add_nodes(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<Queue, ZenonError> {
    let mut current = queue.clone();
    for rule in RULES {
        let result = rule(context, &current, formula, goalness)?;
        current = result.0;
        if result.1 {
            break;
        }
    }
    Ok(current)
}

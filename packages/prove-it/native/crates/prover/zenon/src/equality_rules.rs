// Ported from Zenon's prove.ml, as shipped in tlapm. Copyright 2002 INRIA, see LICENSE.
//! The rules for equality and other relations: instances that unify a metavariable, matching a
//! literal against its negation, congruence, reflexivity, symmetry and transitivity.

use std::rc::Rc;

use crate::ZenonError;
use crate::expr::{Expr, Expressions, Kind};
use crate::index_table::get_head;
use crate::node::{Node, Priority, Queue, insert_node, make_node};
use crate::proof::{Rule, RuleName};
use crate::rules::{RuleResult, SearchContext, insert_all, unequal};

fn make_instance(
    exprs: &Expressions,
    queue: &Queue,
    quantified: &Expr,
    term: &Expr,
    goalness: i64,
) -> Result<Queue, ZenonError> {
    if quantified.kind == Kind::All {
        let instance = exprs.substitute(
            &[(quantified.args[0].clone(), term.clone())],
            &quantified.args[1],
        );
        return Ok(insert_node(
            queue,
            make_node(
                vec![quantified.clone()],
                Rule::new(RuleName::All, vec![quantified.clone(), term.clone()]),
                Priority::Instance(quantified.clone()),
                goalness,
                vec![vec![instance]],
            ),
        ));
    }
    if quantified.kind == Kind::Ex {
        let instance = exprs.substitute(
            &[(quantified.args[0].clone(), term.clone())],
            &exprs.enot(&quantified.args[1]),
        );
        let negated = exprs.enot(quantified);
        return Ok(insert_node(
            queue,
            make_node(
                vec![negated.clone()],
                Rule::new(RuleName::NotEx, vec![negated, term.clone()]),
                Priority::Instance(quantified.clone()),
                goalness,
                vec![vec![instance]],
            ),
        ));
    }
    // Zenon hands applications to the extension named by the symbol's prefix, and tla has none.
    if quantified.kind == Kind::App {
        return Ok(queue.clone());
    }
    Err(ZenonError::new(
        "Zenon: make_inst on a formula that isn't quantified",
    ))
}

fn make_inequalities(exprs: &Expressions, left: &[Expr], right: &[Expr]) -> Vec<Vec<Expr>> {
    left.iter()
        .zip(right)
        .map(|(inner, other)| vec![unequal(exprs, inner, other)])
        .collect()
}

fn is_good_match(left: &Expr, right: &Expr) -> bool {
    if left.kind == Kind::Meta || right.kind == Kind::Meta {
        return true;
    }
    if left.kind != right.kind {
        return false;
    }
    match left.kind {
        Kind::Var | Kind::App => left.symbol == right.symbol,
        Kind::Not => is_good_match(&left.args[0], &right.args[0]),
        Kind::And | Kind::Or | Kind::Imply | Kind::Equiv => {
            is_good_match(&left.args[0], &right.args[0])
                || is_good_match(&left.args[1], &right.args[1])
        }
        Kind::True | Kind::False => true,
        Kind::Tau => left == right,
        _ => false,
    }
}

fn make_not_equiv(
    exprs: &Expressions,
    queue: &Queue,
    is_symmetric: bool,
    positive: &(Expr, i64),
    negative: &(Expr, i64),
) -> Queue {
    let atom = &positive.0;
    let negation = &negative.0;
    let negated = &negation.args[0];
    let args = &atom.args;
    let negated_args = &negated.args;
    if atom.is_app_with_arity("TLA.in", 2)
        && args[1].kind == Kind::Var
        && negated_args.len() == 2
        && args[1] != negated_args[1]
        && !args[0].is_meta()
        && !args[1].is_meta()
        && !negated_args[0].is_meta()
        && !negated_args[1].is_meta()
        && args[0] != negated_args[0]
    {
        return queue.clone();
    }
    if (is_symmetric && negated_args.len() != 2) || args.len() != negated_args.len() {
        return queue.clone();
    }
    let is_good = args
        .iter()
        .zip(negated_args)
        .all(|(inner, other)| is_good_match(inner, other));
    let priority = match (is_good, &*atom.symbol == "=") {
        (true, true) => Priority::ArityEq,
        (true, false) => Priority::Arity,
        (false, _) => Priority::Instance(atom.clone()),
    };
    let pair = vec![atom.clone(), negation.clone()];
    let rule = if is_symmetric {
        Rule::relation(RuleName::PNotPSym, &atom.symbol, pair)
    } else {
        Rule::new(RuleName::PNotP, pair)
    };
    let ordered: Vec<Expr> = if is_symmetric {
        args.iter().rev().cloned().collect()
    } else {
        args.clone()
    };
    insert_node(
        queue,
        make_node(
            vec![atom.clone(), negation.clone()],
            rule,
            priority,
            positive.1.min(negative.1),
            make_inequalities(exprs, &ordered, negated_args),
        ),
    )
}

/// The string literal's value, an expression, if `expression` is `$string` applied to one.
pub fn get_string_value(expression: &Expr) -> Option<Expr> {
    expression
        .is_app_with_arity("$string", 1)
        .then(|| expression.args[0].clone())
}

pub fn add_string_equalities(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let exprs = &context.exprs;
    if !formula.is_app_with_arity("=", 2) {
        return Ok((queue.clone(), false));
    }
    let is_right_string = get_string_value(&formula.args[1]).is_some();
    if !is_right_string && get_string_value(&formula.args[0]).is_none() {
        return Ok((queue.clone(), false));
    }
    let (string, term) = if is_right_string {
        (&formula.args[1], &formula.args[0])
    } else {
        (&formula.args[0], &formula.args[1])
    };
    let names = if is_right_string {
        [RuleName::Stringdiffll, RuleName::Stringdifflr]
    } else {
        [RuleName::Stringdiffrl, RuleName::Stringdiffrr]
    };
    let mut current = queue.clone();
    let mut visit = |name: RuleName, is_reversed: bool, pairs: Vec<(Expr, Rc<str>)>| {
        for pair in pairs {
            let other_string = exprs.eapp("$string", &[exprs.evar(&pair.1)]);
            let equality = exprs.eapp(
                "=",
                &if is_reversed {
                    [other_string.clone(), pair.0.clone()]
                } else {
                    [pair.0.clone(), other_string.clone()]
                },
            );
            if *string == other_string {
                continue;
            }
            current = insert_node(
                &current,
                make_node(
                    vec![formula.clone(), equality],
                    Rule::new(
                        name,
                        vec![term.clone(), string.clone(), pair.0.clone(), other_string],
                    ),
                    Priority::Prop,
                    goalness,
                    vec![vec![unequal(exprs, term, &pair.0)]],
                ),
            );
        }
    };
    visit(
        names[0],
        false,
        context
            .index
            .get_string_equalities()
            .iter()
            .cloned()
            .collect(),
    );
    visit(
        names[1],
        true,
        context
            .index
            .get_reversed_string_equalities()
            .iter()
            .cloned()
            .collect(),
    );
    Ok((current, false))
}

pub fn add_reflexivity(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let exprs = &context.exprs;
    if formula.kind != Kind::Not {
        return Ok((queue.clone(), false));
    }
    let atom = &formula.args[0];
    if !atom.is_relation() {
        return Ok((queue.clone(), false));
    }
    let left = &atom.args[0];
    let right = &atom.args[1];
    if &*atom.symbol != "=" {
        if !context.relations.is_reflexive(&atom.symbol) {
            return Ok((queue.clone(), false));
        }
        return Ok((
            insert_node(
                queue,
                make_node(
                    vec![formula.clone()],
                    Rule::relation(
                        RuleName::Refl,
                        &atom.symbol,
                        vec![left.clone(), right.clone()],
                    ),
                    Priority::Arity,
                    goalness,
                    vec![vec![unequal(exprs, left, right)]],
                ),
            ),
            false,
        ));
    }
    if left.kind == Kind::Meta && right.kind == Kind::Meta {
        let instantiated = make_instance(exprs, queue, &right.args[0], left, goalness)?;
        return Ok((
            make_instance(exprs, &instantiated, &left.args[0], right, goalness)?,
            false,
        ));
    }
    if left.kind == Kind::Meta {
        return Ok((
            make_instance(exprs, queue, &left.args[0], right, goalness)?,
            false,
        ));
    }
    if right.kind == Kind::Meta {
        return Ok((
            make_instance(exprs, queue, &right.args[0], left, goalness)?,
            false,
        ));
    }
    Ok((queue.clone(), false))
}

pub fn add_congruence(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let exprs = &context.exprs;
    if formula.kind != Kind::Not || !formula.args[0].is_app_with_arity("=", 2) {
        return Ok((queue.clone(), false));
    }
    let left = &formula.args[0].args[0];
    let right = &formula.args[0].args[1];
    if let (Some(left_string), Some(right_string)) =
        (get_string_value(left), get_string_value(right))
        && left_string != right_string
    {
        return Ok((queue.clone(), false));
    }
    if left.kind != Kind::App || right.kind != Kind::App || left.symbol != right.symbol {
        return Ok((queue.clone(), false));
    }
    if left.args.len() != right.args.len() {
        return Ok((queue.clone(), false));
    }
    Ok((
        insert_node(
            queue,
            make_node(
                vec![formula.clone()],
                Rule::new(RuleName::NotEqual, vec![left.clone(), right.clone()]),
                Priority::Arity,
                goalness,
                make_inequalities(exprs, &left.args, &right.args),
            ),
        ),
        false,
    ))
}

fn make_trans_node(
    exprs: &Expressions,
    is_symmetric: bool,
    positive: &(Expr, i64),
    negative: &(Expr, i64),
) -> Rc<Node> {
    let atom = &positive.0;
    let negated = &negative.0.args[0];
    let relation = &atom.symbol;
    let left = &atom.args[0];
    let right = &atom.args[1];
    let negated_left = &negated.args[0];
    let negated_right = &negated.args[1];
    let terms = if is_symmetric {
        [negated_right, left, right, negated_left]
    } else {
        [negated_left, left, right, negated_right]
    };
    let name = if is_symmetric {
        RuleName::TransSym
    } else {
        RuleName::Trans
    };
    make_node(
        vec![atom.clone(), negative.0.clone()],
        Rule::new(name, vec![atom.clone(), negative.0.clone()]),
        if &**relation == "=" {
            Priority::ArityEq
        } else {
            Priority::Arity
        },
        positive.1.min(negative.1),
        vec![
            vec![
                unequal(exprs, terms[0], terms[1]),
                exprs.enot(&exprs.eapp(relation, &[terms[0].clone(), terms[1].clone()])),
            ],
            vec![
                unequal(exprs, terms[2], terms[3]),
                exprs.enot(&exprs.eapp(relation, &[terms[2].clone(), terms[3].clone()])),
            ],
        ],
    )
}

fn make_trans_equality_node(
    context: &SearchContext,
    is_symmetric: bool,
    equality: &(Expr, i64),
    negative: &(Expr, i64),
) -> Rc<Node> {
    let exprs = &context.exprs;
    let left = &equality.0.args[0];
    let right = &equality.0.args[1];
    let negated = &negative.0.args[0];
    let relation = &negated.symbol;
    let negated_left = &negated.args[0];
    let negated_right = &negated.args[1];
    let is_relation_symmetric = context.relations.is_symmetric(relation);
    let terms = match (is_symmetric, is_relation_symmetric) {
        (true, true) => [negated_right, left, right, negated_left],
        (true, false) => [negated_left, right, left, negated_right],
        (false, _) => [negated_left, left, right, negated_right],
    };
    let first = exprs.enot(&exprs.eapp(relation, &[terms[0].clone(), terms[1].clone()]));
    let second = exprs.enot(&exprs.eapp(relation, &[terms[2].clone(), terms[3].clone()]));
    let name = match (is_symmetric, is_relation_symmetric) {
        (true, true) => RuleName::TransEqSym,
        (true, false) => RuleName::TransEq2,
        (false, _) => RuleName::TransEq,
    };
    make_node(
        vec![equality.0.clone(), negative.0.clone()],
        Rule::new(name, vec![left.clone(), right.clone(), negative.0.clone()]),
        if &**relation == "=" {
            Priority::ArityEq
        } else {
            Priority::Arity
        },
        equality.1.min(negative.1),
        vec![
            vec![unequal(exprs, terms[0], terms[1]), first.clone()],
            vec![first, second.clone()],
            vec![unequal(exprs, terms[2], terms[3]), second],
        ],
    )
}

pub fn add_transitivity(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    if formula.is_relation() && &*formula.symbol == "=" {
        let entry = (formula.clone(), goalness);
        let left = &formula.args[0];
        let right = &formula.args[1];
        if left.kind == Kind::Meta && right.kind == Kind::Meta {
            let nodes = context
                .index
                .find_negative("=")
                .iter()
                .filter(|matched| matched.0.is_negated_relation())
                .map(|matched| make_trans_equality_node(context, false, &entry, matched))
                .collect();
            return Ok((insert_all(queue, nodes), false));
        }
        if !context.index.add_trans(formula) {
            return Ok((queue.clone(), false));
        }
        let (Some(left_head), Some(right_head)) = (get_head(left), get_head(right)) else {
            return Ok((queue.clone(), false));
        };
        let index = &context.index;
        let trans_eq = |is_symmetric: bool, matches: Vec<(Expr, i64)>| {
            matches
                .iter()
                .map(|matched| make_trans_equality_node(context, is_symmetric, &entry, matched))
                .collect::<Vec<_>>()
        };
        let nodes = [
            trans_eq(false, index.find_all_neg_trans_left(&left_head)),
            trans_eq(true, index.find_all_neg_trans_left(&right_head)),
            trans_eq(true, index.find_all_neg_trans_right(&left_head)),
            trans_eq(false, index.find_all_neg_trans_right(&right_head)),
        ]
        .concat();
        return Ok((insert_all(queue, nodes), false));
    }
    let exprs = &context.exprs;
    if formula.is_relation() && context.relations.is_transitive(&formula.symbol) {
        let entry = (formula.clone(), goalness);
        let trans = |is_symmetric: bool, matches: Vec<(Expr, i64)>| {
            matches
                .iter()
                .map(|matched| make_trans_node(exprs, is_symmetric, &entry, matched))
                .collect::<Vec<_>>()
        };
        if !context.index.add_trans(formula) {
            return Ok((queue.clone(), false));
        }
        let relation = &formula.symbol;
        let (Some(left_head), Some(right_head)) =
            (get_head(&formula.args[0]), get_head(&formula.args[1]))
        else {
            return Ok((queue.clone(), false));
        };
        let index = &context.index;
        let is_symmetric = context.relations.is_symmetric(relation);
        let nodes = [
            trans(false, index.find_neg_trans_left(relation, &left_head)),
            trans(
                true,
                if is_symmetric {
                    index.find_neg_trans_left(relation, &right_head)
                } else {
                    Vec::new()
                },
            ),
            trans(
                true,
                if is_symmetric {
                    index.find_neg_trans_right(relation, &left_head)
                } else {
                    Vec::new()
                },
            ),
            trans(false, index.find_neg_trans_right(relation, &right_head)),
        ]
        .concat();
        return Ok((insert_all(queue, nodes), false));
    }
    if !formula.is_negated_relation() {
        return Ok((queue.clone(), false));
    }
    let atom = &formula.args[0];
    if !context.relations.is_transitive(&atom.symbol) {
        return Ok((queue.clone(), false));
    }
    let entry = (formula.clone(), goalness);
    let relation = &atom.symbol;
    context.index.add_neg_trans(formula);
    let (Some(left_head), Some(right_head)) = (get_head(&atom.args[0]), get_head(&atom.args[1]))
    else {
        return Ok((queue.clone(), false));
    };
    let context = &*context;
    let index = &context.index;
    let neg_trans = |is_symmetric: bool, matches: Vec<(Expr, i64)>| {
        matches
            .iter()
            .map(|matched| make_trans_node(&context.exprs, is_symmetric, matched, &entry))
            .collect::<Vec<_>>()
    };
    let neg_trans_eq = |is_symmetric: bool, matches: Vec<(Expr, i64)>| {
        matches
            .iter()
            .map(|matched| make_trans_equality_node(context, is_symmetric, matched, &entry))
            .collect::<Vec<_>>()
    };
    let is_symmetric = context.relations.is_symmetric(relation);
    let nodes = [
        neg_trans(false, index.find_trans_left(relation, &left_head)),
        neg_trans(
            true,
            if is_symmetric {
                index.find_trans_right(relation, &left_head)
            } else {
                Vec::new()
            },
        ),
        neg_trans(
            true,
            if is_symmetric {
                index.find_trans_left(relation, &right_head)
            } else {
                Vec::new()
            },
        ),
        neg_trans(false, index.find_trans_right(relation, &right_head)),
    ]
    .concat();
    let mut equality_nodes = if &**relation == "=" {
        Vec::new()
    } else {
        [
            neg_trans_eq(false, index.find_trans_left("=", &left_head)),
            neg_trans_eq(true, index.find_trans_right("=", &left_head)),
            neg_trans_eq(true, index.find_trans_left("=", &right_head)),
            neg_trans_eq(false, index.find_trans_right("=", &right_head)),
        ]
        .concat()
    };
    equality_nodes.reverse();
    equality_nodes.extend(nodes);
    Ok((insert_all(queue, equality_nodes), false))
}

pub fn add_symmetric_matches(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let entry = (formula.clone(), goalness);
    let atom = if formula.kind == Kind::Not {
        &formula.args[0]
    } else {
        formula
    };
    if !atom.is_relation() || &*atom.symbol == "=" {
        return Ok((queue.clone(), false));
    }
    if !context.relations.is_symmetric(&atom.symbol) {
        return Ok((queue.clone(), false));
    }
    let exprs = &context.exprs;
    if formula.kind == Kind::Not {
        let matches = context.index.find_positive(&atom.symbol);
        return Ok((
            matches.iter().fold(queue.clone(), |current, matched| {
                make_not_equiv(exprs, &current, true, matched, &entry)
            }),
            false,
        ));
    }
    let matches = context.index.find_negative(&atom.symbol);
    Ok((
        matches.iter().fold(queue.clone(), |current, matched| {
            make_not_equiv(exprs, &current, true, &entry, matched)
        }),
        false,
    ))
}

pub fn add_matches(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let entry = (formula.clone(), goalness);
    let atom = if formula.kind == Kind::Not {
        &formula.args[0]
    } else {
        formula
    };
    if atom.kind != Kind::App || &*atom.symbol == "=" {
        return Ok((queue.clone(), false));
    }
    let exprs = &context.exprs;
    if formula.kind == Kind::Not {
        let matches = context.index.find_positive(&atom.symbol);
        return Ok((
            matches.iter().fold(queue.clone(), |current, matched| {
                make_not_equiv(exprs, &current, false, matched, &entry)
            }),
            true,
        ));
    }
    let matches = context.index.find_negative(&atom.symbol);
    Ok((
        matches.iter().fold(queue.clone(), |current, matched| {
            make_not_equiv(exprs, &current, false, &entry, matched)
        }),
        true,
    ))
}

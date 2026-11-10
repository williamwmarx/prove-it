// Ported from Zenon's ext_tla.ml, as shipped in tlapm. Copyright 2008 INRIA, see LICENSE.
//! The rules for tuples and records.

use std::cmp::Ordering;
use std::rc::Rc;

use crate::expr::{Expr, Kind, compare_exprs};
use crate::node::Priority;
use crate::ocaml::stable_sort;
use crate::proof::{Rule, RuleName};
use crate::tla::terms::{
    Item, Literal, domain, equal, fapply, get_branches, get_pairs, is_trivially_not_in,
    make_extension_node, make_natural, member,
};

fn get_string_name(expression: &Expr) -> Option<Rc<str>> {
    (expression.is_app_with_arity("$string", 1) && expression.args[0].kind == Kind::Var)
        .then(|| expression.args[0].symbol.clone())
}

/// Zenon's check_record_labels on sorted fields: false for Invalid_record, a repeated label.
fn has_distinct_labels(pairs: &[(Expr, Expr)]) -> bool {
    pairs.windows(2).all(|window| {
        let left = &window[0].0;
        let right = &window[1].0;
        let left_name = get_string_name(left);
        !(left_name.is_some() && left_name == get_string_name(right)) && left != right
    })
}

fn sort_pairs(pairs: &[(Expr, Expr)]) -> Vec<(Expr, Expr)> {
    stable_sort(pairs, &|left: &(Expr, Expr), right: &(Expr, Expr)| {
        compare_exprs(&left.0, &right.0)
    })
}

fn get_sorted_labels(args: &[Expr]) -> Vec<Expr> {
    let labels: Vec<Expr> = get_pairs(args).into_iter().map(|pair| pair.0).collect();
    let sorted = stable_sort(&labels, &compare_exprs);
    sorted
        .iter()
        .enumerate()
        .filter(|(index, label)| {
            *index == 0 || compare_exprs(&sorted[index - 1], label) != Ordering::Equal
        })
        .map(|(_, label)| label.clone())
        .collect()
}

pub fn get_tuple_nodes(literal: &Literal) -> Option<Vec<Item>> {
    let exprs = literal.context.exprs;
    let formula = &literal.formula;
    let is_negated = literal.is_negated;
    let atom = &literal.atom;
    let node = |priority, rule, branches| make_extension_node(literal, priority, rule, branches);
    if is_negated && atom.is_app_with_arity("TLA.isASeq", 1) && atom.args[0].is_app("TLA.tuple") {
        return Some(node(
            Priority::Prop,
            Rule::new(RuleName::TupleNotisaseq, vec![formula.clone()]),
            vec![],
        ));
    }
    let relation = literal.relation.as_ref()?;
    let left = &relation.args[0];
    let right = &relation.args[1];
    let is_equality = &*relation.symbol == "=";
    let is_membership = &*relation.symbol == "TLA.in";
    if !is_negated && is_equality && left.is_app("TLA.tuple") && right.is_app("TLA.tuple") {
        if left.args.len() != right.args.len() {
            return Some(node(
                Priority::Prop,
                Rule::new(
                    RuleName::TupleEqMismatch,
                    vec![formula.clone(), formula.clone()],
                ),
                vec![],
            ));
        }
        let equalities: Vec<Expr> = left
            .args
            .iter()
            .zip(&right.args)
            .map(|(inner, other)| equal(exprs, inner, other))
            .collect();
        return Some(node(
            Priority::Prop,
            Rule::new(
                RuleName::TupleEqMatch,
                [vec![formula.clone()], equalities.clone()].concat(),
            ),
            vec![equalities],
        ));
    }
    if is_membership
        && right.is_app_with_arity("TLA.Product", 1)
        && right.args[0].is_app("TLA.tuple")
    {
        let element = left;
        let tuple = &right.args[0];
        if !is_negated {
            let components: Vec<Expr> = tuple
                .args
                .iter()
                .enumerate()
                .map(|(position, inner)| {
                    member(
                        exprs,
                        &fapply(exprs, element, &make_natural(exprs, position + 1)),
                        inner,
                    )
                })
                .collect();
            let is_sequence = exprs.eapp("TLA.isASeq", std::slice::from_ref(element));
            let has_length = equal(
                exprs,
                &exprs.eapp("TLA.Len", std::slice::from_ref(element)),
                &make_natural(exprs, tuple.args.len()),
            );
            return Some(node(
                Priority::Prop,
                Rule::new(
                    RuleName::InProduct,
                    [
                        vec![
                            formula.clone(),
                            element.clone(),
                            tuple.clone(),
                            is_sequence.clone(),
                            has_length.clone(),
                        ],
                        components.clone(),
                    ]
                    .concat(),
                ),
                vec![[vec![is_sequence, has_length], components].concat()],
            ));
        }
        if element.is_app("TLA.tuple")
            && (element.args.len() != tuple.args.len()
                || element
                    .args
                    .iter()
                    .zip(&tuple.args)
                    .any(|(inner, other)| is_trivially_not_in(inner, other)))
        {
            return Some(vec![]);
        }
        let components: Vec<Expr> = tuple
            .args
            .iter()
            .enumerate()
            .map(|(position, inner)| {
                exprs.enot(&member(
                    exprs,
                    &fapply(exprs, element, &make_natural(exprs, position + 1)),
                    inner,
                ))
            })
            .collect();
        let formulas = [
            vec![
                exprs.enot(&exprs.eapp("TLA.isASeq", std::slice::from_ref(element))),
                exprs.enot(&equal(
                    exprs,
                    &exprs.eapp("TLA.Len", std::slice::from_ref(element)),
                    &make_natural(exprs, tuple.args.len()),
                )),
            ],
            components,
        ]
        .concat();
        return Some(node(
            Priority::Prop,
            Rule::new(
                RuleName::NotinProduct,
                [
                    vec![formula.clone(), element.clone(), tuple.clone()],
                    formulas.clone(),
                ]
                .concat(),
            ),
            get_branches(formulas),
        ));
    }
    None
}

pub fn get_record_nodes(literal: &Literal) -> Option<Vec<Item>> {
    let exprs = literal.context.exprs;
    let formula = &literal.formula;
    let is_negated = literal.is_negated;
    let atom = &literal.atom;
    let node = |priority, rule, branches| make_extension_node(literal, priority, rule, branches);
    if is_negated && atom.is_app_with_arity("TLA.isAFcn", 1) && atom.args[0].is_app("TLA.record") {
        return Some(node(
            Priority::Prop,
            Rule::new(RuleName::RecordNotisafcn, vec![formula.clone()]),
            vec![],
        ));
    }
    let relation = literal.relation.as_ref()?;
    let left = &relation.args[0];
    let right = &relation.args[1];
    let is_equality = &*relation.symbol == "=";
    let is_membership = &*relation.symbol == "TLA.in";
    if is_equality && left.is_app("TLA.record") && right.is_app("TLA.record") {
        let left_fields = sort_pairs(&get_pairs(&left.args));
        let right_fields = sort_pairs(&get_pairs(&right.args));
        if !has_distinct_labels(&left_fields) || !has_distinct_labels(&right_fields) {
            return Some(vec![]);
        }
        let is_match = left_fields.len() == right_fields.len()
            && left_fields
                .iter()
                .zip(&right_fields)
                .all(|(field, other)| field.0 == other.0);
        if !is_match {
            return Some(if is_negated {
                vec![]
            } else {
                node(
                    Priority::Prop,
                    Rule::new(
                        RuleName::RecordEqMismatch,
                        vec![formula.clone(), formula.clone()],
                    ),
                    vec![],
                )
            });
        }
        let equalities: Vec<Expr> = left_fields
            .iter()
            .zip(&right_fields)
            .map(|(field, other)| equal(exprs, &field.1, &other.1))
            .collect();
        if !is_negated {
            return Some(node(
                Priority::Prop,
                Rule::new(
                    RuleName::RecordEqMatch,
                    [vec![formula.clone()], equalities.clone()].concat(),
                ),
                vec![equalities],
            ));
        }
        let inequalities: Vec<Expr> = equalities.iter().map(|inner| exprs.enot(inner)).collect();
        return Some(node(
            Priority::Prop,
            Rule::new(
                RuleName::RecordNeqMatch,
                [vec![formula.clone()], inequalities.clone()].concat(),
            ),
            get_branches(inequalities),
        ));
    }
    if is_negated && is_equality && (right.is_app("TLA.record") || left.is_app("TLA.record")) {
        let is_right = right.is_app("TLA.record");
        let record = if is_right { right } else { left };
        let other = if is_right { left } else { right };
        let pairs = get_pairs(&record.args);
        let formulas = [
            vec![
                exprs.enot(&exprs.eapp("TLA.isAFcn", std::slice::from_ref(other))),
                exprs.enot(&equal(
                    exprs,
                    &domain(exprs, other),
                    &exprs.eapp(
                        "TLA.set",
                        &pairs.iter().map(|pair| pair.0.clone()).collect::<Vec<_>>(),
                    ),
                )),
            ],
            pairs
                .iter()
                .map(|pair| exprs.enot(&equal(exprs, &fapply(exprs, other, &pair.0), &pair.1)))
                .collect(),
        ]
        .concat();
        return Some(node(
            Priority::Prop,
            Rule::new(
                if record == right {
                    RuleName::NeqRecord
                } else {
                    RuleName::RecordNeq
                },
                [
                    vec![formula.clone(), other.clone(), record.clone()],
                    formulas.clone(),
                ]
                .concat(),
            ),
            get_branches(formulas),
        ));
    }
    if is_membership && right.is_app("TLA.recordset") {
        let pairs = get_pairs(&right.args);
        let labels = exprs.eapp(
            "TLA.set",
            &pairs.iter().map(|pair| pair.0.clone()).collect::<Vec<_>>(),
        );
        if !is_negated {
            let formulas = [
                vec![
                    exprs.eapp("TLA.isAFcn", std::slice::from_ref(left)),
                    equal(exprs, &domain(exprs, left), &labels),
                ],
                pairs
                    .iter()
                    .map(|pair| member(exprs, &fapply(exprs, left, &pair.0), &pair.1))
                    .collect(),
            ]
            .concat();
            return Some(node(
                Priority::Prop,
                Rule::new(
                    RuleName::InRecordset,
                    [
                        vec![formula.clone(), left.clone(), right.clone()],
                        formulas.clone(),
                    ]
                    .concat(),
                ),
                vec![formulas],
            ));
        }
        if left.is_app("TLA.record") {
            let left_labels = get_sorted_labels(&left.args);
            let right_labels = get_sorted_labels(&right.args);
            let is_same_labels = left_labels == right_labels;
            let is_field_not_in = get_pairs(&left.args).iter().any(|field| {
                pairs
                    .iter()
                    .find(|pair| pair.0 == field.0)
                    .is_none_or(|kind| is_trivially_not_in(&field.1, &kind.1))
            });
            if !is_same_labels || is_field_not_in {
                return Some(vec![]);
            }
        }
        let formulas = [
            vec![
                exprs.enot(&exprs.eapp("TLA.isAFcn", std::slice::from_ref(left))),
                exprs.enot(&equal(exprs, &domain(exprs, left), &labels)),
            ],
            pairs
                .iter()
                .map(|pair| exprs.enot(&member(exprs, &fapply(exprs, left, &pair.0), &pair.1)))
                .collect(),
        ]
        .concat();
        return Some(node(
            Priority::Prop,
            Rule::new(
                RuleName::NotinRecordset,
                [
                    vec![formula.clone(), left.clone(), right.clone()],
                    formulas.clone(),
                ]
                .concat(),
            ),
            get_branches(formulas),
        ));
    }
    None
}

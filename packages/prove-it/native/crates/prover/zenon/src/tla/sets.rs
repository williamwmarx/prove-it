// Ported from Zenon's ext_tla.ml, as shipped in tlapm. Copyright 2008 INRIA, see LICENSE.
//! The rules for sets: membership in each kind of set, set equality and inclusion.

use crate::ZenonError;
use crate::expr::{Expr, Kind};
use crate::node::Priority;
use crate::proof::{Rule, RuleName};
use crate::tla::terms::{
    Item, Literal, SET_CONSTRUCTORS, equal, get_branches, is_constructor, is_variable,
    make_extension_node, make_instance_node, member,
};

fn decompose_add(set: &Expr) -> (Vec<Expr>, Expr) {
    let mut elements = Vec::new();
    let mut rest = set.clone();
    while rest.is_app_with_arity("TLA.addElt", 2) {
        elements.push(rest.args[0].clone());
        rest = rest.args[1].clone();
    }
    (elements, rest)
}

pub fn get_membership_nodes(literal: &Literal) -> Result<Option<Vec<Item>>, ZenonError> {
    let exprs = literal.context.exprs;
    let formula = &literal.formula;
    let is_negated = literal.is_negated;
    let node = |priority, rule, branches| make_extension_node(literal, priority, rule, branches);
    let Some(relation) = literal
        .relation
        .as_ref()
        .filter(|inner| inner.is_app("TLA.in"))
    else {
        return Ok(None);
    };
    let element = &relation.args[0];
    let set = &relation.args[1];
    if !is_negated && is_variable(set, "TLA.emptyset") {
        return Ok(Some(node(
            Priority::Prop,
            Rule::new(RuleName::InEmptyset, vec![formula.clone(), element.clone()]),
            vec![],
        )));
    }
    if set.is_app_with_arity("TLA.upair", 2) {
        let first = equal(exprs, element, &set.args[0]);
        let second = equal(exprs, element, &set.args[1]);
        return Ok(Some(if is_negated {
            node(
                Priority::Prop,
                Rule::new(
                    RuleName::NotinUpair,
                    vec![
                        formula.clone(),
                        exprs.enot(&first),
                        exprs.enot(&second),
                        element.clone(),
                        set.args[0].clone(),
                        set.args[1].clone(),
                    ],
                ),
                vec![vec![exprs.enot(&first), exprs.enot(&second)]],
            )
        } else {
            node(
                Priority::Prop,
                Rule::new(
                    RuleName::InUpair,
                    vec![
                        formula.clone(),
                        first.clone(),
                        second.clone(),
                        element.clone(),
                        set.args[0].clone(),
                        set.args[1].clone(),
                    ],
                ),
                vec![vec![first], vec![second]],
            )
        }));
    }
    if set.is_app_with_arity("TLA.addElt", 2) {
        let decomposed = decompose_add(set);
        let is_empty_rest = decomposed.1 == exprs.evar("TLA.emptyset");
        if !is_negated {
            let equalities: Vec<Expr> = decomposed
                .0
                .iter()
                .map(|inner| equal(exprs, element, inner))
                .collect();
            let formulas = if is_empty_rest {
                equalities
            } else {
                [equalities, vec![member(exprs, element, &decomposed.1)]].concat()
            };
            return Ok(Some(node(
                Priority::Prop,
                Rule::new(
                    RuleName::InAddElt,
                    vec![formula.clone(), element.clone(), set.clone()],
                ),
                get_branches(formulas),
            )));
        }
        let inequalities: Vec<Expr> = decomposed
            .0
            .iter()
            .map(|inner| exprs.enot(&equal(exprs, element, inner)))
            .collect();
        let formulas = if is_empty_rest {
            inequalities
        } else {
            [
                vec![exprs.enot(&member(exprs, element, &decomposed.1))],
                inequalities,
            ]
            .concat()
        };
        return Ok(Some(node(
            Priority::Prop,
            Rule::new(
                RuleName::NotinAddElt,
                vec![formula.clone(), element.clone(), set.clone()],
            ),
            vec![formulas],
        )));
    }
    if set.is_app("TLA.set") {
        return Ok(Some(if is_negated {
            node(
                Priority::Prop,
                Rule::new(
                    RuleName::NotinSet,
                    vec![formula.clone(), element.clone(), set.clone()],
                ),
                vec![
                    set.args
                        .iter()
                        .map(|inner| exprs.enot(&equal(exprs, element, inner)))
                        .collect(),
                ],
            )
        } else {
            node(
                Priority::Prop,
                Rule::new(
                    RuleName::InSet,
                    vec![formula.clone(), element.clone(), set.clone()],
                ),
                get_branches(
                    set.args
                        .iter()
                        .map(|inner| equal(exprs, element, inner))
                        .collect(),
                ),
            )
        }));
    }
    if is_negated && set.kind == Kind::Meta {
        return make_instance_node(
            literal,
            Priority::Instance(set.args[0].clone()),
            &set.args[0],
            &exprs.eapp("TLA.set", std::slice::from_ref(element)),
        )
        .map(Some);
    }
    if set.is_app_with_arity("TLA.SUBSET", 1) {
        let subset = exprs.eapp("TLA.subseteq", &[element.clone(), set.args[0].clone()]);
        return Ok(Some(if is_negated {
            node(
                Priority::Prop,
                Rule::new(
                    RuleName::NotinSUBSET,
                    vec![
                        formula.clone(),
                        exprs.enot(&subset),
                        element.clone(),
                        set.args[0].clone(),
                    ],
                ),
                vec![vec![exprs.enot(&subset)]],
            )
        } else {
            node(
                Priority::Prop,
                Rule::new(
                    RuleName::InSUBSET,
                    vec![
                        formula.clone(),
                        subset.clone(),
                        element.clone(),
                        set.args[0].clone(),
                    ],
                ),
                vec![vec![subset]],
            )
        }));
    }
    if set.is_app_with_arity("TLA.UNION", 1) {
        let bound = exprs.new_var();
        let exists = exprs.eex(
            &bound,
            "",
            &exprs.eand(
                &member(exprs, &bound, &set.args[0]),
                &member(exprs, element, &bound),
            ),
        );
        return Ok(Some(if is_negated {
            node(
                Priority::Arity,
                Rule::new(
                    RuleName::NotinUNION,
                    vec![
                        formula.clone(),
                        exprs.enot(&exists),
                        element.clone(),
                        set.args[0].clone(),
                    ],
                ),
                vec![vec![exprs.enot(&exists)]],
            )
        } else {
            node(
                Priority::Prop,
                Rule::new(
                    RuleName::InUNION,
                    vec![
                        formula.clone(),
                        exists.clone(),
                        element.clone(),
                        set.args[0].clone(),
                    ],
                ),
                vec![vec![exists]],
            )
        }));
    }
    let binary_set_rule = match (set.kind, &*set.symbol) {
        (Kind::App, "TLA.cup") => Some((RuleName::InCup, RuleName::NotinCup, true, false)),
        (Kind::App, "TLA.cap") => Some((RuleName::InCap, RuleName::NotinCap, false, true)),
        (Kind::App, "TLA.setminus") => {
            Some((RuleName::InSetminus, RuleName::NotinSetminus, false, true))
        }
        _ => None,
    };
    if let Some(binary_set_rule) = binary_set_rule
        && set.args.len() == 2
    {
        let first = member(exprs, element, &set.args[0]);
        let second_positive = member(exprs, element, &set.args[1]);
        let is_minus = &*set.symbol == "TLA.setminus";
        let second = if is_minus != is_negated {
            exprs.enot(&second_positive)
        } else {
            second_positive
        };
        let first_literal = if is_negated {
            exprs.enot(&first)
        } else {
            first
        };
        let is_split = if is_negated {
            binary_set_rule.3
        } else {
            binary_set_rule.2
        };
        return Ok(Some(node(
            Priority::Prop,
            Rule::new(
                if is_negated {
                    binary_set_rule.1
                } else {
                    binary_set_rule.0
                },
                vec![
                    formula.clone(),
                    first_literal.clone(),
                    second.clone(),
                    element.clone(),
                    set.args[0].clone(),
                    set.args[1].clone(),
                ],
            ),
            if is_split {
                vec![vec![first_literal], vec![second]]
            } else {
                vec![vec![first_literal, second]]
            },
        )));
    }
    if set.is_app_with_arity("TLA.subsetOf", 2) && set.args[1].kind == Kind::Lam {
        let predicate = &set.args[1];
        let in_base = member(exprs, element, &set.args[0]);
        let holds = exprs.substitute(
            &[(predicate.args[0].clone(), element.clone())],
            &predicate.args[1],
        );
        return Ok(Some(if is_negated {
            node(
                Priority::Prop,
                Rule::new(
                    RuleName::NotinSubsetof,
                    vec![
                        formula.clone(),
                        exprs.enot(&in_base),
                        exprs.enot(&holds),
                        element.clone(),
                        set.args[0].clone(),
                        predicate.clone(),
                    ],
                ),
                vec![vec![exprs.enot(&in_base)], vec![exprs.enot(&holds)]],
            )
        } else {
            node(
                Priority::Prop,
                Rule::new(
                    RuleName::InSubsetof,
                    vec![
                        formula.clone(),
                        in_base.clone(),
                        holds.clone(),
                        element.clone(),
                        set.args[0].clone(),
                        predicate.clone(),
                    ],
                ),
                vec![vec![in_base, holds]],
            )
        }));
    }
    if set.is_app_with_arity("TLA.setOfAll", 2) && set.args[1].kind == Kind::Lam {
        let predicate = &set.args[1];
        let bound = exprs.new_var();
        let exists = exprs.eex(
            &bound,
            "",
            &exprs.eand(
                &member(exprs, &bound, &set.args[0]),
                &equal(
                    exprs,
                    element,
                    &exprs.substitute(
                        &[(predicate.args[0].clone(), bound.clone())],
                        &predicate.args[1],
                    ),
                ),
            ),
        );
        let result = if is_negated {
            exprs.enot(&exists)
        } else {
            exists
        };
        return Ok(Some(node(
            Priority::Instance(result.clone()),
            Rule::new(
                if is_negated {
                    RuleName::NotinSetofall
                } else {
                    RuleName::InSetofall
                },
                vec![
                    formula.clone(),
                    result.clone(),
                    element.clone(),
                    set.args[0].clone(),
                    predicate.clone(),
                ],
            ),
            vec![vec![result]],
        )));
    }
    Ok(None)
}

pub fn get_set_equality_nodes(literal: &Literal) -> Option<Vec<Item>> {
    let exprs = literal.context.exprs;
    let formula = &literal.formula;
    let is_negated = literal.is_negated;
    let node = |priority, rule, branches| make_extension_node(literal, priority, rule, branches);
    let relation = literal
        .relation
        .as_ref()
        .filter(|inner| inner.is_app("="))?;
    let left = &relation.args[0];
    let right = &relation.args[1];
    if !is_negated && is_variable(right, "TLA.emptyset") {
        let bound = exprs.new_var();
        let empty = exprs.eall(&bound, "", &exprs.enot(&member(exprs, &bound, left)));
        return Some(node(
            Priority::Arity,
            Rule::new(
                RuleName::Setequalempty,
                vec![formula.clone(), empty.clone(), left.clone()],
            ),
            vec![vec![empty]],
        ));
    }
    if !is_negated && is_variable(left, "TLA.emptyset") {
        let bound = exprs.new_var();
        let empty = exprs.eall(&bound, "", &exprs.enot(&member(exprs, &bound, right)));
        return Some(node(
            Priority::Arity,
            Rule::new(
                RuleName::Setemptyequal,
                vec![formula.clone(), empty.clone(), right.clone()],
            ),
            vec![vec![empty]],
        ));
    }
    if is_constructor(SET_CONSTRUCTORS, left) || is_constructor(SET_CONSTRUCTORS, right) {
        let bound = exprs.new_var();
        let extensional = exprs.eall(
            &bound,
            "",
            &exprs.eequiv(&member(exprs, &bound, left), &member(exprs, &bound, right)),
        );
        let result = if is_negated {
            exprs.enot(&extensional)
        } else {
            extensional
        };
        return Some(node(
            Priority::Instance(result.clone()),
            Rule::new(
                if is_negated {
                    RuleName::Notsetequal
                } else {
                    RuleName::Setequal
                },
                vec![formula.clone(), result.clone(), left.clone(), right.clone()],
            ),
            vec![vec![result]],
        ));
    }
    None
}

/// A metavariable in a set, against the disequalities of that set.
pub fn get_meta_membership_nodes(literal: &Literal) -> Option<Vec<Item>> {
    let exprs = literal.context.exprs;
    let index = literal.context.index;
    let node = |priority, rule, branches| make_extension_node(literal, priority, rule, branches);
    let relation = literal
        .relation
        .as_ref()
        .filter(|inner| inner.is_app("TLA.in") && inner.args[0].kind == Kind::Meta)?;
    let bound = exprs.new_var();
    Some(
        index
            .find_disequalities(exprs, &relation.args[1])
            .into_iter()
            .flat_map(|disequality| {
                let sides = disequality.args[0].args.clone();
                let different = exprs.enot(&exprs.eall(
                    &bound,
                    "",
                    &exprs.eequiv(
                        &member(exprs, &bound, &sides[0]),
                        &member(exprs, &bound, &sides[1]),
                    ),
                ));
                node(
                    Priority::Instance(different.clone()),
                    Rule::new(
                        RuleName::Notsetequal,
                        vec![
                            disequality,
                            different.clone(),
                            sides[0].clone(),
                            sides[1].clone(),
                        ],
                    ),
                    vec![vec![different]],
                )
            })
            .collect(),
    )
}

pub fn get_subset_nodes(literal: &Literal) -> Option<Vec<Item>> {
    let exprs = literal.context.exprs;
    let formula = &literal.formula;
    let is_negated = literal.is_negated;
    let node = |priority, rule, branches| make_extension_node(literal, priority, rule, branches);
    let relation = literal
        .relation
        .as_ref()
        .filter(|inner| inner.is_app("TLA.subseteq"))?;
    let left = &relation.args[0];
    let right = &relation.args[1];
    if left.is_app_with_arity("TLA.cup", 2) {
        let first = exprs.eapp("TLA.subseteq", &[left.args[0].clone(), right.clone()]);
        let second = exprs.eapp("TLA.subseteq", &[left.args[1].clone(), right.clone()]);
        return Some(if is_negated {
            node(
                Priority::Arity,
                Rule::new(
                    RuleName::NotCupSubseteq,
                    vec![formula.clone(), exprs.enot(&first), exprs.enot(&second)],
                ),
                vec![vec![exprs.enot(&first)], vec![exprs.enot(&second)]],
            )
        } else {
            node(
                Priority::Arity,
                Rule::new(
                    RuleName::CupSubseteq,
                    vec![formula.clone(), first.clone(), second.clone()],
                ),
                vec![vec![first, second]],
            )
        });
    }
    if right.is_app_with_arity("TLA.cap", 2) {
        // Zenon builds the same subset twice here, from the second set.
        let subset = exprs.eapp("TLA.subseteq", &[left.clone(), right.args[1].clone()]);
        return Some(if is_negated {
            node(
                Priority::Arity,
                Rule::new(
                    RuleName::NotSubseteqCap,
                    vec![formula.clone(), exprs.enot(&subset), exprs.enot(&subset)],
                ),
                vec![vec![exprs.enot(&subset)], vec![exprs.enot(&subset)]],
            )
        } else {
            node(
                Priority::Arity,
                Rule::new(
                    RuleName::SubseteqCap,
                    vec![formula.clone(), subset.clone(), subset.clone()],
                ),
                vec![vec![subset.clone(), subset]],
            )
        });
    }
    None
}

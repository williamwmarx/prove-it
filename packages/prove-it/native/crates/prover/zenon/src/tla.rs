// Ported from Zenon's ext_tla.ml, as shipped in tlapm. Copyright 2008 INRIA, see LICENSE.
//! The TLA+ extension: rules for set theory, functions, records, tuples, CHOOSE, IF and CASE, and
//! rewriting a subterm with an equality on the branch.

pub mod functions;
pub mod records;
pub mod rewrites;
pub mod sets;
pub mod terms;
#[cfg(test)]
mod tests;

use std::rc::Rc;

use crate::ZenonError;
use crate::expr::{Expr, Expressions, Kind, efalse, etrue};
use crate::index_table::{Head, Index};
use crate::node::{Node, Priority, make_node};
use crate::parse::{Definition, Phrase};
use crate::proof::{Rule, RuleName};
use functions::{get_function_nodes, get_function_set_nodes};
use records::{get_record_nodes, get_tuple_nodes};
use rewrites::get_rewrite_nodes;
use sets::{
    get_membership_nodes, get_meta_membership_nodes, get_set_equality_nodes, get_subset_nodes,
};
use terms::{
    Item, Literal, TlaContext, equal, get_literal, is_not_equiv, is_variable, make_extension_node,
    make_instance_node, member,
};

/// The symbols that hypotheses can't define, as Zenon's predef with the tla extension: "=", then
/// [`terms::SET_CONSTRUCTORS`], [`terms::FUNCTION_CONSTRUCTORS`] and the other symbols the
/// extension knows.
pub const PREDEFINED_SYMBOLS: &[&str] = &[
    "=",
    "TLA.emptyset",
    "TLA.upair",
    "TLA.addElt",
    "TLA.set",
    "TLA.infinity",
    "TLA.SUBSET",
    "TLA.UNION",
    "TLA.INTER",
    "TLA.cup",
    "TLA.cap",
    "TLA.setminus",
    "TLA.subsetOf",
    "TLA.setOfAll",
    "TLA.FuncSet",
    "TLA.DOMAIN",
    "TLA.Product",
    "arith.N",
    "arith.Z",
    "arith.R",
    "arith.natrange",
    "arith.intrange",
    "TLA.Seq",
    "TLA.recordset",
    "TLA.Fcn",
    "TLA.except",
    "TLA.oneArg",
    "TLA.extend",
    "TLA.in",
    "TLA.isAFcn",
    "TLA.cond",
    "TLA.CASE",
    "TLA.tuple",
    "TLA.record",
    "TLA.fapply",
    "TLA.box",
];

fn definition(
    exprs: &Expressions,
    name: &str,
    symbol: &str,
    params: &[&str],
    body: Expr,
) -> Phrase {
    Phrase::Def(Rc::new(Definition::Real {
        name: name.to_owned(),
        symbol: symbol.to_owned(),
        params: params.iter().map(|param| exprs.evar(param)).collect(),
        body,
    }))
}

/// Zenon's built_in_defs. Expressions belong to one run of the prover, so each run builds them.
pub fn get_built_in_definitions(exprs: &Expressions) -> Vec<Phrase> {
    let bound = exprs.evar("x");
    let is_in_set = exprs.eapp("TLA.in", &[bound.clone(), exprs.evar("S")]);
    let holds = exprs.eapp("P", std::slice::from_ref(&bound));
    vec![
        definition(
            exprs,
            "subset_def",
            "TLA.subseteq",
            &["A", "B"],
            exprs.eapp(
                "TLA.bAll",
                &[
                    exprs.evar("A"),
                    exprs.elam(
                        &bound,
                        "",
                        &exprs.eapp("TLA.in", &[bound.clone(), exprs.evar("B")]),
                    ),
                ],
            ),
        ),
        definition(
            exprs,
            "bAll_def",
            "TLA.bAll",
            &["S", "P"],
            exprs.eall(&bound, "", &exprs.eimply(&is_in_set, &holds)),
        ),
        definition(
            exprs,
            "bEx_def",
            "TLA.bEx",
            &["S", "P"],
            exprs.eex(&bound, "", &exprs.eand(&is_in_set, &holds)),
        ),
        definition(
            exprs,
            "bChoose_def",
            "TLA.bChoice",
            &["S", "P"],
            exprs.etau(&bound, "", &exprs.eand(&is_in_set, &holds)),
        ),
        definition(
            exprs,
            "prod_def",
            "TLA.prod",
            &["A", "B"],
            exprs.eapp(
                "TLA.Product",
                &[exprs.eapp("TLA.tuple", &[exprs.evar("A"), exprs.evar("B")])],
            ),
        ),
    ]
}

/// The elements of a set given by enumeration, and whether it may hold more.
fn get_set_values(set: &Expr) -> (Vec<Expr>, bool) {
    if is_variable(set, "TLA.emptyset") {
        return (vec![], false);
    }
    if set.is_app_with_arity("TLA.upair", 2) || set.is_app("TLA.set") {
        return (set.args.clone(), false);
    }
    if set.is_app_with_arity("TLA.addElt", 2) {
        let rest = get_set_values(&set.args[1]);
        return ([vec![set.args[0].clone()], rest.0].concat(), rest.1);
    }
    if set.is_app_with_arity("TLA.union", 2) {
        let left = get_set_values(&set.args[0]);
        let right = get_set_values(&set.args[1]);
        return ([left.0, right.0].concat(), left.1 || right.1);
    }
    (vec![], true)
}

fn get_boolean_nodes(literal: &Literal) -> Result<Option<Vec<Item>>, ZenonError> {
    let exprs = literal.context.exprs;
    let formula = &literal.formula;
    let is_negated = literal.is_negated;
    let atom = &literal.atom;
    let node = |priority, rule, branches| make_extension_node(literal, priority, rule, branches);
    if atom.kind == Kind::Meta {
        return make_instance_node(
            literal,
            Priority::Arity,
            &atom.args[0],
            &if is_negated { etrue() } else { efalse() },
        )
        .map(Some);
    }
    let Some(relation) = literal.relation.as_ref().filter(|inner| inner.is_app("=")) else {
        return Ok(None);
    };
    let left = &relation.args[0];
    let right = &relation.args[1];
    if right.kind == Kind::True {
        return Ok(Some(if is_negated {
            node(
                Priority::Prop,
                Rule::new(
                    RuleName::NoteqXTrue,
                    vec![formula.clone(), exprs.enot(left), left.clone()],
                ),
                vec![vec![exprs.enot(left)]],
            )
        } else {
            node(
                Priority::Prop,
                Rule::new(
                    RuleName::EqXTrue,
                    vec![formula.clone(), left.clone(), left.clone()],
                ),
                vec![vec![left.clone()]],
            )
        }));
    }
    if left.kind == Kind::True {
        return Ok(Some(if is_negated {
            node(
                Priority::Prop,
                Rule::new(
                    RuleName::NoteqTrueX,
                    vec![formula.clone(), exprs.enot(right), right.clone()],
                ),
                vec![vec![exprs.enot(right)]],
            )
        } else {
            node(
                Priority::Prop,
                Rule::new(
                    RuleName::EqTrueX,
                    vec![formula.clone(), right.clone(), right.clone()],
                ),
                vec![vec![right.clone()]],
            )
        }));
    }
    if !is_negated && right.kind == Kind::False {
        return Ok(Some(node(
            Priority::Prop,
            Rule::new(
                RuleName::EqXFalse,
                vec![formula.clone(), exprs.enot(left), left.clone()],
            ),
            vec![vec![exprs.enot(left)]],
        )));
    }
    if !is_negated && left.kind == Kind::False {
        return Ok(Some(node(
            Priority::Prop,
            Rule::new(
                RuleName::EqFalseX,
                vec![formula.clone(), exprs.enot(right), right.clone()],
            ),
            vec![vec![exprs.enot(right)]],
        )));
    }
    Ok(None)
}

fn get_choice_nodes(literal: &Literal) -> Option<Vec<Item>> {
    let exprs = literal.context.exprs;
    let formula = &literal.formula;
    let goalness = literal.goalness;
    let is_negated = literal.is_negated;
    let node = |priority, rule, branches| make_extension_node(literal, priority, rule, branches);
    let relation = literal.relation.as_ref()?;
    let left = &relation.args[0];
    let right = &relation.args[1];
    let is_equality = &*relation.symbol == "=";
    if is_negated
        && is_equality
        && left.kind == Kind::Tau
        && right.kind == Kind::Tau
        && !is_not_equiv(&left.args[1])
        && !is_not_equiv(&right.args[1])
    {
        let bound = exprs.new_var();
        let left_body = exprs.substitute(&[(left.args[0].clone(), bound.clone())], &left.args[1]);
        let right_body =
            exprs.substitute(&[(right.args[0].clone(), bound.clone())], &right.args[1]);
        let differ = exprs.eex(
            &bound,
            &left.symbol,
            &exprs.eapp("$notequiv", &[left_body, right_body]),
        );
        return Some(node(
            Priority::Instance(differ.clone()),
            Rule::new(
                RuleName::ChooseDiffChoose,
                vec![
                    formula.clone(),
                    differ.clone(),
                    exprs.elam(&left.args[0], &left.symbol, &left.args[1]),
                    exprs.elam(&right.args[0], &right.symbol, &right.args[1]),
                ],
            ),
            vec![vec![differ]],
        ));
    }
    if !is_negated && &*relation.symbol == "$notequiv" {
        return Some(node(
            Priority::Arity,
            Rule::new(RuleName::Notequivdef, vec![]),
            vec![vec![exprs.enot(&exprs.eequiv(left, right))]],
        ));
    }
    let choice = if right.kind == Kind::Tau {
        Some(right)
    } else if left.kind == Kind::Tau {
        Some(left)
    } else {
        None
    };
    if is_negated
        && is_equality
        && let Some(choice) = choice
    {
        let term = if right.kind == Kind::Tau { left } else { right };
        let exists = exprs.eex(&choice.args[0], &choice.symbol, &choice.args[1]);
        let not_exists = exprs.enot(&exists);
        let not_holds = exprs
            .enot(&exprs.substitute(&[(choice.args[0].clone(), term.clone())], &choice.args[1]));
        return Some(vec![Item::Node(make_node(
            vec![],
            Rule::new(
                RuleName::Notequalchoose,
                vec![
                    exists.clone(),
                    not_exists.clone(),
                    not_holds.clone(),
                    exprs.elam(&choice.args[0], &choice.symbol, &choice.args[1]),
                    term.clone(),
                ],
            ),
            Priority::Instance(not_exists.clone()),
            goalness,
            vec![vec![exists], vec![not_exists, not_holds]],
        ))]);
    }
    None
}

/// The bounded quantifier over an enumerated set in \A x : x \in S => P or ~\E x : x \in S /\ P:
/// the quantifier and the set.
fn get_enumerated_quantifier(formula: &Expr) -> Option<(Expr, Expr)> {
    let is_enumerated = |set: &Expr| {
        is_variable(set, "TLA.emptyset")
            || (set.kind == Kind::App
                && ["TLA.addElt", "TLA.upair", "TLA.set", "TLA.union"].contains(&&*set.symbol))
    };
    if formula.kind == Kind::All {
        let body = &formula.args[1];
        if body.kind == Kind::Imply
            && body.args[0].is_app_with_arity("TLA.in", 2)
            && is_enumerated(&body.args[0].args[1])
        {
            return Some((formula.clone(), body.args[0].args[1].clone()));
        }
    }
    if formula.kind == Kind::Not && formula.args[0].kind == Kind::Ex {
        let body = &formula.args[0].args[1];
        if body.kind == Kind::And
            && body.args[0].is_app_with_arity("TLA.in", 2)
            && is_enumerated(&body.args[0].args[1])
        {
            return Some((formula.args[0].clone(), body.args[0].args[1].clone()));
        }
    }
    None
}

fn get_enumerated_nodes(literal: &Literal) -> Result<Option<Vec<Item>>, ZenonError> {
    let Some(enumerated) = get_enumerated_quantifier(&literal.formula) else {
        return Ok(None);
    };
    let values = get_set_values(&enumerated.1);
    let nodes = values
        .0
        .iter()
        .map(|value| make_instance_node(literal, Priority::Arity, &enumerated.0, value))
        .collect::<Result<Vec<_>, ZenonError>>()?
        .concat();
    Ok(Some(if values.1 {
        nodes
    } else {
        [nodes, vec![Item::Stop]].concat()
    }))
}

fn get_natural_nodes(literal: &Literal) -> Result<Option<Vec<Item>>, ZenonError> {
    let exprs = literal.context.exprs;
    let formula = &literal.formula;
    let node = |priority, rule, branches| make_extension_node(literal, priority, rule, branches);
    let Some(relation) = literal.relation.as_ref().filter(|inner| {
        literal.is_negated && inner.is_app("TLA.in") && is_variable(&inner.args[1], "arith.N")
    }) else {
        return Ok(None);
    };
    let left = &relation.args[0];
    if is_variable(left, "0") {
        return Ok(Some(node(
            Priority::Prop,
            Rule::new(RuleName::InNat0, vec![formula.clone()]),
            vec![],
        )));
    }
    if left.is_app_with_arity("TLA.fapply", 2) && is_variable(&left.args[0], "TLA.Succ") {
        let previous = exprs.enot(&member(exprs, &left.args[1], &exprs.evar("arith.N")));
        return Ok(Some(node(
            Priority::Prop,
            Rule::new(
                RuleName::InNatSucc,
                vec![formula.clone(), previous.clone(), left.args[1].clone()],
            ),
            vec![vec![previous]],
        )));
    }
    if left.kind == Kind::Meta {
        return make_instance_node(
            literal,
            Priority::Instance(left.args[0].clone()),
            &left.args[0],
            &exprs.evar("0"),
        )
        .map(Some);
    }
    Ok(None)
}

fn get_box_nodes(literal: &Literal) -> Option<Vec<Item>> {
    (!literal.is_negated && literal.atom.is_app_with_arity("TLA.box", 1)).then(|| {
        make_extension_node(
            literal,
            Priority::Prop,
            Rule::new(
                RuleName::BoxP,
                vec![literal.formula.clone(), literal.atom.args[0].clone()],
            ),
            vec![vec![literal.atom.args[0].clone()]],
        )
    })
}

fn get_prop_nodes(
    context: TlaContext,
    formula: &Expr,
    goalness: i64,
) -> Result<Vec<Item>, ZenonError> {
    let literal = get_literal(context, formula, goalness);
    let found = if let Some(nodes) = get_boolean_nodes(&literal)? {
        Some(nodes)
    } else if let Some(nodes) = get_membership_nodes(&literal)? {
        Some(nodes)
    } else {
        get_function_set_nodes(&literal)
            .or_else(|| get_set_equality_nodes(&literal))
            .or_else(|| get_function_nodes(&literal))
            .or_else(|| get_choice_nodes(&literal))
    };
    if let Some(nodes) = found {
        return Ok(nodes);
    }
    if let Some(nodes) = get_enumerated_nodes(&literal)? {
        return Ok(nodes);
    }
    if let Some(nodes) = get_natural_nodes(&literal)? {
        return Ok(nodes);
    }
    Ok(get_meta_membership_nodes(&literal)
        .or_else(|| get_box_nodes(&literal))
        .or_else(|| get_tuple_nodes(&literal))
        .or_else(|| get_record_nodes(&literal))
        .or_else(|| get_subset_nodes(&literal))
        .unwrap_or_default())
}

/// Zenon's newnodes_inst_bounded: instantiates \A x \in S : P and ~\E x \in S : P with the terms
/// known to be in S.
fn get_bounded_instances(
    context: TlaContext,
    formula: &Expr,
    goalness: i64,
) -> Result<Vec<Rc<Node>>, ZenonError> {
    let exprs = context.exprs;
    let index = context.index;
    let make = |name: RuleName,
                bounded: &Expr,
                membership: &Expr,
                set: &Expr,
                predicate: &Expr,
                term: &Expr|
     -> Result<Rc<Node>, ZenonError> {
        let instance = if name == RuleName::AllIn {
            exprs.apply(predicate, term)?
        } else {
            exprs.enot(&exprs.apply(predicate, term)?)
        };
        Ok(make_node(
            if bounded == formula {
                vec![membership.clone(), formula.clone()]
            } else {
                vec![formula.clone(), bounded.clone()]
            },
            Rule::new(
                name,
                vec![
                    bounded.clone(),
                    membership.clone(),
                    instance.clone(),
                    set.clone(),
                    predicate.clone(),
                ],
            ),
            Priority::Instance(formula.clone()),
            goalness,
            vec![vec![instance]],
        ))
    };
    let get_terms_in = |set: &Expr| -> Vec<Expr> {
        index
            .find_positive("TLA.in")
            .into_iter()
            .map(|entry| entry.0)
            .filter(|membership| {
                membership.is_app_with_arity("TLA.in", 2)
                    && membership.args[0].metas.is_empty()
                    && membership.args[1] == *set
            })
            .collect()
    };
    if formula.is_app_with_arity("TLA.in", 2) && formula.args[0].metas.is_empty() {
        let term = &formula.args[0];
        let set = &formula.args[1];
        let universals: Vec<Expr> = index
            .find_positive("TLA.bAll")
            .into_iter()
            .map(|entry| entry.0)
            .filter(|bounded| bounded.is_app_with_arity("TLA.bAll", 2) && bounded.args[0] == *set)
            .collect();
        let existentials: Vec<Expr> = index
            .find_negative("TLA.bEx")
            .into_iter()
            .map(|entry| entry.0)
            .filter(|bounded| {
                bounded.kind == Kind::Not
                    && bounded.args[0].is_app_with_arity("TLA.bEx", 2)
                    && bounded.args[0].args[0] == *set
            })
            .collect();
        let not_exists = existentials
            .iter()
            .map(|bounded| {
                make(
                    RuleName::NotexIn,
                    bounded,
                    formula,
                    set,
                    &bounded.args[0].args[1],
                    term,
                )
            })
            .collect::<Result<Vec<_>, ZenonError>>()?;
        let for_all = universals
            .iter()
            .map(|bounded| {
                make(
                    RuleName::AllIn,
                    bounded,
                    formula,
                    set,
                    &bounded.args[1],
                    term,
                )
            })
            .collect::<Result<Vec<_>, ZenonError>>()?;
        return Ok(for_all.into_iter().rev().chain(not_exists).collect());
    }
    if formula.is_app_with_arity("TLA.bAll", 2) {
        return get_terms_in(&formula.args[0])
            .iter()
            .map(|membership| {
                make(
                    RuleName::AllIn,
                    formula,
                    membership,
                    &formula.args[0],
                    &formula.args[1],
                    &membership.args[0],
                )
            })
            .collect();
    }
    if formula.kind == Kind::Not && formula.args[0].is_app_with_arity("TLA.bEx", 2) {
        let bounded = &formula.args[0];
        return get_terms_in(&bounded.args[0])
            .iter()
            .map(|membership| {
                make(
                    RuleName::NotexIn,
                    formula,
                    membership,
                    &bounded.args[0],
                    &bounded.args[1],
                    &membership.args[0],
                )
            })
            .collect();
    }
    Ok(vec![])
}

fn make_proposition_equality_node(
    exprs: &Expressions,
    name: RuleName,
    formula: &Expr,
    left: &Expr,
    right: &Expr,
    goalness: i64,
) -> Rc<Node> {
    let is_negated = matches!(name, RuleName::NpEqL | RuleName::NpEqR);
    let is_left = matches!(name, RuleName::PEqL | RuleName::NpEqL);
    let proposition = if is_negated && formula.kind == Kind::Not {
        &formula.args[0]
    } else {
        formula
    };
    let equality = equal(exprs, left, right);
    let differ = exprs.enot(&equal(
        exprs,
        proposition,
        if is_left { left } else { right },
    ));
    let other = if is_left { right } else { left };
    let rest = if is_negated {
        exprs.enot(other)
    } else {
        other.clone()
    };
    make_node(
        vec![formula.clone(), equality.clone()],
        Rule::new(
            name,
            if is_negated {
                vec![
                    formula.clone(),
                    equality,
                    differ.clone(),
                    rest.clone(),
                    proposition.clone(),
                    left.clone(),
                    right.clone(),
                ]
            } else {
                vec![
                    formula.clone(),
                    equality,
                    differ.clone(),
                    other.clone(),
                    formula.clone(),
                    left.clone(),
                    right.clone(),
                ]
            },
        ),
        Priority::ArityEq,
        goalness,
        vec![vec![differ], vec![rest]],
    )
}

fn get_proposition_equality_name(is_negated: bool, is_left: bool) -> RuleName {
    match (is_negated, is_left) {
        (true, true) => RuleName::NpEqL,
        (true, false) => RuleName::NpEqR,
        (false, true) => RuleName::PEqL,
        (false, false) => RuleName::PEqR,
    }
}

fn get_proposition_equality_nodes(
    context: TlaContext,
    formula: &Expr,
    goalness: i64,
) -> Vec<Rc<Node>> {
    let exprs = context.exprs;
    let index = context.index;
    let atom = if formula.kind == Kind::Not {
        &formula.args[0]
    } else {
        formula
    };
    if atom.kind != Kind::App {
        return vec![];
    }
    let is_negated = formula.kind == Kind::Not;
    let make = |is_left: bool| {
        move |entry: (Expr, i64)| {
            make_proposition_equality_node(
                exprs,
                get_proposition_equality_name(is_negated, is_left),
                formula,
                &entry.0.args[0],
                &entry.0.args[1],
                goalness,
            )
        }
    };
    let head = Head::Symbol(atom.symbol.clone());
    let lefts: Vec<Rc<Node>> = index
        .find_trans_left("=", &head)
        .into_iter()
        .map(make(true))
        .collect();
    let rights = index
        .find_trans_right("=", &head)
        .into_iter()
        .map(make(false));
    lefts.into_iter().chain(rights).collect()
}

fn get_equality_proposition_nodes(
    context: TlaContext,
    formula: &Expr,
    is_left: bool,
) -> Vec<Rc<Node>> {
    let exprs = context.exprs;
    if !formula.is_app_with_arity("=", 2) {
        return vec![];
    }
    let term = &formula.args[if is_left { 0 } else { 1 }];
    if term.kind != Kind::App {
        return vec![];
    }
    let index = context.index;
    let make = |is_negated: bool| {
        move |entry: (Expr, i64)| {
            make_proposition_equality_node(
                exprs,
                get_proposition_equality_name(is_negated, is_left),
                &entry.0,
                &formula.args[0],
                &formula.args[1],
                entry.1,
            )
        }
    };
    let positives: Vec<Rc<Node>> = index
        .find_positive(&term.symbol)
        .into_iter()
        .map(make(false))
        .collect();
    let negatives = index
        .find_negative(&term.symbol)
        .into_iter()
        .map(make(true));
    positives.into_iter().chain(negatives).collect()
}

pub struct ExtensionNodes {
    pub nodes: Vec<Rc<Node>>,
    pub is_stopped: bool,
}

pub fn get_extension_nodes(
    index: &Index,
    exprs: &Expressions,
    formula: &Expr,
    goalness: i64,
) -> Result<ExtensionNodes, ZenonError> {
    let context = TlaContext { index, exprs };
    // OCaml evaluates the operands of @ right to left, so the last rules run first. The order
    // decides the names of fresh variables.
    let bounded = get_bounded_instances(context, formula, goalness)?;
    let right = get_equality_proposition_nodes(context, formula, false);
    let left = get_equality_proposition_nodes(context, formula, true);
    let propositions = get_proposition_equality_nodes(context, formula, goalness);
    let rewrites = get_rewrite_nodes(context, formula, goalness)?;
    let props = get_prop_nodes(context, formula, goalness)?;
    let mut nodes = Vec::new();
    let items = props.into_iter().chain(rewrites).chain(
        [propositions, left, right, bounded]
            .into_iter()
            .flatten()
            .map(Item::Node),
    );
    for item in items {
        match item {
            Item::Node(node) => nodes.push(node),
            Item::Stop => {
                return Ok(ExtensionNodes {
                    nodes,
                    is_stopped: true,
                });
            }
        }
    }
    Ok(ExtensionNodes {
        nodes,
        is_stopped: false,
    })
}

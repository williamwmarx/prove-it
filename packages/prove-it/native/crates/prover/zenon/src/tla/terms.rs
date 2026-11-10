// Ported from Zenon's ext_tla.ml, as shipped in tlapm. Copyright 2008 INRIA, see LICENSE.
//! What the rules of the TLA+ extension share: the symbols it knows, a literal taken apart, and the
//! nodes it makes.

use std::rc::Rc;

use crate::ZenonError;
use crate::expr::{Expr, Expressions, Kind};
use crate::index_table::Index;
use crate::node::{Node, Priority, make_node};
use crate::proof::{Rule, RuleName};

/// A node, or Zenon's Stop: the rules after it don't apply to the formula.
#[derive(Clone)]
pub enum Item {
    Node(Rc<Node>),
    Stop,
}

pub const SET_CONSTRUCTORS: &[&str] = &[
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
];

pub const FUNCTION_CONSTRUCTORS: &[&str] = &["TLA.Fcn", "TLA.except", "TLA.oneArg", "TLA.extend"];

pub fn is_variable(expression: &Expr, name: &str) -> bool {
    expression.kind == Kind::Var && &*expression.symbol == name
}

pub fn is_constructor(constructors: &[&str], expression: &Expr) -> bool {
    matches!(expression.kind, Kind::Var | Kind::App) && constructors.contains(&&*expression.symbol)
}

pub fn is_not_equiv(expression: &Expr) -> bool {
    expression.is_app("$notequiv")
}

fn is_string(expression: &Expr) -> bool {
    expression.is_app("$string")
}

pub fn equal(exprs: &Expressions, left: &Expr, right: &Expr) -> Expr {
    exprs.eapp("=", &[left.clone(), right.clone()])
}

pub fn member(exprs: &Expressions, element: &Expr, set: &Expr) -> Expr {
    exprs.eapp("TLA.in", &[element.clone(), set.clone()])
}

pub fn fapply(exprs: &Expressions, fcn: &Expr, argument: &Expr) -> Expr {
    exprs.eapp("TLA.fapply", &[fcn.clone(), argument.clone()])
}

pub fn domain(exprs: &Expressions, fcn: &Expr) -> Expr {
    exprs.eapp("TLA.DOMAIN", std::slice::from_ref(fcn))
}

pub fn get_branches(formulas: Vec<Expr>) -> Vec<Vec<Expr>> {
    formulas.into_iter().map(|formula| vec![formula]).collect()
}

pub fn make_natural(exprs: &Expressions, count: usize) -> Expr {
    (0..count).fold(exprs.evar("0"), |result, _| {
        fapply(exprs, &exprs.evar("TLA.Succ"), &result)
    })
}

pub fn is_trivially_not_in(element: &Expr, set: &Expr) -> bool {
    is_string(element)
        && set.is_app("TLA.set")
        && set
            .args
            .iter()
            .all(|inner| is_string(inner) && inner != element)
}

pub fn get_pairs(args: &[Expr]) -> Vec<(Expr, Expr)> {
    args.as_chunks::<2>()
        .0
        .iter()
        .map(|pair| (pair[0].clone(), pair[1].clone()))
        .collect()
}

#[derive(Clone, Copy)]
pub struct TlaContext<'a> {
    pub index: &'a Index,
    pub exprs: &'a Expressions,
}

/// A formula that the propositional rules look at: a literal, its atom and, when the atom relates
/// two terms, the atom as a relation.
pub struct Literal<'a> {
    pub context: TlaContext<'a>,
    pub formula: Expr,
    pub goalness: i64,
    pub is_negated: bool,
    pub atom: Expr,
    pub relation: Option<Expr>,
}

impl Literal<'_> {
    /// The relation's symbol, or "" when the atom isn't a relation, for `relation?.symbol`.
    pub fn relation_symbol(&self) -> &str {
        self.relation
            .as_ref()
            .map_or("", |relation| &*relation.symbol)
    }
}

pub fn get_literal<'a>(context: TlaContext<'a>, formula: &Expr, goalness: i64) -> Literal<'a> {
    let atom = if formula.kind == Kind::Not {
        formula.args[0].clone()
    } else {
        formula.clone()
    };
    Literal {
        context,
        formula: formula.clone(),
        goalness,
        is_negated: formula.kind == Kind::Not,
        relation: atom.is_relation().then(|| atom.clone()),
        atom,
    }
}

pub fn make_extension_node(
    literal: &Literal,
    priority: Priority,
    rule: Rule,
    branches: Vec<Vec<Expr>>,
) -> Vec<Item> {
    vec![Item::Node(make_node(
        vec![literal.formula.clone()],
        rule,
        priority,
        literal.goalness,
        branches,
    ))]
}

pub fn make_instance_node(
    literal: &Literal,
    priority: Priority,
    quantified: &Expr,
    term: &Expr,
) -> Result<Vec<Item>, ZenonError> {
    let exprs = literal.context.exprs;
    let goalness = literal.goalness;
    if quantified.kind == Kind::All {
        return Ok(vec![Item::Node(make_node(
            vec![quantified.clone()],
            Rule::new(RuleName::All, vec![quantified.clone(), term.clone()]),
            priority,
            goalness,
            vec![vec![exprs.substitute(
                &[(quantified.args[0].clone(), term.clone())],
                &quantified.args[1],
            )]],
        ))]);
    }
    if quantified.kind == Kind::Ex {
        let negated = exprs.enot(quantified);
        return Ok(vec![Item::Node(make_node(
            vec![negated.clone()],
            Rule::new(RuleName::NotEx, vec![negated, term.clone()]),
            priority,
            goalness,
            vec![vec![exprs.substitute(
                &[(quantified.args[0].clone(), term.clone())],
                &exprs.enot(&quantified.args[1]),
            )]],
        ))]);
    }
    Err(ZenonError::new(
        "Zenon: instantiating a formula that isn't quantified",
    ))
}

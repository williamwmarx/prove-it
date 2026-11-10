// Ported from Zenon's prove.ml, as shipped in tlapm. Copyright 2002 INRIA, see LICENSE.
//! The rules for connectives and quantifiers, closing a branch, and unfolding definitions.

use std::rc::Rc;

use crate::ZenonError;
use crate::equality_rules::get_string_value;
use crate::expr::{Expr, Expressions, Kind};
use crate::node::{Priority, Queue, insert_node, make_node};
use crate::parse::Definition;
use crate::proof::{Rule, RuleName};
use crate::rules::{RuleResult, SearchContext};

// Zenon's is_conj and is_disj: how many more conjuncts or disjuncts a formula needs to reach m.
fn count_conjuncts(formula: &Expr, needed: i64) -> i64 {
    if needed <= 0 {
        return 0;
    }
    match formula.kind {
        Kind::And => count_conjuncts(&formula.args[1], count_conjuncts(&formula.args[0], needed)),
        Kind::Not => count_disjuncts(&formula.args[0], needed),
        _ => needed - 1,
    }
}

fn count_disjuncts(formula: &Expr, needed: i64) -> i64 {
    if needed <= 0 {
        return 0;
    }
    match formula.kind {
        Kind::Or => count_disjuncts(&formula.args[1], count_disjuncts(&formula.args[0], needed)),
        Kind::Imply => count_disjuncts(&formula.args[1], count_conjuncts(&formula.args[0], needed)),
        Kind::Not => count_conjuncts(&formula.args[0], needed),
        _ => needed - 1,
    }
}

/// Prepends the conjuncts to the accumulator, which `reversed` holds last first.
fn decompose_conjunction(
    exprs: &Expressions,
    is_negated: bool,
    reversed: &mut Vec<Expr>,
    formula: &Expr,
) {
    match formula.kind {
        Kind::And => {
            decompose_conjunction(exprs, is_negated, reversed, &formula.args[1]);
            decompose_conjunction(exprs, is_negated, reversed, &formula.args[0]);
        }
        Kind::Not => decompose_disjunction(exprs, !is_negated, reversed, &formula.args[0]),
        _ => reversed.push(if is_negated {
            exprs.enot(formula)
        } else {
            formula.clone()
        }),
    }
}

fn decompose_disjunction(
    exprs: &Expressions,
    is_negated: bool,
    reversed: &mut Vec<Expr>,
    formula: &Expr,
) {
    match formula.kind {
        Kind::Or => {
            decompose_disjunction(exprs, is_negated, reversed, &formula.args[1]);
            decompose_disjunction(exprs, is_negated, reversed, &formula.args[0]);
        }
        Kind::Imply => {
            decompose_disjunction(exprs, is_negated, reversed, &formula.args[1]);
            decompose_conjunction(exprs, !is_negated, reversed, &formula.args[0]);
        }
        Kind::Not => decompose_conjunction(exprs, !is_negated, reversed, &formula.args[0]),
        _ => reversed.push(if is_negated {
            exprs.enot(formula)
        } else {
            formula.clone()
        }),
    }
}

fn get_conjuncts(exprs: &Expressions, formula: &Expr) -> Vec<Expr> {
    let mut reversed = Vec::new();
    decompose_conjunction(exprs, false, &mut reversed, formula);
    reversed.reverse();
    reversed
}

fn get_disjuncts(exprs: &Expressions, formula: &Expr) -> Vec<Expr> {
    let mut reversed = Vec::new();
    decompose_disjunction(exprs, false, &mut reversed, formula);
    reversed.reverse();
    reversed
}

pub fn add_absurd(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let exprs = &context.exprs;
    if formula.kind == Kind::Not && context.index.is_member(&formula.args[0]) {
        let operand = &formula.args[0];
        return Ok((
            insert_node(
                queue,
                make_node(
                    vec![formula.clone(), operand.clone()],
                    Rule::new(RuleName::Close, vec![operand.clone()]),
                    Priority::Prop,
                    goalness,
                    Vec::new(),
                ),
            ),
            true,
        ));
    }
    let negation = exprs.enot(formula);
    if !context.index.is_member(&negation) {
        return Ok((queue.clone(), false));
    }
    Ok((
        insert_node(
            queue,
            make_node(
                vec![formula.clone(), negation],
                Rule::new(RuleName::Close, vec![formula.clone()]),
                Priority::Prop,
                goalness,
                Vec::new(),
            ),
        ),
        true,
    ))
}

pub fn add_closure(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let exprs = &context.exprs;
    let close = |conclusions: Vec<Expr>, rule: Rule| -> Result<RuleResult, ZenonError> {
        Ok((
            insert_node(
                queue,
                make_node(conclusions, rule, Priority::Prop, goalness, Vec::new()),
            ),
            true,
        ))
    };
    if formula.kind == Kind::False {
        return close(
            vec![formula.clone()],
            Rule::new(RuleName::False, Vec::new()),
        );
    }
    let operand = (formula.kind == Kind::Not).then(|| &formula.args[0]);
    if operand.is_some_and(|operand| operand.kind == Kind::True) {
        return close(
            vec![formula.clone()],
            Rule::new(RuleName::NotTrue, Vec::new()),
        );
    }
    let relations = &context.relations;
    if let Some(operand) = operand
        && operand.is_relation()
        && relations.is_reflexive(&operand.symbol)
        && operand.args[0] == operand.args[1]
    {
        return close(
            vec![formula.clone()],
            Rule::relation(
                RuleName::CloseRefl,
                &operand.symbol,
                vec![operand.args[0].clone()],
            ),
        );
    }
    if formula.is_relation() && relations.is_symmetric(&formula.symbol) {
        let reversed = exprs.enot(&exprs.eapp(
            &formula.symbol,
            &[formula.args[1].clone(), formula.args[0].clone()],
        ));
        if context.index.is_member(&reversed) {
            return close(
                vec![formula.clone(), reversed],
                Rule::relation(
                    RuleName::CloseSym,
                    &formula.symbol,
                    vec![formula.args[0].clone(), formula.args[1].clone()],
                ),
            );
        }
    }
    if let Some(operand) = operand
        && operand.is_relation()
        && relations.is_symmetric(&operand.symbol)
    {
        let reversed = exprs.eapp(
            &operand.symbol,
            &[operand.args[1].clone(), operand.args[0].clone()],
        );
        if context.index.is_member(&reversed) {
            return close(
                vec![formula.clone(), reversed],
                Rule::relation(
                    RuleName::CloseSym,
                    &operand.symbol,
                    vec![operand.args[1].clone(), operand.args[0].clone()],
                ),
            );
        }
    }
    if formula.is_app_with_arity("=", 2) {
        let left = get_string_value(&formula.args[0]);
        let right = get_string_value(&formula.args[1]);
        if let (Some(left), Some(right)) = (left, right)
            && left != right
        {
            return close(
                vec![formula.clone()],
                Rule::new(RuleName::Stringequal, vec![left, right]),
            );
        }
    }
    Ok((queue.clone(), false))
}

pub fn add_junction_tree(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let exprs = &context.exprs;
    let operand_kind = (formula.kind == Kind::Not).then(|| formula.args[0].kind);
    let is_conjunctive = formula.kind == Kind::And
        || operand_kind == Some(Kind::Or)
        || operand_kind == Some(Kind::Imply);
    if is_conjunctive && count_conjuncts(formula, 3) == 0 {
        return Ok((
            insert_node(
                queue,
                make_node(
                    vec![formula.clone()],
                    Rule::new(RuleName::ConjTree, vec![formula.clone()]),
                    Priority::Prop,
                    goalness,
                    vec![get_conjuncts(exprs, formula)],
                ),
            ),
            true,
        ));
    }
    let is_disjunctive =
        formula.kind == Kind::Or || operand_kind == Some(Kind::And) || formula.kind == Kind::Imply;
    if is_disjunctive && count_disjuncts(formula, 3) == 0 {
        return Ok((
            insert_node(
                queue,
                make_node(
                    vec![formula.clone()],
                    Rule::new(RuleName::DisjTree, vec![formula.clone()]),
                    Priority::Prop,
                    goalness,
                    get_disjuncts(exprs, formula)
                        .into_iter()
                        .map(|inner| vec![inner])
                        .collect(),
                ),
            ),
            true,
        ));
    }
    Ok((queue.clone(), false))
}

pub fn add_alpha(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let exprs = &context.exprs;
    let add = |rule: Rule, branch: Vec<Expr>| -> Result<RuleResult, ZenonError> {
        Ok((
            insert_node(
                queue,
                make_node(
                    vec![formula.clone()],
                    rule,
                    Priority::Prop,
                    goalness,
                    vec![branch],
                ),
            ),
            true,
        ))
    };
    if formula.kind == Kind::And {
        let args = &formula.args;
        return add(
            Rule::new(RuleName::And, vec![args[0].clone(), args[1].clone()]),
            vec![args[0].clone(), args[1].clone()],
        );
    }
    if formula.kind != Kind::Not {
        return Ok((queue.clone(), false));
    }
    let operand = &formula.args[0];
    let args = &operand.args;
    match operand.kind {
        Kind::Not => add(
            Rule::new(RuleName::NotNot, vec![args[0].clone()]),
            vec![args[0].clone()],
        ),
        Kind::Or => add(
            Rule::new(RuleName::NotOr, vec![args[0].clone(), args[1].clone()]),
            vec![exprs.enot(&args[0]), exprs.enot(&args[1])],
        ),
        Kind::Imply => add(
            Rule::new(RuleName::NotImpl, vec![args[0].clone(), args[1].clone()]),
            vec![args[0].clone(), exprs.enot(&args[1])],
        ),
        _ => Ok((queue.clone(), false)),
    }
}

pub fn add_beta(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let exprs = &context.exprs;
    let add = |rule: Rule, branches: Vec<Vec<Expr>>| -> Result<RuleResult, ZenonError> {
        Ok((
            insert_node(
                queue,
                make_node(
                    vec![formula.clone()],
                    rule,
                    Priority::Prop,
                    goalness,
                    branches,
                ),
            ),
            true,
        ))
    };
    if matches!(formula.kind, Kind::Or | Kind::Imply | Kind::Equiv) {
        let left = &formula.args[0];
        let right = &formula.args[1];
        let pair = vec![left.clone(), right.clone()];
        return match formula.kind {
            Kind::Or => add(
                Rule::new(RuleName::Or, pair),
                vec![vec![left.clone()], vec![right.clone()]],
            ),
            Kind::Imply => add(
                Rule::new(RuleName::Impl, pair),
                vec![vec![exprs.enot(left)], vec![right.clone()]],
            ),
            _ => add(
                Rule::new(RuleName::Equiv, pair),
                vec![
                    vec![exprs.enot(left), exprs.enot(right)],
                    vec![left.clone(), right.clone()],
                ],
            ),
        };
    }
    if formula.kind != Kind::Not {
        return Ok((queue.clone(), false));
    }
    let operand = &formula.args[0];
    if operand.kind != Kind::And && operand.kind != Kind::Equiv {
        return Ok((queue.clone(), false));
    }
    let first = &operand.args[0];
    let second = &operand.args[1];
    let pair = vec![first.clone(), second.clone()];
    if operand.kind == Kind::And {
        return add(
            Rule::new(RuleName::NotAnd, pair),
            vec![vec![exprs.enot(first)], vec![exprs.enot(second)]],
        );
    }
    add(
        Rule::new(RuleName::NotEquiv, pair),
        vec![
            vec![exprs.enot(first), second.clone()],
            vec![first.clone(), exprs.enot(second)],
        ],
    )
}

pub fn add_delta(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let exprs = &context.exprs;
    if formula.kind == Kind::Ex {
        let variable = &formula.args[0];
        let body = &formula.args[1];
        let witness = exprs.substitute(
            &[(
                variable.clone(),
                exprs.etau(variable, &formula.symbol, body),
            )],
            body,
        );
        return Ok((
            insert_node(
                queue,
                make_node(
                    vec![formula.clone()],
                    Rule::new(RuleName::Ex, vec![formula.clone()]),
                    Priority::Prop,
                    goalness,
                    vec![vec![witness]],
                ),
            ),
            true,
        ));
    }
    if formula.kind != Kind::Not || formula.args[0].kind != Kind::All {
        return Ok((queue.clone(), false));
    }
    let quantified = &formula.args[0];
    let variable = &quantified.args[0];
    let negated_body = exprs.enot(&quantified.args[1]);
    let witness = exprs.substitute(
        &[(
            variable.clone(),
            exprs.etau(variable, &quantified.symbol, &negated_body),
        )],
        &negated_body,
    );
    let existential = exprs.eex(variable, &quantified.symbol, &negated_body);
    Ok((
        insert_node(
            queue,
            make_node(
                vec![formula.clone()],
                Rule::new(RuleName::NotAllEx, vec![formula.clone()]),
                Priority::Prop,
                goalness,
                vec![vec![witness, existential]],
            ),
        ),
        true,
    ))
}

pub fn add_gamma(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let exprs = &context.exprs;
    if formula.kind == Kind::All {
        let meta = exprs.emeta(formula);
        let instance =
            exprs.substitute(&[(formula.args[0].clone(), meta.clone())], &formula.args[1]);
        return Ok((
            insert_node(
                queue,
                make_node(
                    vec![formula.clone()],
                    Rule::new(RuleName::All, vec![formula.clone(), meta]),
                    Priority::Arity,
                    goalness,
                    vec![vec![instance]],
                ),
            ),
            true,
        ));
    }
    if formula.kind != Kind::Not || formula.args[0].kind != Kind::Ex {
        return Ok((queue.clone(), false));
    }
    let quantified = &formula.args[0];
    let meta = exprs.emeta(quantified);
    let instance = exprs.enot(&exprs.substitute(
        &[(quantified.args[0].clone(), meta.clone())],
        &quantified.args[1],
    ));
    Ok((
        insert_node(
            queue,
            make_node(
                vec![formula.clone()],
                Rule::new(RuleName::NotEx, vec![formula.clone(), meta]),
                Priority::Arity,
                goalness,
                vec![vec![instance]],
            ),
        ),
        true,
    ))
}

fn unfold(
    exprs: &Expressions,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
    definition: &Rc<Definition>,
    args: Option<&[Expr]>,
    wrap: &dyn Fn(Expr) -> Expr,
) -> RuleResult {
    let params = definition.params();
    let body = definition.body();
    let add = |unfolded: Expr| -> RuleResult {
        let rule = Rule::definition(definition.clone(), formula.clone(), unfolded.clone());
        (
            insert_node(
                queue,
                make_node(
                    vec![formula.clone()],
                    rule,
                    Priority::Prop,
                    goalness,
                    vec![vec![unfolded]],
                ),
            ),
            true,
        )
    };
    if let Some(args) = args
        && params.is_empty()
        && body.kind == Kind::Var
    {
        return add(wrap(exprs.eapp(&body.symbol, args)));
    }
    let actuals = args.unwrap_or_default();
    if params.len() != actuals.len() {
        return (queue.clone(), false);
    }
    let map: Vec<(Expr, Expr)> = params
        .iter()
        .cloned()
        .zip(actuals.iter().cloned())
        .collect();
    match exprs.substitute_second_order(&map, body) {
        None => (queue.clone(), false),
        Some(unfolded) => add(wrap(unfolded)),
    }
}

pub fn add_unfold(
    context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let exprs = &context.exprs;
    let index = &context.index;
    let relations = &context.relations;
    let is_negated = formula.kind == Kind::Not;
    let atom = if is_negated {
        &formula.args[0]
    } else {
        formula
    };
    let negate = |inner: Expr| {
        if is_negated {
            exprs.enot(&inner)
        } else {
            inner
        }
    };
    let try_unfold = |term: &Expr, wrap: &dyn Fn(Expr) -> Expr| {
        let definition = matches!(term.kind, Kind::App | Kind::Var)
            .then(|| index.get_definition(&term.symbol))
            .flatten()?;
        Some(unfold(
            exprs,
            queue,
            formula,
            goalness,
            &definition,
            (term.kind == Kind::App).then_some(term.args.as_slice()),
            wrap,
        ))
    };
    // Zenon tries applications before variables, each first as the formula itself, then as either
    // side of a relation that is reflexive, symmetric or transitive.
    for kind in [Kind::App, Kind::Var] {
        if atom.kind == kind
            && let Some(result) = try_unfold(atom, &negate)
        {
            return Ok(result);
        }
        if !atom.is_relation() || !relations.is_any(&atom.symbol) {
            continue;
        }
        let left = &atom.args[0];
        let right = &atom.args[1];
        if left.kind == kind
            && let Some(result) = try_unfold(left, &|unfolded| {
                negate(exprs.eapp(&atom.symbol, &[unfolded, right.clone()]))
            })
        {
            return Ok(result);
        }
        if right.kind == kind
            && let Some(result) = try_unfold(right, &|unfolded| {
                negate(exprs.eapp(&atom.symbol, &[left.clone(), unfolded]))
            })
        {
            return Ok(result);
        }
    }
    Ok((queue.clone(), false))
}

pub fn add_useless(
    _context: &mut SearchContext,
    queue: &Queue,
    formula: &Expr,
    _goalness: i64,
) -> Result<RuleResult, ZenonError> {
    let atom = if formula.kind == Kind::Not {
        &formula.args[0]
    } else {
        formula
    };
    let is_useless = atom.kind == Kind::Var
        || atom.kind == Kind::Tau
        || formula.kind == Kind::True
        || (formula.kind == Kind::Not && atom.kind == Kind::False);
    Ok((queue.clone(), is_useless))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::{Phrase, parse_zenon};

    fn parse_formula(exprs: &Expressions, text: &str) -> Expr {
        let phrases = parse_zenon(exprs, &format!("$hyp \"h\" {text}")).expect("a formula");
        match phrases.first() {
            Some(Phrase::Hyp { formula, .. }) => formula.clone(),
            _ => panic!("a hypothesis"),
        }
    }

    fn parse_all(exprs: &Expressions, texts: &[&str]) -> Vec<Expr> {
        texts
            .iter()
            .map(|text| parse_formula(exprs, text))
            .collect()
    }

    #[test]
    fn decomposes_junction_trees_in_order() {
        let exprs = Expressions::new();
        let conjunction = parse_formula(&exprs, r"(/\ (P a) (/\ (-. (\/ (P b) (P c))) (P d)))");
        assert_eq!(count_conjuncts(&conjunction, 3), 0);
        assert_eq!(
            get_conjuncts(&exprs, &conjunction),
            parse_all(&exprs, &["(P a)", "(-. (P b))", "(-. (P c))", "(P d)"])
        );
        let implication = parse_formula(&exprs, r"(=> (/\ (P a) (P b)) (P c))");
        assert_eq!(count_disjuncts(&implication, 3), 0);
        assert_eq!(
            get_disjuncts(&exprs, &implication),
            parse_all(&exprs, &["(-. (P a))", "(-. (P b))", "(P c)"])
        );
        assert_eq!(
            count_conjuncts(&parse_formula(&exprs, r"(/\ (P a) (P b))"), 3),
            1
        );
    }
}

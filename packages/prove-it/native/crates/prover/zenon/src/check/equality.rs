//! The checks of Zenon's rules for equality, strings and the relations that the hypotheses make
//! reflexive, symmetric or transitive.

use super::terms::{
    Checked, Checker, RelationProperty, RuleSpec, Term, TermKind, UncheckedError, app, ensure,
    equal, expect_app, expect_kind, expect_not, get_string_text, instantiate, not, spec,
};
use crate::proof::RuleName;

fn relate(symbol: &str, left: &Term, right: &Term) -> Term {
    app(symbol, vec![left.clone(), right.clone()])
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TransitiveOrder {
    TransEq,
    TransEqSym,
    TransEq2,
}

// The two branches that the relation fails to link and the ends differ. The ends come from
// r(a, b) and ~r(c, d) in the order that Zenon's Trans or Trans_sym takes them.
fn get_transitivity_spec(
    checker: &mut Checker<'_>,
    args: &[Term],
    is_symmetric: bool,
) -> Checked<RuleSpec> {
    let negated = expect_not(&args[1])?;
    let symbol = negated.symbol().clone();
    let positive = expect_app(&args[0], &symbol, Some(2))?;
    let negative = expect_app(&negated, &symbol, Some(2))?;
    checker.ensure_relation(
        &symbol,
        if is_symmetric {
            &[RelationProperty::Transitive, RelationProperty::Symmetric]
        } else {
            &[RelationProperty::Transitive]
        },
    )?;
    let left = &positive[0];
    let right = &positive[1];
    let negated_left = &negative[0];
    let negated_right = &negative[1];
    let ends = if is_symmetric {
        [negated_right, left, right, negated_left]
    } else {
        [negated_left, left, right, negated_right]
    };
    spec(
        vec![args[0].clone(), args[1].clone()],
        vec![
            vec![
                not(&equal(ends[0], ends[1])),
                not(&relate(&symbol, ends[0], ends[1])),
            ],
            vec![
                not(&equal(ends[2], ends[3])),
                not(&relate(&symbol, ends[2], ends[3])),
            ],
        ],
    )
}

// a = b against ~r(c, d), in the order of Zenon's TransEq, TransEq_sym or TransEq2.
fn get_transitive_equality_spec(
    checker: &mut Checker<'_>,
    args: &[Term],
    order: TransitiveOrder,
) -> Checked<RuleSpec> {
    let left = &args[0];
    let right = &args[1];
    let negated = expect_not(&args[2])?;
    let symbol = negated.symbol().clone();
    let negative = expect_app(&negated, &symbol, Some(2))?;
    checker.ensure_relation(
        &symbol,
        if order == TransitiveOrder::TransEqSym {
            &[RelationProperty::Transitive, RelationProperty::Symmetric]
        } else {
            &[RelationProperty::Transitive]
        },
    )?;
    let negated_left = &negative[0];
    let negated_right = &negative[1];
    let ends = match order {
        TransitiveOrder::TransEq => [negated_left, left, right, negated_right],
        TransitiveOrder::TransEqSym => [negated_right, left, right, negated_left],
        TransitiveOrder::TransEq2 => [negated_left, right, left, negated_right],
    };
    let first = not(&relate(&symbol, ends[0], ends[1]));
    let second = not(&relate(&symbol, ends[2], ends[3]));
    spec(
        vec![equal(left, right), args[2].clone()],
        vec![
            vec![not(&equal(ends[0], ends[1])), first.clone()],
            vec![first, second.clone()],
            vec![not(&equal(ends[2], ends[3])), second],
        ],
    )
}

// Of t1 = s1 and t2 = s2 with distinct strings s1 and s2, in the order of the rule's sides.
fn get_string_difference_spec(args: &[Term], sides: &str) -> Checked<RuleSpec> {
    let term1 = &args[0];
    let string1 = &args[1];
    let term2 = &args[2];
    let string2 = &args[3];
    ensure(get_string_text(string1)? != get_string_text(string2)?)?;
    let is_left = |index: usize| sides.as_bytes()[index] == b'l';
    spec(
        vec![
            if is_left(0) {
                equal(term1, string1)
            } else {
                equal(string1, term1)
            },
            if is_left(1) {
                equal(term2, string2)
            } else {
                equal(string2, term2)
            },
        ],
        vec![vec![not(&equal(term1, term2))]],
    )
}

// Of f(a1, ..., an) and ~g(b1, ..., bn) with f and g the same: some argument differs.
fn get_arguments_differ_spec(premises: Vec<Term>, left: &Term, right: &Term) -> Checked<RuleSpec> {
    let left_args = expect_kind(left, TermKind::App)?;
    let right_args = expect_kind(right, TermKind::App)?;
    ensure(left.symbol() == right.symbol() && left_args.len() == right_args.len())?;
    spec(
        premises,
        left_args
            .iter()
            .zip(&right_args)
            .map(|(inner, other)| vec![not(&equal(inner, other))])
            .collect(),
    )
}

fn congruence(args: &[Term], is_left_to_right: bool) -> Checked<RuleSpec> {
    ensure(args[0].kind() == TermKind::Lam)?;
    spec(
        vec![
            instantiate(&args[0], &args[1]),
            if is_left_to_right {
                equal(&args[1], &args[2])
            } else {
                equal(&args[2], &args[1])
            },
        ],
        vec![vec![instantiate(&args[0], &args[2])]],
    )
}

fn string_equal(args: &[Term]) -> Checked<RuleSpec> {
    ensure(
        get_string_text(&app("$string", vec![args[0].clone()]))?
            != get_string_text(&app("$string", vec![args[1].clone()]))?,
    )?;
    spec(
        vec![equal(
            &app("$string", vec![args[0].clone()]),
            &app("$string", vec![args[1].clone()]),
        )],
        vec![],
    )
}

/// `EQUALITY_RULES`.
pub fn equality_rules(
    name: RuleName,
    args: &[Term],
    checker: &mut Checker<'_>,
    _uses: &[Term],
) -> Option<Checked<RuleSpec>> {
    Some(match name {
        RuleName::NotEqual => {
            get_arguments_differ_spec(vec![not(&equal(&args[0], &args[1]))], &args[0], &args[1])
        }
        RuleName::PNotP => expect_not(&args[1]).and_then(|negated| {
            get_arguments_differ_spec(vec![args[0].clone(), args[1].clone()], &args[0], &negated)
        }),
        RuleName::Trans => get_transitivity_spec(checker, args, false),
        RuleName::TransSym => get_transitivity_spec(checker, args, true),
        RuleName::TransEq => get_transitive_equality_spec(checker, args, TransitiveOrder::TransEq),
        RuleName::TransEqSym => {
            get_transitive_equality_spec(checker, args, TransitiveOrder::TransEqSym)
        }
        RuleName::TransEq2 => {
            get_transitive_equality_spec(checker, args, TransitiveOrder::TransEq2)
        }
        RuleName::CongruenceLr => congruence(args, true),
        RuleName::CongruenceRl => congruence(args, false),
        RuleName::Stringequal => string_equal(args),
        RuleName::Stringdiffll => get_string_difference_spec(args, "ll"),
        RuleName::Stringdifflr => get_string_difference_spec(args, "lr"),
        RuleName::Stringdiffrl => get_string_difference_spec(args, "rl"),
        RuleName::Stringdiffrr => get_string_difference_spec(args, "rr"),
        _ => return None,
    })
}

/// The check of a rule that names its relation: `getRelationRuleSpec`.
pub fn get_relation_rule_spec(
    name: RuleName,
    symbol: &str,
    args: &[Term],
    checker: &mut Checker<'_>,
) -> Checked<RuleSpec> {
    match name {
        RuleName::CloseRefl => {
            checker.ensure_relation(symbol, &[RelationProperty::Reflexive])?;
            spec(vec![not(&relate(symbol, &args[0], &args[0]))], vec![])
        }
        RuleName::CloseSym => {
            checker.ensure_relation(symbol, &[RelationProperty::Symmetric])?;
            spec(
                vec![
                    relate(symbol, &args[0], &args[1]),
                    not(&relate(symbol, &args[1], &args[0])),
                ],
                vec![],
            )
        }
        RuleName::Refl => {
            checker.ensure_relation(symbol, &[RelationProperty::Reflexive])?;
            spec(
                vec![not(&relate(symbol, &args[0], &args[1]))],
                vec![vec![not(&equal(&args[0], &args[1]))]],
            )
        }
        RuleName::PNotPSym => {
            checker.ensure_relation(symbol, &[RelationProperty::Symmetric])?;
            let left = expect_app(&args[0], symbol, Some(2))?;
            let right = expect_app(&expect_not(&args[1])?, symbol, Some(2))?;
            spec(
                vec![args[0].clone(), args[1].clone()],
                vec![
                    vec![not(&equal(&left[1], &right[0]))],
                    vec![not(&equal(&left[0], &right[1]))],
                ],
            )
        }
        _ => Err(UncheckedError),
    }
}

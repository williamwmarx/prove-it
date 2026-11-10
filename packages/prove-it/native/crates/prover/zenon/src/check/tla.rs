//! The checks of the TLA+ extension's rules for booleans, CHOOSE, natural numbers, bounded
//! quantifiers and equal propositions, after the lemmas in Zenon.thy that justify them.

use super::terms::{
    Checked, Checker, RuleSpec, Term, TermKind, ensure, equal, equiv, expect_app, expect_not,
    instantiate, is_variable, member, not, spec, term,
};
use crate::proof::RuleName;

// From P and a = b, or ~P and a = b, where P is one side: P differs from that side, or the other
// side holds.
fn get_proposition_equality_spec(
    args: &[Term],
    is_negated: bool,
    is_left: bool,
) -> Checked<RuleSpec> {
    let proposition = if is_negated {
        expect_not(&args[0])?
    } else {
        args[0].clone()
    };
    let sides = expect_app(&args[1], "=", Some(2))?;
    let matched = if is_left { &sides[0] } else { &sides[1] };
    let other = if is_left { &sides[1] } else { &sides[0] };
    spec(
        vec![args[0].clone(), args[1].clone()],
        vec![
            vec![not(&equal(&proposition, matched))],
            vec![if is_negated {
                not(other)
            } else {
                other.clone()
            }],
        ],
    )
}

// a = TRUE, TRUE = a, ~(a = TRUE) and the like: the side `constant` is TRUE or FALSE, and the
// other side holds or fails.
fn get_boolean_equality_spec(
    args: &[Term],
    is_negated: bool,
    constant: usize,
    kind: TermKind,
    is_holding: bool,
) -> Checked<RuleSpec> {
    let atom = if is_negated {
        expect_not(&args[0])?
    } else {
        args[0].clone()
    };
    let sides = expect_app(&atom, "=", Some(2))?;
    ensure(sides[constant].kind() == kind)?;
    let other = &sides[1 - constant];
    spec(
        vec![args[0].clone()],
        vec![vec![if is_holding {
            other.clone()
        } else {
            not(other)
        }]],
    )
}

fn choose_diff_choose(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    let left = &args[2];
    let right = &args[3];
    ensure(
        left.kind() == TermKind::Lam
            && right.kind() == TermKind::Lam
            && left.symbol() == right.symbol(),
    )?;
    let choice = |lambda: &Term| term(TermKind::Tau, lambda.symbol(), lambda.args());
    ensure(checker.is_same(&args[0], &not(&equal(&choice(left), &choice(right))))?)?;
    let differ = checker.bind(TermKind::Ex, left.symbol(), |bound| {
        not(&equiv(
            &instantiate(left, bound),
            &instantiate(right, bound),
        ))
    });
    spec(vec![args[0].clone()], vec![vec![differ]])
}

// Zenon writes ~(P <=> Q) as $notequiv(P, Q).
fn notequivdef(uses: &[Term]) -> Checked<RuleSpec> {
    ensure(uses.len() == 1)?;
    let sides = expect_app(&uses[0], "$notequiv", Some(2))?;
    spec(
        vec![uses[0].clone()],
        vec![vec![not(&equiv(&sides[0], &sides[1]))]],
    )
}

fn notequalchoose(args: &[Term]) -> Checked<RuleSpec> {
    let predicate = &args[3];
    ensure(predicate.kind() == TermKind::Lam)?;
    let exists = term(TermKind::Ex, predicate.symbol(), predicate.args());
    spec(
        vec![],
        vec![
            vec![exists.clone()],
            vec![not(&exists), not(&instantiate(predicate, &args[4]))],
        ],
    )
}

fn in_nat_0(args: &[Term]) -> Checked<RuleSpec> {
    let sides = expect_app(&expect_not(&args[0])?, "TLA.in", Some(2))?;
    ensure(is_variable(&sides[0], "0") && is_variable(&sides[1], "arith.N"))?;
    spec(vec![args[0].clone()], vec![])
}

fn in_nat_succ(args: &[Term]) -> Checked<RuleSpec> {
    let sides = expect_app(&expect_not(&args[0])?, "TLA.in", Some(2))?;
    let successor = expect_app(&sides[0], "TLA.fapply", Some(2))?;
    ensure(is_variable(&successor[0], "TLA.Succ") && is_variable(&sides[1], "arith.N"))?;
    spec(
        vec![args[0].clone()],
        vec![vec![not(&member(&successor[1], &sides[1]))]],
    )
}

fn box_p(args: &[Term]) -> Checked<RuleSpec> {
    let operand = expect_app(&args[0], "TLA.box", Some(1))?[0].clone();
    spec(vec![args[0].clone()], vec![vec![operand]])
}

fn all_in(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    let bounded = expect_app(&args[0], "TLA.bAll", Some(2))?;
    let sides = expect_app(&args[1], "TLA.in", Some(2))?;
    ensure(checker.is_same(&bounded[0], &sides[1])? && bounded[1].kind() == TermKind::Lam)?;
    spec(
        vec![args[0].clone(), args[1].clone()],
        vec![vec![instantiate(&bounded[1], &sides[0])]],
    )
}

fn notex_in(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    let bounded = expect_app(&expect_not(&args[0])?, "TLA.bEx", Some(2))?;
    let sides = expect_app(&args[1], "TLA.in", Some(2))?;
    ensure(checker.is_same(&bounded[0], &sides[1])? && bounded[1].kind() == TermKind::Lam)?;
    spec(
        vec![args[0].clone(), args[1].clone()],
        vec![vec![not(&instantiate(&bounded[1], &sides[0]))]],
    )
}

/// `TLA_RULES`.
pub fn tla_rules(
    name: RuleName,
    args: &[Term],
    checker: &mut Checker<'_>,
    uses: &[Term],
) -> Option<Checked<RuleSpec>> {
    Some(match name {
        RuleName::EqXTrue => get_boolean_equality_spec(args, false, 1, TermKind::True, true),
        RuleName::EqTrueX => get_boolean_equality_spec(args, false, 0, TermKind::True, true),
        RuleName::NoteqXTrue => get_boolean_equality_spec(args, true, 1, TermKind::True, false),
        RuleName::NoteqTrueX => get_boolean_equality_spec(args, true, 0, TermKind::True, false),
        RuleName::EqXFalse => get_boolean_equality_spec(args, false, 1, TermKind::False, false),
        RuleName::EqFalseX => get_boolean_equality_spec(args, false, 0, TermKind::False, false),
        RuleName::ChooseDiffChoose => choose_diff_choose(args, checker),
        RuleName::Notequivdef => notequivdef(uses),
        RuleName::Notequalchoose => notequalchoose(args),
        RuleName::InNat0 => in_nat_0(args),
        RuleName::InNatSucc => in_nat_succ(args),
        RuleName::BoxP => box_p(args),
        RuleName::AllIn => all_in(args, checker),
        RuleName::NotexIn => notex_in(args, checker),
        RuleName::PEqL => get_proposition_equality_spec(args, false, true),
        RuleName::PEqR => get_proposition_equality_spec(args, false, false),
        RuleName::NpEqL => get_proposition_equality_spec(args, true, true),
        RuleName::NpEqR => get_proposition_equality_spec(args, true, false),
        _ => return None,
    })
}

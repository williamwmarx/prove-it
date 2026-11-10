//! The checks of the TLA+ extension's rules for functions, after the lemmas in Zenon.thy that
//! justify them.

use super::terms::{
    Checked, Checker, RuleSpec, Term, TermKind, and, app, domain, equal, equiv, expect_app,
    expect_not, fapply, imply, member, not, spec,
};
use crate::proof::RuleName;

// ~isAFcn(f) where f is built by a function constructor closes the branch.
fn get_not_function_spec(formula: &Term, constructor: &str, arity: usize) -> Checked<RuleSpec> {
    expect_app(
        &expect_app(&expect_not(formula)?, "TLA.isAFcn", Some(1))?[0],
        constructor,
        Some(arity),
    )?;
    spec(vec![formula.clone()], vec![])
}

fn fun_equal(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    let sides = expect_app(&args[0], "=", Some(2))?;
    let left = &sides[0];
    let right = &sides[1];
    let result = and(
        &and(
            &equiv(
                &app("TLA.isAFcn", vec![left.clone()]),
                &app("TLA.isAFcn", vec![right.clone()]),
            ),
            &equal(&domain(left), &domain(right)),
        ),
        &checker.bind(TermKind::All, "", |bound| {
            equal(&fapply(left, bound), &fapply(right, bound))
        }),
    );
    spec(vec![args[0].clone()], vec![vec![result]])
}

fn not_fun_equal(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    let sides = expect_app(&expect_not(&args[0])?, "=", Some(2))?;
    let left = &sides[0];
    let right = &sides[1];
    let result = not(&and(
        &and(
            &and(
                &app("TLA.isAFcn", vec![left.clone()]),
                &app("TLA.isAFcn", vec![right.clone()]),
            ),
            &equal(&domain(left), &domain(right)),
        ),
        &checker.bind(TermKind::All, "", |bound| {
            imply(
                &member(bound, &domain(right)),
                &equal(&fapply(left, bound), &fapply(right, bound)),
            )
        }),
    ));
    spec(vec![args[0].clone()], vec![vec![result]])
}

/// `FUNCTION_RULES`.
pub fn function_rules(
    name: RuleName,
    args: &[Term],
    checker: &mut Checker<'_>,
    _uses: &[Term],
) -> Option<Checked<RuleSpec>> {
    Some(match name {
        RuleName::NotisafcnFcn => get_not_function_spec(&args[0], "TLA.Fcn", 2),
        RuleName::NotisafcnExcept => get_not_function_spec(&args[0], "TLA.except", 3),
        RuleName::NotisafcnOnearg => get_not_function_spec(&args[0], "TLA.oneArg", 2),
        RuleName::NotisafcnExtend => get_not_function_spec(&args[0], "TLA.extend", 2),
        RuleName::Funequal => fun_equal(args, checker),
        RuleName::Notfunequal => not_fun_equal(args, checker),
        _ => return None,
    })
}

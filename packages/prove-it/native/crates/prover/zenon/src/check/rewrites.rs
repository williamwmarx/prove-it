//! The checks of the TLA+ extension's rules that rewrite a subterm in place: evaluating a function
//! application, DOMAIN, IF, CASE, Len, or a formula used as a term. Each rule names the context of
//! the subterm as a lambda, (\x. context).

use super::records::get_fields;
use super::terms::{
    Checked, Checker, RuleSpec, Term, TermKind, UncheckedError, and, app, domain, ensure, equal,
    expect_app, false_term, fapply, get_pairs, get_string_text, instantiate, is_app, is_variable,
    make_natural, member, not, spec, true_term,
};
use crate::proof::RuleName;

fn find(hole: &str, context: &Term, candidate: &Term) -> Option<Term> {
    if context.kind() == TermKind::Var && &**context.symbol() == hole {
        return Some(candidate.clone());
    }
    if context.kind() != candidate.kind() || context.symbol() != candidate.symbol() {
        return None;
    }
    if context.arity() != candidate.arity() {
        return None;
    }
    if context.kind() != TermKind::App && context.kind() != TermKind::Not {
        return None;
    }
    (0..context.arity()).find_map(|index| find(hole, &context.arg(index), &candidate.arg(index)))
}

// The term that fills the hole of a context to give a formula.
fn get_filled(lambda: &Term, formula: &Term) -> Checked<Term> {
    ensure(lambda.kind() == TermKind::Lam)?;
    find(lambda.arg(0).symbol(), &lambda.arg(1), formula).ok_or(UncheckedError)
}

fn get_rewrite_spec(
    checker: &mut Checker<'_>,
    formula: &Term,
    lambda: &Term,
    build: impl FnOnce(&Term) -> Checked<Vec<Vec<Term>>>,
) -> Checked<RuleSpec> {
    let filled = get_filled(lambda, formula)?;
    ensure(checker.is_same(formula, &instantiate(lambda, &filled))?)?;
    spec(vec![formula.clone()], build(&filled)?)
}

fn get_case_branches(lambda: &Term, args: &[Term], condition: &Term) -> Vec<Vec<Term>> {
    match args {
        [] => vec![vec![condition.clone()]],
        [only] => vec![vec![condition.clone(), instantiate(lambda, only)]],
        [guard, value, rest @ ..] => {
            let mut branches = vec![vec![guard.clone(), instantiate(lambda, value)]];
            branches.extend(get_case_branches(
                lambda,
                rest,
                &and(&not(guard), condition),
            ));
            branches
        }
    }
}

// A formula used as a term splits into the cases where it equals TRUE and FALSE.
fn get_bool_case_spec(
    checker: &mut Checker<'_>,
    args: &[Term],
    is_kind: impl FnOnce(&Term) -> bool,
) -> Checked<RuleSpec> {
    let operand = expect_app(&args[1], "=", Some(2))?[0].clone();
    ensure(is_kind(&operand))?;
    let lambda = &args[5];
    let filled = get_filled(lambda, &args[0])?;
    ensure(
        checker.is_same(&filled, &operand)?
            && checker.is_same(&args[0], &instantiate(lambda, &operand))?,
    )?;
    spec(
        vec![args[0].clone()],
        vec![
            vec![
                equal(&operand, &true_term()),
                instantiate(lambda, &true_term()),
            ],
            vec![
                equal(&operand, &false_term()),
                instantiate(lambda, &false_term()),
            ],
        ],
    )
}

// `/^(0|[1-9][0-9]*)$/`.
fn is_numeral(text: &str) -> bool {
    text == "0"
        || (!text.is_empty()
            && !text.starts_with('0')
            && text.bytes().all(|byte| byte.is_ascii_digit()))
}

// A JavaScript number, as `Number` reads a numeral.
fn get_natural(formula: &Term) -> Checked<f64> {
    let mut count = 0.0;
    let mut current = formula.clone();
    while is_app(&current, "TLA.fapply", Some(2)) && is_variable(&current.arg(0), "TLA.Succ") {
        count += 1.0;
        current = current.arg(1);
    }
    ensure(current.kind() == TermKind::Var && is_numeral(current.symbol()))?;
    let value: f64 = current.symbol().parse().map_err(|_| UncheckedError)?;
    Ok(count + value)
}

fn trueistrue(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    let lambda = &args[3];
    let subterm = &args[1];
    ensure(
        lambda.kind() == TermKind::Lam
            && checker.is_same(&args[0], &instantiate(lambda, subterm))?,
    )?;
    spec(
        vec![args[0].clone(), subterm.clone()],
        vec![vec![instantiate(lambda, &true_term())]],
    )
}

fn fapplyfcn(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    get_rewrite_spec(checker, &args[0], &args[3], |filled| {
        let applied = expect_app(filled, "TLA.fapply", Some(2))?;
        let fcn = expect_app(&applied[0], "TLA.Fcn", Some(2))?;
        ensure(fcn[1].kind() == TermKind::Lam)?;
        Ok(vec![
            vec![not(&member(&applied[1], &fcn[0]))],
            vec![instantiate(&args[3], &instantiate(&fcn[1], &applied[1]))],
        ])
    })
}

fn fapplyexcept(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    get_rewrite_spec(checker, &args[0], &args[8], |filled| {
        let applied = expect_app(filled, "TLA.fapply", Some(2))?;
        let except = expect_app(&applied[0], "TLA.except", Some(3))?;
        let argument = &applied[1];
        let in_domain = member(argument, &domain(&except[0]));
        Ok(vec![
            vec![
                in_domain.clone(),
                equal(&except[1], argument),
                instantiate(&args[8], &except[2]),
            ],
            vec![
                in_domain.clone(),
                not(&equal(&except[1], argument)),
                instantiate(&args[8], &fapply(&except[0], argument)),
            ],
            vec![not(&in_domain)],
        ])
    })
}

fn tuple_access(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    get_rewrite_spec(checker, &args[0], &args[2], |filled| {
        let applied = expect_app(filled, "TLA.fapply", Some(2))?;
        let components = expect_app(&applied[0], "TLA.tuple", None)?;
        let position = get_natural(&applied[1])?;
        ensure((1.0..=components.len() as f64).contains(&position))?;
        let component = components
            .get(position as usize - 1)
            .ok_or(UncheckedError)?;
        Ok(vec![vec![instantiate(&args[2], component)]])
    })
}

fn record_access(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    get_rewrite_spec(checker, &args[0], &args[2], |filled| {
        let applied = expect_app(filled, "TLA.fapply", Some(2))?;
        let label = get_string_text(&applied[1])?;
        let mut found = None;
        for inner in get_fields(&applied[0], "TLA.record")? {
            if get_string_text(&inner.0)? == label {
                found = Some(inner);
                break;
            }
        }
        let field = found.ok_or(UncheckedError)?;
        Ok(vec![vec![instantiate(&args[2], &field.1)]])
    })
}

fn domain_fcn(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    get_rewrite_spec(checker, &args[0], &args[2], |filled| {
        let fcn = expect_app(
            &expect_app(filled, "TLA.DOMAIN", Some(1))?[0],
            "TLA.Fcn",
            Some(2),
        )?;
        Ok(vec![vec![instantiate(&args[2], &fcn[0])]])
    })
}

fn domain_except(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    get_rewrite_spec(checker, &args[0], &args[2], |filled| {
        let except = expect_app(
            &expect_app(filled, "TLA.DOMAIN", Some(1))?[0],
            "TLA.except",
            Some(3),
        )?;
        Ok(vec![vec![instantiate(&args[2], &domain(&except[0]))]])
    })
}

fn record_domain(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    get_rewrite_spec(checker, &args[0], &args[2], |filled| {
        let record = expect_app(filled, "TLA.DOMAIN", Some(1))?[0].clone();
        let fields = get_pairs(&expect_app(&record, "TLA.record", None)?)?;
        Ok(vec![vec![instantiate(
            &args[2],
            &app("TLA.set", fields.into_iter().map(|field| field.0).collect()),
        )]])
    })
}

fn iftrue(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    get_rewrite_spec(checker, &args[0], &args[2], |filled| {
        let operands = expect_app(filled, "TLA.cond", Some(3))?;
        ensure(operands[0].kind() == TermKind::True)?;
        Ok(vec![vec![instantiate(&args[2], &operands[1])]])
    })
}

fn iffalse(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    get_rewrite_spec(checker, &args[0], &args[2], |filled| {
        let operands = expect_app(filled, "TLA.cond", Some(3))?;
        ensure(operands[0].kind() == TermKind::False)?;
        Ok(vec![vec![instantiate(&args[2], &operands[2])]])
    })
}

fn ifthenelse(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    get_rewrite_spec(checker, &args[0], &args[5], |filled| {
        let operands = expect_app(filled, "TLA.cond", Some(3))?;
        Ok(vec![
            vec![operands[0].clone(), instantiate(&args[5], &operands[1])],
            vec![not(&operands[0]), instantiate(&args[5], &operands[2])],
        ])
    })
}

fn case(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    get_rewrite_spec(checker, &args[0], &args[1], |filled| {
        Ok(get_case_branches(
            &args[1],
            &expect_app(filled, "TLA.CASE", None)?,
            &true_term(),
        ))
    })
}

fn tuple_len(args: &[Term], checker: &mut Checker<'_>) -> Checked<RuleSpec> {
    get_rewrite_spec(checker, &args[0], &args[2], |filled| {
        let components = expect_app(
            &expect_app(filled, "TLA.Len", Some(1))?[0],
            "TLA.tuple",
            None,
        )?;
        Ok(vec![vec![instantiate(
            &args[2],
            &make_natural(components.len()),
        )]])
    })
}

/// `REWRITE_RULES`.
pub fn rewrite_rules(
    name: RuleName,
    args: &[Term],
    checker: &mut Checker<'_>,
    _uses: &[Term],
) -> Option<Checked<RuleSpec>> {
    let is_kind = |kind: TermKind| move |operand: &Term| operand.kind() == kind;
    Some(match name {
        RuleName::Trueistrue => trueistrue(args, checker),
        RuleName::Fapplyfcn => fapplyfcn(args, checker),
        RuleName::Fapplyexcept => fapplyexcept(args, checker),
        RuleName::TupleAccess => tuple_access(args, checker),
        RuleName::RecordAccess => record_access(args, checker),
        RuleName::DomainFcn => domain_fcn(args, checker),
        RuleName::DomainExcept => domain_except(args, checker),
        RuleName::RecordDomain => record_domain(args, checker),
        RuleName::BoolcaseNot => get_bool_case_spec(checker, args, is_kind(TermKind::Not)),
        RuleName::BoolcaseAnd => get_bool_case_spec(checker, args, is_kind(TermKind::And)),
        RuleName::BoolcaseOr => get_bool_case_spec(checker, args, is_kind(TermKind::Or)),
        RuleName::BoolcaseImply => get_bool_case_spec(checker, args, is_kind(TermKind::Imply)),
        RuleName::BoolcaseEquiv => get_bool_case_spec(checker, args, is_kind(TermKind::Equiv)),
        RuleName::BoolcaseEqual => {
            get_bool_case_spec(checker, args, |operand| is_app(operand, "=", Some(2)))
        }
        RuleName::BoolcaseAll => get_bool_case_spec(checker, args, is_kind(TermKind::All)),
        RuleName::BoolcaseEx => get_bool_case_spec(checker, args, is_kind(TermKind::Ex)),
        RuleName::Iftrue => iftrue(args, checker),
        RuleName::Iffalse => iffalse(args, checker),
        RuleName::Ifthenelse => ifthenelse(args, checker),
        RuleName::Case => case(args, checker),
        RuleName::TupleLen => tuple_len(args, checker),
        _ => return None,
    })
}

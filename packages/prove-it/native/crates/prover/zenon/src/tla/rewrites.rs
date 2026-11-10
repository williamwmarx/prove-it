// Ported from Zenon's ext_tla.ml, as shipped in tlapm. Copyright 2008 INRIA, see LICENSE.
//! Rewriting a subterm: unfolding a definition, evaluating a function application, IF, CASE or a
//! formula used as a term, or replacing the subterm with an equal one from the branch.

use crate::ZenonError;
use crate::expr::{Expr, Expressions, Kind, efalse, etrue};
use crate::index_table::Index;
use crate::node::{Priority, make_node};
use crate::proof::{Rule, RuleName};
use crate::tla::terms::{
    Item, TlaContext, domain, equal, fapply, get_pairs, is_variable, make_natural, member,
};

/// The digits of an integer in `radix`, as a JavaScript number.
fn parse_digits(digits: &str, radix: u32) -> f64 {
    if digits.is_empty() {
        return f64::NAN;
    }
    digits.chars().fold(0.0, |value, digit| {
        value * f64::from(radix) + f64::from(digit.to_digit(radix).unwrap_or(0))
    })
}

/// JavaScript's `Number` on a sign and decimal digits, where no digits read as 0 without a sign.
fn parse_decimal(sign: &str, digits: &str) -> f64 {
    let value = match digits {
        "" if sign.is_empty() => 0.0,
        "" => f64::NAN,
        _ => digits.parse::<f64>().unwrap_or(f64::NAN),
    };
    if sign == "-" { -value } else { value }
}

/// OCaml's int_of_string, for the numerals that tlapm writes as variables, as the TypeScript
/// reads them into a JavaScript number: a sign before a radix prefix gives NaN, as `Number` does.
fn parse_integer(text: &str) -> Option<f64> {
    let unsigned = text.strip_prefix(['-', '+']).unwrap_or(text);
    let sign = &text[..text.len() - unsigned.len()];
    let prefix = unsigned.get(..2).map(str::to_ascii_lowercase);
    let radix = match prefix.as_deref() {
        Some("0x") => Some(16),
        Some("0o") => Some(8),
        Some("0b") => Some(2),
        Some("0u") => Some(10),
        _ => None,
    };
    let Some(radix) = radix else {
        let is_decimal = unsigned.starts_with(|inner: char| inner.is_ascii_digit())
            && unsigned
                .chars()
                .all(|inner| inner == '_' || inner.is_ascii_digit());
        return is_decimal.then(|| parse_decimal(sign, &unsigned.replace('_', "")));
    };
    let rest = &unsigned[2..];
    let is_valid = !rest.is_empty()
        && rest
            .chars()
            .all(|inner| inner == '_' || inner.is_digit(radix));
    if !is_valid {
        return None;
    }
    let digits = rest.replace('_', "");
    Some(match (radix, sign) {
        (10, _) => parse_decimal(sign, &digits),
        (_, "") => parse_digits(&digits, radix),
        _ => f64::NAN,
    })
}

fn get_natural_constant(expression: &Expr) -> Option<f64> {
    let mut accumulator = 0.0;
    let mut current = expression.clone();
    while current.is_app_with_arity("TLA.fapply", 2) && is_variable(&current.args[0], "TLA.Succ") {
        accumulator += 1.0;
        current = current.args[1].clone();
    }
    if current.kind != Kind::Var {
        return None;
    }
    parse_integer(&current.symbol).map(|value| accumulator + value)
}

fn is_in_one_to(term: &Expr, maximum: usize) -> bool {
    get_natural_constant(term).is_some_and(|value| value > 0.0 && value <= maximum as f64)
}

fn get_case_branches(
    exprs: &Expressions,
    fill: &dyn Fn(&Expr) -> Expr,
    args: &[Expr],
    condition: Expr,
) -> Vec<Vec<Expr>> {
    match args {
        [] => vec![vec![condition]],
        [only] => vec![vec![condition, fill(only)]],
        [guard, value, rest @ ..] => {
            let rest = get_case_branches(
                exprs,
                fill,
                rest,
                exprs.eand(&exprs.enot(guard), &condition),
            );
            [vec![vec![guard.clone(), fill(value)]], rest].concat()
        }
    }
}

type MakeRewrite<'a> = dyn Fn(Rule, Vec<Expr>, Vec<Vec<Expr>>) -> Vec<Item> + 'a;

const SET_HEADS: &[&str] = &[
    "TLA.emptyset",
    "TLA.upair",
    "TLA.addElt",
    "TLA.set",
    "TLA.SUBSET",
    "TLA.UNION",
    "TLA.cup",
    "TLA.cap",
    "TLA.setminus",
    "TLA.subsetOf",
    "TLA.setOfAll",
    "TLA.FuncSet",
    "TLA.Product",
];

fn get_rewrites(
    context: TlaContext,
    is_in_term: bool,
    hole: &Expr,
    frame: &Expr,
    term: &Expr,
    make: &MakeRewrite,
) -> Result<Vec<Item>, ZenonError> {
    let exprs = context.exprs;
    let index = context.index;
    let lambda = exprs.elam(hole, "", frame);
    let fill = |inner: &Expr| exprs.substitute(&[(hole.clone(), inner.clone())], frame);
    let make_bool_case = |get_rule: &dyn Fn([Expr; 6]) -> Rule| {
        let is_true = equal(exprs, term, &etrue());
        let when_true = fill(&etrue());
        let is_false = equal(exprs, term, &efalse());
        let when_false = fill(&efalse());
        make(
            get_rule([
                fill(term),
                is_true.clone(),
                when_true.clone(),
                is_false.clone(),
                when_false.clone(),
                lambda.clone(),
            ]),
            vec![],
            vec![vec![is_true, when_true], vec![is_false, when_false]],
        )
    };
    // Rewrites the term with the equalities on the branch whose other side has one of these heads.
    let make_equality_rewrites =
        |wrapped: &Expr, heads: &[&str], subterm: &Expr| -> Result<Vec<Item>, ZenonError> {
            let has_good_head = |other: &Expr| {
                matches!(other.kind, Kind::App | Kind::Var)
                    && (heads.is_empty() || heads.contains(&&*other.symbol))
            };
            let rights: Vec<Expr> = index
                .find_equal_right(subterm)
                .into_iter()
                .filter(|inner| has_good_head(inner))
                .collect();
            let lefts: Vec<Expr> = index
                .find_equal_left(subterm)
                .into_iter()
                .filter(|inner| has_good_head(inner))
                .collect();
            let left_to_right = rights
                .iter()
                .map(|other| {
                    let rule = Rule::new(
                        RuleName::CongruenceLr,
                        vec![wrapped.clone(), subterm.clone(), other.clone()],
                    );
                    let added = vec![equal(exprs, subterm, other)];
                    Ok(make(rule, added, vec![vec![exprs.apply(wrapped, other)?]]))
                })
                .collect::<Result<Vec<_>, ZenonError>>()?;
            let right_to_left = lefts
                .iter()
                .map(|other| {
                    let rule = Rule::new(
                        RuleName::CongruenceRl,
                        vec![wrapped.clone(), subterm.clone(), other.clone()],
                    );
                    let added = vec![equal(exprs, other, subterm)];
                    Ok(make(rule, added, vec![vec![exprs.apply(wrapped, other)?]]))
                })
                .collect::<Result<Vec<_>, ZenonError>>()?;
            Ok([left_to_right.concat(), right_to_left.concat()].concat())
        };
    let make_hole_rewrites = |symbol: &str,
                              heads: &[&str],
                              subterm: &Expr,
                              other: Option<&Expr>|
     -> Result<Vec<Item>, ZenonError> {
        let inner = exprs.new_var();
        let wrapped = exprs.elam(
            &inner,
            "",
            &fill(&exprs.eapp(
                symbol,
                &match other {
                    None => vec![inner.clone()],
                    Some(other) => vec![other.clone(), inner.clone()],
                },
            )),
        );
        make_equality_rewrites(&wrapped, heads, subterm)
    };

    if is_in_term && index.is_member(term) {
        let replaced = fill(&etrue());
        return Ok(make(
            Rule::new(
                RuleName::Trueistrue,
                vec![
                    fill(term),
                    term.clone(),
                    replaced.clone(),
                    lambda.clone(),
                    term.clone(),
                ],
            ),
            vec![term.clone()],
            vec![vec![replaced]],
        ));
    }
    if term.is_app_with_arity("$notequiv", 2) {
        return Ok(vec![]);
    }
    if is_in_term
        && matches!(term.kind, Kind::Var | Kind::App)
        && let Some(definition) = index.get_definition(&term.symbol)
    {
        if term.kind == Kind::Var {
            if !definition.params().is_empty() {
                return Ok(vec![]);
            }
            let unfolded = fill(definition.body());
            return Ok(make(
                Rule::definition(definition.clone(), fill(term), unfolded.clone()),
                vec![],
                vec![vec![unfolded]],
            ));
        }
        if definition.params().len() != term.args.len() {
            return Ok(vec![]);
        }
        let map: Vec<(Expr, Expr)> = definition
            .params()
            .iter()
            .cloned()
            .zip(term.args.iter().cloned())
            .collect();
        let Some(body) = exprs.substitute_second_order(&map, definition.body()) else {
            return Err(ZenonError::new("Zenon: higher-order definition"));
        };
        let unfolded = fill(&body);
        return Ok(make(
            Rule::definition(definition.clone(), fill(term), unfolded.clone()),
            vec![],
            vec![vec![unfolded]],
        ));
    }
    if term.is_app_with_arity("TLA.fapply", 2) {
        let fcn = &term.args[0];
        let argument = &term.args[1];
        if fcn.is_app_with_arity("TLA.Fcn", 2) && fcn.args[1].kind == Kind::Lam {
            let body = &fcn.args[1];
            let outside = exprs.enot(&member(exprs, argument, &fcn.args[0]));
            let applied =
                fill(&exprs.substitute(&[(body.args[0].clone(), argument.clone())], &body.args[1]));
            return Ok(make(
                Rule::new(
                    RuleName::Fapplyfcn,
                    vec![
                        fill(term),
                        outside.clone(),
                        applied.clone(),
                        lambda.clone(),
                        fcn.args[0].clone(),
                        body.clone(),
                        argument.clone(),
                    ],
                ),
                vec![],
                vec![vec![outside], vec![applied]],
            ));
        }
        if fcn.is_app_with_arity("TLA.except", 3) {
            let base = &fcn.args[0];
            let point = &fcn.args[1];
            let value = &fcn.args[2];
            let in_domain = member(exprs, argument, &domain(exprs, base));
            let is_point = equal(exprs, point, argument);
            let changed = fill(value);
            let is_other = exprs.enot(&equal(exprs, point, argument));
            let unchanged = fill(&fapply(exprs, base, argument));
            let outside = exprs.enot(&in_domain);
            return Ok(make(
                Rule::new(
                    RuleName::Fapplyexcept,
                    vec![
                        fill(term),
                        in_domain.clone(),
                        is_point.clone(),
                        changed.clone(),
                        in_domain.clone(),
                        is_other.clone(),
                        unchanged.clone(),
                        outside.clone(),
                        lambda.clone(),
                        base.clone(),
                        point.clone(),
                        value.clone(),
                        argument.clone(),
                    ],
                ),
                vec![],
                vec![
                    vec![in_domain.clone(), is_point, changed],
                    vec![in_domain, is_other, unchanged],
                    vec![outside],
                ],
            ));
        }
        if fcn.is_app("TLA.tuple") && is_in_one_to(argument, fcn.args.len()) {
            // In range, so the constant is a whole number from 1 to the tuple's length.
            let position = get_natural_constant(argument).unwrap_or(0.0) as usize - 1;
            let component = &fcn.args[position];
            let replaced = fill(component);
            return Ok(make(
                Rule::new(
                    RuleName::TupleAccess,
                    vec![
                        fill(term),
                        replaced.clone(),
                        lambda.clone(),
                        term.clone(),
                        component.clone(),
                    ],
                ),
                vec![],
                vec![vec![replaced]],
            ));
        }
        if fcn.is_app("TLA.record") {
            let Some(field) = get_pairs(&fcn.args)
                .into_iter()
                .find(|pair| pair.0 == *argument)
            else {
                return Ok(vec![]);
            };
            let replaced = fill(&field.1);
            return Ok(make(
                Rule::new(
                    RuleName::RecordAccess,
                    vec![
                        fill(term),
                        replaced.clone(),
                        lambda.clone(),
                        term.clone(),
                        field.1,
                    ],
                ),
                vec![],
                vec![vec![replaced]],
            ));
        }
    }
    if term.is_app_with_arity("TLA.DOMAIN", 1) {
        let fcn = &term.args[0];
        if fcn.is_app_with_arity("TLA.Fcn", 2) {
            let replaced = fill(&fcn.args[0]);
            return Ok(make(
                Rule::new(
                    RuleName::DomainFcn,
                    vec![
                        fill(term),
                        replaced.clone(),
                        lambda.clone(),
                        fcn.args[0].clone(),
                        fcn.args[1].clone(),
                    ],
                ),
                vec![],
                vec![vec![replaced]],
            ));
        }
        if fcn.is_app_with_arity("TLA.except", 3) {
            let replaced = fill(&domain(exprs, &fcn.args[0]));
            return Ok(make(
                Rule::new(
                    RuleName::DomainExcept,
                    vec![
                        fill(term),
                        replaced.clone(),
                        lambda.clone(),
                        fcn.args[0].clone(),
                        fcn.args[1].clone(),
                        fcn.args[2].clone(),
                    ],
                ),
                vec![],
                vec![vec![replaced]],
            ));
        }
        if fcn.is_app("TLA.record") {
            let labels = exprs.eapp(
                "TLA.set",
                &get_pairs(&fcn.args)
                    .into_iter()
                    .map(|pair| pair.0)
                    .collect::<Vec<_>>(),
            );
            let replaced = fill(&labels);
            return Ok(make(
                Rule::new(
                    RuleName::RecordDomain,
                    vec![
                        fill(term),
                        replaced.clone(),
                        lambda.clone(),
                        term.clone(),
                        labels,
                    ],
                ),
                vec![],
                vec![vec![replaced]],
            ));
        }
        return make_hole_rewrites(
            "TLA.DOMAIN",
            &["TLA.Fcn", "TLA.except", "TLA.record"],
            fcn,
            None,
        );
    }
    if is_in_term {
        let with_args = |name: RuleName| {
            move |prefix: [Expr; 6]| Rule::new(name, [prefix.to_vec(), term.args.clone()].concat())
        };
        match term.kind {
            Kind::Not => return Ok(make_bool_case(&with_args(RuleName::BoolcaseNot))),
            Kind::And => return Ok(make_bool_case(&with_args(RuleName::BoolcaseAnd))),
            Kind::Or => return Ok(make_bool_case(&with_args(RuleName::BoolcaseOr))),
            Kind::Imply => return Ok(make_bool_case(&with_args(RuleName::BoolcaseImply))),
            Kind::Equiv => return Ok(make_bool_case(&with_args(RuleName::BoolcaseEquiv))),
            _ => {}
        }
        if term.is_relation() && &*term.symbol == "=" {
            return Ok(make_bool_case(&with_args(RuleName::BoolcaseEqual)));
        }
        if matches!(term.kind, Kind::All | Kind::Ex) {
            let predicate = exprs.elam(&term.args[0], &term.symbol, &term.args[1]);
            let name = if term.kind == Kind::All {
                RuleName::BoolcaseAll
            } else {
                RuleName::BoolcaseEx
            };
            return Ok(make_bool_case(&|prefix: [Expr; 6]| {
                Rule::new(name, [prefix.to_vec(), vec![predicate.clone()]].concat())
            }));
        }
    }
    if term.is_app_with_arity("TLA.cond", 3) {
        let condition = &term.args[0];
        let when_true = &term.args[1];
        let when_false = &term.args[2];
        if condition.kind == Kind::True {
            let replaced = fill(when_true);
            return Ok(make(
                Rule::new(
                    RuleName::Iftrue,
                    vec![
                        fill(term),
                        replaced.clone(),
                        lambda.clone(),
                        when_true.clone(),
                        when_false.clone(),
                    ],
                ),
                vec![],
                vec![vec![replaced]],
            ));
        }
        if condition.kind == Kind::False {
            let replaced = fill(when_false);
            return Ok(make(
                Rule::new(
                    RuleName::Iffalse,
                    vec![
                        fill(term),
                        replaced.clone(),
                        lambda.clone(),
                        when_true.clone(),
                        when_false.clone(),
                    ],
                ),
                vec![],
                vec![vec![replaced]],
            ));
        }
        let then_branch = fill(when_true);
        let negated = exprs.enot(condition);
        let else_branch = fill(when_false);
        return Ok(make(
            Rule::new(
                RuleName::Ifthenelse,
                vec![
                    fill(term),
                    condition.clone(),
                    then_branch.clone(),
                    negated.clone(),
                    else_branch.clone(),
                    lambda.clone(),
                    condition.clone(),
                    when_true.clone(),
                    when_false.clone(),
                ],
            ),
            vec![],
            vec![
                vec![condition.clone(), then_branch],
                vec![negated, else_branch],
            ],
        ));
    }
    if term.is_app("TLA.CASE") {
        let branches = get_case_branches(exprs, &fill, &term.args, etrue());
        let filled = fill(term);
        return Ok(make(
            Rule::new(
                RuleName::Case,
                [vec![filled.clone(), lambda.clone()], branches.concat()].concat(),
            ),
            vec![filled],
            branches,
        ));
    }
    if term.kind == Kind::Tau && !has_existential(exprs, index, term) {
        let exists = exprs.eex(&term.args[0], &term.symbol, &term.args[1]);
        return Ok(make(
            Rule::new(RuleName::Cut, vec![exists.clone()]),
            vec![],
            vec![vec![exists.clone()], vec![exprs.enot(&exists)]],
        ));
    }
    if term.is_app_with_arity("TLA.Len", 1) {
        let sequence = &term.args[0];
        if sequence.is_app("TLA.tuple") {
            let length = make_natural(exprs, sequence.args.len());
            let replaced = fill(&length);
            return Ok(make(
                Rule::new(
                    RuleName::TupleLen,
                    vec![
                        fill(term),
                        replaced.clone(),
                        lambda.clone(),
                        term.clone(),
                        length,
                    ],
                ),
                vec![],
                vec![vec![replaced]],
            ));
        }
        return make_hole_rewrites("TLA.Len", &["TLA.tuple"], sequence, None);
    }
    if term.is_app_with_arity("TLA.isASeq", 1) {
        return make_hole_rewrites("TLA.isASeq", &["TLA.tuple"], &term.args[0], None);
    }
    if term.is_app_with_arity("TLA.in", 2) {
        let set = &term.args[1];
        return make_hole_rewrites(
            "TLA.in",
            if set.kind == Kind::Var {
                &[]
            } else {
                SET_HEADS
            },
            set,
            Some(&term.args[0]),
        );
    }
    if term.is_app_with_arity("TLA.isAFcn", 1) {
        return make_hole_rewrites(
            "TLA.isAFcn",
            &[
                "TLA.Fcn",
                "TLA.except",
                "TLA.oneArg",
                "TLA.extend",
                "TLA.record",
            ],
            &term.args[0],
            None,
        );
    }
    Ok(vec![])
}

fn has_existential(exprs: &Expressions, index: &Index, choice: &Expr) -> bool {
    let body = &choice.args[1];
    if body.kind == Kind::Not {
        return index.is_member(&exprs.eex(&choice.args[0], &choice.symbol, body))
            || index.is_member(&exprs.enot(&exprs.eall(
                &choice.args[0],
                &choice.symbol,
                &body.args[0],
            )));
    }
    index.is_member(&exprs.eex(&choice.args[0], &choice.symbol, body))
}

/// Zenon's find_rewrites: the rewrites of the outermost subterm that has some, looking through
/// applications and negations.
fn find_rewrites(
    context: TlaContext,
    is_in_term: bool,
    hole: &Expr,
    frame: &Expr,
    term: &Expr,
    make: &MakeRewrite,
) -> Result<Vec<Item>, ZenonError> {
    let exprs = context.exprs;
    let local = get_rewrites(context, is_in_term, hole, frame, term, make)?;
    if !local.is_empty() {
        return Ok(local);
    }
    if term.is_app_with_arity("$notequiv", 2) {
        return Ok(vec![]);
    }
    if term.kind == Kind::App {
        for position in 0..term.args.len() {
            let mut args = term.args.clone();
            args[position] = hole.clone();
            let inner = exprs.substitute(&[(hole.clone(), exprs.eapp(&term.symbol, &args))], frame);
            let found = find_rewrites(context, true, hole, &inner, &term.args[position], make)?;
            if !found.is_empty() {
                return Ok(found);
            }
        }
        return Ok(vec![]);
    }
    if term.kind == Kind::Not {
        return find_rewrites(
            context,
            false,
            hole,
            &exprs.substitute(&[(hole.clone(), exprs.enot(hole))], frame),
            &term.args[0],
            make,
        );
    }
    Ok(vec![])
}

pub fn get_rewrite_nodes(
    context: TlaContext,
    formula: &Expr,
    goalness: i64,
) -> Result<Vec<Item>, ZenonError> {
    let exprs = context.exprs;
    let make = |rule: Rule, added: Vec<Expr>, branches: Vec<Vec<Expr>>| {
        let is_cut = rule.name == RuleName::Cut;
        let is_stopping = rule.name == RuleName::Ifthenelse;
        let node = Item::Node(make_node(
            if is_cut {
                added
            } else {
                [vec![formula.clone()], added].concat()
            },
            rule,
            Priority::Arity,
            goalness,
            branches,
        ));
        if is_stopping {
            vec![node, Item::Stop]
        } else {
            vec![node]
        }
    };
    let hole = exprs.new_var();
    find_rewrites(context, false, &hole, &hole, formula, &make)
}

#[cfg(test)]
mod tests {
    use super::parse_integer;

    #[test]
    fn reads_numerals_as_the_typescript_does() {
        let cases = [
            ("12", Some(12.0)),
            ("1_0", Some(10.0)),
            ("-3", Some(-3.0)),
            ("+4", Some(4.0)),
            ("0x1F", Some(31.0)),
            ("0o17", Some(15.0)),
            ("0b101", Some(5.0)),
            ("0u12", Some(12.0)),
            ("-0u12", Some(-12.0)),
            ("0u_", Some(0.0)),
            ("007", Some(7.0)),
            ("x", None),
            ("0xg", None),
            ("", None),
        ];
        for (text, expected) in cases {
            assert_eq!(parse_integer(text), expected, "{text}");
        }
        for text in ["-0x1F", "-0u_", "0x_"] {
            assert!(parse_integer(text).is_some_and(f64::is_nan), "{text}");
        }
    }
}

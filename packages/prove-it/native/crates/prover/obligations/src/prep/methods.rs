//! Prep.find_meth and Prep.compute_meth: the methods the pragmas an obligation cites select, each a
//! prover with its time limit, or a frontend that rewrites the obligation first. A malformed method
//! throws a TlaProverError, since Prep.ship catches compute_meth's failure and fails only that
//! obligation. A port of `src/prover/prep/methods.ts`.

use crate::errors::{ObligationError, Result};
use crate::expression::{DefnCore, Expr, ExprCore, HypCore, Locus, Sequent, Visibility, to_index};
use crate::pragma::{OldMethod, PragmaSetting, PragmaValue};

/// A method, named after the Method.t constructor tlapm reports it by. A Z3 resource budget turns
/// the time limit off (`time_limit_ms` is infinite).
#[derive(Clone, Debug, PartialEq)]
pub struct Method {
    pub prover: String,
    pub time_limit_ms: f64,
    pub rlimit: Option<u64>,
    pub tactic: Option<String>,
}

/// What `findMethods` returns: the frontends to apply, in the order first cited, and the provers to
/// try in order.
#[derive(Clone, Debug, PartialEq)]
pub struct FoundMethods {
    pub frontends: Vec<String>,
    pub provers: Vec<Method>,
}

// The methods that rewrite an obligation in Prep.expand_enabled_cdot instead of proving it.
const FRONTENDS: [&str; 6] = [
    "expandenabled",
    "expandcdot",
    "autouse",
    "lambdify",
    "enabledaxioms",
    "levelcomparison",
];

// Method.default_*_timeout, in seconds.
const SMT_SECONDS: f64 = 5.0;
const ZENON_SECONDS: f64 = 10.0;
const ISABELLE_SECONDS: f64 = 30.0;
const LS4_SECONDS: f64 = 10.0;

// Method.rlimit_base and Method.max_rlimit.
const RLIMIT_BASE: f64 = 3_000_000.0;
const MAX_RLIMIT: f64 = 4_294_967_295.0;

fn is_frontend(prover: &str) -> bool {
    FRONTENDS.contains(&prover)
}

// Params.default_method: what tlapm tries when a step cites no prover.
fn get_default_methods() -> Vec<Method> {
    let method = |prover: &str, seconds: f64, tactic: Option<&str>| Method {
        prover: prover.to_owned(),
        time_limit_ms: seconds * 1000.0,
        rlimit: None,
        tactic: tactic.map(str::to_owned),
    };
    vec![
        method("smt", SMT_SECONDS, None),
        method("zenon", ZENON_SECONDS, None),
        method("isabelle", ISABELLE_SECONDS, Some("auto")),
    ]
}

struct KnownProver {
    prover: &'static str,
    seconds: f64,
    is_budgeted: bool,
}

// compute_meth's names for each prover, and the Method.t constructor and default time each
// selects. The SMT solvers take a resource budget.
fn get_known_prover(name: &str) -> Option<KnownProver> {
    let (prover, seconds, is_budgeted) = match name {
        "zenon" => ("zenon", ZENON_SECONDS, false),
        "isabelle" => ("isabelle", ISABELLE_SECONDS, false),
        "yices" => ("yices", 30.0, false),
        "ls4" => ("ls4", LS4_SECONDS, false),
        "z3" => ("z3", SMT_SECONDS, true),
        "smt" => ("smt", SMT_SECONDS, true),
        "cvc3" => ("cvc3", SMT_SECONDS, false),
        "cooper" => ("cooper", 0.0, false),
        "fail" => ("fail", 0.0, false),
        "smt2lib" => ("smt", SMT_SECONDS, true),
        "smt2z3" => ("z3", SMT_SECONDS, true),
        "smt3" => ("smt", SMT_SECONDS, true),
        "z33" => ("z3", SMT_SECONDS, true),
        "cvc33" => ("cvc3", SMT_SECONDS, false),
        "yices3" => ("yices", SMT_SECONDS, false),
        "verit" => ("verit", SMT_SECONDS, false),
        "zipper" => ("zipper", 30.0, false),
        "spass" => ("spass", SMT_SECONDS, false),
        "tptp" => ("tptp", SMT_SECONDS, false),
        "trivial" => ("trivial", 0.0, false),
        _ => (
            FRONTENDS.into_iter().find(|frontend| *frontend == name)?,
            0.0,
            false,
        ),
    };
    Some(KnownProver {
        prover,
        seconds,
        is_budgeted,
    })
}

fn get_prover_method(
    name: &str,
    timeout: Option<f64>,
    rlimit: Option<u64>,
    tactic: Option<&str>,
) -> Result<Method> {
    let Some(known) = get_known_prover(name) else {
        return Err(ObligationError::prover(format!("Unknown prover: {name}")));
    };
    if rlimit.is_some() && !known.is_budgeted {
        return Err(ObligationError::prover(
            "A Z3 rlimit budget (\"rN\") is only supported by the SMT and Z3 backends.",
        ));
    }
    Ok(Method {
        prover: known.prover.to_owned(),
        time_limit_ms: match rlimit {
            None => timeout.unwrap_or(known.seconds) * 1000.0,
            Some(_) => f64::INFINITY,
        },
        rlimit,
        tactic: (known.prover == "isabelle").then(|| tactic.unwrap_or("auto").to_owned()),
    })
}

/// A StrWhiteSpaceChar of ECMAScript, which `parseFloat` skips.
fn is_js_whitespace(character: char) -> bool {
    matches!(
        character,
        '\t' | '\n' | '\u{b}' | '\u{c}' | '\r' | ' ' | '\u{a0}' | '\u{1680}' | '\u{2000}'
            ..='\u{200a}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202f}'
                | '\u{205f}'
                | '\u{3000}'
                | '\u{feff}'
    )
}

/// `Number.parseFloat`: the longest decimal literal after leading white space, or NaN. Infinity
/// reads as NaN, which the one caller rejects just the same.
fn parse_js_float(text: &str) -> f64 {
    let trimmed = text.trim_start_matches(is_js_whitespace).as_bytes();
    let count_digits = |from: usize| {
        trimmed[from.min(trimmed.len())..]
            .iter()
            .take_while(|byte| byte.is_ascii_digit())
            .count()
    };
    let sign_length = usize::from(matches!(trimmed.first(), Some(b'+' | b'-')));
    let integer_digits = count_digits(sign_length);
    let mut end = sign_length + integer_digits;
    let fraction_digits = if trimmed.get(end) == Some(&b'.') {
        count_digits(end + 1)
    } else {
        0
    };
    if integer_digits == 0 && fraction_digits == 0 {
        return f64::NAN;
    }
    if trimmed.get(end) == Some(&b'.') {
        end += 1 + fraction_digits;
    }
    if matches!(trimmed.get(end), Some(b'e' | b'E')) {
        let exponent_sign_length = usize::from(matches!(trimmed.get(end + 1), Some(b'+' | b'-')));
        let exponent_digits = count_digits(end + 1 + exponent_sign_length);
        if exponent_digits > 0 {
            end += 1 + exponent_sign_length + exponent_digits;
        }
    }
    String::from_utf8_lossy(&trimmed[..end])
        .parse()
        .unwrap_or(f64::NAN)
}

// parse_rlimit: "rN" is N times the base resource count, at least 1.
fn get_rlimit(budget: &str) -> Result<u64> {
    let mut characters = budget.chars();
    let is_shaped = matches!(characters.next(), Some('r' | 'R'))
        && characters
            .next()
            .is_some_and(|character| !matches!(character, '\n' | '\r' | '\u{2028}' | '\u{2029}'));
    let count = if is_shaped {
        parse_js_float(&budget[1..])
    } else {
        f64::NAN
    };
    if !is_shaped || !count.is_finite() || count <= 0.0 {
        return Err(ObligationError::prover(format!(
            "Invalid SMT budget \"{budget}\""
        )));
    }
    // The product is at most MAX_RLIMIT, a whole number below 2^32.
    Ok((count * RLIMIT_BASE).min(MAX_RLIMIT).trunc().max(1.0) as u64)
}

#[derive(Default)]
struct MethodValues<'a> {
    prover: Option<&'a str>,
    timeout: Option<f64>,
    rlimit: Option<u64>,
    tactic: Option<&'a str>,
}

// compute_meth: a group of a pragma's settings, where each @ takes the next argument the pragma is
// applied to.
fn compute_method(settings: &[PragmaSetting], args: &[Expr]) -> Result<Method> {
    let mut values = MethodValues::default();
    let mut rest = args;
    for setting in settings {
        let value = &setting.value;
        let argument = match value {
            PragmaValue::Default => {
                let Some((argument, remaining)) = rest.split_first() else {
                    return Err(ObligationError::prover("Some arguments are missing"));
                };
                rest = remaining;
                Some(argument)
            }
            _ => None,
        };
        let text = match (value, argument.map(|argument| &argument.core)) {
            (PragmaValue::String(text), _) => Some(text.as_str()),
            (_, Some(ExprCore::String { value })) => Some(value.as_str()),
            _ => None,
        };
        match setting.hint.as_str() {
            "prover" | "tactic" => {
                let Some(text) = text else {
                    return Err(ObligationError::prover("This argument should be a string"));
                };
                if setting.hint == "prover" {
                    values.prover = Some(text);
                } else {
                    values.tactic = Some(text);
                }
            }
            "timeout" => {
                if let PragmaValue::Float(seconds) = value {
                    values.timeout = Some(*seconds);
                } else if let Some(text) = text {
                    values.rlimit = Some(get_rlimit(text)?);
                } else if let Some(ExprCore::Num { integer, fraction }) =
                    argument.map(|argument| &argument.core)
                {
                    // Number(`${integer}.${fraction}`).
                    values.timeout =
                        Some(format!("{integer}.{fraction}").parse().unwrap_or(f64::NAN));
                } else {
                    return Err(ObligationError::prover(
                        "This argument should be a number of seconds",
                    ));
                }
            }
            hint => {
                return Err(ObligationError::prover(format!(
                    "Unknown keyword in proof method definition: {hint}"
                )));
            }
        }
    }
    if !rest.is_empty() {
        return Err(ObligationError::prover("Too many arguments"));
    }
    let Some(prover) = values.prover else {
        return Err(ObligationError::prover("Missing prover name"));
    };
    get_prover_method(prover, values.timeout, values.rlimit, values.tactic)
}

// An old-style method, as Method_prs reads it, with its default time unless it names one.
fn get_old_method(method: &OldMethod) -> Result<Method> {
    get_prover_method(&method.name, method.timeout, None, method.tactic.as_deref())
}

enum Cited<'a> {
    Premeth(&'a [Vec<PragmaSetting>]),
    Meth(&'a OldMethod),
}

// find_meth: an obligation whose proof names a method keeps it. Otherwise each visible fact that
// cites a pragma, alone or applied to arguments, adds the methods its groups compute, and each that
// cites a theorem or carries an old-style method adds that method. A pragma that a fact from
// another BY or USE cites drops the methods found so far: tlapm compares the USE locations
// physically, as tla-ts compares the objects. Here they are compared by value: each BY or USE
// has its own place in the source.
fn get_cited_methods(sequent: &Sequent) -> Result<Vec<Method>> {
    let mut cited: Vec<Option<Cited>> = Vec::with_capacity(sequent.context.len());
    let mut methods = Vec::new();
    // `null` before any pragma is cited, which no fact's location equals.
    let mut use_location: Option<Option<&Locus>> = None;
    for (index, hyp) in sequent.context.iter().enumerate() {
        let fact = match &hyp.core {
            HypCore::Fact {
                expression,
                visibility: Visibility::Visible,
                use_location: fact_use_location,
                ..
            } => Some((expression, fact_use_location)),
            _ => None,
        };
        if let Some((expression, _)) = fact
            && let ExprCore::With { method, .. } = &expression.core
        {
            methods.push(get_old_method(method)?);
            cited.push(None);
            continue;
        }
        if let HypCore::Defn {
            definition,
            visibility,
            ..
        } = &hyp.core
        {
            match &definition.core {
                DefnCore::Bpragma {
                    methods: groups, ..
                } => {
                    cited.push(Some(Cited::Premeth(groups)));
                    continue;
                }
                DefnCore::Operator { body, .. } if *visibility == Visibility::Visible => {
                    cited.push(match &body.core {
                        ExprCore::With { method, .. } => Some(Cited::Meth(method)),
                        _ => None,
                    });
                    continue;
                }
                _ => {}
            }
        }
        cited.push(None);
        let Some((expression, hyp_use_location)) = fact else {
            continue;
        };
        let (operator, args) = match &expression.core {
            ExprCore::Apply { operator, args } => (operator, args.as_slice()),
            _ => (expression, [].as_slice()),
        };
        let ExprCore::Ix { index: offset } = operator.core else {
            continue;
        };
        let entry = usize::try_from(to_index(index) - offset)
            .ok()
            .and_then(|cited_index| cited.get(cited_index))
            .and_then(Option::as_ref);
        match entry {
            Some(Cited::Premeth(groups)) => {
                if use_location != Some(hyp_use_location.as_ref()) {
                    methods.clear();
                    use_location = Some(hyp_use_location.as_ref());
                }
                let computed = groups
                    .iter()
                    .map(|group| compute_method(group, args))
                    .collect::<Result<Vec<_>>>()?;
                methods.extend(computed);
            }
            Some(Cited::Meth(method)) => {
                // find_meth asserts that a theorem with a method is not applied to arguments.
                if matches!(expression.core, ExprCore::Apply { .. }) {
                    return Err(ObligationError::assert_failure());
                }
                methods.push(get_old_method(method)?);
            }
            None => {}
        }
    }
    Ok(methods)
}

/// The methods find_meth selects: the frontends to apply, and the provers to try in order, which
/// are tlapm's default ones when the obligation cites only frontends or nothing.
pub fn find_methods(sequent: &Sequent, method: Option<&OldMethod>) -> Result<FoundMethods> {
    let methods = match method {
        None => get_cited_methods(sequent)?,
        Some(method) => vec![get_old_method(method)?],
    };
    let mut frontends: Vec<String> = Vec::new();
    for method in &methods {
        if is_frontend(&method.prover) && !frontends.contains(&method.prover) {
            frontends.push(method.prover.clone());
        }
    }
    let provers: Vec<Method> = methods
        .into_iter()
        .filter(|method| !is_frontend(&method.prover))
        .collect();
    Ok(FoundMethods {
        frontends,
        provers: if provers.is_empty() {
            get_default_methods()
        } else {
            provers
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::{Builtin, Defn, Hyp, Time, WhereDefined, expr, hyp};
    use std::rc::Rc;

    fn ix(index: isize) -> Expr {
        expr(ExprCore::Ix { index })
    }

    fn apply(operator: Expr, args: Vec<Expr>) -> Expr {
        expr(ExprCore::Apply { operator, args })
    }

    fn string(value: &str) -> Expr {
        expr(ExprCore::String {
            value: value.to_owned(),
        })
    }

    fn num(integer: &str, fraction: &str) -> Expr {
        expr(ExprCore::Num {
            integer: integer.to_owned(),
            fraction: fraction.to_owned(),
        })
    }

    fn truth() -> Expr {
        expr(ExprCore::Internal {
            builtin: Builtin::TRUE,
        })
    }

    fn old(name: &str, tactic: Option<&str>, timeout: Option<f64>) -> OldMethod {
        OldMethod {
            name: name.to_owned(),
            tactic: tactic.map(str::to_owned),
            timeout,
        }
    }

    fn with(method: OldMethod) -> Expr {
        expr(ExprCore::With {
            expression: truth(),
            method,
        })
    }

    fn locus(line: u32) -> Option<Locus> {
        Some(Locus {
            file: Rc::from("M"),
            start_line: line,
            start_column: 1,
            end_line: line,
            end_column: 2,
        })
    }

    fn fact_with(expression: Expr, use_location: Option<Locus>, visibility: Visibility) -> Hyp {
        hyp(HypCore::Fact {
            expression,
            visibility,
            time: Time::Now,
            use_location,
        })
    }

    fn fact(expression: Expr, use_location: Option<Locus>) -> Hyp {
        fact_with(expression, use_location, Visibility::Visible)
    }

    fn definition(core: DefnCore, visibility: Visibility) -> Hyp {
        hyp(HypCore::Defn {
            definition: Defn {
                core,
                location: None,
            },
            where_defined: WhereDefined::User,
            visibility,
            is_local: false,
            is_constness_unset: false,
        })
    }

    fn pragma_with(groups: Vec<Vec<PragmaSetting>>, visibility: Visibility) -> Hyp {
        definition(
            DefnCore::Bpragma {
                name: "P".to_owned(),
                body: truth(),
                methods: groups,
            },
            visibility,
        )
    }

    fn pragma(groups: Vec<Vec<PragmaSetting>>) -> Hyp {
        pragma_with(groups, Visibility::Visible)
    }

    fn theorem(body: Expr) -> Hyp {
        definition(
            DefnCore::Operator {
                name: "T".to_owned(),
                body,
            },
            Visibility::Visible,
        )
    }

    fn set(hint: &str, value: PragmaValue) -> PragmaSetting {
        PragmaSetting {
            hint: hint.to_owned(),
            value,
        }
    }

    fn text(hint: &str, value: &str) -> PragmaSetting {
        set(hint, PragmaValue::String(value.to_owned()))
    }

    fn prover(name: &str) -> Vec<PragmaSetting> {
        vec![text("prover", name)]
    }

    fn smt_at() -> Vec<Vec<PragmaSetting>> {
        vec![vec![
            text("prover", "smt"),
            set("timeout", PragmaValue::Default),
        ]]
    }

    /// A JavaScript number as a template literal prints it.
    fn show_number(number: f64) -> String {
        if number.is_infinite() {
            "Infinity".to_owned()
        } else {
            format!("{number}")
        }
    }

    /// The scratch script's rendering of findMethods' result.
    fn show(context: Vec<Hyp>, method: Option<OldMethod>) -> String {
        let sequent = Sequent {
            context,
            active: truth(),
        };
        match find_methods(&sequent, method.as_ref()) {
            Ok(found) => format!(
                "frontends=[{}] provers=[{}]",
                found.frontends.join(","),
                found
                    .provers
                    .iter()
                    .map(|method| format!(
                        "{}:{}:{}:{}",
                        method.prover,
                        show_number(method.time_limit_ms),
                        method
                            .rlimit
                            .map_or("-".to_owned(), |rlimit| rlimit.to_string()),
                        method.tactic.as_deref().unwrap_or("-")
                    ))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Err(error) => format!("{}: {}", error.name(), error.message()),
        }
    }

    fn cite(groups: Vec<Vec<PragmaSetting>>, args: Vec<Expr>) -> String {
        show(
            vec![pragma(groups), fact(apply(ix(1), args), locus(1))],
            None,
        )
    }

    const DEFAULTS: &str =
        "frontends=[] provers=[smt:5000:-:-,zenon:10000:-:-,isabelle:30000:-:auto]";

    // The expected values below come from Bun, running the TypeScript.
    #[test]
    fn keeps_the_obligation_method() {
        assert_eq!(show(vec![], None), DEFAULTS);
        assert_eq!(
            show(vec![], Some(old("zenon", None, None))),
            "frontends=[] provers=[zenon:10000:-:-]"
        );
        assert_eq!(
            show(vec![], Some(old("isabelle", Some("blast"), Some(2.5)))),
            "frontends=[] provers=[isabelle:2500:-:blast]"
        );
        assert_eq!(
            show(vec![], Some(old("isabelle", None, None))),
            "frontends=[] provers=[isabelle:30000:-:auto]"
        );
        assert_eq!(
            show(vec![], Some(old("bogus", None, None))),
            "TlaProverError: Unknown prover: bogus"
        );
        assert_eq!(
            show(vec![], Some(old("expandenabled", None, None))),
            "frontends=[expandenabled] provers=[smt:5000:-:-,zenon:10000:-:-,isabelle:30000:-:auto]"
        );
        assert_eq!(
            show(
                vec![pragma(vec![prover("zenon")]), fact(ix(1), locus(1))],
                Some(old("smt3", None, None))
            ),
            "frontends=[] provers=[smt:5000:-:-]"
        );
    }

    #[test]
    fn reads_old_style_methods() {
        let smt = || with(old("smt", None, Some(3.0)));
        assert_eq!(
            show(vec![fact(smt(), None)], None),
            "frontends=[] provers=[smt:3000:-:-]"
        );
        assert_eq!(
            show(vec![fact_with(smt(), None, Visibility::Hidden)], None),
            DEFAULTS
        );
        let cvc3 = || theorem(with(old("cvc3", None, None)));
        assert_eq!(
            show(vec![cvc3(), fact(ix(1), locus(1))], None),
            "frontends=[] provers=[cvc3:5000:-:-]"
        );
        assert_eq!(
            show(
                vec![cvc3(), fact(apply(ix(1), vec![truth()]), locus(1))],
                None
            ),
            "TlaProofError: Oops, this seems to be a bug in TLAPM."
        );
    }

    #[test]
    fn computes_pragma_timeouts() {
        assert_eq!(
            cite(smt_at(), vec![num("7", "5")]),
            "frontends=[] provers=[smt:7500:-:-]"
        );
        assert_eq!(
            cite(smt_at(), vec![num("12", "")]),
            "frontends=[] provers=[smt:12000:-:-]"
        );
        assert_eq!(
            cite(
                vec![vec![
                    text("prover", "zenon"),
                    set("timeout", PragmaValue::Float(12.5))
                ]],
                vec![]
            ),
            "frontends=[] provers=[zenon:12500:-:-]"
        );
    }

    #[test]
    fn parses_budgets() {
        let cases = [
            ("r2", "frontends=[] provers=[smt:Infinity:6000000:-]"),
            ("R0.5", "frontends=[] provers=[smt:Infinity:1500000:-]"),
            ("r1e3", "frontends=[] provers=[smt:Infinity:3000000000:-]"),
            ("r 3", "frontends=[] provers=[smt:Infinity:9000000:-]"),
            ("rx", "TlaProverError: Invalid SMT budget \"rx\""),
            ("r", "TlaProverError: Invalid SMT budget \"r\""),
            ("r-1", "TlaProverError: Invalid SMT budget \"r-1\""),
            ("r1e10", "frontends=[] provers=[smt:Infinity:4294967295:-]"),
            ("r0.0000001", "frontends=[] provers=[smt:Infinity:1:-]"),
            ("r\n3", "TlaProverError: Invalid SMT budget \"r\n3\""),
            ("x2", "TlaProverError: Invalid SMT budget \"x2\""),
            ("r2.5e", "frontends=[] provers=[smt:Infinity:7500000:-]"),
            ("r+4", "frontends=[] provers=[smt:Infinity:12000000:-]"),
            ("r.5", "frontends=[] provers=[smt:Infinity:1500000:-]"),
            (
                "rInfinity",
                "TlaProverError: Invalid SMT budget \"rInfinity\"",
            ),
            ("r\u{a0}2", "frontends=[] provers=[smt:Infinity:6000000:-]"),
        ];
        for (budget, expected) in cases {
            assert_eq!(cite(smt_at(), vec![string(budget)]), expected, "{budget:?}");
        }
        assert_eq!(
            cite(
                vec![vec![text("prover", "zenon"), text("timeout", "r2")]],
                vec![]
            ),
            "TlaProverError: A Z3 rlimit budget (\"rN\") is only supported by the SMT and Z3 backends."
        );
    }

    #[test]
    fn rejects_malformed_pragmas() {
        assert_eq!(
            show(vec![pragma(smt_at()), fact(ix(1), locus(1))], None),
            "TlaProverError: Some arguments are missing"
        );
        assert_eq!(
            cite(vec![prover("smt")], vec![num("1", "")]),
            "TlaProverError: Too many arguments"
        );
        assert_eq!(
            cite(vec![vec![set("timeout", PragmaValue::Float(4.5))]], vec![]),
            "TlaProverError: Missing prover name"
        );
        assert_eq!(
            cite(
                vec![vec![text("prover", "smt"), text("speed", "fast")]],
                vec![]
            ),
            "TlaProverError: Unknown keyword in proof method definition: speed"
        );
        assert_eq!(
            cite(vec![vec![set("prover", PragmaValue::Float(1.5))]], vec![]),
            "TlaProverError: This argument should be a string"
        );
        assert_eq!(
            cite(
                vec![vec![
                    set("prover", PragmaValue::Default),
                    set("tactic", PragmaValue::Default)
                ]],
                vec![string("isabelle"), string("simp")]
            ),
            "frontends=[] provers=[isabelle:30000:-:simp]"
        );
        assert_eq!(
            cite(
                vec![vec![set("prover", PragmaValue::Default)]],
                vec![num("1", "")]
            ),
            "TlaProverError: This argument should be a string"
        );
        assert_eq!(
            cite(smt_at(), vec![truth()]),
            "TlaProverError: This argument should be a number of seconds"
        );
    }

    #[test]
    fn collects_frontends_once() {
        assert_eq!(
            cite(
                vec![
                    prover("autouse"),
                    prover("lambdify"),
                    prover("autouse"),
                    prover("zenon")
                ],
                vec![]
            ),
            "frontends=[autouse,lambdify] provers=[zenon:10000:-:-]"
        );
    }

    #[test]
    fn restarts_at_each_use() {
        let two_uses = |first: Option<Locus>, second: Option<Locus>| {
            show(
                vec![
                    pragma(vec![prover("zenon")]),
                    pragma(vec![prover("smt")]),
                    fact(ix(2), first),
                    fact(ix(2), second),
                ],
                None,
            )
        };
        assert_eq!(
            two_uses(locus(1), locus(1)),
            "frontends=[] provers=[zenon:10000:-:-,smt:5000:-:-]"
        );
        assert_eq!(
            two_uses(locus(1), locus(2)),
            "frontends=[] provers=[smt:5000:-:-]"
        );
        assert_eq!(
            two_uses(None, None),
            "frontends=[] provers=[zenon:10000:-:-,smt:5000:-:-]"
        );
        assert_eq!(
            show(
                vec![
                    pragma(vec![prover("zenon")]),
                    fact(with(old("ls4", None, None)), None),
                    fact(ix(2), locus(1))
                ],
                None
            ),
            "frontends=[] provers=[zenon:10000:-:-]"
        );
    }

    #[test]
    fn ignores_what_is_not_cited() {
        let zenon = || pragma(vec![prover("zenon")]);
        assert_eq!(show(vec![zenon(), fact(ix(5), locus(1))], None), DEFAULTS);
        assert_eq!(show(vec![zenon(), fact(ix(0), locus(1))], None), DEFAULTS);
        assert_eq!(
            show(
                vec![zenon(), fact_with(ix(1), locus(1), Visibility::Hidden)],
                None
            ),
            DEFAULTS
        );
        assert_eq!(
            show(
                vec![
                    pragma_with(vec![prover("zenon")], Visibility::Hidden),
                    fact(ix(1), locus(1))
                ],
                None
            ),
            "frontends=[] provers=[zenon:10000:-:-]"
        );
    }
}

//! Prep.find_meth and Prep.compute_meth: the methods the pragmas an obligation cites select, each a
//! prover with its time limit, or a frontend that rewrites the obligation first. A malformed method
//! is a located `ObligationError::Method`: tlapm warns where it is and Prep.ship catches
//! compute_meth's failure, leaving only that obligation untreated. A port of
//! `src/prover/prep/methods.ts`.

use crate::errors::{ObligationError, Result, quote_ocaml};
use crate::expression::{DefnCore, Expr, ExprCore, HypCore, Locus, Sequent, Visibility, to_index};
use crate::pragma::{OldMethod, PragmaSetting, PragmaSpan, PragmaValue};

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
    known: &KnownProver,
    timeout: Option<f64>,
    rlimit: Option<u64>,
    tactic: Option<&str>,
) -> Method {
    Method {
        prover: known.prover.to_owned(),
        time_limit_ms: match rlimit {
            None => timeout.unwrap_or(known.seconds) * 1000.0,
            Some(_) => f64::INFINITY,
        },
        rlimit,
        tactic: (known.prover == "isabelle").then(|| tactic.unwrap_or("auto").to_owned()),
    }
}

// Errors.err ~at: where compute_meth's error points, the setting's hint, the pragma's use or an
// argument, which Prep.ship then fails on.
fn method_error(message: impl Into<String>, at: Option<&Locus>) -> ObligationError {
    ObligationError::Method {
        message: message.into(),
        at: at.cloned(),
    }
}

/// A hint's locus in the pragma's file: the span's line and columns, each counted from 1, as the
/// loci of the file's expressions are.
fn get_span_locus(pragma: &Locus, span: PragmaSpan) -> Locus {
    let line = u32::try_from(span.line + 1).unwrap_or(u32::MAX);
    Locus {
        file: pragma.file.clone(),
        start_line: line,
        start_column: u32::try_from(span.start + 1).unwrap_or(u32::MAX),
        end_line: line,
        end_column: u32::try_from(span.end + 1).unwrap_or(u32::MAX),
    }
}

fn is_c_space(character: char) -> bool {
    matches!(character, '\t'..='\r' | ' ')
}

fn is_hex_digit(character: char) -> bool {
    character.is_ascii_hexdigit()
}

// caml_float_of_hex: `0x` digits, a point among them, and `p` with a binary exponent.
fn parse_hex_float(text: &str) -> Option<f64> {
    let (mantissa, exponent) = match text.find(['p', 'P']) {
        Some(at) => (&text[..at], Some(&text[at + 1..])),
        None => (text, None),
    };
    let (whole, fraction) = match mantissa.split_once('.') {
        Some((whole, fraction)) => (whole, fraction),
        None => (mantissa, ""),
    };
    if whole.is_empty() && fraction.is_empty()
        || !whole.chars().all(is_hex_digit)
        || !fraction.chars().all(is_hex_digit)
    {
        return None;
    }
    let exponent: i32 = match exponent {
        Some(exponent) => {
            let digits = exponent.trim_start_matches(is_c_space);
            let unsigned = digits.strip_prefix(['+', '-']).unwrap_or(digits);
            if unsigned.is_empty() || !unsigned.chars().all(|character| character.is_ascii_digit())
            {
                return None;
            }
            digits.parse().unwrap_or(if digits.starts_with('-') {
                i32::MIN
            } else {
                i32::MAX
            })
        }
        None => 0,
    };
    let value = whole
        .chars()
        .chain(fraction.chars())
        .fold(0.0, |value, digit| {
            value * 16.0 + f64::from(digit.to_digit(16).unwrap_or(0))
        });
    let scale = exponent.saturating_sub(i32::try_from(4 * fraction.len()).unwrap_or(i32::MAX));
    Some(ldexp(value, scale))
}

/// C's `ldexp`, which `caml_float_of_hex` scales the mantissa by: `value * 2^exponent`, rounded
/// to nearest, ties to even, once, where the result is subnormal.
fn ldexp(value: f64, exponent: i32) -> f64 {
    if value == 0.0 || !value.is_finite() {
        return value;
    }
    let bits = value.to_bits();
    let sign = bits & (1 << 63);
    let mut biased = i64::try_from((bits >> 52) & 0x7ff).expect("eleven bits");
    let mut mantissa = bits & ((1 << 52) - 1);
    if biased == 0 {
        let shift = i64::from(mantissa.leading_zeros()) - 11;
        mantissa = (mantissa << shift) & ((1 << 52) - 1);
        biased = 1 - shift;
    }
    let scaled = biased + i64::from(exponent);
    if scaled >= 0x7ff {
        return f64::from_bits(sign | (0x7ff << 52));
    }
    if scaled >= 1 {
        return f64::from_bits(sign | ((scaled as u64) << 52) | mantissa);
    }
    let shift = 1 - scaled;
    if shift > 54 {
        return f64::from_bits(sign);
    }
    let full = mantissa | (1 << 52);
    let remainder = full & ((1u64 << shift) - 1);
    let half = 1u64 << (shift - 1);
    let mut result = full >> shift;
    if remainder > half || (remainder == half && result & 1 == 1) {
        result += 1;
    }
    f64::from_bits(sign | result)
}

// A C99 decimal float: `\d+\.?\d*|\.\d+` with an optional `e[+-]?\d+`.
fn is_decimal_float(text: &str) -> bool {
    let (mantissa, exponent) = match text.find(['e', 'E']) {
        Some(at) => (&text[..at], Some(&text[at + 1..])),
        None => (text, None),
    };
    let (whole, fraction) = match mantissa.split_once('.') {
        Some((whole, fraction)) => (whole, Some(fraction)),
        None => (mantissa, None),
    };
    let is_digits = |text: &str| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit());
    let is_mantissa = match fraction {
        Some(fraction) => {
            is_digits(whole) && (fraction.is_empty() || is_digits(fraction))
                || whole.is_empty() && is_digits(fraction)
        }
        None => is_digits(whole),
    };
    is_mantissa
        && exponent
            .is_none_or(|exponent| is_digits(exponent.strip_prefix(['+', '-']).unwrap_or(exponent)))
}

/// OCaml's `float_of_string_opt`: `caml_float_of_string` drops every underscore, then reads the
/// whole text as C does, past leading white space: a hexadecimal float, `inf`, `infinity` or
/// `nan` in any case, or a decimal float.
pub fn parse_ocaml_float(text: &str) -> Option<f64> {
    let digits: String = text.chars().filter(|&character| character != '_').collect();
    let unsigned = digits.trim_start_matches(is_c_space);
    let (sign, unsigned) = match unsigned.strip_prefix('-') {
        Some(rest) => (-1.0, rest),
        None => (1.0, unsigned.strip_prefix('+').unwrap_or(unsigned)),
    };
    if let Some(hex) = unsigned
        .strip_prefix("0x")
        .or_else(|| unsigned.strip_prefix("0X"))
    {
        return parse_hex_float(hex).map(|value| sign * value);
    }
    let lower = unsigned.to_ascii_lowercase();
    if lower == "inf" || lower == "infinity" {
        return Some(sign * f64::INFINITY);
    }
    if lower == "nan"
        || lower
            .strip_prefix("nan(")
            .and_then(|rest| rest.strip_suffix(')'))
            .is_some_and(|inside| !inside.contains(')'))
    {
        return Some(f64::NAN);
    }
    is_decimal_float(unsigned).then(|| sign * unsigned.parse::<f64>().unwrap_or(f64::NAN))
}

// parse_rlimit: "rN" is N times the base resource count, at least 1, for a finite positive N
// `float_of_string_opt` reads.
fn get_rlimit(budget: &str, at: Option<&Locus>) -> Result<u64> {
    let count = budget
        .strip_prefix(['r', 'R'])
        .filter(|rest| !rest.is_empty())
        .and_then(parse_ocaml_float);
    let Some(count) = count.filter(|count| count.is_finite() && *count > 0.0) else {
        return Err(method_error(
            format!(
                "Invalid SMT budget {}: expected a number of seconds (wall-clock timeout), or a \
                 deterministic Z3 rlimit budget of the form \"rN\" (e.g. \"r5\").",
                quote_ocaml(budget)
            ),
            at,
        ));
    };
    // The product is at most MAX_RLIMIT, a whole number below 2^32.
    Ok((count * RLIMIT_BASE).min(MAX_RLIMIT).trunc().max(1.0) as u64)
}

// compute_meth: a group of a pragma's settings, read in order, where each @ takes the next
// argument the pragma is applied to at `use_locus`; `pragma` is where the definition carrying the
// pragma is, which names the file its hints are in.
fn compute_method(
    settings: &[PragmaSetting],
    args: &[Expr],
    use_locus: Option<&Locus>,
    pragma: Option<&Locus>,
) -> Result<Method> {
    let hint_locus =
        |setting: &PragmaSetting| pragma.map(|pragma| get_span_locus(pragma, setting.span));
    let mut prover: Option<(&str, Option<Locus>)> = None;
    let mut timeout = None;
    let mut rlimit = None;
    let mut tactic = None;
    let mut rest = args;
    // The next argument the pragma is applied to, for an @.
    fn take<'a>(rest: &mut &'a [Expr], use_locus: Option<&Locus>) -> Result<&'a Expr> {
        match rest.split_first() {
            Some((argument, remaining)) => {
                *rest = remaining;
                Ok(argument)
            }
            None => Err(method_error("Some arguments are missing", use_locus)),
        }
    }
    for setting in settings {
        let at_hint = hint_locus(setting);
        match setting.hint.as_str() {
            "prover" | "tactic" => {
                let is_prover = setting.hint == "prover";
                let (text, at) = match &setting.value {
                    PragmaValue::String(text) => (text.as_str(), at_hint),
                    PragmaValue::Default => {
                        let argument = take(&mut rest, use_locus)?;
                        match &argument.core {
                            ExprCore::String { value } => (value.as_str(), use_locus.cloned()),
                            _ => {
                                return Err(method_error(
                                    format!(
                                        "This argument should be a string ({})",
                                        if is_prover {
                                            "prover name"
                                        } else {
                                            "proof tactic"
                                        }
                                    ),
                                    argument.location.as_ref(),
                                ));
                            }
                        }
                    }
                    PragmaValue::Float(_) => {
                        return Err(method_error(
                            "Argument should be a string or @",
                            at_hint.as_ref(),
                        ));
                    }
                };
                if is_prover {
                    prover = Some((text, at));
                } else {
                    tactic = Some(text);
                }
            }
            "timeout" => match &setting.value {
                PragmaValue::Float(seconds) => timeout = Some(*seconds),
                PragmaValue::String(budget) => rlimit = Some(get_rlimit(budget, at_hint.as_ref())?),
                PragmaValue::Default => {
                    let argument = take(&mut rest, use_locus)?;
                    match &argument.core {
                        ExprCore::Num { integer, fraction } => {
                            // float_of_string (Printf.sprintf "%s.%s" s1 s2).
                            timeout = Some(
                                parse_ocaml_float(&format!("{integer}.{fraction}"))
                                    .unwrap_or(f64::NAN),
                            );
                        }
                        ExprCore::String { value } => {
                            rlimit = Some(get_rlimit(value, argument.location.as_ref())?);
                        }
                        _ => {
                            return Err(method_error(
                                "This argument should be a number of seconds (wall-clock \
                                 timeout), or a deterministic Z3 rlimit budget of the form \
                                 \"rN\" (e.g. \"r5\")",
                                argument.location.as_ref(),
                            ));
                        }
                    }
                }
            },
            keyword => {
                return Err(method_error(
                    format!("Unknown keyword in proof method definition: {keyword}"),
                    at_hint.as_ref(),
                ));
            }
        }
    }
    if !rest.is_empty() {
        return Err(method_error("Too many arguments", use_locus));
    }
    let Some((name, prover_locus)) = prover else {
        return Err(method_error(
            "Missing prover name",
            settings.first().and_then(hint_locus).as_ref(),
        ));
    };
    let Some(known) = get_known_prover(name) else {
        return Err(method_error(
            format!("Unknown prover: {name}"),
            prover_locus.as_ref(),
        ));
    };
    if rlimit.is_some() && !known.is_budgeted {
        return Err(method_error(
            "A Z3 rlimit budget (\"rN\") is only supported by the SMT and Z3 backends.",
            use_locus,
        ));
    }
    Ok(get_prover_method(&known, timeout, rlimit, tactic))
}

// An old-style method, as Method_prs reads it, with its default time unless it names one.
fn get_old_method(method: &OldMethod) -> Result<Method> {
    let Some(known) = get_known_prover(&method.name) else {
        return Err(ObligationError::prover(format!(
            "Unknown prover: {}",
            method.name
        )));
    };
    Ok(get_prover_method(
        &known,
        method.timeout,
        None,
        method.tactic.as_deref(),
    ))
}

enum Cited<'a> {
    Premeth(&'a [Vec<PragmaSetting>], Option<&'a Locus>),
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
                    cited.push(Some(Cited::Premeth(groups, definition.location.as_ref())));
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
            Some(Cited::Premeth(groups, pragma)) => {
                if use_location != Some(hyp_use_location.as_ref()) {
                    methods.clear();
                    use_location = Some(hyp_use_location.as_ref());
                }
                let computed = groups
                    .iter()
                    .map(|group| compute_method(group, args, expression.location.as_ref(), *pragma))
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
            span: PragmaSpan::default(),
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

    fn invalid(budget: &str) -> String {
        format!(
            "TlaMethodError: Invalid SMT budget {}: expected a number of seconds (wall-clock \
             timeout), or a deterministic Z3 rlimit budget of the form \"rN\" (e.g. \"r5\").",
            quote_ocaml(budget)
        )
    }

    // A budget is "r" and what OCaml's float_of_string_opt reads whole, C's way.
    #[test]
    fn parses_budgets() {
        let cases = [
            (
                "r2",
                "frontends=[] provers=[smt:Infinity:6000000:-]".to_owned(),
            ),
            (
                "R0.5",
                "frontends=[] provers=[smt:Infinity:1500000:-]".to_owned(),
            ),
            (
                "r1e3",
                "frontends=[] provers=[smt:Infinity:3000000000:-]".to_owned(),
            ),
            (
                "r 3",
                "frontends=[] provers=[smt:Infinity:9000000:-]".to_owned(),
            ),
            ("rx", invalid("rx")),
            ("r", invalid("r")),
            ("r-1", invalid("r-1")),
            (
                "r1e10",
                "frontends=[] provers=[smt:Infinity:4294967295:-]".to_owned(),
            ),
            (
                "r0.0000001",
                "frontends=[] provers=[smt:Infinity:1:-]".to_owned(),
            ),
            (
                "r\n3",
                "frontends=[] provers=[smt:Infinity:9000000:-]".to_owned(),
            ),
            ("x2", invalid("x2")),
            ("r2.5e", invalid("r2.5e")),
            (
                "r+4",
                "frontends=[] provers=[smt:Infinity:12000000:-]".to_owned(),
            ),
            (
                "r.5",
                "frontends=[] provers=[smt:Infinity:1500000:-]".to_owned(),
            ),
            ("rInfinity", invalid("rInfinity")),
            ("rnan", invalid("rnan")),
            ("r\u{a0}2", invalid("r\u{a0}2")),
            (
                "r1_0",
                "frontends=[] provers=[smt:Infinity:30000000:-]".to_owned(),
            ),
            (
                "r0x1p2",
                "frontends=[] provers=[smt:Infinity:12000000:-]".to_owned(),
            ),
            (
                "r0x.8",
                "frontends=[] provers=[smt:Infinity:1500000:-]".to_owned(),
            ),
            ("r0x", invalid("r0x")),
            ("r1\"", invalid("r1\"")),
        ];
        for (budget, expected) in cases {
            assert_eq!(cite(smt_at(), vec![string(budget)]), expected, "{budget:?}");
        }
        assert_eq!(
            cite(
                vec![vec![text("prover", "zenon"), text("timeout", "r2")]],
                vec![]
            ),
            "TlaMethodError: A Z3 rlimit budget (\"rN\") is only supported by the SMT and Z3 backends."
        );
    }

    #[test]
    fn reads_floats_as_ocaml_does() {
        for (text, expected) in [
            ("1.5", Some(1.5)),
            (" \t1.", Some(1.0)),
            (".5", Some(0.5)),
            ("1e3", Some(1000.0)),
            ("1E-2", Some(0.01)),
            ("1_000.5", Some(1000.5)),
            ("-2", Some(-2.0)),
            ("+2", Some(2.0)),
            ("0x10", Some(16.0)),
            ("0X1.8p1", Some(3.0)),
            ("-0x1p-1", Some(-0.5)),
            ("0x1P+2", Some(4.0)),
            ("0x1p-1024", Some(2f64.powi(-1022) / 4.0)),
            ("0x1p-1074", Some(f64::from_bits(1))),
            ("0x3p-1075", Some(f64::from_bits(2))),
            ("0x1p-1075", Some(0.0)),
            ("0x1.8p-1074", Some(f64::from_bits(2))),
            ("0x1p1024", Some(f64::INFINITY)),
            ("0x1.fffffffffffffp1023", Some(f64::MAX)),
            ("0x", None),
            ("0x.", None),
            ("0x1p", None),
            ("inf", Some(f64::INFINITY)),
            ("-Infinity", Some(f64::NEG_INFINITY)),
            ("1.5 ", None),
            ("1e", None),
            ("e1", None),
            ("", None),
            ("1.2.3", None),
            ("1.5x", None),
        ] {
            assert_eq!(parse_ocaml_float(text), expected, "{text:?}");
        }
        assert!(parse_ocaml_float("nan").is_some_and(f64::is_nan));
        assert!(parse_ocaml_float("NaN(abc)").is_some_and(f64::is_nan));
        assert_eq!(parse_ocaml_float("nan(a)b"), None);
    }

    #[test]
    fn rejects_malformed_pragmas() {
        assert_eq!(
            show(vec![pragma(smt_at()), fact(ix(1), locus(1))], None),
            "TlaMethodError: Some arguments are missing"
        );
        assert_eq!(
            cite(vec![prover("smt")], vec![num("1", "")]),
            "TlaMethodError: Too many arguments"
        );
        assert_eq!(
            cite(vec![vec![set("timeout", PragmaValue::Float(4.5))]], vec![]),
            "TlaMethodError: Missing prover name"
        );
        assert_eq!(
            cite(
                vec![vec![text("prover", "smt"), text("speed", "fast")]],
                vec![]
            ),
            "TlaMethodError: Unknown keyword in proof method definition: speed"
        );
        assert_eq!(
            cite(vec![vec![set("prover", PragmaValue::Float(1.5))]], vec![]),
            "TlaMethodError: Argument should be a string or @"
        );
        assert_eq!(
            cite(vec![vec![set("tactic", PragmaValue::Float(1.5))]], vec![]),
            "TlaMethodError: Argument should be a string or @"
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
            "TlaMethodError: This argument should be a string (prover name)"
        );
        assert_eq!(
            cite(
                vec![vec![
                    text("prover", "isabelle"),
                    set("tactic", PragmaValue::Default)
                ]],
                vec![num("1", "")]
            ),
            "TlaMethodError: This argument should be a string (proof tactic)"
        );
        assert_eq!(
            cite(smt_at(), vec![truth()]),
            "TlaMethodError: This argument should be a number of seconds (wall-clock timeout), or a deterministic Z3 rlimit budget of the form \"rN\" (e.g. \"r5\")"
        );
        assert_eq!(
            cite(vec![prover("foo")], vec![]),
            "TlaMethodError: Unknown prover: foo"
        );
    }

    fn at(line: u32, start_column: u32, end_column: u32) -> Option<Locus> {
        Some(Locus {
            file: Rc::from("M"),
            start_line: line,
            start_column,
            end_line: line,
            end_column,
        })
    }

    fn placed(expression: Expr, location: Option<Locus>) -> Expr {
        crate::expression::located(expression.core.clone(), location)
    }

    // Where each error points: the setting's hint (defpt), the use (usept), or the argument.
    #[test]
    fn places_its_errors() {
        let hint = |hint: &str, value: PragmaValue, start: usize, end: usize| PragmaSetting {
            hint: hint.to_owned(),
            value,
            span: PragmaSpan {
                line: 2,
                start,
                end,
            },
        };
        let defined = |groups: Vec<Vec<PragmaSetting>>| {
            hyp(HypCore::Defn {
                definition: Defn {
                    core: DefnCore::Bpragma {
                        name: "P".to_owned(),
                        body: truth(),
                        methods: groups,
                    },
                    location: at(3, 1, 40),
                },
                where_defined: WhereDefined::User,
                visibility: Visibility::Visible,
                is_local: false,
                is_constness_unset: false,
            })
        };
        let place = |groups: Vec<Vec<PragmaSetting>>, args: Vec<Expr>| {
            let citing = placed(apply(ix(1), args), at(9, 6, 10));
            let sequent = Sequent {
                context: vec![defined(groups), fact(citing, locus(9))],
                active: truth(),
            };
            match find_methods(&sequent, None) {
                Err(ObligationError::Method { message, at }) => (message, at),
                other => panic!("{other:?}"),
            }
        };
        let foo = |value: PragmaValue| hint("prover", value, 21, 27);
        assert_eq!(
            place(
                vec![vec![foo(PragmaValue::String("foo".to_owned()))]],
                vec![]
            ),
            ("Unknown prover: foo".to_owned(), at(3, 22, 28))
        );
        assert_eq!(
            place(vec![vec![foo(PragmaValue::Default)]], vec![string("foo")]),
            ("Unknown prover: foo".to_owned(), at(9, 6, 10))
        );
        assert_eq!(
            place(vec![vec![foo(PragmaValue::Default)]], vec![]),
            ("Some arguments are missing".to_owned(), at(9, 6, 10))
        );
        assert_eq!(
            place(
                vec![vec![foo(PragmaValue::Default)]],
                vec![placed(num("1", ""), at(9, 13, 14))]
            ),
            (
                "This argument should be a string (prover name)".to_owned(),
                at(9, 13, 14)
            )
        );
        assert_eq!(
            place(
                vec![vec![hint("timeout", PragmaValue::Float(3.0), 21, 28)]],
                vec![]
            ),
            ("Missing prover name".to_owned(), at(3, 22, 29))
        );
        assert_eq!(
            place(
                vec![vec![
                    hint("prover", PragmaValue::String("smt".to_owned()), 21, 27),
                    hint("timeout", PragmaValue::Default, 34, 41)
                ]],
                vec![placed(string("r0"), at(9, 13, 14))]
            ),
            (
                invalid("r0")
                    .trim_start_matches("TlaMethodError: ")
                    .to_owned(),
                at(9, 13, 14)
            )
        );
        assert_eq!(
            place(
                vec![vec![
                    hint("prover", PragmaValue::String("zenon".to_owned()), 21, 27),
                    hint("timeout", PragmaValue::String("r2".to_owned()), 34, 41)
                ]],
                vec![]
            ),
            (
                "A Z3 rlimit budget (\"rN\") is only supported by the SMT and Z3 backends."
                    .to_owned(),
                at(9, 6, 10)
            )
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

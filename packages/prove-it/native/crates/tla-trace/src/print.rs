//! TLC's text of a value, `Value.toString`, as `formatValue` in `values.ts` writes it over the
//! evaluator's values: a record in the order written until TLC sorts it, an interval as `1..3`,
//! and a lazy set expanded where TLC enumerates it to print it.

use tla_values::print::{get_field_name, is_field_name, java_text};

use crate::sets::cardinality;
use crate::value::{Class, Function, Lazy, Value, normalize};

/// The most functions TLC expands a set of functions, records or tuples into to print it.
const MAXIMUM_EXPANDED_PRODUCT: usize = 1999;
/// The largest base whose SUBSET TLC expands to print it.
const MAXIMUM_EXPANDED_SUBSET_BASE: usize = 6;

/// A value's text as TLC's Java string holds it, in UTF-16, a lone surrogate kept.
#[derive(Default)]
struct Units(Vec<u16>);

impl Units {
    fn push_str(&mut self, text: &str) {
        self.0.extend(text.encode_utf16());
    }

    fn push(&mut self, character: char) {
        let mut buffer = [0; 2];
        self.0
            .extend_from_slice(character.encode_utf16(&mut buffer));
    }
}

/// A value's text, pretty printed as TLC's messages print it.
pub fn format_pretty(value: &Value) -> String {
    crate::pretty::pretty_print(&format_units(value))
}

/// TLC's text of a value in a state (`formatValue(value)`), as its output writes it: a lone
/// surrogate as `?` ([`java_text`]).
pub fn format_value(value: &Value) -> String {
    java_text(&format_units(value))
}

/// TLC's text of a value in a state as its Java string holds it, which ToString makes a string
/// of: a lone surrogate stays one.
pub fn format_units(value: &Value) -> Vec<u16> {
    let mut out = Units::default();
    crate::sets::unordered(|| write_value(value, false, false, &mut out));
    out.0
}

/// TLC's text of a value Print or PrintT prints (`formatValue(value, true, true)`): records
/// sorted, except in the range of a lambda, which TLC evaluates again to print.
pub fn format_printed(value: &Value) -> String {
    let mut out = Units::default();
    crate::sets::unordered(|| write_value(value, true, true, &mut out));
    java_text(&out.0)
}

fn write_text(units: &[u16], out: &mut Units) {
    out.0.extend_from_slice(units);
}

fn write_string(units: &[u16], out: &mut Units) {
    out.push('"');
    for &unit in units {
        match u8::try_from(unit) {
            Ok(b'"') => out.push_str("\\\""),
            Ok(b'\\') => out.push_str("\\\\"),
            Ok(b'\t') => out.push_str("\\t"),
            Ok(b'\n') => out.push_str("\\n"),
            Ok(0x0c) => out.push_str("\\f"),
            Ok(b'\r') => out.push_str("\\r"),
            _ => out.0.push(unit),
        }
    }
    out.push('"');
}

fn write_joined(
    values: &[Value],
    open: &str,
    close: &str,
    is_strict: bool,
    is_normalized: bool,
    out: &mut Units,
) {
    out.push_str(open);
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        write_value(value, is_strict, is_normalized, out);
    }
    out.push_str(close);
}

thread_local! {
    static UNSORTED_PRINTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static NULL_PRINTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static UNEXPANDED_PRINTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// How many times the evaluator wrote the operation of a lazy set whose `toString` throws as it
/// fails to expand the set: a `UnionValue`, which catches nothing, or a `SubsetValue` of a base
/// under 7 elements, which expands outside its catch. TLC prints neither so but under `-terse`.
pub(crate) fn unexpanded_prints() -> usize {
    UNEXPANDED_PRINTS.with(|prints| prints.get())
}

/// How many times the evaluator wrote the text of a value TLC never initialized, a THEOREM's or
/// an ASSUME's of an INSTANCE: TLC's `toString` of a value holding it throws a
/// NullPointerException, whose text depends on the class that holds it, where the evaluator
/// writes `null`.
pub(crate) fn null_prints() -> usize {
    NULL_PRINTS.with(|prints| prints.get())
}

/// How many times the evaluator wrote the text of a set TLC can't normalize since the count was
/// last cleared: TLC normalizes a `SetEnumValue` to print it (`SetEnumValue.toString`), which
/// fails comparing its elements, where the evaluator writes it as built.
pub(crate) fn unsorted_prints() -> usize {
    UNSORTED_PRINTS.with(|prints| prints.get())
}

/// Clears the count of `unsorted_prints`.
pub(crate) fn clear_unsorted_prints() {
    UNSORTED_PRINTS.with(|prints| prints.set(0));
}

fn write_value(value: &Value, is_strict: bool, is_normalized: bool, out: &mut Units) {
    if matches!(value, Value::Unsorted(_)) {
        UNSORTED_PRINTS.with(|prints| prints.set(prints.get() + 1));
    }
    if matches!(value, Value::Null) {
        NULL_PRINTS.with(|prints| prints.set(prints.get() + 1));
    }
    match value {
        Value::Null => out.push_str("null"),
        Value::Bool(boolean) => out.push_str(if *boolean { "TRUE" } else { "FALSE" }),
        Value::Int(int) => out.push_str(&int.to_string()),
        Value::Str(text) => write_string(&text.units, out),
        Value::Model(text) => write_text(&text.units, out),
        Value::Set(_) | Value::Unsorted(_) => {
            normalize(value);
            write_joined(
                value.set_items().expect("an enumeration"),
                "{",
                "}",
                is_strict,
                is_normalized,
                out,
            )
        }
        Value::Interval(low, high, _) => {
            if low <= high {
                out.push_str(&format!("{low}..{high}"));
            } else {
                out.push_str("{}");
            }
        }
        Value::Lazy(lazy) => write_lazy(lazy, is_strict, is_normalized, out),
        // `FcnLambdaValue.toString`, which can't build the function: its parameter and domain,
        // and where its body is written.
        Value::Lambda(lambda) => {
            let (before, after) = lambda.text();
            out.push_str(before);
            if lambda.is_domain_printed() {
                write_value(lambda.domain(), is_strict, false, out);
            }
            out.push_str(after);
        }
        Value::Function(function) => write_function(function, is_strict, is_normalized, out),
    }
}

// The set TLC expands a lazy one into to print it, if any (`getExpandedLazySet`).
fn expand(lazy: &Lazy) -> Option<Vec<Value>> {
    let size = match lazy {
        Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_) | Lazy::Any => {
            return None;
        }
        // TLC prints the set it enumerates, and the operation where it can't (`toString` with
        // `TLCGlobals.expand`, swallowing the failure).
        Lazy::Cap(..) | Lazy::Cup(..) | Lazy::Diff(..) | Lazy::Filter(..) => {
            return crate::sets::enumerate(lazy).ok();
        }
        Lazy::Union(_) => {
            let expanded = crate::sets::enumerate(lazy).ok();
            if expanded.is_none() {
                UNEXPANDED_PRINTS.with(|prints| prints.set(prints.get() + 1));
            }
            return expanded;
        }
        Lazy::Subset(base) => {
            if cardinality(base).ok()? > MAXIMUM_EXPANDED_SUBSET_BASE {
                return None;
            }
            let expanded = crate::sets::enumerate(lazy).ok();
            if expanded.is_none() {
                UNEXPANDED_PRINTS.with(|prints| prints.set(prints.get() + 1));
            }
            return expanded;
        }
        Lazy::FunctionSet(domain, range) => {
            let domain = cardinality(domain).ok()?;
            if domain == 0 {
                return Some(vec![Value::function(Vec::new(), Vec::new(), Class::Plain)]);
            }
            let range = cardinality(range).ok()?;
            u32::try_from(domain)
                .ok()
                .and_then(|domain| range.checked_pow(domain))
                .unwrap_or(usize::MAX)
        }
        Lazy::RecordSet(fields, _) => product_size(fields.iter().map(|(_, set)| set))?,
        Lazy::Product(factors) => product_size(factors.iter())?,
    };
    if size == 0 {
        return Some(Vec::new());
    }
    if size > MAXIMUM_EXPANDED_PRODUCT {
        return None;
    }
    // TLC expands a set of this size to print it, where the evaluator may fail to, as for a
    // function set over a domain of ANY (`[{Any} -> {1, 2}]`, which TLC prints as
    // `{(ANY :> 1), (ANY :> 2)}`): the text the evaluator falls back to isn't TLC's.
    let expanded = crate::sets::enumerate(lazy).ok();
    if expanded.is_none() {
        UNEXPANDED_PRINTS.with(|prints| prints.set(prints.get() + 1));
    }
    expanded
}

fn product_size<'a>(sets: impl Iterator<Item = &'a Value>) -> Option<usize> {
    let mut size: usize = 1;
    for set in sets {
        if size == 0 {
            return Some(0);
        }
        size = size.saturating_mul(cardinality(set).ok()?);
    }
    Some(size)
}

fn write_lazy(lazy: &Lazy, is_strict: bool, is_normalized: bool, out: &mut Units) {
    if let Some(expanded) = expand(lazy) {
        return write_joined(&expanded, "{", "}", is_strict, is_normalized, out);
    }
    let format = |value: &Value, out: &mut Units| write_value(value, is_strict, false, out);
    match lazy {
        Lazy::Nat => out.push_str("Nat"),
        Lazy::Any => out.push_str("ANY"),
        Lazy::Int => out.push_str("Int"),
        Lazy::Real => out.push_str("Real"),
        Lazy::Strings => out.push_str("STRING"),
        Lazy::Seq(base) => {
            out.push_str("Seq(");
            format(base, out);
            out.push(')');
        }
        Lazy::Subset(base) => {
            // A `ParenthesizedSubset` operand, whatever its text.
            let is_parenthesized = match base {
                Value::Interval(..) => true,
                Value::Lazy(lazy) => {
                    matches!(***lazy, Lazy::Cap(..) | Lazy::Cup(..) | Lazy::Diff(..))
                }
                _ => false,
            };
            if is_parenthesized {
                out.push_str("SUBSET (");
                format(base, out);
                out.push(')');
            } else {
                out.push_str("SUBSET ");
                format(base, out);
            }
        }
        Lazy::FunctionSet(domain, range) => {
            out.push('[');
            format(domain, out);
            out.push_str(" -> ");
            format(range, out);
            out.push(']');
        }
        Lazy::RecordSet(fields, written) => {
            out.push('[');
            for (index, &position) in written.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                let (name, set) = &fields[position as usize];
                write_text(&name.units, out);
                out.push_str(": ");
                format(set, out);
            }
            out.push(']');
        }
        Lazy::Product(factors) => {
            out.push('(');
            for (index, factor) in factors.iter().enumerate() {
                if index > 0 {
                    out.push_str(" \\X ");
                }
                format(factor, out);
            }
            out.push(')');
        }
        Lazy::Filter(base, predicate) => {
            let (before, after) = predicate.text();
            out.push_str(before);
            format(base, out);
            out.push_str(after);
        }
        Lazy::Union(sets) => {
            out.push_str("UNION(");
            format(sets, out);
            out.push(')');
        }
        Lazy::Cap(left, right) | Lazy::Cup(left, right) | Lazy::Diff(left, right) => {
            let operator = match lazy {
                Lazy::Cap(..) => " \\cap ",
                Lazy::Cup(..) => " \\cup ",
                _ => " \\ ",
            };
            // `toStringForCupCapDiff`: an `EnumerableValue` operand in parentheses.
            let operand = |value: &Value, out: &mut Units| {
                if crate::value::is_enumerable(value) {
                    out.push('(');
                    format(value, out);
                    out.push(')');
                } else {
                    format(value, out);
                }
            };
            operand(left, out);
            out.push_str(operator);
            operand(right, out);
        }
    }
}

fn write_function(function: &Function, is_strict: bool, is_normalized: bool, out: &mut Units) {
    // TLC normalizes a lambda's domain to print it, but evaluates its body afterward.
    let is_range_normalized = is_normalized && function.class.get() != Class::Lambda;
    let is_tuple = function
        .domain
        .iter()
        .enumerate()
        .all(|(index, key)| matches!(key, Value::Int(int) if *int == index as i32 + 1));
    if is_tuple {
        return write_joined(
            &function.range,
            "<<",
            ">>",
            is_strict,
            is_range_normalized,
            out,
        );
    }
    let is_record = function.class.get() == Class::Record
        || function
            .domain
            .iter()
            .all(|key| matches!(key, Value::Str(text) if is_field_name(&text.units)));
    let order = print_order(function, is_normalized || !is_record);
    let (open, arrow, separator, close) = if is_record {
        ("[", " |-> ", ", ", "]")
    } else {
        ("(", " :> ", " @@ ", ")")
    };
    out.push_str(open);
    for (index, &position) in order.iter().enumerate() {
        if index > 0 {
            out.push_str(separator);
        }
        let key = &function.domain[position];
        match key {
            Value::Str(text) if is_record => write_text(&text.units, out),
            _ => write_value(key, is_strict, is_normalized, out),
        }
        out.push_str(arrow);
        write_value(
            &function.range[position],
            is_strict,
            is_range_normalized,
            out,
        );
    }
    out.push_str(close);
}

/// The positions of a function's keys in the order TLC prints them: as written until TLC sorts the
/// function, unless `is_sorted`.
pub(crate) fn print_order(function: &Function, is_sorted: bool) -> Vec<usize> {
    match (&*function.written.borrow(), is_sorted) {
        // `written[i]` is where the i-th key written sits in the domain.
        (Some(written), false) => written.iter().map(|&position| position as usize).collect(),
        _ => (0..function.domain.len()).collect(),
    }
}

/// A text's units as a string.
pub(crate) fn text_string(units: &[u16]) -> String {
    java_text(units)
}

/// Whether TLC's text of a value turns on a string key whose letters Unicode's categories decide
/// (`get_field_name`), whether it prints the function holding it as a record.
pub fn holds_unknown_key(value: &Value) -> bool {
    match value {
        Value::Set(_) | Value::Unsorted(_) => value
            .set_items()
            .expect("an enumeration")
            .iter()
            .any(holds_unknown_key),
        Value::Function(function) => {
            function.domain.iter().any(|key| {
                matches!(key, Value::Str(text) if get_field_name(&text.units).is_none())
                    || holds_unknown_key(key)
            }) || function.range.iter().any(holds_unknown_key)
        }
        _ => false,
    }
}

/// Whether a value holds the string TLCGet("config") gives for TLC's install, which the
/// evaluator words "unknown" and TLC as where its jar is (`TLCGlobals.Version.installLocation`).
/// Whether a value holds a set of functions, of records or of tuples that TLC expands to print
/// into two elements or more, one of whose component sets holds ANY: TLC writes the expansion in
/// the order it builds it (`{(ANY :> 1), (ANY :> 2)}`), where the evaluator, normalizing it,
/// compares ANY with itself and fails.
pub fn holds_any_expansion(value: &Value) -> bool {
    let Value::Lazy(lazy) = value else {
        return held_values(value).iter().any(holds_any_expansion);
    };
    let components: Vec<&Value> = match &***lazy {
        Lazy::FunctionSet(domain, range) => vec![domain, range],
        Lazy::RecordSet(fields, _) => fields.iter().map(|(_, set)| set).collect(),
        Lazy::Product(factors) => factors.iter().collect(),
        _ => return held_values(value).iter().any(holds_any_expansion),
    };
    components
        .iter()
        .any(|component| holds_any_expansion(component))
        || components.iter().any(|component| holds_any(component))
            && !matches!(expansion_size(lazy), Some(0 | 1))
}

// Whether a value is or holds ANY.
fn holds_any(value: &Value) -> bool {
    matches!(value, Value::Lazy(lazy) if matches!(&***lazy, Lazy::Any))
        || held_values(value).iter().any(holds_any)
}

// The values a value holds: a set's elements, a function's keys and values, a lambda's domain
// and a lazy set's operands.
fn held_values(value: &Value) -> Vec<Value> {
    match value {
        Value::Set(_) | Value::Unsorted(_) => value.set_items().expect("an enumeration").to_vec(),
        Value::Function(function) => function
            .domain
            .iter()
            .chain(function.range.iter())
            .cloned()
            .collect(),
        Value::Lambda(lambda) => vec![lambda.domain().clone()],
        Value::Lazy(lazy) => match &***lazy {
            Lazy::Subset(base) | Lazy::Seq(base) | Lazy::Union(base) | Lazy::Filter(base, _) => {
                vec![base.clone()]
            }
            Lazy::FunctionSet(left, right)
            | Lazy::Cap(left, right)
            | Lazy::Cup(left, right)
            | Lazy::Diff(left, right) => vec![left.clone(), right.clone()],
            Lazy::RecordSet(fields, _) => fields.iter().map(|(_, set)| set.clone()).collect(),
            Lazy::Product(factors) => factors.clone(),
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => Vec::new(),
        },
        _ => Vec::new(),
    }
}

// How many elements a set of functions, of records or of tuples has, where it is known.
fn expansion_size(lazy: &Lazy) -> Option<usize> {
    match lazy {
        Lazy::FunctionSet(domain, range) => {
            let domain = cardinality(domain).ok()?;
            if domain == 0 {
                return Some(1);
            }
            let range = cardinality(range).ok()?;
            u32::try_from(domain)
                .ok()
                .and_then(|domain| range.checked_pow(domain))
        }
        Lazy::RecordSet(fields, _) => product_size(fields.iter().map(|(_, set)| set)),
        Lazy::Product(factors) => product_size(factors.iter()),
        _ => None,
    }
}

pub fn holds_install(value: &Value) -> bool {
    match value {
        Value::Str(text) => *text.units == *"unknown".encode_utf16().collect::<Vec<_>>(),
        Value::Set(_) | Value::Unsorted(_) => value
            .set_items()
            .expect("an enumeration")
            .iter()
            .any(holds_install),
        Value::Function(function) => {
            function.domain.iter().any(holds_install) || function.range.iter().any(holds_install)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;
    use crate::value::{Text, set_of, settle, settle_deep, settle_normalized};

    fn text(name: &str, rank: i32) -> Rc<Text> {
        Rc::new(Text {
            units: name.encode_utf16().collect(),
            rank,
        })
    }

    fn string(name: &str, rank: i32) -> Value {
        Value::Str(text(name, rank))
    }

    #[test]
    fn prints_a_record_as_written_until_tlc_sorts_it() {
        // `b` was interned before `a`, so TLC sorts the record [a |-> 1, b |-> 2] as b, a.
        let record = Value::record(vec![
            (text("a", 1), Value::Int(1)),
            (text("b", 0), Value::Int(2)),
        ])
        .expect("a record");
        assert_eq!(format_value(&record), "[a |-> 1, b |-> 2]");
        assert_eq!(format_printed(&record), "[b |-> 2, a |-> 1]");
        settle(&record);
        assert_eq!(format_value(&record), "[b |-> 2, a |-> 1]");
    }

    #[test]
    fn forgets_the_written_order_of_a_record_it_compares() {
        let record = || {
            Value::record(vec![
                (text("a", 1), Value::Int(1)),
                (text("b", 0), Value::Int(2)),
            ])
            .expect("a record")
        };
        let (left, right) = (record(), record());
        assert!(crate::value::equals(&left, &right).expect("records compare"));
        assert_eq!(format_value(&left), "[b |-> 2, a |-> 1]");
    }

    #[test]
    fn settles_the_values_a_lazy_set_enumerates_into() {
        let record = Value::record(vec![
            (text("a", 1), Value::Int(1)),
            (text("b", 0), Value::Int(1)),
        ])
        .expect("a record");
        let subset = Value::lazy(Lazy::Subset(set_of(vec![record]).expect("a set")));
        assert_eq!(format_value(&subset), "{{}, {[a |-> 1, b |-> 1]}}");
        settle(&subset);
        assert_eq!(format_value(&subset), "{{}, {[b |-> 1, a |-> 1]}}");
    }

    #[test]
    fn sorts_the_values_within_a_value_compared_with_itself() {
        let inner = Value::record(vec![
            (text("b", 1), Value::Int(1)),
            (text("a", 0), Value::Int(2)),
        ])
        .expect("a record");
        let outer = Value::record(vec![(text("a", 0), inner)]).expect("a record");
        assert_eq!(format_value(&outer), "[a |-> [b |-> 1, a |-> 2]]");
        assert!(crate::value::equals(&outer, &outer).expect("an equality"));
        assert_eq!(format_value(&outer), "[a |-> [a |-> 2, b |-> 1]]");
    }

    #[test]
    fn leaves_a_lambda_as_written_under_view_or_symmetry() {
        let lambda = || {
            let record = Value::record(vec![
                (text("a", 1), Value::Int(1)),
                (text("b", 0), Value::Int(1)),
            ])
            .expect("a record");
            Value::over_interval(1, vec![record], Class::Lambda)
        };
        let deep = lambda();
        settle_deep(&deep);
        assert_eq!(format_value(&deep), "<<[a |-> 1, b |-> 1]>>");
        let normalized = lambda();
        settle_normalized(&normalized);
        assert_eq!(format_value(&normalized), "<<[a |-> 1, b |-> 1]>>");
        let fingerprinted = lambda();
        settle(&fingerprinted);
        assert_eq!(format_value(&fingerprinted), "<<[b |-> 1, a |-> 1]>>");
    }

    #[test]
    fn enumerates_the_functions_from_the_empty_set_without_their_range() {
        let functions = Value::lazy(Lazy::FunctionSet(
            Value::empty_set(),
            Value::lazy(Lazy::Nat),
        ));
        let elements = crate::value::elements(&functions).expect("an enumerable set");
        assert_eq!(elements.len(), 1);
        assert_eq!(format_value(&elements[0]), "<<>>");
    }

    #[test]
    fn keeps_the_other_operand_of_a_union_with_an_empty_set() {
        let union = |left: &Value, right: &Value| {
            format_value(&crate::sets::union(left, right).expect("a union"))
        };
        assert_eq!(union(&Value::empty_set(), &Value::interval(0, 0)), "0..0");
        let subset = Value::lazy(Lazy::Subset(Value::interval(1, 7)));
        assert_eq!(union(&subset, &Value::empty_set()), "SUBSET (1..7)");
        assert_eq!(union(&Value::interval(1, 2), &Value::empty_set()), "{1, 2}");
    }

    #[test]
    fn prints_intervals_functions_and_tuples() {
        assert_eq!(format_value(&Value::interval(1, 3)), "1..3");
        assert_eq!(format_value(&Value::interval(2, 1)), "{}");
        let set = set_of(vec![Value::Int(3), Value::Int(1), Value::Int(2)]).expect("a set");
        assert_eq!(format_value(&set), "{1, 2, 3}");
        let function = Value::function(
            vec![Value::Int(0), Value::Int(1)],
            vec![string("white", -1), string("a\"b", -1)],
            Class::Plain,
        );
        assert_eq!(format_value(&function), r#"(0 :> "white" @@ 1 :> "a\"b")"#);
        let tuple = Value::tuple(vec![Value::Bool(true), Value::Int(-1)]);
        assert_eq!(format_value(&tuple), "<<TRUE, -1>>");
        assert_eq!(format_value(&Value::tuple(Vec::new())), "<<>>");
    }

    #[test]
    fn prints_a_lazy_set_expanded_where_tlc_enumerates_it() {
        let base = set_of(vec![Value::Int(1), Value::Int(2)]).expect("a set");
        let subset = Value::lazy(Lazy::Subset(base));
        assert_eq!(format_value(&subset), "{{}, {1}, {2}, {1, 2}}");
        let large = Value::lazy(Lazy::Subset(Value::interval(1, 7)));
        assert_eq!(format_value(&large), "SUBSET (1..7)");
        let functions = Value::lazy(Lazy::FunctionSet(
            Value::lazy(Lazy::Nat),
            Value::interval(0, 1),
        ));
        assert_eq!(format_value(&functions), "[Nat -> 0..1]");
        assert_eq!(
            format_value(&Value::lazy(Lazy::Seq(Value::interval(1, 2)))),
            "Seq(1..2)"
        );
    }
}

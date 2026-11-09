//! TLC's text of a value, `Value.toString`, as `formatValue` in `values.ts` writes it over the
//! evaluator's values: a record in the order written until TLC sorts it, an interval as `1..3`,
//! and a lazy set expanded where TLC enumerates it to print it.

use tla_values::print::is_field_name;

use crate::sets::cardinality;
use crate::value::{Class, Function, Lazy, Value};

/// The most functions TLC expands a set of functions, records or tuples into to print it.
const MAXIMUM_EXPANDED_PRODUCT: usize = 1999;
/// The largest base whose SUBSET TLC expands to print it.
const MAXIMUM_EXPANDED_SUBSET_BASE: usize = 6;

/// TLC's text of a value in a state (`formatValue(value)`).
pub fn format_value(value: &Value) -> String {
    let mut out = String::new();
    write_value(value, false, false, &mut out);
    out
}

/// TLC's text of a value Print or PrintT prints (`formatValue(value, true, true)`): records
/// sorted, except in the range of a lambda, which TLC evaluates again to print.
pub fn format_printed(value: &Value) -> String {
    let mut out = String::new();
    write_value(value, true, true, &mut out);
    out
}

fn write_text(units: &[u16], out: &mut String) {
    out.extend(char::decode_utf16(units.iter().copied()).map(|unit| unit.unwrap_or('\u{fffd}')));
}

fn write_string(units: &[u16], out: &mut String) {
    out.push('"');
    for item in char::decode_utf16(units.iter().copied()) {
        match item {
            Ok('"') => out.push_str("\\\""),
            Ok('\\') => out.push_str("\\\\"),
            Ok('\t') => out.push_str("\\t"),
            Ok('\n') => out.push_str("\\n"),
            Ok('\u{c}') => out.push_str("\\f"),
            Ok('\r') => out.push_str("\\r"),
            Ok(character) => out.push(character),
            Err(_) => out.push('\u{fffd}'),
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
    out: &mut String,
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

fn write_value(value: &Value, is_strict: bool, is_normalized: bool, out: &mut String) {
    match value {
        Value::Bool(boolean) => out.push_str(if *boolean { "TRUE" } else { "FALSE" }),
        Value::Int(int) => out.push_str(&int.to_string()),
        Value::Str(text) => write_string(&text.units, out),
        Value::Model(text) => write_text(&text.units, out),
        Value::Set(elements) => write_joined(elements, "{", "}", is_strict, is_normalized, out),
        Value::Interval(low, high) => {
            if low <= high {
                out.push_str(&format!("{low}..{high}"));
            } else {
                out.push_str("{}");
            }
        }
        Value::Lazy(lazy) => write_lazy(lazy, is_strict, is_normalized, out),
        Value::Function(function) => write_function(function, is_strict, is_normalized, out),
    }
}

// The set TLC expands a lazy one into to print it, if any (`getExpandedLazySet`).
fn expand(lazy: &Lazy) -> Option<Vec<Value>> {
    let size = match lazy {
        Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_) => return None,
        Lazy::Subset(base) => {
            return (cardinality(base).ok()? <= MAXIMUM_EXPANDED_SUBSET_BASE)
                .then(|| crate::sets::enumerate(lazy).ok())
                .flatten();
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
    (size <= MAXIMUM_EXPANDED_PRODUCT)
        .then(|| crate::sets::enumerate(lazy).ok())
        .flatten()
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

fn write_lazy(lazy: &Lazy, is_strict: bool, is_normalized: bool, out: &mut String) {
    if let Some(expanded) = expand(lazy) {
        return write_joined(&expanded, "{", "}", is_strict, is_normalized, out);
    }
    let format = |value: &Value, out: &mut String| write_value(value, is_strict, false, out);
    match lazy {
        Lazy::Nat => out.push_str("Nat"),
        Lazy::Int => out.push_str("Int"),
        Lazy::Real => out.push_str("Real"),
        Lazy::Strings => out.push_str("STRING"),
        Lazy::Seq(base) => {
            out.push_str("Seq(");
            format(base, out);
            out.push(')');
        }
        Lazy::Subset(base) => {
            if matches!(base, Value::Interval(..)) {
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
    }
}

fn write_function(function: &Function, is_strict: bool, is_normalized: bool, out: &mut String) {
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
    let written = function.written.borrow();
    let order: Vec<usize> = match (&*written, is_normalized || !is_record) {
        // `written[i]` is where the i-th key written sits in the domain.
        (Some(written), false) => written.iter().map(|&position| position as usize).collect(),
        _ => (0..function.domain.len()).collect(),
    };
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
        let subset = Value::Lazy(Rc::new(Lazy::Subset(set_of(vec![record]).expect("a set"))));
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
        let functions = Value::Lazy(Rc::new(Lazy::FunctionSet(
            Value::empty_set(),
            Value::Lazy(Rc::new(Lazy::Nat)),
        )));
        let elements = crate::value::elements(&functions).expect("an enumerable set");
        assert_eq!(elements.len(), 1);
        assert_eq!(format_value(&elements[0]), "<<>>");
    }

    #[test]
    fn keeps_the_other_operand_of_a_union_with_an_empty_set() {
        let union = |left: &Value, right: &Value| {
            format_value(&crate::sets::union(left, right).expect("a union"))
        };
        assert_eq!(union(&Value::empty_set(), &Value::Interval(0, 0)), "0..0");
        let subset = Value::Lazy(Rc::new(Lazy::Subset(Value::Interval(1, 7))));
        assert_eq!(union(&subset, &Value::empty_set()), "SUBSET (1..7)");
        assert_eq!(union(&Value::Interval(1, 2), &Value::empty_set()), "{1, 2}");
    }

    #[test]
    fn prints_intervals_functions_and_tuples() {
        assert_eq!(format_value(&Value::Interval(1, 3)), "1..3");
        assert_eq!(format_value(&Value::Interval(2, 1)), "{}");
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
        let subset = Value::Lazy(Rc::new(Lazy::Subset(base)));
        assert_eq!(format_value(&subset), "{{}, {1}, {2}, {1, 2}}");
        let large = Value::Lazy(Rc::new(Lazy::Subset(Value::Interval(1, 7))));
        assert_eq!(format_value(&large), "SUBSET (1..7)");
        let functions = Value::Lazy(Rc::new(Lazy::FunctionSet(
            Value::Lazy(Rc::new(Lazy::Nat)),
            Value::Interval(0, 1),
        )));
        assert_eq!(format_value(&functions), "[Nat -> 0..1]");
        assert_eq!(
            format_value(&Value::Lazy(Rc::new(Lazy::Seq(Value::Interval(1, 2))))),
            "Seq(1..2)"
        );
    }
}

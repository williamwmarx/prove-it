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
        write_value(&function.range[position], is_strict, is_range_normalized, out);
    }
    out.push_str(close);
}


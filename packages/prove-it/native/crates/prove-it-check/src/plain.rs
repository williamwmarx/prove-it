//! A value as plain data, the library's `PlainValue` (`src/check-result.ts`), written as JSON for
//! the host to parse: a boolean, an integer or a string as itself; a function over `1..n` as an
//! array; one whose keys are all strings, none starting with `@`, as an object; and, tagged, any
//! other function as `{"@function": [[key, value], ...]}`, a set TLC holds enumerated or as an
//! interval as `{"@set": [...]}`, a model value as `{"@model": name}`, and a set or function TLC
//! keeps lazy as `{"@lazy": text}`, with TLC's text of it as its `toString` writes it, which the
//! trace printer writes exactly as it writes the states. Keys and elements are in TLC's order. A
//! value holding a set TLC can't normalize, which TLC can't print, is `null`.

use std::fmt::Write;

use tla_trace::{Value, format_value};

/// A variable of a state TLC prints: its name, TLC's text of its value, and the value as plain
/// data, `null` where TLC prints `null` for a variable a successor leaves undefined or where the
/// data can't be TLC's.
#[derive(Clone)]
pub struct Variable {
    pub name: String,
    pub text: String,
    pub data: String,
}

pub fn to_plain(value: &Value) -> String {
    let mut out = String::new();
    write_plain(value, &mut out).map_or_else(|| "null".into(), |()| out)
}

fn write_plain(value: &Value, out: &mut String) -> Option<()> {
    match value {
        Value::Bool(value) => out.push_str(if *value { "true" } else { "false" }),
        Value::Int(value) => {
            let _ = write!(out, "{value}");
        }
        Value::Str(text) => write_string(&text.units, out),
        Value::Model(text) => {
            out.push_str("{\"@model\":");
            write_string(&text.units, out);
            out.push('}');
        }
        Value::Set(elements) => write_tagged("@set", elements.iter(), out)?,
        Value::Interval(low, high) => write_tagged(
            "@set",
            (*low..=*high).map(Value::Int).collect::<Vec<_>>().iter(),
            out,
        )?,
        Value::Function(function) => {
            let is_sequence = function
                .domain
                .iter()
                .enumerate()
                .all(|(position, key)| matches!(key, Value::Int(key) if i64::from(*key) == position as i64 + 1));
            let is_record = !function.domain.is_empty()
                && function.domain.iter().all(
                    |key| matches!(key, Value::Str(text) if text.units.first() != Some(&u16::from(b'@'))),
                );
            if is_sequence {
                write_array(function.range.iter(), out)?;
            } else if is_record {
                out.push('{');
                for (position, (key, value)) in
                    function.domain.iter().zip(&function.range).enumerate()
                {
                    if position > 0 {
                        out.push(',');
                    }
                    if let Value::Str(text) = key {
                        write_string(&text.units, out);
                    }
                    out.push(':');
                    write_plain(value, out)?;
                }
                out.push('}');
            } else {
                out.push_str("{\"@function\":[");
                for (position, (key, value)) in
                    function.domain.iter().zip(&function.range).enumerate()
                {
                    if position > 0 {
                        out.push(',');
                    }
                    out.push('[');
                    write_plain(key, out)?;
                    out.push(',');
                    write_plain(value, out)?;
                    out.push(']');
                }
                out.push_str("]}");
            }
        }
        Value::Unsorted(_) => return None,
        Value::Lazy(_) | Value::Lambda(_) => {
            out.push_str("{\"@lazy\":");
            write_string(&format_value(value).encode_utf16().collect::<Vec<_>>(), out);
            out.push('}');
        }
    }
    Some(())
}

fn write_array<'v>(values: impl Iterator<Item = &'v Value>, out: &mut String) -> Option<()> {
    out.push('[');
    for (position, value) in values.enumerate() {
        if position > 0 {
            out.push(',');
        }
        write_plain(value, out)?;
    }
    out.push(']');
    Some(())
}

fn write_tagged<'v>(
    tag: &str,
    values: impl Iterator<Item = &'v Value>,
    out: &mut String,
) -> Option<()> {
    let _ = write!(out, "{{\"{tag}\":");
    write_array(values, out)?;
    out.push('}');
    Some(())
}

// A JSON string of UTF-16 units, each unit outside printable ASCII escaped, so that a lone
// surrogate survives.
fn write_string(units: &[u16], out: &mut String) {
    out.push('"');
    for &unit in units {
        match char::from_u32(u32::from(unit)) {
            Some('"') => out.push_str("\\\""),
            Some('\\') => out.push_str("\\\\"),
            Some(character @ ' '..='~') => out.push(character),
            _ => {
                let _ = write!(out, "\\u{unit:04x}");
            }
        }
    }
    out.push('"');
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use tla_trace::{Class, Text, Value};

    use super::to_plain;

    fn text(name: &str) -> Rc<Text> {
        Rc::new(Text {
            units: name.encode_utf16().collect(),
            rank: -1,
        })
    }

    #[test]
    fn writes_values_as_plain_data() {
        let tuple = Value::tuple(vec![Value::Int(1), Value::Bool(true)]);
        assert_eq!(to_plain(&tuple), "[1,true]");
        assert_eq!(to_plain(&Value::tuple(Vec::new())), "[]");
        assert_eq!(
            to_plain(&Value::Set(Rc::new(vec![Value::Str(text("a\"\n\u{e9}"))]))),
            "{\"@set\":[\"a\\\"\\u000a\\u00e9\"]}"
        );
        assert_eq!(to_plain(&Value::Interval(2, 3)), "{\"@set\":[2,3]}");
        assert_eq!(to_plain(&Value::Model(text("m"))), "{\"@model\":\"m\"}");
        let record = Value::function(
            vec![Value::Str(text("a")), Value::Str(text("b"))],
            vec![Value::Int(1), Value::Int(2)],
            Class::Record,
        );
        assert_eq!(to_plain(&record), "{\"a\":1,\"b\":2}");
        let tagged = Value::function(
            vec![Value::Str(text("@set"))],
            vec![Value::Int(1)],
            Class::Plain,
        );
        assert_eq!(to_plain(&tagged), "{\"@function\":[[\"@set\",1]]}");
        let function = Value::function(vec![Value::Int(0)], vec![Value::Int(1)], Class::Plain);
        assert_eq!(to_plain(&function), "{\"@function\":[[0,1]]}");
        let unsorted = Value::Unsorted(Rc::new(vec![Value::Int(1), Value::Str(text("a"))]));
        assert_eq!(
            to_plain(&Value::tuple(vec![Value::Int(1), unsorted])),
            "null"
        );
    }
}

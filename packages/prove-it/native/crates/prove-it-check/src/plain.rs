//! A value as plain data, the library's `PlainValue` (`src/check-result.ts`), written as JSON for
//! the host to parse: a boolean, an integer or a string as itself; a function over `1..n` as an
//! array; one whose keys are all strings, none starting with `@`, as an object; and, tagged, any
//! other function as `{"@function": [[key, value], ...]}`, a set TLC holds enumerated or as an
//! interval as `{"@set": [...]}`, a model value as `{"@model": name}`, and a set or function TLC
//! keeps lazy as `{"@lazy": text}`, with TLC's text of it as its `toString` writes it, which the
//! trace printer writes exactly as it writes the states. Keys and elements are in TLC's order. A
//! value holding a set TLC can't normalize, which TLC can't print, is `null`, as is one past
//! `MAXIMUM_PLAIN_ELEMENTS`. Only the library's check asks for it (`Host::is_plain`).

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

/// The most elements, of sets, functions and sequences at any depth, that a variable's plain data
/// holds; past it the data is `null`, while the text stays TLC's. It is TLC's own bound on the
/// elements of a set it builds (`TLCGlobals.setBound`, 1000000 by default), so data the bound cuts
/// off is of a value TLC itself would refuse to enumerate, such as an interval it prints as `1..n`.
/// `MAXIMUM_PLAIN_ELEMENTS` in `src/check-result.ts` counts alike.
const MAXIMUM_PLAIN_ELEMENTS: u64 = 1_000_000;

pub fn to_plain(value: &Value) -> String {
    let mut writer = Writer {
        out: String::new(),
        remaining: MAXIMUM_PLAIN_ELEMENTS,
    };
    writer
        .write(value)
        .map_or_else(|| "null".into(), |()| writer.out)
}

/// Writes plain data, taking each element it writes from what remains of the bound.
struct Writer {
    out: String,
    remaining: u64,
}

impl Writer {
    // Takes `count` elements from what remains, if that many do.
    fn take(&mut self, count: u64) -> Option<()> {
        self.remaining = self.remaining.checked_sub(count)?;
        Some(())
    }

    fn write(&mut self, value: &Value) -> Option<()> {
        match value {
            Value::Bool(value) => self.out.push_str(if *value { "true" } else { "false" }),
            Value::Int(value) => {
                let _ = write!(self.out, "{value}");
            }
            Value::Str(text) => write_string(&text.units, &mut self.out),
            Value::Model(text) => {
                self.out.push_str("{\"@model\":");
                write_string(&text.units, &mut self.out);
                self.out.push('}');
            }
            Value::Set(elements) => {
                self.out.push_str("{\"@set\":");
                self.write_array(elements)?;
                self.out.push('}');
            }
            Value::Interval(low, high) => {
                self.take(u64::try_from(i64::from(*high) - i64::from(*low) + 1).unwrap_or(0))?;
                self.out.push_str("{\"@set\":[");
                for (position, element) in (*low..=*high).enumerate() {
                    if position > 0 {
                        self.out.push(',');
                    }
                    let _ = write!(self.out, "{element}");
                }
                self.out.push_str("]}");
            }
            Value::Function(function) => self.write_function(&function.domain, &function.range)?,
            Value::Unsorted(_) => return None,
            Value::Lazy(_) | Value::Lambda(_) => {
                self.out.push_str("{\"@lazy\":");
                write_string(
                    &format_value(value).encode_utf16().collect::<Vec<_>>(),
                    &mut self.out,
                );
                self.out.push('}');
            }
        }
        Some(())
    }

    // A function's keys and values each count as elements.
    fn write_function(&mut self, domain: &[Value], range: &[Value]) -> Option<()> {
        self.take(2 * domain.len() as u64)?;
        let is_sequence = domain.iter().enumerate().all(
            |(position, key)| matches!(key, Value::Int(key) if i64::from(*key) == position as i64 + 1),
        );
        let is_record = !domain.is_empty()
            && domain.iter().all(
                |key| matches!(key, Value::Str(text) if text.units.first() != Some(&u16::from(b'@'))),
            );
        if is_sequence {
            self.out.push('[');
            for (position, value) in range.iter().enumerate() {
                if position > 0 {
                    self.out.push(',');
                }
                self.write(value)?;
            }
            self.out.push(']');
        } else if is_record {
            self.out.push('{');
            for (position, (key, value)) in domain.iter().zip(range).enumerate() {
                if position > 0 {
                    self.out.push(',');
                }
                if let Value::Str(text) = key {
                    write_string(&text.units, &mut self.out);
                }
                self.out.push(':');
                self.write(value)?;
            }
            self.out.push('}');
        } else {
            self.out.push_str("{\"@function\":[");
            for (position, (key, value)) in domain.iter().zip(range).enumerate() {
                if position > 0 {
                    self.out.push(',');
                }
                self.out.push('[');
                self.write(key)?;
                self.out.push(',');
                self.write(value)?;
                self.out.push(']');
            }
            self.out.push_str("]}");
        }
        Some(())
    }

    fn write_array(&mut self, values: &[Value]) -> Option<()> {
        self.take(values.len() as u64)?;
        self.out.push('[');
        for (position, value) in values.iter().enumerate() {
            if position > 0 {
                self.out.push(',');
            }
            self.write(value)?;
        }
        self.out.push(']');
        Some(())
    }
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

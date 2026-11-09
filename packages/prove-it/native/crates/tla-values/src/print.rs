//! TLC's printer of values (`Value.toString`), as `formatValue` in `values.ts` writes it, for
//! ToString, Print and the traces: [`format_value`] writes a value the store holds, and
//! [`is_printable`] says whether that is TLC's text, since the store forgets how TLC built a
//! value, such as an interval or a record's written field order, which TLC prints.

use crate::store::{
    KIND_BOOL, KIND_FUNCTION, KIND_INT, KIND_MODEL, KIND_SET, KIND_STRING, KIND_TUPLE, TRUE,
    is_function_kind,
};
use crate::{Id, Store};

/// Whether TLC writes the value an id holds as [`format_value`] does: whether its text doesn't
/// depend on how TLC built it, which the store forgets. It is false for a value holding a set of
/// consecutive integers (an interval prints as `1..3`), a record of several fields (printed in
/// the order written until TLC normalizes it), a function whose one key is a string that isn't a
/// field name (a record or not), a set of 2^n sets past n = 6 (a SUBSET prints as written), or a
/// set of more than 1,999 functions (as does a set of functions, records or tuples).
pub fn is_printable(store: &Store, id: Id) -> bool {
    let kind = store.kind_of(id);
    if kind != KIND_SET && kind != KIND_TUPLE && kind != KIND_FUNCTION {
        return true;
    }
    let size = store.size_of(id);
    let part = |index: u32| {
        if kind == KIND_SET {
            Some(store.element_at(id, index))
        } else {
            store.peek_key(id, index)
        }
    };
    for index in 0..size {
        if kind == KIND_TUPLE {
            if !is_printable(store, store.get_range_value(id, index)) {
                return false;
            }
            continue;
        }
        let (Some(element), Some(first)) = (part(index), part(0)) else {
            return false;
        };
        if store.kind_of(element) != store.kind_of(first) || !is_printable(store, element) {
            return false;
        }
        if kind == KIND_FUNCTION {
            if store.kind_of(element) == KIND_STRING
                && (size > 1 || !is_field_name(store.text_of(element)))
            {
                return false;
            }
            if !is_printable(store, store.get_range_value(id, index)) {
                return false;
            }
        }
    }
    if kind != KIND_SET || size == 0 {
        return true;
    }
    // A set of consecutive integers may be an interval, a set of 2^n sets past n = 6 a SUBSET, and
    // a set of more than 1999 functions a set of functions, records or tuples, which TLC prints
    // as written (`expandLazySet`).
    let element_kind = store.kind_of(store.element_at(id, 0));
    match element_kind {
        KIND_INT => {
            i64::from(store.int_of(store.element_at(id, size - 1)))
                - i64::from(store.int_of(store.element_at(id, 0)))
                != i64::from(size) - 1
        }
        KIND_SET => size < 128 || !size.is_power_of_two(),
        _ => !is_function_kind(element_kind) || size <= 1999,
    }
}

/// TLC's text of a value (`Value.toStringUnchecked`, `formatValue(v, true)` in `values.ts`), as
/// ToString gives it: `TRUE`, `-3`, `"a\"b"`, a model value's name, `{1, 2}` in TLC's order,
/// `<<1, 2>>`, `[f |-> 1]` for a function whose keys are all field names, and `(1 :> 2 @@ 3 :> 4)`
/// for any other function. A string escapes `"`, `\\`, tab, newline, form feed and carriage
/// return, as `StringValue.PrintVersion` does. It is TLC's text where [`is_printable`] holds.
pub fn format_value(store: &Store, id: Id) -> String {
    let mut text = Vec::new();
    write_value(store, id, &mut text);
    String::from_utf16_lossy(&text)
}

/// [`format_value`] appended to UTF-16 text, the store's form of a string.
pub fn write_value(store: &Store, id: Id, out: &mut Vec<u16>) {
    let push = |out: &mut Vec<u16>, text: &str| out.extend(text.encode_utf16());
    let size = store.size_of(id);
    let join = |out: &mut Vec<u16>,
                open: &str,
                separator: &str,
                close: &str,
                part: &dyn Fn(&mut Vec<u16>, u32)| {
        push(out, open);
        for index in 0..size {
            if index > 0 {
                push(out, separator);
            }
            part(out, index);
        }
        push(out, close);
    };
    match store.kind_of(id) {
        KIND_BOOL => push(out, if id == TRUE { "TRUE" } else { "FALSE" }),
        KIND_INT => push(out, &store.int_of(id).to_string()),
        KIND_MODEL => out.extend_from_slice(store.text_of(id)),
        KIND_STRING => {
            out.push(u16::from(b'"'));
            for &unit in store.text_of(id) {
                let escaped = match u8::try_from(unit) {
                    Ok(b'"') => "\\\"",
                    Ok(b'\\') => "\\\\",
                    Ok(b'\t') => "\\t",
                    Ok(b'\n') => "\\n",
                    Ok(0x0c) => "\\f",
                    Ok(b'\r') => "\\r",
                    _ => {
                        out.push(unit);
                        continue;
                    }
                };
                push(out, escaped);
            }
            out.push(u16::from(b'"'));
        }
        KIND_SET => join(out, "{", ", ", "}", &|out, index| {
            write_value(store, store.element_at(id, index), out);
        }),
        KIND_TUPLE => join(out, "<<", ", ", ">>", &|out, index| {
            write_value(store, store.get_range_value(id, index), out);
        }),
        _ => {
            // A function's keys are interned; only a tuple's may not be.
            let keys: Vec<Id> = (0..size)
                .filter_map(|index| store.peek_key(id, index))
                .collect();
            let is_record = keys
                .iter()
                .all(|&key| store.kind_of(key) == KIND_STRING && is_field_name(store.text_of(key)));
            let (open, arrow, separator, close) = if is_record {
                ("[", " |-> ", ", ", "]")
            } else {
                ("(", " :> ", " @@ ", ")")
            };
            join(out, open, separator, close, &|out, index| {
                let key = keys[index as usize];
                if is_record {
                    out.extend_from_slice(store.text_of(key));
                } else {
                    write_value(store, key, out);
                }
                push(out, arrow);
                write_value(store, store.get_range_value(id, index), out);
            });
        }
    }
}

/// `isFieldName` of `values.ts` (`FcnRcdValue.isName`) on ASCII text: letters, digits and `_`,
/// with a letter, and not `WF_` or `SF_` past three characters. Text past ASCII, whose letters and
/// digits are Unicode's, isn't one here, so a value keyed by it isn't printable.
pub fn is_field_name(text: &[u16]) -> bool {
    if text.iter().any(|&unit| unit > 0x7f) {
        return false;
    }
    let is_word = |unit: u16| (unit as u8).is_ascii_alphanumeric() || unit == u16::from(b'_');
    text.iter().all(|&unit| is_word(unit))
        && text.iter().any(|&unit| (unit as u8).is_ascii_alphabetic())
        && (text.len() < 4
            || !(text.starts_with(&[u16::from(b'W'), u16::from(b'F'), u16::from(b'_')])
                || text.starts_with(&[u16::from(b'S'), u16::from(b'F'), u16::from(b'_')])))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::{EMPTY_SET, FALSE};

    fn text(store: &mut Store, text: &str) -> Id {
        store.str(&text.encode_utf16().collect::<Vec<u16>>())
    }

    fn new_store() -> Store {
        let mut store = Store::new();
        store.reset(std::iter::empty::<&[u16]>());
        store
    }

    // The texts are TLC's, as `formatValue` writes them.
    #[test]
    fn prints_values_as_tlc_does() {
        let mut store = new_store();
        let integers: Vec<Id> = [-3, 0, 2, 5]
            .iter()
            .map(|&value| store.int(value).expect("an integer"))
            .collect();
        let quoted = text(&mut store, "a\"\\\n\t\u{c}\ré");
        let (a, b, f1) = (
            text(&mut store, "a"),
            text(&mut store, "b"),
            text(&mut store, "f1"),
        );
        let model = store.model(&"m1".encode_utf16().collect::<Vec<u16>>());
        let gappy = store.set_of(&integers[1..]).expect("a set");
        let strings = store.set_of(&[b, a]).expect("a set");
        let tuple = store.tuple_of(&[TRUE, quoted, model]);
        let record = store.function_of(&[f1], &[tuple]).expect("a record");
        let function = store
            .function_of(&[integers[1], integers[2]], &[a, EMPTY_SET])
            .expect("a function");
        let empty = store.tuple_of(&[]);
        for (id, expected) in [
            (integers[0], "-3"),
            (FALSE, "FALSE"),
            (quoted, r#""a\"\\\n\t\f\ré""#),
            (model, "m1"),
            (gappy, "{0, 2, 5}"),
            (strings, r#"{"a", "b"}"#),
            (empty, "<<>>"),
            (EMPTY_SET, "{}"),
            (record, r#"[f1 |-> <<TRUE, "a\"\\\n\t\f\ré", m1>>]"#),
            (function, r#"(0 :> "a" @@ 2 :> {})"#),
        ] {
            assert!(is_printable(&store, id), "{expected}");
            assert_eq!(format_value(&store, id), expected);
        }
    }

    // TLC prints an interval, a SUBSET, a large set of functions and a record as it built them,
    // which the store forgets.
    #[test]
    fn knows_where_the_text_depends_on_how_tlc_built_the_value() {
        let mut store = new_store();
        let integers: Vec<Id> = (1..=3)
            .map(|value| store.int(value).expect("an integer"))
            .collect();
        let interval = store.set_of(&integers).expect("a set");
        let (a, b, spaced) = (
            text(&mut store, "a"),
            text(&mut store, "b"),
            text(&mut store, "a b"),
        );
        let record = store
            .function_of(&[a, b], &[TRUE, FALSE])
            .expect("a record");
        let spaced = store.function_of(&[spaced], &[TRUE]).expect("a record");
        let letters: Vec<Id> = (0..7)
            .map(|index| text(&mut store, &format!("l{index}")))
            .collect();
        let subsets: Vec<Id> = (0..128u32)
            .map(|mask| {
                let chosen: Vec<Id> = (0..7)
                    .filter(|bit| mask & (1 << bit) != 0)
                    .map(|bit| letters[bit])
                    .collect();
                store.set_of(&chosen).expect("a set")
            })
            .collect();
        let power_set = store.set_of(&subsets).expect("a set");
        let pairs: Vec<Id> = (0..2000)
            .map(|value| {
                let value = store.int(value).expect("an integer");
                store.tuple_of(&[value, value])
            })
            .collect();
        let functions = store.set_of(&pairs).expect("a set");
        let nested = store.tuple_of(&[interval]);
        for id in [interval, record, spaced, power_set, functions, nested] {
            assert!(!is_printable(&store, id), "{}", format_value(&store, id));
        }
    }

    #[test]
    fn knows_a_field_name() {
        let utf16 = |text: &str| text.encode_utf16().collect::<Vec<u16>>();
        for (name, expected) in [
            ("a", true),
            ("x_1", true),
            ("1a", true),
            ("12", false),
            ("a b", false),
            ("WF_x", false),
            ("SF_", true),
            ("é", false),
        ] {
            assert_eq!(is_field_name(&utf16(name)), expected, "{name}");
        }
    }
}

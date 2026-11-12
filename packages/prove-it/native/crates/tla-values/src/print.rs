//! TLC's printer of values (`Value.toString`), as `formatValue` in `values.ts` writes it, for
//! ToString, Print and the traces: [`format_value`] writes a value the store holds, and
//! [`is_printable`] says whether that is TLC's text, since the store forgets how TLC built a
//! value, such as an interval or a record's written field order, which TLC prints.

use crate::store::Outcome;
use crate::store::{
    KIND_BOOL, KIND_FUNCTION, KIND_INFINITE_SET, KIND_INT, KIND_MODEL, KIND_SET, KIND_STRING,
    KIND_TUPLE, TRUE, infinite_set_name, is_function_kind,
};
use crate::{Bail, Id, Store};

/// Whether TLC writes the value an id holds as [`format_value`] does: whether its text doesn't
/// depend on how TLC built it, which the store forgets. It is false for a value holding a set of
/// consecutive integers (an interval prints as `1..3`), a record of several fields (printed in
/// the order written until TLC normalizes it), a function whose one key is a string that isn't a
/// field name (a record or not), a set of 2^n sets past n = 6 (a SUBSET prints as written), or a
/// set of more than 1,999 functions (as does a set of functions, records or tuples).
pub fn is_printable(store: &Store, id: Id) -> bool {
    is_written_as_held(store, id, false)
}

/// [`is_printable`] for a value TLC has normalized, as it does each state it fingerprints, such
/// as a trace's: its records' fields are then sorted, so a record of several fields prints as
/// [`format_value`] writes it. The rest still depends on how TLC built the value.
pub fn is_printable_normalized(store: &Store, id: Id) -> bool {
    is_written_as_held(store, id, true)
}

fn is_written_as_held(store: &Store, id: Id, is_normalized: bool) -> bool {
    let kind = store.kind_of(id);
    match kind {
        KIND_BOOL | KIND_INT | KIND_STRING | KIND_MODEL | KIND_INFINITE_SET => return true,
        KIND_SET | KIND_TUPLE | KIND_FUNCTION => {}
        // TLC prints a function it keeps lazy as written.
        _ => return false,
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
            if !is_written_as_held(store, store.get_range_value(id, index), is_normalized) {
                return false;
            }
            continue;
        }
        let (Some(element), Some(first)) = (part(index), part(0)) else {
            return false;
        };
        if store.kind_of(element) != store.kind_of(first)
            || !is_written_as_held(store, element, is_normalized)
        {
            return false;
        }
        if kind == KIND_FUNCTION {
            if store.kind_of(element) == KIND_STRING
                && ((size > 1 && !is_normalized) || !is_field_name(store.text_of(element)))
            {
                return false;
            }
            if !is_written_as_held(store, store.get_range_value(id, index), is_normalized) {
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
pub fn format_value(store: &Store, id: Id) -> Outcome<String> {
    let mut text = Vec::new();
    write_value(store, id, &mut text)?;
    Ok(String::from_utf16_lossy(&text))
}

/// [`format_value`] appended to UTF-16 text, the store's form of a string. A function TLC keeps
/// lazy, which TLC prints as written, isn't [`is_printable`], and fails.
pub fn write_value(store: &Store, id: Id, out: &mut Vec<u16>) -> Outcome<()> {
    let push = |out: &mut Vec<u16>, text: &str| out.extend(text.encode_utf16());
    let size = store.size_of(id);
    let join = |out: &mut Vec<u16>,
                open: &str,
                separator: &str,
                close: &str,
                part: &dyn Fn(&mut Vec<u16>, u32) -> Outcome<()>| {
        push(out, open);
        for index in 0..size {
            if index > 0 {
                push(out, separator);
            }
            part(out, index)?;
        }
        push(out, close);
        Ok(())
    };
    match store.kind_of(id) {
        KIND_BOOL => push(out, if id == TRUE { "TRUE" } else { "FALSE" }),
        KIND_INT => push(out, &store.int_of(id).to_string()),
        KIND_MODEL => out.extend_from_slice(store.text_of(id)),
        KIND_INFINITE_SET => push(out, infinite_set_name(store.infinite_name_of(id))),
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
            write_value(store, store.element_at(id, index), out)
        })?,
        KIND_TUPLE => join(out, "<<", ", ", ">>", &|out, index| {
            write_value(store, store.get_range_value(id, index), out)
        })?,
        KIND_FUNCTION => {
            // A function's keys are interned; only a tuple's may not be.
            let keys: Vec<Id> = (0..size)
                .filter_map(|index| store.peek_key(id, index))
                .collect();
            let mut is_record = true;
            for &key in &keys {
                if store.kind_of(key) != KIND_STRING {
                    is_record = false;
                    continue;
                }
                match get_field_name(store.text_of(key)) {
                    Some(is_name) => is_record &= is_name,
                    None => return Err(Bail("a key whose letters Unicode's categories decide")),
                }
            }
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
                    write_value(store, key, out)?;
                }
                push(out, arrow);
                write_value(store, store.get_range_value(id, index), out)
            })?;
        }
        _ => {
            return Err(Bail(
                "unsupported: printing a function TLC keeps lazy, as TLC writes it",
            ));
        }
    }
    Ok(())
}

/// How TLC built a value an expression writes, where TLC's text of the value depends on it and
/// the store forgets it: the compiler knows it from the expression, and [`write_constructed`]
/// writes the value as TLC prints a value so built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Construction {
    /// Any value, whose text is TLC's where [`is_printable`] holds, or [`is_printable_normalized`]
    /// once TLC has normalized it.
    Held,
    /// `a..b` (`IntervalValue`), which prints as `1..3`, or `{}` where empty.
    Interval,
    /// `{e1, …, en}` (`SetEnumValue`) whose elements are built alike, with how many elements
    /// it writes where that may be more than it holds: TLC sorts the elements written, which
    /// compares, and so normalizes, a duplicate the set then drops.
    Set(Box<Construction>, Option<u32>),
    /// `<<e1, …, en>>`.
    Tuple(Vec<Construction>),
    /// `[f1 |-> e1, …]` (`RecordValue`): its fields in the order written, each with how its
    /// value is built.
    Record(Vec<(Vec<u16>, Construction)>),
    /// A function TLC builds as a `FcnRcdValue` over its keys in their sorted order, such as
    /// `[x \in S |-> e]` over a set enumeration or an interval, or `k :> v`: how its keys are
    /// built, and how its values are.
    Function(Box<Construction>, Box<Construction>),
    /// `[x \in S |-> e]` over a set TLC keeps lazy, such as `S \X T` or `SUBSET S`, which TLC
    /// keeps lazy too (`FcnLambdaValue`) and builds as it prints, from the body's values as they
    /// are, unnormalized: how its keys are built, and how its values are.
    LazyFunction(Box<Construction>, Box<Construction>),
    /// `SUBSET S` (`SubsetValue`) of a set enumeration or an interval.
    Subset(Box<Construction>),
    /// `[S -> T]` (`SetOfFcnsValue`) of set enumerations or intervals.
    FunctionSet(Box<Construction>, Box<Construction>),
}

impl Construction {
    /// How a set's elements are built, where the set is a set enumeration or an interval.
    pub fn of_elements(&self) -> Option<&Construction> {
        match self {
            Construction::Interval => Some(&Construction::Held),
            Construction::Set(element, _) => Some(element),
            _ => None,
        }
    }
}

/// TLC's text of a value built so, as [`write_value`] writes it, once TLC has normalized it
/// (`deepNormalize`, as Print and PrintT do) or not (as ToString doesn't): false, with part of the
/// text written, where it depends on more than how the value is built.
pub fn write_constructed(
    store: &Store,
    id: Id,
    construction: &Construction,
    is_normalized: bool,
    out: &mut Vec<u16>,
) -> bool {
    let normalized = if is_normalized {
        Normalized::Yes
    } else {
        Normalized::No
    };
    write_normalized(store, id, construction, normalized, out)
}

// Whether TLC has normalized a value: `Maybe` where it is part of an element of a set TLC sorted,
// whose comparisons normalize the records and functions they reach, and maybe not all of them.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Normalized {
    No,
    Maybe,
    Yes,
}

fn write_normalized(
    store: &Store,
    id: Id,
    construction: &Construction,
    normalized: Normalized,
    out: &mut Vec<u16>,
) -> bool {
    let push = |out: &mut Vec<u16>, text: &str| out.extend(text.encode_utf16());
    let kind = store.kind_of(id);
    let size = store.size_of(id);
    let join = |out: &mut Vec<u16>,
                (open, separator, close): (&str, &str, &str),
                part: &mut dyn FnMut(&mut Vec<u16>, u32) -> bool| {
        push(out, open);
        for index in 0..size {
            if index > 0 {
                push(out, separator);
            }
            if !part(out, index) {
                return false;
            }
        }
        push(out, close);
        true
    };
    let set = ("{", ", ", "}");
    let tuple = ("<<", ", ", ">>");
    let write = |out: &mut Vec<u16>, id: Id, construction: &Construction| {
        write_normalized(store, id, construction, normalized, out)
    };
    // The elements of a set of two or more written, which TLC sorted.
    let written = match construction {
        Construction::Set(_, Some(written)) => *written,
        _ => size,
    };
    let element_normalized = if normalized == Normalized::No && written > 1 {
        Normalized::Maybe
    } else {
        normalized
    };
    let write_element = |out: &mut Vec<u16>, id: Id, construction: &Construction| {
        write_normalized(store, id, construction, element_normalized, out)
    };
    match construction {
        Construction::Held => {
            is_written_as_held(store, id, normalized == Normalized::Yes)
                && write_value(store, id, out).is_ok()
        }
        Construction::Interval => {
            if kind != KIND_SET || (size > 0 && store.kind_of(store.element_at(id, 0)) != KIND_INT)
            {
                return false;
            }
            if size == 0 {
                push(out, "{}");
            } else {
                let bound = |index| store.int_of(store.element_at(id, index));
                push(out, &format!("{}..{}", bound(0), bound(size - 1)));
            }
            true
        }
        Construction::Set(element, _) => {
            kind == KIND_SET
                && join(out, set, &mut |out, index| {
                    write_element(out, store.element_at(id, index), element)
                })
        }
        Construction::Tuple(elements) => {
            kind == KIND_TUPLE
                && size as usize == elements.len()
                && join(out, tuple, &mut |out, index| {
                    write(
                        out,
                        store.get_range_value(id, index),
                        &elements[index as usize],
                    )
                })
        }
        Construction::Record(fields) => {
            if kind != KIND_FUNCTION || size as usize != fields.len() {
                return false;
            }
            // The position of each field written among the store's keys, which are in the order
            // TLC sorts a record's fields as it normalizes it.
            let mut positions = Vec::with_capacity(fields.len());
            for (name, _) in fields {
                let Some(position) = (0..size).find(|&index| {
                    store
                        .peek_key(id, index)
                        .is_some_and(|key| store.text_of(key) == name.as_slice())
                }) else {
                    return false;
                };
                positions.push(position);
            }
            // A record TLC may have compared, and so sorted, prints alike either way only where
            // its fields are written in their sorted order.
            if normalized == Normalized::Maybe && !positions.is_sorted() {
                return false;
            }
            join(out, ("[", ", ", "]"), &mut |out, index| {
                let field = if normalized == Normalized::Yes {
                    positions
                        .iter()
                        .position(|&position| position == index)
                        .expect("a field at each position")
                } else {
                    index as usize
                };
                let (name, construction) = &fields[field];
                out.extend_from_slice(name);
                push(out, " |-> ");
                write(
                    out,
                    store.get_range_value(id, positions[field]),
                    construction,
                )
            })
        }
        Construction::Function(key, value) | Construction::LazyFunction(key, value) => {
            // TLC doesn't normalize the values of a function it keeps lazy, so a value it may
            // have normalized otherwise prints only where both texts agree.
            let value_normalized = match construction {
                Construction::LazyFunction(..) if normalized == Normalized::Yes => {
                    Normalized::Maybe
                }
                _ => normalized,
            };
            let write = |out: &mut Vec<u16>, id: Id, construction: &Construction| {
                write_normalized(store, id, construction, value_normalized, out)
            };
            if kind == KIND_TUPLE {
                return join(out, tuple, &mut |out, index| {
                    write(out, store.get_range_value(id, index), value)
                });
            }
            if kind != KIND_FUNCTION {
                return false;
            }
            let keys: Vec<Id> = (0..size)
                .filter_map(|index| store.peek_key(id, index))
                .collect();
            let is_string = |key: Id| store.kind_of(key) == KIND_STRING;
            // `FcnRcdValue.isName` takes Unicode's letters and digits, which `get_field_name`
            // doesn't know past Latin-1.
            if keys
                .iter()
                .any(|&key| is_string(key) && get_field_name(store.text_of(key)).is_none())
            {
                return false;
            }
            let is_record = keys
                .iter()
                .all(|&key| is_string(key) && is_field_name(store.text_of(key)));
            let delimiters = if is_record {
                ("[", ", ", "]")
            } else {
                ("(", " @@ ", ")")
            };
            join(out, delimiters, &mut |out, index| {
                let key_id = keys[index as usize];
                if is_record {
                    out.extend_from_slice(store.text_of(key_id));
                    push(out, " |-> ");
                } else {
                    // The keys of a domain of two or more, which TLC sorted.
                    if !write_element(out, key_id, key) {
                        return false;
                    }
                    push(out, " :> ");
                }
                write(out, store.get_range_value(id, index), value)
            })
        }
        Construction::Subset(base) => {
            let Some(element) = base.of_elements() else {
                return false;
            };
            if kind != KIND_SET || !size.is_power_of_two() {
                return false;
            }
            // `SubsetValue.toString` enumerates a power set whose base has fewer than 7
            // elements, and otherwise writes it as SUBSET of its base, in parentheses for an
            // interval (`ParenthesizedSubset`).
            let base_size = size.trailing_zeros();
            if base_size < 7 {
                return join(out, set, &mut |out, index| {
                    write_element(
                        out,
                        store.element_at(id, index),
                        &Construction::Set(Box::new(element.clone()), None),
                    )
                });
            }
            let Some(base_set) = (0..size)
                .map(|index| store.element_at(id, index))
                .find(|&subset| store.size_of(subset) == base_size)
            else {
                return false;
            };
            let is_parenthesized = **base == Construction::Interval;
            push(
                out,
                if is_parenthesized {
                    "SUBSET ("
                } else {
                    "SUBSET "
                },
            );
            let is_written = write(out, base_set, base);
            if is_parenthesized {
                push(out, ")");
            }
            is_written
        }
        Construction::FunctionSet(domain, range) => {
            let (Some(key), Some(value)) = (domain.of_elements(), range.of_elements()) else {
                return false;
            };
            if kind != KIND_SET {
                return false;
            }
            // `SetOfFcnsValue.toString` enumerates a set of fewer than `TLCGlobals.enumBound`
            // (2000) functions, which counts |T|^|S| as the store's size does.
            if size < 2000 {
                let function =
                    Construction::Function(Box::new(key.clone()), Box::new(value.clone()));
                return join(out, set, &mut |out, index| {
                    write_element(out, store.element_at(id, index), &function)
                });
            }
            // Otherwise it writes `[S -> T]`, with S the keys of any of the functions and T, an
            // interval, the values they take.
            if **range != Construction::Interval {
                return false;
            }
            let first = store.element_at(id, 0);
            let mut values = (0..size).flat_map(|index| {
                let function = store.element_at(id, index);
                (0..store.size_of(function)).map(move |key| store.get_range_value(function, key))
            });
            let (mut low, mut high) = (i32::MAX, i32::MIN);
            if !values.all(|value| {
                let is_int = store.kind_of(value) == KIND_INT;
                if is_int {
                    low = low.min(store.int_of(value));
                    high = high.max(store.int_of(value));
                }
                is_int
            }) {
                return false;
            }
            let keys = (0..store.size_of(first))
                .map(|index| store.peek_key(first, index))
                .collect::<Option<Vec<Id>>>();
            let Some(keys) = keys.filter(|keys| {
                is_function_kind(store.kind_of(first))
                    && (**domain != Construction::Interval
                        || keys.iter().all(|&key| store.kind_of(key) == KIND_INT))
            }) else {
                return false;
            };
            push(out, "[");
            let is_domain_written = if **domain == Construction::Interval {
                let (first, last) = (keys[0], keys[keys.len() - 1]);
                push(
                    out,
                    &format!("{}..{}", store.int_of(first), store.int_of(last)),
                );
                true
            } else {
                push(out, "{");
                let mut is_written = true;
                for (index, &key_id) in keys.iter().enumerate() {
                    if index > 0 {
                        push(out, ", ");
                    }
                    let normalized = if normalized == Normalized::No && keys.len() > 1 {
                        Normalized::Maybe
                    } else {
                        normalized
                    };
                    is_written =
                        is_written && write_normalized(store, key_id, key, normalized, out);
                }
                push(out, "}");
                is_written
            };
            push(out, &format!(" -> {low}..{high}]"));
            is_domain_written
        }
    }
}

/// Whether `FcnRcdValue.isName` takes the text for a field name: letters, digits and `_`, with a
/// letter, and not `WF_` or `SF_` past three characters, where Java's `Character` decides what a
/// letter or a digit is. That is exact through Latin-1, and certain wherever the text holds a
/// character that is neither; elsewhere it depends on Unicode's general categories, which the
/// standard library doesn't give, and is `None`.
pub fn get_field_name(text: &[u16]) -> Option<bool> {
    let mut is_known = true;
    let mut has_letter = false;
    for &unit in text {
        let (is_letter, is_digit) = match unit {
            0x5f => continue,
            0x00..=0x7f => (
                (unit as u8).is_ascii_alphabetic(),
                (unit as u8).is_ascii_digit(),
            ),
            // Latin-1's letters; it has no other digits.
            0xaa | 0xb5 | 0xba | 0xc0..=0xd6 | 0xd8..=0xf6 | 0xf8..=0xff => (true, false),
            0x80..=0xff | 0xd800..=0xdfff => (false, false),
            _ => match char::from_u32(u32::from(unit)) {
                Some(character) if character.is_alphanumeric() => {
                    is_known = false;
                    continue;
                }
                _ => (false, false),
            },
        };
        if !is_letter && !is_digit {
            return Some(false);
        }
        has_letter |= is_letter;
    }
    is_known.then(|| {
        has_letter
            && (text.len() < 4
                || !(text.starts_with(&[u16::from(b'W'), u16::from(b'F'), u16::from(b'_')])
                    || text.starts_with(&[u16::from(b'S'), u16::from(b'F'), u16::from(b'_')])))
    })
}

/// Whether [`get_field_name`] knows the text for a field name.
pub fn is_field_name(text: &[u16]) -> bool {
    get_field_name(text) == Some(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::{EMPTY_SET, FALSE};

    // A string of the spec's, which TLC interned as it started.
    fn text(store: &mut Store, text: &str) -> Id {
        let units: Vec<u16> = text.encode_utf16().collect();
        store.get_string_rank(&units);
        store.str(&units)
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
            assert_eq!(format_value(&store, id).unwrap(), expected);
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
            assert!(
                !is_printable(&store, id),
                "{}",
                format_value(&store, id).unwrap()
            );
        }
        // Normalized, a record's fields are sorted, which is the order the store keeps.
        assert!(is_printable_normalized(&store, record));
        for id in [interval, spaced, power_set, functions, nested] {
            assert!(
                !is_printable_normalized(&store, id),
                "{}",
                format_value(&store, id).unwrap()
            );
        }
    }

    // The texts are TLC's of values built as the constructions say.
    #[test]
    fn prints_a_value_as_tlc_built_it() {
        let mut store = new_store();
        let integers: Vec<Id> = (0..=3)
            .map(|value| store.int(value).expect("an integer"))
            .collect();
        let (a, b, spaced) = (
            text(&mut store, "a"),
            text(&mut store, "b"),
            text(&mut store, "a b"),
        );
        let utf16 = |text: &str| text.encode_utf16().collect::<Vec<u16>>();
        let write = |store: &Store, id: Id, construction: &Construction, is_normalized: bool| {
            let mut text = Vec::new();
            write_constructed(store, id, construction, is_normalized, &mut text)
                .then(|| String::from_utf16(&text).expect("UTF-16"))
        };
        let interval = store.set_of(&integers[1..]).expect("a set");
        let pair = store.set_of(&integers[1..3]).expect("a set");
        let set = |inner: Construction| Construction::Set(Box::new(inner), None);
        assert_eq!(
            write(&store, interval, &Construction::Interval, false).as_deref(),
            Some("1..3")
        );
        assert_eq!(
            write(&store, EMPTY_SET, &Construction::Interval, false).as_deref(),
            Some("{}")
        );
        let nested = store.set_of(&[interval]).expect("a set");
        assert_eq!(
            write(&store, nested, &set(Construction::Interval), false).as_deref(),
            Some("{1..3}")
        );
        // Held, a set of consecutive integers may be an interval.
        assert_eq!(write(&store, nested, &set(Construction::Held), false), None);
        // A record prints its fields as written until TLC normalizes it, and as an element of a
        // set TLC sorted only where both orders agree.
        let record = store
            .function_of(&[a, b], &[integers[1], interval])
            .expect("a record");
        let written = Construction::Record(vec![
            (utf16("b"), Construction::Interval),
            (utf16("a"), Construction::Held),
        ]);
        assert_eq!(
            write(&store, record, &written, false).as_deref(),
            Some("[b |-> 1..3, a |-> 1]")
        );
        assert_eq!(
            write(&store, record, &written, true).as_deref(),
            Some("[a |-> 1, b |-> 1..3]")
        );
        let other = store
            .function_of(&[a, b], &[integers[2], interval])
            .expect("a record");
        let records = store.set_of(&[record, other]).expect("a set");
        assert_eq!(write(&store, records, &set(written), false), None);
        // A function over strings that aren't field names prints with :>.
        let function = store.function_of(&[spaced], &[pair]).expect("a function");
        let keyed = Construction::Function(
            Box::new(Construction::Held),
            Box::new(Construction::Interval),
        );
        assert_eq!(
            write(&store, function, &keyed, false).as_deref(),
            Some("(\"a b\" :> 1..2)")
        );
        assert_eq!(write(&store, function, &Construction::Held, true), None);
        // A power set enumerates its subsets below a base of 7 elements.
        let subsets: Vec<Id> = [&[][..], &[integers[1]], &[integers[2]], &integers[1..3]]
            .iter()
            .map(|subset| store.set_of(subset).expect("a set"))
            .collect();
        let power_set = store.set_of(&subsets).expect("a set");
        assert_eq!(
            write(
                &store,
                power_set,
                &Construction::Subset(Box::new(Construction::Interval)),
                false
            )
            .as_deref(),
            Some("{{}, {1}, {2}, {1, 2}}")
        );
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
            ("é", true),
            ("x\u{b2}", false),
            ("x\u{a3}", false),
        ] {
            assert_eq!(is_field_name(&utf16(name)), expected, "{name}");
        }
        assert_eq!(get_field_name(&utf16("x\u{663}")), None);
        assert_eq!(get_field_name(&utf16("x\u{663} y")), Some(false));
    }
}

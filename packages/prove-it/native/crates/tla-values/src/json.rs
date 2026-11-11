//! TLC's Json module over the store's values, as `src/json.ts` has it: `ToJson`'s text of a value,
//! which `JsonSerialize` and `ndJsonSerialize` write, and the values `JsonDeserialize` and
//! `ndJsonDeserialize` read, each string ranked as TLC ranks it when it first meets it.

use crate::print::{is_printable, write_value};
use crate::store::{
    FALSE, KIND_BOOL, KIND_FUNCTION, KIND_INT, KIND_MODEL, KIND_SET, KIND_STRING, KIND_TUPLE,
    Outcome, TRUE,
};
use crate::{Bail, Id, Store};

/// Gson's text of a string as TLC writes it to a file: `JSON.stringify`'s, with U+2028 and U+2029
/// escaped as well (`toJsonString`), and a lone surrogate as the '?' UTF-8 can't encode.
fn write_string(text: &[u16], out: &mut Vec<u16>) {
    let push = |out: &mut Vec<u16>, text: &str| out.extend(text.encode_utf16());
    out.push(u16::from(b'"'));
    for (index, &unit) in text.iter().enumerate() {
        let is_lone = match unit {
            0xD800..=0xDBFF => !text
                .get(index + 1)
                .is_some_and(|next| (0xDC00..=0xDFFF).contains(next)),
            0xDC00..=0xDFFF => !index
                .checked_sub(1)
                .and_then(|previous| text.get(previous))
                .is_some_and(|previous| (0xD800..=0xDBFF).contains(previous)),
            _ => false,
        };
        match unit {
            0x22 => push(out, "\\\""),
            0x5C => push(out, "\\\\"),
            0x08 => push(out, "\\b"),
            0x0C => push(out, "\\f"),
            0x0A => push(out, "\\n"),
            0x0D => push(out, "\\r"),
            0x09 => push(out, "\\t"),
            0x2028 | 0x2029 => push(out, &format!("\\u{unit:04x}")),
            _ if unit < 0x20 => push(out, &format!("\\u{unit:04x}")),
            // Gson keeps a lone surrogate, which the file's UTF-8 encoder writes as '?'.
            _ if is_lone => out.push(u16::from(b'?')),
            _ => out.push(unit),
        }
    }
    out.push(u16::from(b'"'));
}

/// `toJson`: a value's JSON text. A set is an array of its elements and a sequence an array of
/// its values; another function is an object, a key that isn't a string named by its text. TLC
/// fails on a function it keeps lazy and on Nat, Int or STRING, which the engine doesn't model.
pub fn write_json(store: &Store, id: Id, out: &mut Vec<u16>) -> Outcome<()> {
    let size = store.size_of(id);
    let join = |out: &mut Vec<u16>,
                open: u8,
                close: u8,
                part: &mut dyn FnMut(&mut Vec<u16>, u32) -> Outcome<()>| {
        out.push(u16::from(open));
        for index in 0..size {
            if index > 0 {
                out.push(u16::from(b','));
            }
            part(out, index)?;
        }
        out.push(u16::from(close));
        Ok(())
    };
    match store.kind_of(id) {
        KIND_BOOL => out.extend(if id == TRUE { "true" } else { "false" }.encode_utf16()),
        KIND_INT => out.extend(store.int_of(id).to_string().encode_utf16()),
        KIND_STRING | KIND_MODEL => write_string(store.text_of(id), out),
        KIND_SET => join(out, b'[', b']', &mut |out, index| {
            write_json(store, store.element_at(id, index), out)
        })?,
        KIND_TUPLE => join(out, b'[', b']', &mut |out, index| {
            write_json(store, store.get_range_value(id, index), out)
        })?,
        KIND_FUNCTION => join(out, b'{', b'}', &mut |out, index| {
            let key = store
                .peek_key(id, index)
                .ok_or(Bail("a function key the store didn't intern"))?;
            if store.kind_of(key) == KIND_STRING {
                write_string(store.text_of(key), out);
            } else {
                if !is_printable(store, key) {
                    return Err(Bail("a JSON key whose text depends on how TLC built it"));
                }
                let mut text = Vec::new();
                write_value(store, key, &mut text)?;
                write_string(&text, out);
            }
            out.push(u16::from(b':'));
            write_json(store, store.get_range_value(id, index), out)
        })?,
        _ => {
            return Err(Bail(
                "unsupported: JSON of a function TLC keeps lazy, or Nat, Int or STRING",
            ));
        }
    }
    Ok(())
}

/// Whether a value is a record as `isRecord` has it: a function on a nonempty set of strings.
/// Whether a value holds a record or function of several keys, which TLC's Json module writes
/// in the order TLC holds them (`Json.getObjectNode`), sorted only once TLC has normalized the
/// value, which the store forgets.
pub fn holds_ordered_keys(store: &Store, id: Id) -> bool {
    let kind = store.kind_of(id);
    let size = store.size_of(id);
    if kind == KIND_SET {
        return (0..size).any(|index| holds_ordered_keys(store, store.element_at(id, index)));
    }
    if !crate::store::is_function_kind(kind) {
        return false;
    }
    kind != KIND_TUPLE && size > 1
        || (0..size).any(|index| holds_ordered_keys(store, store.get_range_value(id, index)))
}

pub fn is_json_record(store: &Store, id: Id) -> bool {
    let kind = store.kind_of(id);
    let size = store.size_of(id);
    kind != KIND_TUPLE
        && crate::store::is_function_kind(kind)
        && size > 0
        && (0..size).all(|index| {
            store
                .peek_key(id, index)
                .is_some_and(|key| store.kind_of(key) == KIND_STRING)
        })
}

/// A JSON value as `JSON.parse` reads it, a number by its text.
enum Json {
    Bool(bool),
    Null,
    Number(Vec<u16>),
    Text(Vec<u16>),
    Array(Vec<Json>),
    /// The members in the order `Object.entries` gives them: keys that are array indices first,
    /// ascending, then the others as they first appear, each with the value it last has.
    Object(Vec<(Vec<u16>, Json)>),
}

struct Parser<'a> {
    text: &'a [u16],
    at: usize,
}

const SYNTAX: Bail = Bail("JSON that doesn't parse");

impl Parser<'_> {
    fn skip_space(&mut self) {
        while self
            .text
            .get(self.at)
            .is_some_and(|&unit| matches!(unit, 0x20 | 0x09 | 0x0A | 0x0D))
        {
            self.at += 1;
        }
    }

    fn peek(&self) -> Option<u16> {
        self.text.get(self.at).copied()
    }

    fn expect(&mut self, word: &str) -> Outcome<()> {
        for unit in word.encode_utf16() {
            if self.peek() != Some(unit) {
                return Err(SYNTAX);
            }
            self.at += 1;
        }
        Ok(())
    }

    fn value(&mut self, depth: usize) -> Outcome<Json> {
        if depth > 10_000 {
            return Err(Bail("JSON nested too deep"));
        }
        self.skip_space();
        let value = match self.peek().ok_or(SYNTAX)? {
            0x7B => {
                self.at += 1;
                let mut members: Vec<(Vec<u16>, Json)> = Vec::new();
                self.skip_space();
                if self.peek() == Some(0x7D) {
                    self.at += 1;
                } else {
                    loop {
                        self.skip_space();
                        let key = self.string()?;
                        self.skip_space();
                        self.expect(":")?;
                        let value = self.value(depth + 1)?;
                        match members.iter_mut().find(|(known, _)| *known == key) {
                            Some(member) => member.1 = value,
                            None => members.push((key, value)),
                        }
                        self.skip_space();
                        match self.peek() {
                            Some(0x2C) => self.at += 1,
                            Some(0x7D) => {
                                self.at += 1;
                                break;
                            }
                            _ => return Err(SYNTAX),
                        }
                    }
                }
                let index = |key: &[u16]| -> Option<u32> {
                    let text = String::from_utf16(key).ok()?;
                    let index: u32 = text.parse().ok()?;
                    (index != u32::MAX && index.to_string() == text).then_some(index)
                };
                let (mut indices, others): (Vec<_>, Vec<_>) = members
                    .into_iter()
                    .partition(|(key, _)| index(key).is_some());
                indices.sort_by_key(|(key, _)| index(key));
                indices.extend(others);
                Json::Object(indices)
            }
            0x5B => {
                self.at += 1;
                let mut elements = Vec::new();
                self.skip_space();
                if self.peek() == Some(0x5D) {
                    self.at += 1;
                } else {
                    loop {
                        elements.push(self.value(depth + 1)?);
                        self.skip_space();
                        match self.peek() {
                            Some(0x2C) => self.at += 1,
                            Some(0x5D) => {
                                self.at += 1;
                                break;
                            }
                            _ => return Err(SYNTAX),
                        }
                    }
                }
                Json::Array(elements)
            }
            0x22 => Json::Text(self.string()?),
            0x74 => {
                self.expect("true")?;
                Json::Bool(true)
            }
            0x66 => {
                self.expect("false")?;
                Json::Bool(false)
            }
            0x6E => {
                self.expect("null")?;
                Json::Null
            }
            _ => Json::Number(self.number()?),
        };
        Ok(value)
    }

    fn string(&mut self) -> Outcome<Vec<u16>> {
        self.expect("\"")?;
        let mut units = Vec::new();
        loop {
            let unit = self.peek().ok_or(SYNTAX)?;
            self.at += 1;
            match unit {
                0x22 => return Ok(units),
                0x5C => {
                    let escaped = self.peek().ok_or(SYNTAX)?;
                    self.at += 1;
                    units.push(match escaped {
                        0x22 | 0x5C | 0x2F => escaped,
                        0x62 => 0x08,
                        0x66 => 0x0C,
                        0x6E => 0x0A,
                        0x72 => 0x0D,
                        0x74 => 0x09,
                        0x75 => {
                            let digits = self.text.get(self.at..self.at + 4).ok_or(SYNTAX)?;
                            let text = String::from_utf16(digits).map_err(|_| SYNTAX)?;
                            if !text.bytes().all(|byte| byte.is_ascii_hexdigit()) {
                                return Err(SYNTAX);
                            }
                            self.at += 4;
                            u16::from_str_radix(&text, 16).map_err(|_| SYNTAX)?
                        }
                        _ => return Err(SYNTAX),
                    });
                }
                0x00..0x20 => return Err(SYNTAX),
                _ => units.push(unit),
            }
        }
    }

    // JSON's grammar of a number: an optional minus, an integer without leading zeros, then an
    // optional fraction and exponent.
    fn number(&mut self) -> Outcome<Vec<u16>> {
        let start = self.at;
        let digit = |unit: Option<u16>| unit.is_some_and(|unit| (0x30..=0x39).contains(&unit));
        let digits = |parser: &mut Parser<'_>| -> Outcome<()> {
            if !digit(parser.peek()) {
                return Err(SYNTAX);
            }
            while digit(parser.peek()) {
                parser.at += 1;
            }
            Ok(())
        };
        if self.peek() == Some(0x2D) {
            self.at += 1;
        }
        if self.peek() == Some(0x30) {
            self.at += 1;
        } else {
            digits(self)?;
        }
        if self.peek() == Some(0x2E) {
            self.at += 1;
            digits(self)?;
        }
        if matches!(self.peek(), Some(0x65 | 0x45)) {
            self.at += 1;
            if matches!(self.peek(), Some(0x2B | 0x2D)) {
                self.at += 1;
            }
            digits(self)?;
        }
        Ok(self.text[start..self.at].to_vec())
    }
}

/// `toInteger`: TLC reads a JSON number by its text with Integer.parseInt (`Json.getValue`), so
/// it fails on any but a 32-bit integer, which the engine doesn't report.
fn to_integer(source: &[u16]) -> Outcome<i32> {
    String::from_utf16_lossy(source)
        .parse()
        .map_err(|_| Bail("a JSON number that isn't a 32-bit integer, which TLC fails on"))
}

/// A string ranked as `rankString` ranks it.
fn ranked_string(store: &mut Store, text: &[u16]) -> Outcome<Id> {
    if let Some(string) = store.find_str(text)
        && store.text_rank_of(string) < 0
    {
        return Err(Bail("a JSON string the engine made unranked"));
    }
    store.get_string_rank(text);
    Ok(store.str(text))
}

// `fromJson`: an array is a tuple and an object a record, each key ranked before its value.
fn from_json(store: &mut Store, json: Json) -> Outcome<Id> {
    match json {
        Json::Bool(value) => Ok(if value { TRUE } else { FALSE }),
        Json::Number(source) => store.int(i64::from(to_integer(&source)?)),
        Json::Text(text) => ranked_string(store, &text),
        Json::Array(elements) => {
            let values = elements
                .into_iter()
                .map(|element| from_json(store, element))
                .collect::<Outcome<Vec<Id>>>()?;
            Ok(store.tuple_of(&values))
        }
        // TLC reads {} as an empty record, which it prints and writes apart from the empty
        // sequence that the store holds for both.
        Json::Object(members) if members.is_empty() => Err(Bail(
            "unsupported: an empty JSON object, which TLC holds apart from <<>>",
        )),
        Json::Object(members) => {
            let mut keys = Vec::with_capacity(members.len());
            let mut values = Vec::with_capacity(members.len());
            for (key, value) in members {
                keys.push(ranked_string(store, &key)?);
                values.push(from_json(store, value)?);
            }
            store.function_of(&keys, &values)
        }
        Json::Null => Err(Bail("an unsupported JSON value")),
    }
}

/// `parseJson`: the value of a JSON text; an empty one, like null, is no value TLC reads.
pub fn read_json(store: &mut Store, text: &[u16]) -> Outcome<Id> {
    let mut parser = Parser { text, at: 0 };
    let json = parser.value(0)?;
    parser.skip_space();
    if parser.at != text.len() {
        return Err(SYNTAX);
    }
    from_json(store, json)
}

/// `ndJsonDeserialize`'s value of a text: each line that isn't empty once trimmed as Java's
/// `String.trim` trims, of the units up to a space, read as JSON past a byte order mark that
/// starts it, in a tuple.
pub fn read_nd_json(store: &mut Store, text: &[u16]) -> Outcome<Id> {
    let is_space = |unit: &u16| *unit <= 0x20;
    let mut values = Vec::new();
    let mut start = 0;
    while start <= text.len() {
        let end = text[start..]
            .iter()
            .position(|&unit| unit == 0x0A || unit == 0x0D)
            .map_or(text.len(), |offset| start + offset);
        let line = &text[start..end];
        let first = line.iter().position(|unit| !is_space(unit));
        if let Some(first) = first {
            let last = line
                .iter()
                .rposition(|unit| !is_space(unit))
                .unwrap_or(first);
            let line = &line[first..=last];
            values.push(read_json(
                store,
                line.strip_prefix(&[0xFEFF]).unwrap_or(line),
            )?);
        }
        start = match text.get(end) {
            Some(0x0D) if text.get(end + 1) == Some(&0x0A) => end + 2,
            Some(_) => end + 1,
            None => break,
        };
    }
    Ok(store.tuple_of(&values))
}

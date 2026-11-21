//! TLC's Json module over the store's values: `ToJson`'s text of a value, which `JsonSerialize`
//! and `ndJsonSerialize` write, and the values `JsonDeserialize` and `ndJsonDeserialize` read as
//! Gson 2.14, which TLC's jar bundles, parses them, each string ranked as TLC ranks it when it
//! first meets it.

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
    if store.is_empty_tuple_ambiguous() && store.kind_of(id) == KIND_TUPLE && store.size_of(id) == 0
    {
        return Err(crate::print::AMBIGUOUS_EMPTY);
    }
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
        _ => return Err(JSON_OF_UNBUILT),
    }
    Ok(())
}

/// Check the in-memory JSON string before the recursive writer reads it. The store can share a
/// child at different depths, so keep the greatest depth at which each value has been reached.
/// [`write_json`] of a function of one key, written as `key`: TLC's text of the key as it built
/// it, where the store may hold the key as another value of its text (`getObjectNode`).
pub fn write_json_with_key(store: &Store, id: Id, key: &[u16], out: &mut Vec<u16>) -> Outcome<()> {
    out.push(u16::from(b'{'));
    write_string(key, out);
    out.push(u16::from(b':'));
    write_json(store, store.get_range_value(id, 0), out)?;
    out.push(u16::from(b'}'));
    Ok(())
}

pub fn check_json_string_value(store: &Store, root: Id) -> Outcome<()> {
    const MAX_DEPTH: usize = 256;
    let mut pending = vec![(root, 0usize)];
    let mut seen = std::collections::HashMap::new();
    while let Some((id, depth)) = pending.pop() {
        if depth > MAX_DEPTH {
            return Err(Bail(
                "ToJson of a value nested too deeply for the JSON writer",
            ));
        }
        if seen.get(&id).is_some_and(|previous| *previous >= depth) {
            continue;
        }
        seen.insert(id, depth);
        let kind = store.kind_of(id);
        if matches!(kind, KIND_STRING | KIND_MODEL) {
            if String::from_utf16(store.text_of(id)).is_err() {
                return Err(Bail("ToJson of a string with a lone surrogate"));
            }
        } else if kind == KIND_SET {
            for index in 0..store.size_of(id) {
                pending.push((store.element_at(id, index), depth + 1));
            }
        } else if crate::store::is_function_kind(kind) {
            for index in 0..store.size_of(id) {
                if let Some(key) = store.peek_key(id, index) {
                    pending.push((key, depth + 1));
                }
                pending.push((store.get_range_value(id, index), depth + 1));
            }
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

/// A JSON element as Gson's `JsonParser` reads it, a number by its text, an object's members in
/// the order their names first appear, each with the value it last has (`JsonObject.add`).
pub enum Json {
    Bool(bool),
    Null,
    Number(Vec<u16>),
    Text(Vec<u16>),
    Array(Vec<Json>),
    Object(Vec<(Vec<u16>, Json)>),
}

/// Where `Json.getNode` meets a function TLC keeps lazy, which it builds (`toFcnRcd`), or Nat,
/// Int or STRING, which it can't convert: the store holds neither as TLC does, so the evaluator
/// of failures finds whether, and how, TLC fails there.
pub const JSON_OF_UNBUILT: Bail = Bail("JSON of a function TLC keeps lazy, or Nat, Int or STRING");

/// A JSON file TLC's Json module fails to parse (`JsonParser.parseReader`).
pub const JSON_UNPARSED: Bail = Bail("JSON that TLC's Json module fails to parse");
/// A JSON value TLC's Json module fails to convert to a value (`Json.getValue`): null, or a
/// number that isn't a 32-bit integer.
pub const JSON_UNCONVERTED: Bail = Bail("a JSON value TLC's Json module fails to convert");

/// Gson's troubleshooting page for malformed JSON (`TroubleshootingGuide.createUrl`).
const MALFORMED_JSON_URL: &str =
    "https://github.com/google/gson/blob/main/Troubleshooting.md#malformed-json";
/// `JsonReader.DEFAULT_NESTING_LIMIT`.
const NESTING_LIMIT: usize = 255;
/// `JsonReader.BUFFER_SIZE`: a number that fills the buffer is read as an unquoted literal.
const BUFFER_SIZE: usize = 1024;

/// What Gson's `JsonReader` throws: a `MalformedJsonException`, or the `EOFException` of input
/// that ends before a value, each with its message.
enum ReadError {
    Malformed(Vec<u16>),
    EndOfInput(Vec<u16>),
}

impl ReadError {
    /// The message of the `JsonSyntaxException` that wraps it, its `toString`.
    fn message(self) -> Vec<u16> {
        let (class, message) = match self {
            ReadError::Malformed(message) => {
                ("com.google.gson.stream.MalformedJsonException", message)
            }
            ReadError::EndOfInput(message) => ("java.io.EOFException", message),
        };
        let mut text: Vec<u16> = format!("{class}: ").encode_utf16().collect();
        text.extend(message);
        text
    }
}

type Read<T> = Result<T, ReadError>;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Scope {
    EmptyArray,
    NonemptyArray,
    EmptyObject,
    DanglingName,
    NonemptyObject,
    EmptyDocument,
    NonemptyDocument,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Peeked {
    None,
    BeginObject,
    EndObject,
    BeginArray,
    EndArray,
    True,
    False,
    Null,
    SingleQuoted,
    DoubleQuoted,
    Unquoted,
    SingleQuotedName,
    DoubleQuotedName,
    UnquotedName,
    /// `PEEKED_LONG` or `PEEKED_NUMBER`, whose text `nextString` gives the same.
    Number,
    Eof,
}

/// The `NUMBER_CHAR_*` states of `peekNumber`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NumberChar {
    None,
    Sign,
    Digit,
    Decimal,
    FractionDigit,
    ExpE,
    ExpSign,
    ExpDigit,
}

/// Gson 2.14's `JsonReader` over a whole text, as `JsonParser` reads one: leniently, but for the
/// check that nothing follows the value. A position is the one Gson's buffer has in the text.
struct Reader<'a> {
    text: &'a [u16],
    pos: usize,
    line_number: usize,
    line_start: usize,
    is_lenient: bool,
    peeked: Peeked,
    number_length: usize,
    stack: Vec<Scope>,
    stack_size: usize,
    path_names: Vec<Option<Vec<u16>>>,
    path_indices: Vec<i64>,
}

const fn unit(character: char) -> u16 {
    character as u16
}

impl<'a> Reader<'a> {
    fn new(text: &'a [u16]) -> Reader<'a> {
        // `fillBuffer` consumes a byte order mark as it first reads.
        let start = usize::from(text.first() == Some(&0xFEFF));
        Reader {
            text,
            pos: start,
            line_number: 0,
            line_start: start,
            is_lenient: true,
            peeked: Peeked::None,
            number_length: 0,
            stack: vec![Scope::EmptyDocument],
            stack_size: 1,
            path_names: vec![None],
            path_indices: vec![0],
        }
    }

    fn location(&self) -> Vec<u16> {
        let mut text: Vec<u16> = format!(
            " at line {} column {} path $",
            self.line_number + 1,
            self.pos - self.line_start + 1
        )
        .encode_utf16()
        .collect();
        for index in 0..self.stack_size {
            match self.stack[index] {
                Scope::EmptyArray | Scope::NonemptyArray => {
                    text.extend(format!("[{}]", self.path_indices[index]).encode_utf16());
                }
                Scope::EmptyObject | Scope::DanglingName | Scope::NonemptyObject => {
                    text.push(unit('.'));
                    if let Some(name) = &self.path_names[index] {
                        text.extend_from_slice(name);
                    }
                }
                Scope::EmptyDocument | Scope::NonemptyDocument => {}
            }
        }
        text
    }

    fn syntax_error(&self, message: &str) -> ReadError {
        self.syntax_error_units(message.encode_utf16().collect())
    }

    fn syntax_error_units(&self, mut message: Vec<u16>) -> ReadError {
        message.extend(self.location());
        message.extend(format!("\nSee {MALFORMED_JSON_URL}").encode_utf16());
        ReadError::Malformed(message)
    }

    fn check_lenient(&self) -> Read<()> {
        if self.is_lenient {
            return Ok(());
        }
        Err(self.syntax_error(
            "Use JsonReader.setStrictness(Strictness.LENIENT) to accept malformed JSON",
        ))
    }

    fn top(&self) -> Scope {
        self.stack[self.stack_size - 1]
    }

    fn set_top(&mut self, scope: Scope) {
        self.stack[self.stack_size - 1] = scope;
    }

    fn push(&mut self, scope: Scope) -> Read<()> {
        // The stack's first element is the document's.
        if self.stack_size > NESTING_LIMIT {
            let mut message: Vec<u16> = format!("Nesting limit {NESTING_LIMIT} reached")
                .encode_utf16()
                .collect();
            message.extend(self.location());
            return Err(ReadError::Malformed(message));
        }
        if self.stack_size == self.stack.len() {
            self.stack.push(scope);
            self.path_names.push(None);
            self.path_indices.push(0);
        } else {
            self.stack[self.stack_size] = scope;
        }
        self.stack_size += 1;
        Ok(())
    }

    fn peek(&mut self) -> Read<Peeked> {
        if self.peeked == Peeked::None {
            self.peeked = self.do_peek()?;
        }
        Ok(self.peeked)
    }

    fn do_peek(&mut self) -> Read<Peeked> {
        let peek_stack = self.top();
        match peek_stack {
            Scope::EmptyArray => self.set_top(Scope::NonemptyArray),
            Scope::NonemptyArray => match self.next_non_whitespace(true)? {
                c if c == i32::from(unit(']')) => return Ok(Peeked::EndArray),
                c if c == i32::from(unit(';')) => self.check_lenient()?,
                c if c == i32::from(unit(',')) => {}
                _ => return Err(self.syntax_error("Unterminated array")),
            },
            Scope::EmptyObject | Scope::NonemptyObject => {
                self.set_top(Scope::DanglingName);
                if peek_stack == Scope::NonemptyObject {
                    match self.next_non_whitespace(true)? {
                        c if c == i32::from(unit('}')) => return Ok(Peeked::EndObject),
                        c if c == i32::from(unit(';')) => self.check_lenient()?,
                        c if c == i32::from(unit(',')) => {}
                        _ => return Err(self.syntax_error("Unterminated object")),
                    }
                }
                let c = self.next_non_whitespace(true)?;
                return match c {
                    c if c == i32::from(unit('"')) => Ok(Peeked::DoubleQuotedName),
                    c if c == i32::from(unit('\'')) => {
                        self.check_lenient()?;
                        Ok(Peeked::SingleQuotedName)
                    }
                    c if c == i32::from(unit('}')) => {
                        if peek_stack != Scope::NonemptyObject {
                            Ok(Peeked::EndObject)
                        } else {
                            Err(self.syntax_error("Expected name"))
                        }
                    }
                    c => {
                        self.check_lenient()?;
                        self.pos -= 1;
                        if self.is_literal(c as u16)? {
                            Ok(Peeked::UnquotedName)
                        } else {
                            Err(self.syntax_error("Expected name"))
                        }
                    }
                };
            }
            Scope::DanglingName => {
                self.set_top(Scope::NonemptyObject);
                match self.next_non_whitespace(true)? {
                    c if c == i32::from(unit(':')) => {}
                    c if c == i32::from(unit('=')) => {
                        self.check_lenient()?;
                        if self.text.get(self.pos) == Some(&unit('>')) {
                            self.pos += 1;
                        }
                    }
                    _ => return Err(self.syntax_error("Expected ':'")),
                }
            }
            Scope::EmptyDocument => {
                if self.is_lenient {
                    self.consume_non_execute_prefix()?;
                }
                self.set_top(Scope::NonemptyDocument);
            }
            Scope::NonemptyDocument => {
                if self.next_non_whitespace(false)? == -1 {
                    return Ok(Peeked::Eof);
                }
                self.check_lenient()?;
                self.pos -= 1;
            }
        }
        let c = self.next_non_whitespace(true)?;
        let is_array = matches!(peek_stack, Scope::EmptyArray | Scope::NonemptyArray);
        match c {
            c if c == i32::from(unit(']')) && peek_stack == Scope::EmptyArray => {
                return Ok(Peeked::EndArray);
            }
            // In lenient mode, a 0-length literal in an array means null.
            c if c == i32::from(unit(']'))
                || c == i32::from(unit(';'))
                || c == i32::from(unit(',')) =>
            {
                if !is_array {
                    return Err(self.syntax_error("Unexpected value"));
                }
                self.check_lenient()?;
                self.pos -= 1;
                return Ok(Peeked::Null);
            }
            c if c == i32::from(unit('\'')) => {
                self.check_lenient()?;
                return Ok(Peeked::SingleQuoted);
            }
            c if c == i32::from(unit('"')) => return Ok(Peeked::DoubleQuoted),
            c if c == i32::from(unit('[')) => return Ok(Peeked::BeginArray),
            c if c == i32::from(unit('{')) => return Ok(Peeked::BeginObject),
            _ => self.pos -= 1,
        }
        if let Some(peeked) = self.peek_keyword()? {
            return Ok(peeked);
        }
        if let Some(peeked) = self.peek_number()? {
            return Ok(peeked);
        }
        if !self.is_literal(self.text[self.pos])? {
            return Err(self.syntax_error("Expected value"));
        }
        self.check_lenient()?;
        Ok(Peeked::Unquoted)
    }

    fn peek_keyword(&mut self) -> Read<Option<Peeked>> {
        let (keyword, upper, peeking) = match self.text[self.pos] {
            c if c == unit('t') || c == unit('T') => ("true", "TRUE", Peeked::True),
            c if c == unit('f') || c == unit('F') => ("false", "FALSE", Peeked::False),
            c if c == unit('n') || c == unit('N') => ("null", "NULL", Peeked::Null),
            _ => return Ok(None),
        };
        let length = keyword.len();
        for (index, (lower, upper)) in keyword.bytes().zip(upper.bytes()).enumerate() {
            let Some(&c) = self.text.get(self.pos + index) else {
                return Ok(None);
            };
            if c != u16::from(lower) && c != u16::from(upper) {
                return Ok(None);
            }
        }
        if let Some(&next) = self.text.get(self.pos + length)
            && self.is_literal(next)?
        {
            return Ok(None);
        }
        self.pos += length;
        Ok(Some(peeking))
    }

    fn peek_number(&mut self) -> Read<Option<Peeked>> {
        // Negative to accommodate Long.MIN_VALUE, as Gson's.
        let mut value: i64 = 0;
        let mut last = NumberChar::None;
        let mut index = 0;
        loop {
            // A number that fills Gson's buffer is read as an unquoted literal.
            if index == BUFFER_SIZE {
                return Ok(None);
            }
            let Some(&c) = self.text.get(self.pos + index) else {
                break;
            };
            match c {
                c if c == unit('-') => match last {
                    NumberChar::None => last = NumberChar::Sign,
                    NumberChar::ExpE => last = NumberChar::ExpSign,
                    _ => return Ok(None),
                },
                c if c == unit('+') => match last {
                    NumberChar::ExpE => last = NumberChar::ExpSign,
                    _ => return Ok(None),
                },
                c if c == unit('e') || c == unit('E') => match last {
                    NumberChar::Digit | NumberChar::FractionDigit => last = NumberChar::ExpE,
                    _ => return Ok(None),
                },
                c if c == unit('.') => match last {
                    NumberChar::Digit => last = NumberChar::Decimal,
                    _ => return Ok(None),
                },
                c if !(unit('0')..=unit('9')).contains(&c) => {
                    if !self.is_literal(c)? {
                        break;
                    }
                    return Ok(None);
                }
                c => {
                    let digit = i64::from(c - unit('0'));
                    match last {
                        NumberChar::Sign | NumberChar::None => {
                            value = -digit;
                            last = NumberChar::Digit;
                        }
                        NumberChar::Digit => {
                            // A leading '0' isn't allowed, since it could be octal.
                            if value == 0 {
                                return Ok(None);
                            }
                            value = value.wrapping_mul(10).wrapping_sub(digit);
                        }
                        NumberChar::Decimal => last = NumberChar::FractionDigit,
                        NumberChar::ExpE | NumberChar::ExpSign => last = NumberChar::ExpDigit,
                        NumberChar::FractionDigit | NumberChar::ExpDigit => {}
                    }
                }
            }
            index += 1;
        }
        if matches!(
            last,
            NumberChar::Digit | NumberChar::FractionDigit | NumberChar::ExpDigit
        ) {
            self.number_length = index;
            return Ok(Some(Peeked::Number));
        }
        Ok(None)
    }

    fn is_literal(&self, c: u16) -> Read<bool> {
        match char::from_u32(u32::from(c)) {
            Some('/' | '\\' | ';' | '#' | '=') => {
                self.check_lenient()?;
                Ok(false)
            }
            Some('{' | '}' | '[' | ']' | ':' | ',' | ' ' | '\t' | '\u{c}' | '\r' | '\n') => {
                Ok(false)
            }
            _ => Ok(true),
        }
    }

    fn next_non_whitespace(&mut self, throw_on_eof: bool) -> Read<i32> {
        let mut p = self.pos;
        loop {
            let Some(&c) = self.text.get(p) else {
                self.pos = p;
                break;
            };
            p += 1;
            if c == unit('\n') {
                self.line_number += 1;
                self.line_start = p;
                continue;
            } else if c == unit(' ') || c == unit('\r') || c == unit('\t') {
                continue;
            }
            self.pos = p;
            if c == unit('/') {
                if p == self.text.len() {
                    return Ok(i32::from(c));
                }
                self.check_lenient()?;
                match self.text[self.pos] {
                    peek if peek == unit('*') => {
                        // A /* c-style comment */.
                        self.pos += 1;
                        if !self.skip_to_comment_end() {
                            return Err(self.syntax_error("Unterminated comment"));
                        }
                        p = self.pos + 2;
                    }
                    peek if peek == unit('/') => {
                        // A // end-of-line comment.
                        self.pos += 1;
                        self.skip_to_end_of_line();
                        p = self.pos;
                    }
                    _ => return Ok(i32::from(c)),
                }
            } else if c == unit('#') {
                self.check_lenient()?;
                self.skip_to_end_of_line();
                p = self.pos;
            } else {
                return Ok(i32::from(c));
            }
        }
        if throw_on_eof {
            let mut message: Vec<u16> = "End of input".encode_utf16().collect();
            message.extend(self.location());
            return Err(ReadError::EndOfInput(message));
        }
        Ok(-1)
    }

    fn skip_to_end_of_line(&mut self) {
        while let Some(&c) = self.text.get(self.pos) {
            self.pos += 1;
            if c == unit('\n') {
                self.line_number += 1;
                self.line_start = self.pos;
                break;
            } else if c == unit('\r') {
                break;
            }
        }
    }

    // `skipTo("*/")`.
    fn skip_to_comment_end(&mut self) -> bool {
        while self.pos + 2 <= self.text.len() {
            if self.text[self.pos] == unit('\n') {
                self.line_number += 1;
                self.line_start = self.pos + 1;
            } else if self.text[self.pos..self.pos + 2] == [unit('*'), unit('/')] {
                return true;
            }
            self.pos += 1;
        }
        false
    }

    fn consume_non_execute_prefix(&mut self) -> Read<()> {
        self.next_non_whitespace(true)?;
        self.pos -= 1;
        let prefix = [unit(')'), unit(']'), unit('}'), unit('\''), unit('\n')];
        if self.text.get(self.pos..self.pos + 5) == Some(&prefix[..]) {
            self.pos += 5;
        }
        Ok(())
    }

    fn next_quoted_value(&mut self, quote: u16) -> Read<Vec<u16>> {
        let mut units = Vec::new();
        loop {
            let Some(&c) = self.text.get(self.pos) else {
                return Err(self.syntax_error("Unterminated string"));
            };
            self.pos += 1;
            if c == quote {
                return Ok(units);
            } else if c == unit('\\') {
                units.push(self.read_escape_character()?);
            } else {
                if c == unit('\n') {
                    self.line_number += 1;
                    self.line_start = self.pos;
                }
                units.push(c);
            }
        }
    }

    fn read_escape_character(&mut self) -> Read<u16> {
        let Some(&escaped) = self.text.get(self.pos) else {
            return Err(self.syntax_error("Unterminated escape sequence"));
        };
        self.pos += 1;
        Ok(match char::from_u32(u32::from(escaped)) {
            Some('u') => {
                let Some(digits) = self.text.get(self.pos..self.pos + 4) else {
                    return Err(self.syntax_error("Unterminated escape sequence"));
                };
                let mut result: u16 = 0;
                for &digit in digits {
                    let value = char::from_u32(u32::from(digit)).and_then(|c| c.to_digit(16));
                    let Some(value) = value.filter(|_| digit < 0x80) else {
                        let mut message: Vec<u16> =
                            "Malformed Unicode escape \\u".encode_utf16().collect();
                        message.extend_from_slice(digits);
                        return Err(self.syntax_error_units(message));
                    };
                    result = (result << 4) + value as u16;
                }
                self.pos += 4;
                result
            }
            Some('t') => unit('\t'),
            Some('b') => 0x08,
            Some('n') => unit('\n'),
            Some('r') => unit('\r'),
            Some('f') => 0x0C,
            Some('\n') => {
                self.line_number += 1;
                self.line_start = self.pos;
                escaped
            }
            Some('\'' | '"' | '\\' | '/') => escaped,
            _ => return Err(self.syntax_error("Invalid escape sequence")),
        })
    }

    fn next_unquoted_value(&mut self) -> Read<Vec<u16>> {
        let mut end = self.pos;
        while let Some(&c) = self.text.get(end) {
            if !self.is_literal(c)? {
                break;
            }
            end += 1;
        }
        let value = self.text[self.pos..end].to_vec();
        self.pos = end;
        Ok(value)
    }

    fn count_value(&mut self) {
        self.peeked = Peeked::None;
        self.path_indices[self.stack_size - 1] += 1;
    }

    // `nextString`, of the token `peek` found.
    fn next_string(&mut self) -> Read<Vec<u16>> {
        let value = match self.peeked {
            Peeked::Unquoted => self.next_unquoted_value()?,
            Peeked::SingleQuoted => self.next_quoted_value(unit('\''))?,
            Peeked::DoubleQuoted => self.next_quoted_value(unit('"'))?,
            _ => {
                let value = self.text[self.pos..self.pos + self.number_length].to_vec();
                self.pos += self.number_length;
                value
            }
        };
        self.count_value();
        Ok(value)
    }

    fn next_name(&mut self) -> Read<Vec<u16>> {
        let name = match self.peek()? {
            Peeked::UnquotedName => self.next_unquoted_value()?,
            Peeked::SingleQuotedName => self.next_quoted_value(unit('\''))?,
            _ => self.next_quoted_value(unit('"'))?,
        };
        self.peeked = Peeked::None;
        self.path_names[self.stack_size - 1] = Some(name.clone());
        Ok(name)
    }

    fn has_next(&mut self) -> Read<bool> {
        Ok(!matches!(
            self.peek()?,
            Peeked::EndObject | Peeked::EndArray | Peeked::Eof
        ))
    }

    // `JsonElementTypeAdapter.read`, of the token `peek` found.
    fn element(&mut self) -> Read<Json> {
        Ok(match self.peek()? {
            Peeked::BeginArray => {
                self.push(Scope::EmptyArray)?;
                self.path_indices[self.stack_size - 1] = 0;
                self.peeked = Peeked::None;
                let mut elements = Vec::new();
                while self.has_next()? {
                    elements.push(self.element()?);
                }
                // `endArray`.
                self.stack_size -= 1;
                self.count_value();
                Json::Array(elements)
            }
            Peeked::BeginObject => {
                self.push(Scope::EmptyObject)?;
                self.peeked = Peeked::None;
                let mut members: Vec<(Vec<u16>, Json)> = Vec::new();
                while self.has_next()? {
                    let name = self.next_name()?;
                    self.peek()?;
                    let value = self.element()?;
                    match members.iter_mut().find(|(known, _)| *known == name) {
                        Some(member) => member.1 = value,
                        None => members.push((name, value)),
                    }
                }
                // `endObject`.
                self.stack_size -= 1;
                self.path_names[self.stack_size] = None;
                self.count_value();
                Json::Object(members)
            }
            Peeked::True | Peeked::False => {
                let value = self.peeked == Peeked::True;
                self.count_value();
                Json::Bool(value)
            }
            Peeked::Null => {
                self.count_value();
                Json::Null
            }
            Peeked::Number => Json::Number(self.next_string()?),
            Peeked::Unquoted | Peeked::SingleQuoted | Peeked::DoubleQuoted => {
                Json::Text(self.next_string()?)
            }
            // `peek` gives a value where `JsonElementTypeAdapter` reads one.
            Peeked::None
            | Peeked::EndObject
            | Peeked::EndArray
            | Peeked::SingleQuotedName
            | Peeked::DoubleQuotedName
            | Peeked::UnquotedName
            | Peeked::Eof => unreachable!("a JSON token where a value is"),
        })
    }
}

/// `JsonParser.parseReader`: the element of a text, or the message of the exception it throws.
/// An empty text is null, as is one that holds only comments; what follows a value other than
/// null fails the strict check that nothing does.
pub fn parse_json(text: &[u16]) -> Result<Json, Vec<u16>> {
    let mut reader = Reader::new(text);
    // `Streams.parse`.
    match reader.peek() {
        Err(ReadError::EndOfInput(_)) => return Ok(Json::Null),
        Err(error) => return Err(error.message()),
        Ok(_) => {}
    }
    let element = reader.element().map_err(ReadError::message)?;
    if !matches!(element, Json::Null) {
        reader.is_lenient = false;
        match reader.peek() {
            Ok(Peeked::Eof) => {}
            Ok(_) => {
                return Err("Did not consume the entire document."
                    .encode_utf16()
                    .collect());
            }
            Err(error) => return Err(error.message()),
        }
    }
    Ok(element)
}

/// The message of `getValue`'s failure to convert an element to a value, as it converts the
/// elements in order: null, or a number that `Integer.parseInt` doesn't read.
pub fn conversion_failure(json: &Json) -> Option<Vec<u16>> {
    match json {
        Json::Null => Some(
            "Cannot convert value: unsupported JSON value null"
                .encode_utf16()
                .collect(),
        ),
        Json::Number(source) if to_integer(source).is_none() => {
            let mut message: Vec<u16> =
                "Cannot convert value: expected a 32-bit integer JSON number, but found "
                    .encode_utf16()
                    .collect();
            message.extend_from_slice(source);
            Some(message)
        }
        Json::Array(elements) => elements.iter().find_map(conversion_failure),
        Json::Object(members) => members
            .iter()
            .find_map(|(_, value)| conversion_failure(value)),
        _ => None,
    }
}

/// The message of what `Json.deserialize` (or, `is_lines`, `Json.ndDeserialize`) throws reading
/// a file's text, past opening it; `None` where it reads a value.
pub fn read_failure(text: &[u16], is_lines: bool) -> Outcome<Option<Vec<u16>>> {
    let read = |line: &[u16]| -> Outcome<Option<Vec<u16>>> {
        check_byte_order_marks(line)?;
        Ok(match parse_json(line) {
            Ok(json) => conversion_failure(&json),
            Err(message) => Some(message),
        })
    };
    if !is_lines {
        return read(text);
    }
    for line in lines(text) {
        if let Some(message) = read(line)? {
            return Ok(Some(message));
        }
    }
    Ok(None)
}

// Gson's reader takes a second byte order mark after the first as one where it reads the text
// in parts, which it does as the file system gives them.
fn check_byte_order_marks(text: &[u16]) -> Outcome<()> {
    if text.starts_with(&[0xFEFF, 0xFEFF]) {
        return Err(Bail("JSON that starts with two byte order marks"));
    }
    Ok(())
}

/// The lines `ndDeserialize` reads, as `BufferedReader.readLine` splits them, each trimmed as
/// `String.trim` trims, of the units up to a space, past those empty once trimmed.
fn lines(text: &[u16]) -> impl Iterator<Item = &[u16]> {
    let is_space = |unit: &u16| *unit <= 0x20;
    let mut start = Some(0);
    std::iter::from_fn(move || {
        while let Some(at) = start {
            let end = text[at..]
                .iter()
                .position(|&unit| unit == 0x0A || unit == 0x0D)
                .map_or(text.len(), |offset| at + offset);
            start = match text.get(end) {
                Some(0x0D) if text.get(end + 1) == Some(&0x0A) => Some(end + 2),
                Some(_) => Some(end + 1),
                None => None,
            };
            let line = &text[at..end];
            if let Some(first) = line.iter().position(|unit| !is_space(unit)) {
                let last = line
                    .iter()
                    .rposition(|unit| !is_space(unit))
                    .unwrap_or(first);
                return Some(&line[first..=last]);
            }
        }
        None
    })
}

/// `Integer.parseInt` of a JSON number's text, which Gson reads without a '+' or leading zeros.
fn to_integer(source: &[u16]) -> Option<i32> {
    String::from_utf16(source).ok()?.parse().ok()
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

// `getValue`: an array is a tuple and an object a record, each key ranked before its value, as
// `UniqueString.uniqueStringOf` interns it.
fn from_json(store: &mut Store, json: Json) -> Outcome<Id> {
    match json {
        Json::Bool(value) => Ok(if value { TRUE } else { FALSE }),
        Json::Number(source) => store.int(i64::from(to_integer(&source).ok_or(JSON_UNCONVERTED)?)),
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
        Json::Null => Err(JSON_UNCONVERTED),
    }
}

/// `Json.deserialize`'s value of a file's text.
pub fn read_json(store: &mut Store, text: &[u16]) -> Outcome<Id> {
    check_byte_order_marks(text)?;
    from_json(store, parse_json(text).map_err(|_| JSON_UNPARSED)?)
}

/// `Json.ndDeserialize`'s value of a file's text: each line that isn't empty once trimmed, read
/// as JSON and converted before the next is read, in a tuple.
pub fn read_nd_json(store: &mut Store, text: &[u16]) -> Outcome<Id> {
    let mut values = Vec::new();
    for line in lines(text) {
        check_byte_order_marks(line)?;
        values.push(from_json(
            store,
            parse_json(line).map_err(|_| JSON_UNPARSED)?,
        )?);
    }
    Ok(store.tuple_of(&values))
}

/// The text `Json.deserialize` and `Json.ndDeserialize` read from a file's bytes: a `FileReader`'s,
/// whose `StreamDecoder` decodes with the default charset, UTF-8 on Java 18 and later, and replaces
/// each malformed sequence with one U+FFFD (`CodingErrorAction.REPLACE`). Java's decoder
/// (`sun.nio.cs.UTF_8.Decoder.decodeArrayLoop`) measures a malformed sequence otherwise than
/// `String::from_utf8_lossy`: it takes a UTF-8-encoded surrogate (`ED A0 80`) as one malformed
/// sequence of three bytes, and `ED` and a continuation byte before a byte that doesn't continue as
/// one of two, where Rust replaces each byte. A sequence the input ends in the middle of is one
/// malformed sequence of what is left (`CharsetDecoder.decode` at the end of input). The stream
/// decodes the same bytes in chunks alike, as the decoder waits for the rest of a sequence a chunk
/// cuts.
pub fn decode_file_text(bytes: &[u8]) -> Vec<u16> {
    const REPLACEMENT: u16 = 0xFFFD;
    let is_continuation = |byte: u8| byte & 0xC0 == 0x80;
    let mut text = Vec::with_capacity(bytes.len());
    let mut at = 0;
    while at < bytes.len() {
        let rest = &bytes[at..];
        let b1 = rest[0];
        // How many bytes a character or a malformed sequence takes, and the character.
        let (taken, unit): (usize, Option<u32>) = match b1 {
            0x00..=0x7F => (1, Some(u32::from(b1))),
            0xC2..=0xDF => match rest.get(1) {
                None => (1, None),
                Some(&b2) if !is_continuation(b2) => (1, None),
                Some(&b2) => (2, Some(u32::from(b1 & 0x1F) << 6 | u32::from(b2 & 0x3F))),
            },
            0xE0..=0xEF => {
                // `isMalformed3`, `isMalformed3_2`: an overlong E0 or a second byte that doesn't
                // continue is malformed at the first byte.
                let is_bad_second =
                    |b2: u8| (b1 == 0xE0 && b2 & 0xE0 == 0x80) || !is_continuation(b2);
                match (rest.get(1), rest.get(2)) {
                    (Some(&b2), _) if is_bad_second(b2) => (1, None),
                    (Some(_), None) | (None, _) => (rest.len(), None),
                    (Some(_), Some(&b3)) if !is_continuation(b3) => (2, None),
                    (Some(&b2), Some(&b3)) => {
                        let unit = u32::from(b1 & 0x0F) << 12
                            | u32::from(b2 & 0x3F) << 6
                            | u32::from(b3 & 0x3F);
                        // A surrogate is malformed for all three bytes.
                        if (0xD800..=0xDFFF).contains(&unit) {
                            (3, None)
                        } else {
                            (3, Some(unit))
                        }
                    }
                }
            }
            0xF0..=0xF7 => {
                // `malformedN(src, 4)` and `isMalformed4_2`: a first byte past F4, or a second
                // byte out of its range, is malformed at the first byte.
                let is_bad_second = |b2: u8| {
                    b1 > 0xF4
                        || (b1 == 0xF0 && !(0x90..=0xBF).contains(&b2))
                        || (b1 == 0xF4 && b2 & 0xF0 != 0x80)
                        || !is_continuation(b2)
                };
                match (rest.get(1), rest.get(2), rest.get(3)) {
                    _ if b1 > 0xF4 => (1, None),
                    (Some(&b2), _, _) if is_bad_second(b2) => (1, None),
                    (Some(_), Some(&b3), _) if !is_continuation(b3) => (2, None),
                    (Some(_), Some(_), Some(&b4)) if !is_continuation(b4) => (3, None),
                    (Some(&b2), Some(&b3), Some(&b4)) => (
                        4,
                        Some(
                            u32::from(b1 & 0x07) << 18
                                | u32::from(b2 & 0x3F) << 12
                                | u32::from(b3 & 0x3F) << 6
                                | u32::from(b4 & 0x3F),
                        ),
                    ),
                    _ => (rest.len(), None),
                }
            }
            // C0, C1, a continuation byte, F8 to FF.
            _ => (1, None),
        };
        match unit {
            Some(unit) if unit >= 0x10000 => {
                let unit = unit - 0x10000;
                text.push(0xD800 | (unit >> 10) as u16);
                text.push(0xDC00 | (unit & 0x3FF) as u16);
            }
            Some(unit) => text.push(unit as u16),
            None => text.push(REPLACEMENT),
        }
        at += taken;
    }
    text
}

#[cfg(test)]
mod tests {
    use super::decode_file_text;

    fn decoded(bytes: &[u8]) -> Vec<u16> {
        decode_file_text(bytes)
    }

    // Each case as Java 21's `FileReader` reads the bytes from a file, recorded with the pinned
    // JDK.
    #[test]
    fn decodes_malformed_input_as_java_reads_a_file() {
        let fffd = 0xFFFD;
        let cases: &[(&[u8], &[u16])] = &[
            (b"'\xED\xA0\x80'", &[0x27, fffd, 0x27]),
            (b"\"\xED\xA0\x80\"", &[0x22, fffd, 0x22]),
            (b"\xED\xA0A", &[fffd, 0x41]),
            (b"\xED\xA0", &[fffd]),
            (b"\xE0\x80\x80", &[fffd, fffd, fffd]),
            (b"\xE0\xA0A", &[fffd, 0x41]),
            (b"\xF0\x9F\x98\x80", &[0xD83D, 0xDE00]),
            (b"\xF0\x9F\x98", &[fffd]),
            (b"\xF0\x9FA", &[fffd, 0x41]),
            (b"\xF0\x8F\x80\x80", &[fffd, fffd, fffd, fffd]),
            (b"\xF4\x90\x80\x80", &[fffd, fffd, fffd, fffd]),
            (b"\xF5\x80\x80\x80", &[fffd, fffd, fffd, fffd]),
            (b"\xC0\x80", &[fffd, fffd]),
            (b"\xC2", &[fffd]),
            (b"\xFFa", &[fffd, 0x61]),
            ("é€".as_bytes(), &[0xE9, 0x20AC]),
        ];
        for (bytes, expected) in cases {
            assert_eq!(decoded(bytes), *expected, "{bytes:02X?}");
        }
    }

    // Valid UTF-8 decodes as Rust decodes it.
    #[test]
    fn decodes_valid_utf8_as_rust_does() {
        let text = "a\u{7F}\u{80}\u{7FF}\u{800}\u{D7FF}\u{E000}\u{FFFF}\u{10000}\u{10FFFF}";
        assert_eq!(
            decoded(text.as_bytes()),
            text.encode_utf16().collect::<Vec<_>>()
        );
    }
}

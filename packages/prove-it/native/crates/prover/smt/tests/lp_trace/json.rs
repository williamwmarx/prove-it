//! A JSON value and a parser for the lines of an `.lptrace`, with the standard library only.

use std::fmt;

#[derive(Clone, Debug)]
pub enum Value {
    Null,
    Bool(bool),
    Number(f64),
    String(String),
    Array(Vec<Value>),
    // In the order of the text, as `JSON.stringify` writes the fields.
    Object(Vec<(String, Value)>),
}

impl Value {
    pub fn get(&self, key: &str) -> Option<&Value> {
        match self {
            Value::Object(fields) => fields
                .iter()
                .find(|field| field.0 == key)
                .map(|field| &field.1),
            _ => None,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Value::String(text) => Some(text),
            _ => None,
        }
    }

    pub fn as_array(&self) -> Option<&[Value]> {
        match self {
            Value::Array(items) => Some(items),
            _ => None,
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(value) => Some(*value),
            _ => None,
        }
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Value::Number(value) => Some(*value),
            _ => None,
        }
    }
}

// Objects are equal when they have the same fields, whatever their order.
impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Null, Value::Null) => true,
            (Value::Bool(left), Value::Bool(right)) => left == right,
            (Value::Number(left), Value::Number(right)) => left == right,
            (Value::String(left), Value::String(right)) => left == right,
            (Value::Array(left), Value::Array(right)) => left == right,
            (Value::Object(left), Value::Object(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .all(|field| other.get(&field.0) == Some(&field.1))
            }
            _ => false,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Null => write!(formatter, "null"),
            Value::Bool(value) => write!(formatter, "{value}"),
            Value::Number(value) => write!(formatter, "{value}"),
            Value::String(text) => write!(formatter, "{text:?}"),
            Value::Array(items) => {
                write!(formatter, "[")?;
                for (index, item) in items.iter().enumerate() {
                    if index > 0 {
                        write!(formatter, ",")?;
                    }
                    write!(formatter, "{item}")?;
                }
                write!(formatter, "]")
            }
            Value::Object(fields) => {
                write!(formatter, "{{")?;
                for (index, field) in fields.iter().enumerate() {
                    if index > 0 {
                        write!(formatter, ",")?;
                    }
                    write!(formatter, "{:?}:{}", field.0, field.1)?;
                }
                write!(formatter, "}}")
            }
        }
    }
}

pub fn parse(text: &str) -> Result<Value, String> {
    let mut parser = Parser {
        bytes: text.as_bytes(),
        position: 0,
    };
    let value = parser.parse_value()?;
    parser.skip_whitespace();
    if parser.position != parser.bytes.len() {
        return Err(format!("trailing text at {}", parser.position));
    }
    Ok(value)
}

struct Parser<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl Parser<'_> {
    fn skip_whitespace(&mut self) {
        while self
            .bytes
            .get(self.position)
            .is_some_and(u8::is_ascii_whitespace)
        {
            self.position += 1;
        }
    }

    fn expect(&mut self, byte: u8) -> Result<(), String> {
        self.skip_whitespace();
        if self.bytes.get(self.position) != Some(&byte) {
            return Err(format!("expected '{}' at {}", byte as char, self.position));
        }
        self.position += 1;
        Ok(())
    }

    fn peek(&mut self) -> Option<u8> {
        self.skip_whitespace();
        self.bytes.get(self.position).copied()
    }

    fn parse_literal(&mut self, literal: &str, value: Value) -> Result<Value, String> {
        if !self.bytes[self.position..].starts_with(literal.as_bytes()) {
            return Err(format!("unexpected text at {}", self.position));
        }
        self.position += literal.len();
        Ok(value)
    }

    fn parse_value(&mut self) -> Result<Value, String> {
        match self.peek() {
            Some(b'{') => {
                self.position += 1;
                let mut fields = Vec::new();
                if self.peek() == Some(b'}') {
                    self.position += 1;
                    return Ok(Value::Object(fields));
                }
                loop {
                    self.skip_whitespace();
                    let key = self.parse_string()?;
                    self.expect(b':')?;
                    fields.push((key, self.parse_value()?));
                    match self.peek() {
                        Some(b',') => self.position += 1,
                        _ => break,
                    }
                }
                self.expect(b'}')?;
                Ok(Value::Object(fields))
            }
            Some(b'[') => {
                self.position += 1;
                let mut items = Vec::new();
                if self.peek() == Some(b']') {
                    self.position += 1;
                    return Ok(Value::Array(items));
                }
                loop {
                    items.push(self.parse_value()?);
                    match self.peek() {
                        Some(b',') => self.position += 1,
                        _ => break,
                    }
                }
                self.expect(b']')?;
                Ok(Value::Array(items))
            }
            Some(b'"') => Ok(Value::String(self.parse_string()?)),
            Some(b't') => self.parse_literal("true", Value::Bool(true)),
            Some(b'f') => self.parse_literal("false", Value::Bool(false)),
            Some(b'n') => self.parse_literal("null", Value::Null),
            Some(_) => self.parse_number(),
            None => Err("unexpected end".into()),
        }
    }

    fn parse_number(&mut self) -> Result<Value, String> {
        let start = self.position;
        while self
            .bytes
            .get(self.position)
            .is_some_and(|byte| byte.is_ascii_digit() || b"+-.eE".contains(byte))
        {
            self.position += 1;
        }
        let text = std::str::from_utf8(&self.bytes[start..self.position])
            .map_err(|error| error.to_string())?;
        text.parse()
            .map(Value::Number)
            .map_err(|_| format!("bad number {text:?} at {start}"))
    }

    fn parse_string(&mut self) -> Result<String, String> {
        if self.bytes.get(self.position) != Some(&b'"') {
            return Err(format!("expected a string at {}", self.position));
        }
        self.position += 1;
        let mut units: Vec<u16> = Vec::new();
        let mut result = String::new();
        loop {
            let byte = *self.bytes.get(self.position).ok_or("unterminated string")?;
            self.position += 1;
            if byte != b'\\' && !units.is_empty() {
                result.push_str(&String::from_utf16_lossy(&units));
                units.clear();
            }
            match byte {
                b'"' => return Ok(result),
                b'\\' => {
                    let escape = *self.bytes.get(self.position).ok_or("unterminated escape")?;
                    self.position += 1;
                    let character = match escape {
                        b'u' => {
                            let hex = self
                                .bytes
                                .get(self.position..self.position + 4)
                                .ok_or("short \\u escape")?;
                            self.position += 4;
                            let text =
                                std::str::from_utf8(hex).map_err(|error| error.to_string())?;
                            units.push(
                                u16::from_str_radix(text, 16).map_err(|error| error.to_string())?,
                            );
                            continue;
                        }
                        b'n' => '\n',
                        b't' => '\t',
                        b'r' => '\r',
                        b'b' => '\u{8}',
                        b'f' => '\u{c}',
                        other => other as char,
                    };
                    if !units.is_empty() {
                        result.push_str(&String::from_utf16_lossy(&units));
                        units.clear();
                    }
                    result.push(character);
                }
                _ => {
                    // Copy the whole UTF-8 sequence that starts here.
                    let start = self.position - 1;
                    let length = match byte {
                        0x00..=0x7f => 1,
                        0xc0..=0xdf => 2,
                        0xe0..=0xef => 3,
                        _ => 4,
                    };
                    self.position = start + length;
                    result.push_str(
                        std::str::from_utf8(&self.bytes[start..self.position])
                            .map_err(|error| error.to_string())?,
                    );
                }
            }
        }
    }
}

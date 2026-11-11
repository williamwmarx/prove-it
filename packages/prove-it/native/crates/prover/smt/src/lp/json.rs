//! The JSON of the LP call trace (`trace.rs`): a value, its text as JavaScript's `JSON.stringify`
//! writes it, and a parser, with the standard library only.

use std::fmt;

#[derive(Clone, Debug)]
pub enum Json {
    Null,
    Bool(bool),
    Number(f64),
    String(String),
    Array(Vec<Json>),
    // In insertion order, which is the order `JSON.stringify` writes the fields in.
    Object(Vec<(String, Json)>),
}

impl Json {
    /// An object of the fields, in order.
    pub fn object<const N: usize>(fields: [(&str, Json); N]) -> Json {
        Json::Object(
            fields
                .into_iter()
                .map(|field| (field.0.to_string(), field.1))
                .collect(),
        )
    }

    pub fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Object(fields) => fields
                .iter()
                .find(|field| field.0 == key)
                .map(|field| &field.1),
            _ => None,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Json::String(text) => Some(text),
            _ => None,
        }
    }

    pub fn as_array(&self) -> Option<&[Json]> {
        match self {
            Json::Array(items) => Some(items),
            _ => None,
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Json::Bool(value) => Some(*value),
            _ => None,
        }
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Json::Number(value) => Some(*value),
            _ => None,
        }
    }
}

// Objects are equal when they have the same fields, whatever their order.
impl PartialEq for Json {
    fn eq(&self, other: &Json) -> bool {
        match (self, other) {
            (Json::Null, Json::Null) => true,
            (Json::Bool(left), Json::Bool(right)) => left == right,
            (Json::Number(left), Json::Number(right)) => left == right,
            (Json::String(left), Json::String(right)) => left == right,
            (Json::Array(left), Json::Array(right)) => left == right,
            (Json::Object(left), Json::Object(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .all(|field| other.get(&field.0) == Some(&field.1))
            }
            _ => false,
        }
    }
}

/// A string as `JSON.stringify` quotes it: `"` and `\` escaped, the control characters with the
/// short escapes or `\u00xx`, everything else as it is.
fn write_string(formatter: &mut fmt::Formatter<'_>, text: &str) -> fmt::Result {
    formatter.write_str("\"")?;
    for character in text.chars() {
        match character {
            '"' => formatter.write_str("\\\"")?,
            '\\' => formatter.write_str("\\\\")?,
            '\u{8}' => formatter.write_str("\\b")?,
            '\u{c}' => formatter.write_str("\\f")?,
            '\n' => formatter.write_str("\\n")?,
            '\r' => formatter.write_str("\\r")?,
            '\t' => formatter.write_str("\\t")?,
            '\0'..='\u{1f}' => write!(formatter, "\\u{:04x}", u32::from(character))?,
            _ => write!(formatter, "{character}")?,
        }
    }
    formatter.write_str("\"")
}

/// A number as JavaScript's `Number.prototype.toString` writes it (ECMA-262 Number::toString),
/// which `JSON.stringify` uses for finite numbers; it writes the others as `null`.
fn write_number(formatter: &mut fmt::Formatter<'_>, value: f64) -> fmt::Result {
    if !value.is_finite() {
        return formatter.write_str("null");
    }
    if value == 0.0 {
        return formatter.write_str("0");
    }
    if value < 0.0 {
        formatter.write_str("-")?;
    }
    // The shortest digits that read back as the value, and the exponent of the first.
    let scientific = format!("{:e}", value.abs());
    let (mantissa, exponent) = scientific
        .split_once('e')
        .expect("an f64's LowerExp has an exponent");
    let digits = mantissa.replace('.', "");
    let count = digits.len() as i64;
    let point = exponent
        .parse::<i64>()
        .expect("an f64's LowerExp exponent is a number")
        + 1;
    if count <= point && point <= 21 {
        return write!(
            formatter,
            "{digits}{}",
            "0".repeat((point - count) as usize)
        );
    }
    if 0 < point && point <= 21 {
        let (whole, fraction) = digits.split_at(point as usize);
        return write!(formatter, "{whole}.{fraction}");
    }
    if -6 < point && point <= 0 {
        return write!(formatter, "0.{}{digits}", "0".repeat((-point) as usize));
    }
    let sign = if point - 1 < 0 { '-' } else { '+' };
    let (first, rest) = digits.split_at(1);
    let fraction = if rest.is_empty() {
        String::new()
    } else {
        format!(".{rest}")
    };
    write!(formatter, "{first}{fraction}e{sign}{}", (point - 1).abs())
}

/// The text `JSON.stringify` writes for the value: no spaces, fields in order.
impl fmt::Display for Json {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Json::Null => formatter.write_str("null"),
            Json::Bool(value) => write!(formatter, "{value}"),
            Json::Number(value) => write_number(formatter, *value),
            Json::String(text) => write_string(formatter, text),
            Json::Array(items) => {
                formatter.write_str("[")?;
                for (index, item) in items.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(",")?;
                    }
                    write!(formatter, "{item}")?;
                }
                formatter.write_str("]")
            }
            Json::Object(fields) => {
                formatter.write_str("{")?;
                for (index, field) in fields.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(",")?;
                    }
                    write_string(formatter, &field.0)?;
                    write!(formatter, ":{}", field.1)?;
                }
                formatter.write_str("}")
            }
        }
    }
}

pub fn parse(text: &str) -> Result<Json, String> {
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

    fn parse_literal(&mut self, literal: &str, value: Json) -> Result<Json, String> {
        if !self.bytes[self.position..].starts_with(literal.as_bytes()) {
            return Err(format!("unexpected text at {}", self.position));
        }
        self.position += literal.len();
        Ok(value)
    }

    fn parse_value(&mut self) -> Result<Json, String> {
        match self.peek() {
            Some(b'{') => {
                self.position += 1;
                let mut fields = Vec::new();
                if self.peek() == Some(b'}') {
                    self.position += 1;
                    return Ok(Json::Object(fields));
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
                Ok(Json::Object(fields))
            }
            Some(b'[') => {
                self.position += 1;
                let mut items = Vec::new();
                if self.peek() == Some(b']') {
                    self.position += 1;
                    return Ok(Json::Array(items));
                }
                loop {
                    items.push(self.parse_value()?);
                    match self.peek() {
                        Some(b',') => self.position += 1,
                        _ => break,
                    }
                }
                self.expect(b']')?;
                Ok(Json::Array(items))
            }
            Some(b'"') => Ok(Json::String(self.parse_string()?)),
            Some(b't') => self.parse_literal("true", Json::Bool(true)),
            Some(b'f') => self.parse_literal("false", Json::Bool(false)),
            Some(b'n') => self.parse_literal("null", Json::Null),
            Some(_) => self.parse_number(),
            None => Err("unexpected end".into()),
        }
    }

    fn parse_number(&mut self) -> Result<Json, String> {
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
            .map(Json::Number)
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

#[cfg(test)]
mod tests {
    use super::{Json, parse};

    // The expected texts are what `JSON.stringify` writes under Bun 1.4.4 and Node 22.
    #[test]
    fn writes_strings_as_json_stringify() {
        let cases = [
            ("plain", r#""plain""#),
            (
                "quote \" and backslash \\",
                r#""quote \" and backslash \\""#,
            ),
            ("\u{8}\u{c}\n\r\t", r#""\b\f\n\r\t""#),
            ("\0\u{1}\u{1b}\u{1f}", r#""\u0000\u0001\u001b\u001f""#),
            ("\u{7f} é ∑ 𝔸 /", "\"\u{7f} é ∑ 𝔸 /\""),
        ];
        for case in cases {
            assert_eq!(Json::String(case.0.into()).to_string(), case.1);
        }
    }

    #[test]
    fn writes_numbers_as_json_stringify() {
        let cases = [
            (0.0, "0"),
            (-0.0, "0"),
            (7.0, "7"),
            (-1.0, "-1"),
            (9_007_199_254_740_993.0, "9007199254740992"),
            (1e21, "1e+21"),
            (123_456_789_012_345_680_000.0, "123456789012345680000"),
            (0.5, "0.5"),
            (-2.25, "-2.25"),
            (0.1 + 0.2, "0.30000000000000004"),
            (0.000_001, "0.000001"),
            (1e-7, "1e-7"),
            (1.5e-7, "1.5e-7"),
            (2.5e300, "2.5e+300"),
            (f64::NAN, "null"),
            (f64::INFINITY, "null"),
        ];
        for case in cases {
            assert_eq!(Json::Number(case.0).to_string(), case.1, "{}", case.0);
        }
    }

    #[test]
    fn writes_values_without_spaces_in_field_order() {
        let value = Json::object([
            ("c", Json::String("lar#0".into())),
            ("a", Json::Array(vec![Json::Number(1.0), Json::Null])),
            ("r", Json::object([("b", Json::Bool(true))])),
        ]);
        assert_eq!(
            value.to_string(),
            r#"{"c":"lar#0","a":[1,null],"r":{"b":true}}"#
        );
    }

    #[test]
    fn parses_what_it_writes() {
        let text =
            r#"{"s":"a\"\\\n\u0001é𝔸","n":[-1.5e-7,1e+21,3],"o":{"t":true,"f":false,"z":null}}"#;
        let value = parse(text).expect("the text is JSON");
        assert_eq!(value.to_string(), text);
        assert_eq!(parse(&value.to_string()), Ok(value));
    }

    #[test]
    fn compares_objects_whatever_their_field_order() {
        assert_eq!(parse(r#"{"a":1,"b":[2]}"#), parse(r#"{"b":[2.0],"a":1e0}"#));
        assert_ne!(parse(r#"{"a":1}"#), parse(r#"{"a":1,"b":2}"#));
    }
}

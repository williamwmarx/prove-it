//! Just enough JSON for the lines of a store trace and a state log. Strings are kept as UTF-16
//! code units, as JavaScript wrote them, so an unpaired surrogate escaped as `\udXXX` survives.

#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Number(f64),
    String(Vec<u16>),
    Array(Vec<Json>),
    Object(Vec<(String, Json)>),
}

impl Json {
    pub fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Object(fields) => fields
                .iter()
                .find(|(name, _)| name == key)
                .map(|(_, value)| value),
            _ => None,
        }
    }

    pub fn as_array(&self) -> Option<&[Json]> {
        match self {
            Json::Array(items) => Some(items),
            _ => None,
        }
    }

    pub fn as_number(&self) -> Option<f64> {
        match self {
            Json::Number(number) => Some(*number),
            _ => None,
        }
    }

    pub fn as_text(&self) -> Option<&[u16]> {
        match self {
            Json::String(units) => Some(units),
            _ => None,
        }
    }
}

pub fn parse(text: &str) -> Result<Json, String> {
    let mut parser = Parser {
        bytes: text.as_bytes(),
        index: 0,
    };
    let value = parser.value()?;
    parser.space();
    if parser.index != parser.bytes.len() {
        return Err(format!("text after the value at {}", parser.index));
    }
    Ok(value)
}

struct Parser<'a> {
    bytes: &'a [u8],
    index: usize,
}

impl Parser<'_> {
    fn space(&mut self) {
        while self.index < self.bytes.len()
            && matches!(self.bytes[self.index], b' ' | b'\t' | b'\n' | b'\r')
        {
            self.index += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.index).copied()
    }

    fn expect(&mut self, byte: u8) -> Result<(), String> {
        self.space();
        if self.peek() == Some(byte) {
            self.index += 1;
            Ok(())
        } else {
            Err(format!("expected {} at {}", byte as char, self.index))
        }
    }

    fn literal(&mut self, word: &str, value: Json) -> Result<Json, String> {
        if self.bytes[self.index..].starts_with(word.as_bytes()) {
            self.index += word.len();
            Ok(value)
        } else {
            Err(format!("unexpected text at {}", self.index))
        }
    }

    fn value(&mut self) -> Result<Json, String> {
        self.space();
        match self.peek() {
            Some(b'n') => self.literal("null", Json::Null),
            Some(b't') => self.literal("true", Json::Bool(true)),
            Some(b'f') => self.literal("false", Json::Bool(false)),
            Some(b'"') => Ok(Json::String(self.string()?)),
            Some(b'[') => {
                self.index += 1;
                let mut items = Vec::new();
                self.space();
                if self.peek() == Some(b']') {
                    self.index += 1;
                    return Ok(Json::Array(items));
                }
                loop {
                    items.push(self.value()?);
                    self.space();
                    match self.peek() {
                        Some(b',') => self.index += 1,
                        Some(b']') => {
                            self.index += 1;
                            return Ok(Json::Array(items));
                        }
                        _ => return Err(format!("expected , or ] at {}", self.index)),
                    }
                }
            }
            Some(b'{') => {
                self.index += 1;
                let mut fields = Vec::new();
                self.space();
                if self.peek() == Some(b'}') {
                    self.index += 1;
                    return Ok(Json::Object(fields));
                }
                loop {
                    self.space();
                    let name = String::from_utf16_lossy(&self.string()?);
                    self.expect(b':')?;
                    fields.push((name, self.value()?));
                    self.space();
                    match self.peek() {
                        Some(b',') => self.index += 1,
                        Some(b'}') => {
                            self.index += 1;
                            return Ok(Json::Object(fields));
                        }
                        _ => return Err(format!("expected , or }} at {}", self.index)),
                    }
                }
            }
            Some(_) => self.number(),
            None => Err("the line ends before a value".into()),
        }
    }

    fn number(&mut self) -> Result<Json, String> {
        let start = self.index;
        while self.index < self.bytes.len()
            && matches!(
                self.bytes[self.index],
                b'-' | b'+' | b'.' | b'e' | b'E' | b'0'..=b'9'
            )
        {
            self.index += 1;
        }
        let text = std::str::from_utf8(&self.bytes[start..self.index])
            .map_err(|error| error.to_string())?;
        text.parse::<f64>()
            .map(Json::Number)
            .map_err(|_| format!("not a number at {start}: {text:?}"))
    }

    fn hex(&mut self) -> Result<u16, String> {
        let digits = self
            .bytes
            .get(self.index..self.index + 4)
            .ok_or("a short escape")?;
        self.index += 4;
        u16::from_str_radix(
            std::str::from_utf8(digits).map_err(|error| error.to_string())?,
            16,
        )
        .map_err(|error| error.to_string())
    }

    fn string(&mut self) -> Result<Vec<u16>, String> {
        if self.peek() != Some(b'"') {
            return Err(format!("expected a string at {}", self.index));
        }
        self.index += 1;
        let mut units = Vec::new();
        loop {
            let start = self.index;
            while self.index < self.bytes.len() && !matches!(self.bytes[self.index], b'"' | b'\\') {
                self.index += 1;
            }
            let run = std::str::from_utf8(&self.bytes[start..self.index])
                .map_err(|error| error.to_string())?;
            units.extend(run.encode_utf16());
            match self.peek() {
                Some(b'"') => {
                    self.index += 1;
                    return Ok(units);
                }
                Some(b'\\') => {
                    self.index += 1;
                    let escape = self.peek().ok_or("an escape at the end")?;
                    self.index += 1;
                    units.push(match escape {
                        b'"' => u16::from(b'"'),
                        b'\\' => u16::from(b'\\'),
                        b'/' => u16::from(b'/'),
                        b'b' => 8,
                        b'f' => 12,
                        b'n' => u16::from(b'\n'),
                        b'r' => u16::from(b'\r'),
                        b't' => u16::from(b'\t'),
                        b'u' => self.hex()?,
                        _ => return Err(format!("an unknown escape at {}", self.index)),
                    });
                }
                _ => return Err("the line ends inside a string".into()),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_what_json_stringify_writes() {
        let value =
            parse(r#"["str",["a\"b\\é\ud800é"],{"bail":"x"}, -1.5e3, null, true]"#).unwrap();
        let items = value.as_array().unwrap();
        let mut text: Vec<u16> = "a\"b\\é".encode_utf16().collect();
        text.push(0xd800);
        text.extend("é".encode_utf16());
        assert_eq!(items[1], Json::Array(vec![Json::String(text)]));
        assert_eq!(
            items[2].get("bail"),
            Some(&Json::String("x".encode_utf16().collect()))
        );
        assert_eq!(items[3], Json::Number(-1500.0));
        assert_eq!(items[4], Json::Null);
        assert!(parse("[1,").is_err());
        assert!(parse("[1] 2").is_err());
    }
}

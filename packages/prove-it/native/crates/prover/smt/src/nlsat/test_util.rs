//! What the ported tests of `tests/unit/smt-nlsat.test.ts` share: reading its fixtures.

use std::fs;
use std::path::PathBuf;

/// The `[input, expected]` pairs of `tests/fixtures/nlsat/<name>`.
pub fn read_fixture(name: &str) -> Vec<(String, String)> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../../../tests/fixtures/nlsat")
        .join(name);
    let text = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("reading {}: {error}", path.display()));
    let mut parser = JsonParser {
        bytes: text.as_bytes(),
        position: 0,
    };
    let mut pairs = Vec::new();
    parser.expect(b'[');
    if parser.peek() == b']' {
        return pairs;
    }
    loop {
        parser.expect(b'[');
        let input = parser.parse_string();
        parser.expect(b',');
        let expected = parser.parse_string();
        parser.expect(b']');
        pairs.push((input, expected));
        if parser.peek() == b']' {
            return pairs;
        }
        parser.expect(b',');
    }
}

struct JsonParser<'text> {
    bytes: &'text [u8],
    position: usize,
}

impl JsonParser<'_> {
    fn peek(&mut self) -> u8 {
        while self.bytes[self.position].is_ascii_whitespace() {
            self.position += 1;
        }
        self.bytes[self.position]
    }

    fn expect(&mut self, byte: u8) {
        assert_eq!(self.peek(), byte, "fixture JSON at byte {}", self.position);
        self.position += 1;
    }

    fn parse_string(&mut self) -> String {
        self.expect(b'"');
        let mut text = Vec::new();
        loop {
            let byte = self.bytes[self.position];
            self.position += 1;
            match byte {
                b'"' => return String::from_utf8(text).expect("fixture strings are UTF-8"),
                b'\\' => {
                    let escaped = self.bytes[self.position];
                    self.position += 1;
                    match escaped {
                        b'n' => text.push(b'\n'),
                        b't' => text.push(b'\t'),
                        b'"' | b'\\' | b'/' => text.push(escaped),
                        b'u' => {
                            let hex =
                                std::str::from_utf8(&self.bytes[self.position..self.position + 4])
                                    .expect("hex digits");
                            self.position += 4;
                            let code = u32::from_str_radix(hex, 16).expect("a \\u escape");
                            let character = char::from_u32(code).expect("a BMP scalar");
                            text.extend_from_slice(character.to_string().as_bytes());
                        }
                        other => panic!("unexpected escape \\{}", other as char),
                    }
                }
                _ => text.push(byte),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::read_fixture;

    #[test]
    fn reads_every_fixture() {
        for name in ["polynomial.json", "upolynomial.json", "search.json"] {
            assert!(!read_fixture(name).is_empty(), "{name}");
        }
    }
}

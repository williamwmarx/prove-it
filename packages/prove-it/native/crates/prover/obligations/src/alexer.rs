//! What tlapm's lexer (`src/alexer.mll`) reads into OCaml ints, which tla-front's tokens don't
//! show: the `\b`, `\o` and `\h` numerals it converts with `int_of_string` (alexer.mll:105-113)
//! and the levels of step numbers (alexer.mll:92-93). `int_of_string` raises `Failure
//! "int_of_string"` past OCaml's ints, and nothing in the lexer catches it: `lex_string` catches
//! only the lexer's own `Error` (alexer.mll:299-307), `LazyList.make` forces one token at a time
//! (pars/lazyList.ml:137-141), and the parser lets it through to tlapm's top level
//! (tlapm_lib.ml:645-668). So it ends the run where the parser first reads that token.
//!
//! This walks the source as the lexer's rules do, up to where tlapm's parser stops reading: the
//! `====` that closes the module, a TAB, or a character no rule matches, each of which ends the
//! lexer's tokens.

use crate::ocaml::int_of_string;

/// A place in the source: its line from 1, and its column from 1 in UTF-16 code units, as
/// tla-front's tokens and failures count them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Place {
    pub line: u32,
    pub column: u32,
}

// The operators and punctuation of the `token` rule (alexer.mll:79-149), longest first where one
// begins another. Those that begin with a letter or `\` and a letter are read as `\` and a name,
// which reads the same characters; `\b`, `\o` and `\h` before a digit are numerals.
const SYMBOLS: [&str; 74] = [
    "(\\X)", "-+->", "|->", ">>_", "<=>", "::=", "...", "(+)", "(-)", "(/)", "(.)", "(*{", "}*)",
    "<*>", "<+>", "<<", ">>", "]_", "==", "::", "->", "<-", "[]", "-.", "<>", "^+", "^*", "^#",
    ">=", "<=", "=<", "/=", "=>", "~>", "/\\", "\\/", "-|", ":=", "=|", "|-", "|=", "@@", ":>",
    "<:", "..", "!!", "##", "$$", "??", "++", "%%", "||", "--", "&&", "**", "//", "^^", ",", ".",
    "_", "(", ")", "[", "]", "{", "}", "!", "@", ":", ";", "~", "'", "#", "<",
];

// The rest of the one-character symbols.
const SINGLE: &[u8] = b"=>\\$+%|-&*/^";

struct Lexer<'a> {
    units: &'a [u16],
    index: usize,
    line: u32,
    line_start: usize,
    failure: Option<Place>,
    depth: usize,
    // The last token was ----, which opens a module before MODULE.
    is_after_dashes: bool,
}

fn is_unit(unit: Option<&u16>, byte: u8) -> bool {
    unit == Some(&u16::from(byte))
}

fn get_byte(unit: Option<&u16>) -> Option<u8> {
    unit.and_then(|&unit| u8::try_from(unit).ok())
        .filter(u8::is_ascii)
}

fn is_name_unit(unit: Option<&u16>) -> bool {
    get_byte(unit).is_some_and(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

impl Lexer<'_> {
    fn at(&self, offset: usize) -> Option<&u16> {
        self.units.get(self.index + offset)
    }

    fn starts_with(&self, text: &str) -> bool {
        text.bytes()
            .enumerate()
            .all(|(offset, byte)| is_unit(self.at(offset), byte))
    }

    fn place(&self) -> Place {
        Place {
            line: self.line,
            column: (self.index - self.line_start + 1) as u32,
        }
    }

    fn advance(&mut self, length: usize) {
        for _ in 0..length {
            if is_unit(self.at(0), b'\n') {
                self.line += 1;
                self.line_start = self.index + 1;
            }
            self.index += 1;
        }
    }

    fn count_while(&self, from: usize, predicate: impl Fn(Option<&u16>) -> bool) -> usize {
        (from..)
            .take_while(|offset| predicate(self.at(*offset)))
            .count()
    }

    // A comment, which ends at its closing *) and nests (alexer.mll:204-215). None where the lexer
    // stops: at a TAB, or at the end, where no rule matches.
    fn skip_comment(&mut self) -> Option<()> {
        let mut depth = 1;
        self.advance(2);
        while depth > 0 {
            if self.at(0).is_none() || is_unit(self.at(0), b'\t') {
                return None;
            }
            if self.starts_with("*)") {
                depth -= 1;
                self.advance(2);
            } else if self.starts_with("(*") {
                depth += 1;
                self.advance(2);
            } else {
                self.advance(1);
            }
        }
        Some(())
    }

    // A string, whose escapes hide a quote (alexer.mll:172-196). None where the lexer stops: at a
    // TAB, a line end, or the end.
    fn skip_string(&mut self) -> Option<()> {
        self.advance(1);
        loop {
            let unit = get_byte(self.at(0));
            match unit {
                None if self.at(0).is_some() => self.advance(1),
                None | Some(b'\t' | b'\n' | b'\r') => return None,
                Some(b'"') => {
                    self.advance(1);
                    return Some(());
                }
                Some(b'\\') => {
                    let is_octal = |offset| {
                        get_byte(self.at(offset)).is_some_and(|byte| (b'0'..=b'7').contains(&byte))
                    };
                    let length = match get_byte(self.at(1)) {
                        Some(b'"' | b'\\' | b't' | b'n' | b'f' | b'r') => 2,
                        _ if is_octal(1) && is_octal(2) && is_octal(3) => 4,
                        _ => 1,
                    };
                    self.advance(length);
                }
                Some(_) => self.advance(1),
            }
        }
    }

    // Reads an int as int_of_string does, and keeps where it first fails.
    fn read_int(&mut self, text: &str, start: Place) -> Option<i64> {
        let value = int_of_string(text);
        if value.is_none() {
            self.failure = Some(start);
        }
        value
    }

    // The length of the level of a step number such as <12>, or 0.
    fn get_level_length(&self) -> usize {
        let digits = self.count_while(1, |unit| get_byte(unit).is_some_and(|b| b.is_ascii_digit()));
        if digits > 0 && is_unit(self.at(1 + digits), b'>') {
            digits
        } else {
            0
        }
    }

    // A step number: <*>, <+>, or a level in <>, then a label and dots (alexer.mll:88-93).
    fn read_step(&mut self, digits: usize) -> Option<()> {
        let start = self.place();
        let mut length = 3;
        if digits > 0 {
            let text: String = self.units[self.index + 1..self.index + 1 + digits]
                .iter()
                .map(|&unit| char::from(unit as u8))
                .collect();
            self.read_int(&text, start)?;
            length = digits + 2;
            length += self.count_while(length, is_name_unit);
        }
        length += self.count_while(length, |unit| is_unit(unit, b'.'));
        self.advance(length);
        Some(())
    }

    // The length of the digits of \b, \o or \h (alexer.mll:105-113), and the prefix that gives
    // int_of_string their base.
    fn get_numeral(&self) -> (usize, &'static str) {
        let (prefix, radix) = match get_byte(self.at(1)) {
            Some(b'b') => ("0b", 2),
            Some(b'o') => ("0o", 8),
            Some(b'h') => ("0x", 16),
            _ => return (0, ""),
        };
        let digits = self.count_while(2, |unit| {
            get_byte(unit).is_some_and(|byte| char::from(byte).is_digit(radix))
        });
        (digits, prefix)
    }

    fn read_numeral(&mut self, digits: usize, prefix: &str) -> Option<()> {
        let start = self.place();
        let text: String = prefix
            .chars()
            .chain(
                self.units[self.index + 2..self.index + 2 + digits]
                    .iter()
                    .map(|&unit| char::from(unit as u8)),
            )
            .collect();
        self.read_int(&text, start)?;
        self.advance(2 + digits);
        Some(())
    }

    // One token, or None where the lexer stops or fails.
    fn read_token(&mut self) -> Option<()> {
        let unit = self.at(0)?;
        let byte = get_byte(Some(unit))?;
        let mut is_dashes = false;
        match byte {
            b' ' | b'\n' | b'\r' => {
                self.advance(1);
                return Some(());
            }
            b'\t' => return None,
            b'"' => self.skip_string()?,
            b'\\' if is_unit(self.at(1), b'*') => {
                // A line comment, to the line's end (alexer.mll:197-202).
                let length = self.count_while(2, |unit| {
                    !matches!(get_byte(unit), Some(b'\n' | b'\r')) && unit.is_some()
                });
                if (2..2 + length).any(|offset| is_unit(self.at(offset), b'\t'))
                    || self.at(2 + length).is_none()
                {
                    return None;
                }
                self.advance(2 + length);
                return Some(());
            }
            b'(' if self.starts_with("(*") && !self.starts_with("(*{") => {
                self.skip_comment()?;
                return Some(());
            }
            b'-' if self.starts_with("----") => {
                let length = self.count_while(0, |unit| is_unit(unit, b'-'));
                self.advance(length);
                is_dashes = true;
            }
            b'=' if self.starts_with("====") => {
                let length = self.count_while(0, |unit| is_unit(unit, b'='));
                self.advance(length);
                self.depth -= 1;
                if self.depth == 0 {
                    return None;
                }
            }
            b'<' if self.get_level_length() > 0
                || self.starts_with("<*>")
                || self.starts_with("<+>") =>
            {
                self.read_step(self.get_level_length())?;
            }
            b'\\' if self.get_numeral().0 > 0 => {
                let (digits, prefix) = self.get_numeral();
                self.read_numeral(digits, prefix)?;
            }
            _ if is_name_unit(Some(unit)) => {
                let length = self.count_while(0, is_name_unit);
                let is_module = self.units[self.index..self.index + length]
                    .iter()
                    .copied()
                    .eq("MODULE".encode_utf16());
                if is_module && self.is_after_dashes {
                    self.depth += 1;
                }
                self.advance(length);
            }
            _ => {
                let length = SYMBOLS
                    .iter()
                    .find(|symbol| self.starts_with(symbol))
                    .map(|symbol| symbol.len())
                    .or_else(|| SINGLE.contains(&byte).then_some(1))?;
                self.advance(length);
            }
        }
        self.is_after_dashes = is_dashes;
        Some(())
    }
}

/// Where `int_of_string` first fails on a numeral or step number tlapm's lexer reads from the
/// source, which `start` (the first `----` of the header `---- MODULE`) begins.
pub fn find_int_failure(units: &[u16], start: usize) -> Option<Place> {
    let mut lexer = Lexer {
        units,
        index: start,
        line: 1 + units[..start].iter().filter(|&&unit| unit == 10).count() as u32,
        line_start: units[..start]
            .iter()
            .rposition(|&unit| unit == 10)
            .map_or(0, |newline| newline + 1),
        failure: None,
        depth: 1,
        is_after_dashes: false,
    };
    // The header the modfile rule reads (alexer.mll:51-53): ----, dashes, spaces and MODULE.
    let dashes = lexer.count_while(0, |unit| is_unit(unit, b'-'));
    let spaces = lexer.count_while(dashes, |unit| is_unit(unit, b' '));
    lexer.advance(dashes + spaces + "MODULE".len());
    while lexer.read_token().is_some() {}
    lexer.failure
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(body: &str) -> Option<Place> {
        let units: Vec<u16> = format!("---- MODULE M ----\n{body}\n====\n")
            .encode_utf16()
            .collect();
        find_int_failure(&units, 0)
    }

    fn failure(line: u32, column: u32) -> Option<Place> {
        Some(Place { line, column })
    }

    // Each rule of alexer.mll that reads an int, and those that hide one from it.
    #[test]
    fn finds_where_int_of_string_fails() {
        let cases = [
            ("x == \\h7FFFFFFFFFFFFFFF", None),
            ("x == \\h8000000000000000", failure(2, 6)),
            ("x == \\b1 + \\o1777777777777777777777", failure(2, 12)),
            ("x == \\o2000000000000000000000", failure(2, 6)),
            ("<4611686018427387903>1. TRUE", None),
            ("<4611686018427387904>1. TRUE", failure(2, 1)),
            ("BY <0000000000000000000000001>a", None),
            // An operator that ends in < or =, read whole, hides no step number.
            ("x =<99999999999999999999> y", None),
            ("x <<99999999999999999999>> y", None),
            ("x >=<99999999999999999999>a", failure(2, 5)),
            ("x <=<99999999999999999999>a", failure(2, 5)),
            ("x <99999999999999999999 > y", None),
            // /\ hides the \ of a numeral; \/ and \ alone do not.
            ("x /\\h8000000000000000", None),
            ("x \\/\\h8000000000000000", failure(2, 5)),
            ("x \\\\h8000000000000000", failure(2, 4)),
            // Names, comments and strings.
            ("x\\h8000000000000000", failure(2, 2)),
            ("\\H8000000000000000", None),
            ("(* (* *) \\h8000000000000000 *)", None),
            ("\\* \\h8000000000000000", None),
            ("\"\\\" \\h8000000000000000\"", None),
            ("\"\\\\\" \\h8000000000000000", failure(2, 6)),
            ("(*{ \\h8000000000000000 }*)", failure(2, 5)),
            // The lexer stops at a TAB, a character no rule reads, and a line end in a string.
            ("\t\\h8000000000000000", None),
            ("? \\h8000000000000000", None),
            ("é \\h8000000000000000", None),
            ("\"a\n\\h8000000000000000", None),
            ("?? \\h8000000000000000", failure(2, 4)),
        ];
        for (body, expected) in cases {
            assert_eq!(lex(body), expected, "{body}");
        }
    }

    #[test]
    fn stops_at_the_end_of_the_module() {
        let lexed = |source: &str| {
            let units: Vec<u16> = source.encode_utf16().collect();
            find_int_failure(&units, source.find("----").unwrap_or(0))
        };
        assert_eq!(
            lexed("x\n---- MODULE M ----\n====\n\\h8000000000000000"),
            None
        );
        assert_eq!(
            lexed("---- MODULE M ----\n----\nMODULE N ----\n====\n\\h8000000000000000\n====\n"),
            failure(5, 1)
        );
        assert_eq!(
            lexed("---- MODULE M ----\n----\n\\h8000000000000000\n====\n"),
            failure(3, 1)
        );
    }
}

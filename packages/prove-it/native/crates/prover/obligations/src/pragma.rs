//! tlapm's method pragmas: the new `(*{ by (prover:"zenon"; timeout:@) }*)` after a definition,
//! which `E_parser.read_new_method` reads into a Bpragma, and the old `(*{ by (zenon) }*)` of
//! Method_prs. A port of `src/obligations/pragma.ts`.
//!
//! The source's lines are UTF-16 code units (any `AsRef<[u16]>`), so columns count as the
//! TypeScript's string indices do.

use crate::errors::{ObligationError, Result};
use crate::source::get_lexed_numeral;

#[derive(Clone, Debug, PartialEq)]
pub enum PragmaValue {
    Default,
    String(String),
    Float(f64),
}

#[derive(Clone, Debug, PartialEq)]
pub struct PragmaSetting {
    pub hint: String,
    pub value: PragmaValue,
}

/// A place in the source: `line` counts from 0 and `column` counts UTF-16 code units from 0.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Position {
    pub line: usize,
    pub column: usize,
}

#[derive(Clone, Debug, PartialEq)]
enum Token {
    Ident(String),
    String(String),
    Number(String),
    Punct(u8),
}

const PUNCTUATION: &[u8] = b"();:@,";

fn is_unit(unit: Option<&u16>, byte: u8) -> bool {
    unit == Some(&u16::from(byte))
}

fn is_blank(unit: Option<&u16>) -> bool {
    is_unit(unit, b' ') || is_unit(unit, b'\r') || is_unit(unit, b'\t')
}

fn skip_blanks<Line: AsRef<[u16]>>(lines: &[Line], position: &mut Position) {
    while let Some(line) = lines.get(position.line) {
        let line = line.as_ref();
        while is_blank(line.get(position.column)) {
            position.column += 1;
        }
        if position.column < line.len() {
            return;
        }
        position.line += 1;
        position.column = 0;
    }
}

fn get_units(text: &str) -> Vec<u16> {
    text.encode_utf16().collect()
}

/// Where the pragma after start opens, past blanks and line ends.
pub fn find_pragma<Line: AsRef<[u16]>>(lines: &[Line], start: Position) -> Option<Position> {
    let mut position = start;
    skip_blanks(lines, &mut position);
    lines
        .get(position.line)
        .and_then(|line| line.as_ref().get(position.column..))
        .is_some_and(|rest| rest.starts_with(&get_units("(*{")))
        .then_some(position)
}

fn is_ascii_unit(unit: u16, predicate: impl Fn(u8) -> bool) -> bool {
    u8::try_from(unit).is_ok_and(|byte| byte.is_ascii() && predicate(byte))
}

fn is_digit(unit: u16) -> bool {
    is_ascii_unit(unit, |byte| byte.is_ascii_digit())
}

fn get_digits_end(rest: &[u16], start: usize) -> usize {
    start
        + rest
            .get(start..)
            .unwrap_or(&[])
            .iter()
            .take_while(|&&unit| is_digit(unit))
            .count()
}

/// The length of `/^[A-Za-z_][A-Za-z0-9_]*/`'s match.
fn match_ident(rest: &[u16]) -> Option<usize> {
    let is_start = |byte: u8| byte.is_ascii_alphabetic() || byte == b'_';
    let is_part = |byte: u8| byte.is_ascii_alphanumeric() || byte == b'_';
    let first = *rest.first()?;
    is_ascii_unit(first, is_start).then(|| {
        1 + rest[1..]
            .iter()
            .take_while(|&&unit| is_ascii_unit(unit, is_part))
            .count()
    })
}

/// The length of `/^\d+(\.\d+)?/`'s match.
fn match_number(rest: &[u16]) -> Option<usize> {
    let whole = get_digits_end(rest, 0);
    if whole == 0 {
        return None;
    }
    if !is_unit(rest.get(whole), b'.') {
        return Some(whole);
    }
    let fraction = get_digits_end(rest, whole + 1);
    Some(if fraction > whole + 1 {
        fraction
    } else {
        whole
    })
}

/// A `\b`, `\o` or `\h` numeral's length and decimal value, as tlapm's lexer reads the
/// pragma's tokens (alexer.mll:105-113, `source::get_lexed_numeral`).
fn match_based_number(rest: &[u16]) -> Option<(usize, String)> {
    let radix = match u8::try_from(*rest.get(1)?).ok()? {
        b'b' => 2,
        b'o' => 8,
        b'h' => 16,
        _ => return None,
    };
    if !is_unit(rest.first(), b'\\') {
        return None;
    }
    let digits = rest[2..]
        .iter()
        .take_while(|&&unit| is_ascii_unit(unit, |byte| char::from(byte).is_digit(radix)))
        .count();
    let text = String::from_utf16_lossy(&rest[..2 + digits]);
    (digits > 0).then(|| (2 + digits, get_lexed_numeral(&text)))
}

fn is_line_terminator(unit: u16) -> bool {
    matches!(unit, 0x0a | 0x0d | 0x2028 | 0x2029)
}

/// The length of `/^"(\\.|[^"\\])*"/`'s match. Its alternatives start with different characters,
/// so it matches up to the first quote a backslash does not escape.
fn match_string(rest: &[u16]) -> Option<usize> {
    if !is_unit(rest.first(), b'"') {
        return None;
    }
    let mut index = 1;
    loop {
        let unit = *rest.get(index)?;
        if unit == u16::from(b'"') {
            return Some(index + 1);
        }
        if unit != u16::from(b'\\') {
            index += 1;
            continue;
        }
        if rest
            .get(index + 1)
            .is_none_or(|&next| is_line_terminator(next))
        {
            return None;
        }
        index += 2;
    }
}

fn get_syntax_error(message: &str) -> ObligationError {
    ObligationError::bug(format!("SyntaxError: JSON Parse error: {message}"))
}

/// `JSON.parse` of a literal `match_string` matched. JSON is stricter than the pattern, so
/// JSON.parse throws a SyntaxError on a control character or an escape JSON lacks. A lone
/// surrogate the literal escapes becomes U+FFFD, as a Rust string can't hold it.
fn parse_json_string(literal: &[u16]) -> Result<String> {
    let inner = literal
        .get(1..literal.len().saturating_sub(1))
        .unwrap_or(&[]);
    let mut value = Vec::with_capacity(inner.len());
    let mut index = 0;
    while let Some(&unit) = inner.get(index) {
        index += 1;
        if unit < 0x20 {
            return Err(get_syntax_error("Unterminated string"));
        }
        if unit != u16::from(b'\\') {
            value.push(unit);
            continue;
        }
        let escape = inner.get(index).copied().unwrap_or(0);
        index += 1;
        let escaped = match u8::try_from(escape).unwrap_or(0) {
            byte @ (b'"' | b'\\' | b'/') => u16::from(byte),
            b'b' => 0x08,
            b'f' => 0x0c,
            b'n' => 0x0a,
            b'r' => 0x0d,
            b't' => 0x09,
            b'u' => {
                let code = inner
                    .get(index..index + 4)
                    .filter(|hex| {
                        hex.iter()
                            .all(|&unit| is_ascii_unit(unit, |byte| byte.is_ascii_hexdigit()))
                    })
                    .and_then(|hex| u16::from_str_radix(&String::from_utf16_lossy(hex), 16).ok())
                    .ok_or_else(|| get_syntax_error("Invalid escape character u"))?;
                index += 4;
                code
            }
            _ => return Err(get_syntax_error("Invalid escape character")),
        };
        value.push(escaped);
    }
    Ok(String::from_utf16_lossy(&value))
}

fn tokenize_pragma<Line: AsRef<[u16]>>(
    lines: &[Line],
    start: Position,
) -> Result<Option<Vec<Token>>> {
    let Some(open) = find_pragma(lines, start) else {
        return Ok(None);
    };
    let closing = get_units("}*)");
    let mut position = Position {
        line: open.line,
        column: open.column + 3,
    };
    let mut tokens = Vec::new();
    skip_blanks(lines, &mut position);
    while let Some(line) = lines.get(position.line) {
        let rest = line.as_ref().get(position.column..).unwrap_or(&[]);
        if rest.starts_with(&closing) {
            return Ok(Some(tokens));
        }
        if let Some((length, decimal)) = match_based_number(rest) {
            tokens.push(Token::Number(decimal));
            position.column += length;
            skip_blanks(lines, &mut position);
            continue;
        }
        let length = match_ident(rest)
            .or_else(|| match_number(rest))
            .or_else(|| match_string(rest));
        if let Some(length) = length {
            let text = &rest[..length];
            tokens.push(if is_unit(text.first(), b'"') {
                Token::String(parse_json_string(text)?)
            } else if text.first().is_some_and(|&unit| is_digit(unit)) {
                Token::Number(String::from_utf16_lossy(text))
            } else {
                Token::Ident(String::from_utf16_lossy(text))
            });
            position.column += length;
            skip_blanks(lines, &mut position);
            continue;
        }
        let Some(punctuation) = rest
            .first()
            .and_then(|&unit| u8::try_from(unit).ok())
            .filter(|byte| PUNCTUATION.contains(byte))
        else {
            return Ok(None);
        };
        tokens.push(Token::Punct(punctuation));
        position.column += 1;
        skip_blanks(lines, &mut position);
    }
    Ok(None)
}

fn is_punct(token: Option<&Token>, text: u8) -> bool {
    token == Some(&Token::Punct(text))
}

/// `Number.parseFloat` of a number token, `/^\d+(\.\d+)?/`, which Rust reads the same way.
fn parse_float(text: &str) -> f64 {
    text.parse().unwrap_or(f64::NAN)
}

fn get_value(token: Option<&Token>) -> Option<PragmaValue> {
    match token {
        Some(Token::String(text)) => Some(PragmaValue::String(text.clone())),
        Some(Token::Number(text)) => Some(PragmaValue::Float(parse_float(text))),
        _ => is_punct(token, b'@').then_some(PragmaValue::Default),
    }
}

/// The methods of Method_prs's old pragma syntax, by the name Method.prover_meth_of_tac gives them.
const OLD_METHODS: [(&str, &str); 25] = [
    ("smt", "smt"),
    ("cvc3", "cvc4"),
    ("yices", "yices"),
    ("z3", "z3"),
    ("cooper", "cooper"),
    ("presburger", "cooper"),
    ("fail", "fail"),
    ("smt2lib", "smt"),
    ("smt2z3", "z3"),
    ("smt3", "smt"),
    ("z33", "z3"),
    ("cvc33", "cvc4"),
    ("yices3", "yices"),
    ("verit", "verit"),
    ("zipper", "zipper"),
    ("spass", "spass"),
    ("tptp", "tptp"),
    ("ls4", "ls4"),
    ("expandenabled", "expandenabled"),
    ("expandcdot", "expandcdot"),
    ("autouse", "autouse"),
    ("lambdify", "lambdify"),
    ("enabledaxioms", "enabledaxioms"),
    ("levelcomparison", "levelcomparison"),
    ("trivial", "trivial"),
];

/// An old-style method, with the tactic an isabelle method takes and the timeout in seconds an
/// isabelle or zenon method may take.
#[derive(Clone, Debug, PartialEq)]
pub struct OldMethod {
    pub name: String,
    pub tactic: Option<String>,
    pub timeout: Option<f64>,
}

/// The tokens and the index the TypeScript's `readOldMethod` closures share.
struct OldMethodReader {
    tokens: Vec<Token>,
    index: usize,
}

impl OldMethodReader {
    fn read_timeout(&mut self) -> Option<f64> {
        let Some(Token::Number(text)) = self.tokens.get(self.index) else {
            return None;
        };
        let timeout = parse_float(text);
        self.index += 1;
        Some(timeout)
    }

    fn read_method(&mut self) -> Option<OldMethod> {
        if !is_punct(self.tokens.get(self.index), b'(') {
            return None;
        }
        self.index += 1;
        let name = self.tokens.get(self.index).cloned();
        self.index += 1;
        let Some(Token::Ident(name)) = name else {
            return None;
        };
        let method = if name == "isabelle" {
            let Some(Token::String(tactic)) = self.tokens.get(self.index).cloned() else {
                return None;
            };
            self.index += 1;
            OldMethod {
                name,
                tactic: Some(tactic),
                timeout: self.read_timeout(),
            }
        } else if name == "zenon" {
            let timeout = self.read_timeout();
            if is_punct(self.tokens.get(self.index), b'(') && self.read_method().is_none() {
                return None;
            }
            OldMethod {
                name,
                tactic: None,
                timeout,
            }
        } else {
            let (_, known) = OLD_METHODS.iter().find(|(old_name, _)| *old_name == name)?;
            OldMethod {
                name: (*known).to_owned(),
                tactic: None,
                timeout: None,
            }
        };
        if !is_punct(self.tokens.get(self.index), b')') {
            return None;
        }
        self.index += 1;
        Some(method)
    }
}

/// Method_prs.read_method: the (*{ by (zenon) }*) after a BY, OBVIOUS, proof step, theorem, or
/// axiom, which names one method, isabelle with a tactic, or zenon with a timeout and a fallback.
/// The error is the SyntaxError JSON.parse throws on a string literal JSON can't read.
pub fn read_old_method<Line: AsRef<[u16]>>(
    lines: &[Line],
    start: Position,
) -> Result<Option<OldMethod>> {
    let Some(tokens) = tokenize_pragma(lines, start)? else {
        return Ok(None);
    };
    let mut reader = OldMethodReader { tokens, index: 0 };
    if !matches!(reader.tokens.first(), Some(Token::Ident(keyword)) if keyword == "by") {
        return Ok(None);
    }
    reader.index += 1;
    let method = reader.read_method();
    Ok(if reader.index == reader.tokens.len() {
        method
    } else {
        None
    })
}

/// read_new_method: by (hint: value; ...), repeated, where a value is a string, a number, or @ for
/// the argument the definition is applied to. The error is as `read_old_method`'s.
pub fn read_new_method<Line: AsRef<[u16]>>(
    lines: &[Line],
    start: Position,
) -> Result<Option<Vec<Vec<PragmaSetting>>>> {
    let Some(tokens) = tokenize_pragma(lines, start)? else {
        return Ok(None);
    };
    let mut index = 0;
    let mut groups = Vec::new();
    while let Some(keyword) = tokens.get(index) {
        index += 1;
        if !matches!(keyword, Token::Ident(text) if text == "by" || text == "set") {
            return Ok(None);
        }
        if !is_punct(tokens.get(index), b'(') {
            return Ok(None);
        }
        index += 1;
        let mut settings = Vec::new();
        loop {
            let hint = tokens.get(index);
            index += 1;
            let Some(Token::Ident(hint)) = hint else {
                return Ok(None);
            };
            if !is_punct(tokens.get(index), b':') {
                return Ok(None);
            }
            index += 1;
            let value = get_value(tokens.get(index));
            index += 1;
            let Some(value) = value else {
                return Ok(None);
            };
            settings.push(PragmaSetting {
                hint: hint.clone(),
                value,
            });
            if is_punct(tokens.get(index), b')') {
                break;
            }
            if !is_punct(tokens.get(index), b';') {
                return Ok(None);
            }
            index += 1;
        }
        index += 1;
        groups.push(settings);
    }
    Ok(Some(groups))
}

#[cfg(test)]
mod tests {
    use super::*;

    type Expected<Value> = std::result::Result<Option<Value>, ()>;

    fn old(name: &str, tactic: Option<&str>, timeout: Option<f64>) -> OldMethod {
        OldMethod {
            name: name.to_owned(),
            tactic: tactic.map(str::to_owned),
            timeout,
        }
    }

    fn set(hint: &str, value: PragmaValue) -> PragmaSetting {
        PragmaSetting {
            hint: hint.to_owned(),
            value,
        }
    }

    fn get_lines(text: &str) -> Vec<Vec<u16>> {
        text.split('\n').map(get_units).collect()
    }

    /// Source text split on line feeds, a start, and what `src/obligations/pragma.ts` gives under
    /// Bun for findPragma, readOldMethod and readNewMethod; `Err` is a SyntaxError it throws.
    #[test]
    #[allow(clippy::type_complexity)]
    fn reads_pragmas_as_the_typescript_does() {
        let cases: Vec<(
            &str,
            (usize, usize),
            Option<(usize, usize)>,
            Expected<OldMethod>,
            Expected<Vec<Vec<PragmaSetting>>>,
        )> = vec![
            (
                "(*{ by (smt) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("smt", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (cvc3) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("cvc4", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (yices) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("yices", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (z3) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("z3", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (cooper) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("cooper", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (presburger) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("cooper", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (fail) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("fail", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (smt2lib) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("smt", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (smt2z3) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("z3", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (smt3) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("smt", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (z33) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("z3", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (cvc33) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("cvc4", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (yices3) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("yices", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (verit) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("verit", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (zipper) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("zipper", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (spass) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("spass", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (tptp) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("tptp", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (ls4) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("ls4", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (expandenabled) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("expandenabled", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (expandcdot) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("expandcdot", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (autouse) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("autouse", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (lambdify) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("lambdify", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (enabledaxioms) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("enabledaxioms", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (levelcomparison) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("levelcomparison", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (trivial) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("trivial", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (unknown) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            ("(*{ by (SMT) }*)", (0, 0), Some((0, 0)), Ok(None), Ok(None)),
            (
                "(*{ by (zenon) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("zenon", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (isabelle) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "  (*{ by (zenon) }*)",
                (0, 0),
                Some((0, 2)),
                Ok(Some(old("zenon", None, None))),
                Ok(None),
            ),
            (
                "x\n   \n  (*{ by\n  (zenon 30\n (isabelle \"auto\")) }*)",
                (0, 1),
                Some((2, 2)),
                Ok(Some(old("zenon", None, Some(30.0)))),
                Ok(None),
            ),
            (
                "\u{3b1}\u{3b2}\u{2200} (*{ by (smt) }*)",
                (0, 3),
                Some((0, 4)),
                Ok(Some(old("smt", None, None))),
                Ok(None),
            ),
            (
                "\u{1f600} (*{ by (z3) }*)",
                (0, 2),
                Some((0, 3)),
                Ok(Some(old("z3", None, None))),
                Ok(None),
            ),
            (
                "\u{1f600} (*{ by (z3) }*)",
                (0, 1),
                None,
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (isabelle \"auto\") }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("isabelle", Some("auto"), None))),
                Ok(None),
            ),
            (
                "(*{ by (isabelle \"auto\" 12) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("isabelle", Some("auto"), Some(12.0)))),
                Ok(None),
            ),
            (
                "(*{ by (isabelle \"auto\" 12.75) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("isabelle", Some("auto"), Some(12.75)))),
                Ok(None),
            ),
            (
                "(*{ by (isabelle) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (isabelle auto) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (zenon 1.5) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("zenon", None, Some(1.5)))),
                Ok(None),
            ),
            (
                "(*{ by (zenon 10 (smt)) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("zenon", None, Some(10.0)))),
                Ok(None),
            ),
            (
                "(*{ by (zenon (zenon (isabelle \"x\"))) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("zenon", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (zenon (unknown)) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (zenon) (smt) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (zenon }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (zenon, smt) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (smt) extra }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            ("(*{ BY (smt) }*)", (0, 0), Some((0, 0)), Ok(None), Ok(None)),
            ("(*{ (smt) }*)", (0, 0), Some((0, 0)), Ok(None), Ok(None)),
            ("(*{ }*)", (0, 0), Some((0, 0)), Ok(None), Ok(Some(vec![]))),
            ("(*{}*)", (0, 0), Some((0, 0)), Ok(None), Ok(Some(vec![]))),
            ("(*{ by (zenon)", (0, 0), Some((0, 0)), Ok(None), Ok(None)),
            (
                "(*{ by (zenon)\n\n",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{\u{d} by\u{9}(zenon)\u{d}}*)\u{d}",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("zenon", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (smt) }*) trailing junk ! }*)",
                (0, 0),
                Some((0, 0)),
                Ok(Some(old("smt", None, None))),
                Ok(None),
            ),
            (
                "(*{ by (smt) ! }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            ("(*{ by (smt) }*)", (0, 1), None, Ok(None), Ok(None)),
            ("(*{ by (smt) }*)", (0, 40), None, Ok(None), Ok(None)),
            ("(*{ by (smt) }*)", (3, 0), None, Ok(None), Ok(None)),
            ("abc (*{ by (smt) }*)", (0, 0), None, Ok(None), Ok(None)),
            ("", (0, 0), None, Ok(None), Ok(None)),
            ("(* by (smt) *)", (0, 0), None, Ok(None), Ok(None)),
            (
                "(*{ by (prover:\"zenon\"; timeout:@) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(Some(vec![vec![
                    set("prover", PragmaValue::String("zenon".to_owned())),
                    set("timeout", PragmaValue::Default),
                ]])),
            ),
            (
                "(*{ by (prover: \"smt\") set (x: 1.5) by (a: \"s\"; b: 3; c: @) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(Some(vec![
                    vec![set("prover", PragmaValue::String("smt".to_owned()))],
                    vec![set("x", PragmaValue::Float(1.5))],
                    vec![
                        set("a", PragmaValue::String("s".to_owned())),
                        set("b", PragmaValue::Float(3.0)),
                        set("c", PragmaValue::Default),
                    ],
                ])),
            ),
            ("(*{ by () }*)", (0, 0), Some((0, 0)), Ok(None), Ok(None)),
            ("(*{ by (a 1) }*)", (0, 0), Some((0, 0)), Ok(None), Ok(None)),
            (
                "(*{ by (a: 1;) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (a: 1) junk }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ foo (a: 1) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (a: 1.) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (a: 1.2.3) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (a: 007) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(Some(vec![vec![set("a", PragmaValue::Float(7.0))]])),
            ),
            (
                "(*{ by (a: 99999999999999999999999) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(Some(vec![vec![set("a", PragmaValue::Float(1e23))]])),
            ),
            (
                "(*{ by (a: 0.1000000000000000055511151231257827) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(Some(vec![vec![set("a", PragmaValue::Float(0.1))]])),
            ),
            (
                "(*{ by (a: 9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(Some(vec![vec![set(
                    "a",
                    PragmaValue::Float(f64::INFINITY),
                )]])),
            ),
            (
                "(*{ by (a: x) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (a: \"a\\\"b\\\\c\\n\\u0041\\/\\b\\f\\r\\t\") }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(Some(vec![vec![set(
                    "a",
                    PragmaValue::String("a\"b\\c\nA/\u{8}\u{c}\u{d}\u{9}".to_owned()),
                )]])),
            ),
            (
                "(*{ by (a: \"\\x\") }*)",
                (0, 0),
                Some((0, 0)),
                Err(()),
                Err(()),
            ),
            (
                "(*{ by (a: \"tab\u{9}here\") }*)",
                (0, 0),
                Some((0, 0)),
                Err(()),
                Err(()),
            ),
            (
                "(*{ by (a: \"\\u12\") }*)",
                (0, 0),
                Some((0, 0)),
                Err(()),
                Err(()),
            ),
            (
                "(*{ by (a: \"\\u12G4\") }*)",
                (0, 0),
                Some((0, 0)),
                Err(()),
                Err(()),
            ),
            (
                "(*{ by (a: \"\\ud83d\\ude00\") }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(Some(vec![vec![set(
                    "a",
                    PragmaValue::String("\u{1f600}".to_owned()),
                )]])),
            ),
            (
                "(*{ by (a: \"\u{3b1}\u{3b2}\u{1f600}\") }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(Some(vec![vec![set(
                    "a",
                    PragmaValue::String("\u{3b1}\u{3b2}\u{1f600}".to_owned()),
                )]])),
            ),
            (
                "(*{ by (a: \"abc\\",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (a: \"abc) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (a: \"a\\\u{d}b\") }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (a: \"a\u{2028}b\") }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(Some(vec![vec![set(
                    "a",
                    PragmaValue::String("a\u{2028}b".to_owned()),
                )]])),
            ),
            (
                "(*{ by (a: \"a\\\u{2028}b\") }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (isabelle \"a\\qb\") }*)",
                (0, 0),
                Some((0, 0)),
                Err(()),
                Err(()),
            ),
            (
                "(*{ by\n(a:\n\"x\"\n)\n}*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(Some(vec![vec![set(
                    "a",
                    PragmaValue::String("x".to_owned()),
                )]])),
            ),
            (
                "(*{ by (a: 3z) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (_a1: 2) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(Some(vec![vec![set("_a1", PragmaValue::Float(2.0))]])),
            ),
            (
                "(*{ by (a: 2) }*)\n(*{ by (b: 3) }*)",
                (1, 0),
                Some((1, 0)),
                Ok(None),
                Ok(Some(vec![vec![set("b", PragmaValue::Float(3.0))]])),
            ),
            (
                "  \u{9}  \n\u{9}(*{ set (x:@) }*)",
                (0, 0),
                Some((1, 1)),
                Ok(None),
                Ok(Some(vec![vec![set("x", PragmaValue::Default)]])),
            ),
            (
                "(*{ by (a: 1) ; }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
            (
                "(*{ by (a: 1)(b: 2) }*)",
                (0, 0),
                Some((0, 0)),
                Ok(None),
                Ok(None),
            ),
        ];
        for (index, (text, (line, column), found, old_method, new_method)) in
            cases.into_iter().enumerate()
        {
            let lines = get_lines(text);
            let start = Position { line, column };
            assert_eq!(
                find_pragma(&lines, start),
                found.map(|(line, column)| Position { line, column }),
                "case {index}"
            );
            assert_eq!(
                read_old_method(&lines, start).map_err(|_| ()),
                old_method,
                "case {index}"
            );
            assert_eq!(
                read_new_method(&lines, start).map_err(|_| ()),
                new_method,
                "case {index}"
            );
        }
    }

    /// The TypeScript keeps a lone surrogate an escape makes, which a Rust string can't hold.
    #[test]
    fn replaces_a_lone_escaped_surrogate() {
        let lines = get_lines(r#"(*{ by (a: "x\ud800y") }*)"#);
        let start = Position { line: 0, column: 0 };
        assert_eq!(
            read_new_method(&lines, start),
            Ok(Some(vec![vec![set(
                "a",
                PragmaValue::String("x\u{fffd}y".to_owned())
            )]]))
        );
    }

    // alexer.mll:105-113: tlapm's lexer reads a pragma's \b, \o and \h numerals in decimal, as it
    // does any other.
    #[test]
    fn reads_based_numerals_in_decimal() {
        let start = Position { line: 0, column: 0 };
        assert_eq!(
            read_old_method(&get_lines(r"(*{ by (zenon \h1E) }*)"), start),
            Ok(Some(old("zenon", None, Some(30.0))))
        );
        assert_eq!(
            read_new_method(&get_lines(r"(*{ by (timeout: \b11; a: \o17) }*)"), start),
            Ok(Some(vec![vec![
                set("timeout", PragmaValue::Float(3.0)),
                set("a", PragmaValue::Float(15.0))
            ]]))
        );
        assert_eq!(
            read_old_method(&get_lines(r"(*{ by (zenon \h4000000000000000) }*)"), start),
            Ok(Some(old("zenon", None, Some(-4_611_686_018_427_387_904.0))))
        );
    }
}

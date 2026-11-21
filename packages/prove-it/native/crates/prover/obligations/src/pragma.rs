//! tlapm's method pragmas: the new `(*{ by (prover:"zenon"; timeout:@) }*)` after a definition,
//! which `E_parser.read_new_method` reads into a Bpragma, and the old `(*{ by (zenon) }*)` of
//! Method_prs. A port of `src/obligations/pragma.ts`, but for a string's contents, which it keeps
//! as tlapm's lexer does (`read_string`) where the TypeScript reads them with `JSON.parse`.
//!
//! The source's lines are UTF-16 code units (any `AsRef<[u16]>`), so columns count as the
//! TypeScript's string indices do.

use crate::errors::{ObligationError, Result};

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
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
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

/// A pragma as tlapm's lexer finds it: `(*{` and `}*)` are tokens outside comments and strings.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pragma {
    pub open: Position,
    /// After the `}*)`, where one closes it.
    pub close: Option<Position>,
}

/// A module's text as tlapm's lexer reads it (alexer.mll `token`): the comments it drops, which
/// `\*` opens to the line's end and `(*` to the `*)` closing its nesting, where `(*{` and `}*)`
/// nest as `(*` and `*)` do; the strings, which hide what looks like a comment or a pragma; and
/// the pragmas. The parser sees pragmas as tokens, so a comment inside one or between it and the
/// keyword it qualifies is no different from a blank.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Lexical {
    comments: Vec<(Position, Position)>,
    pragmas: Vec<Pragma>,
}

impl Lexical {
    /// The end of the comment `position` is in or at the start of.
    fn get_comment_end(&self, position: Position) -> Option<Position> {
        self.comments
            .iter()
            .find(|(start, end)| *start <= position && position < *end)
            .map(|(_, end)| *end)
    }

    /// The start of the comment `position` is in or at the end of.
    fn get_comment_start(&self, position: Position) -> Option<Position> {
        self.comments
            .iter()
            .find(|(start, end)| *start < position && position <= *end)
            .map(|(start, _)| *start)
    }
}

fn starts_with<Line: AsRef<[u16]>>(lines: &[Line], position: Position, text: &str) -> bool {
    lines
        .get(position.line)
        .and_then(|line| line.as_ref().get(position.column..))
        .is_some_and(|rest| rest.starts_with(&get_units(text)))
}

/// Where tlapm's lexer starts reading tokens: after `---- MODULE` (alexer.mll `modfile`), or at
/// the start where there is no header, which tlapm doesn't parse at all.
fn find_module_header<Line: AsRef<[u16]>>(lines: &[Line]) -> Position {
    let dashes = get_units("----");
    let module = get_units("MODULE");
    for (index, line) in lines.iter().enumerate() {
        let line = line.as_ref();
        for start in 0..line.len() {
            if !line[start..].starts_with(&dashes) {
                continue;
            }
            let mut column = start + dashes.len();
            while is_unit(line.get(column), b'-') {
                column += 1;
            }
            while is_unit(line.get(column), b' ') {
                column += 1;
            }
            if line[column..].starts_with(&module) {
                return Position {
                    line: index,
                    column: column + module.len(),
                };
            }
        }
    }
    Position { line: 0, column: 0 }
}

/// The end of the comment `(*` opens at `start`, nesting `(*` and `*)`, or of the text where no
/// `*)` closes it.
fn skip_comment<Line: AsRef<[u16]>>(lines: &[Line], start: Position) -> Position {
    let mut depth = 0;
    let mut position = start;
    while let Some(line) = lines.get(position.line) {
        let line = line.as_ref();
        if position.column >= line.len() {
            if position.line + 1 == lines.len() {
                break;
            }
            position = Position {
                line: position.line + 1,
                column: 0,
            };
            continue;
        }
        if starts_with(lines, position, "(*") {
            depth += 1;
            position.column += 2;
        } else if starts_with(lines, position, "*)") {
            depth -= 1;
            position.column += 2;
            if depth == 0 {
                return position;
            }
        } else {
            position.column += 1;
        }
    }
    position
}

/// The end of the string `"` opens at `start` (alexer.mll `string`): past its escapes, at the
/// closing quote, or at the line's end, where tlapm stops with an error.
fn skip_string(line: &[u16], start: Position) -> Position {
    let mut column = start.column + 1;
    while let Some(&unit) = line.get(column) {
        if unit == u16::from(b'"') {
            return Position {
                column: column + 1,
                ..start
            };
        }
        if unit == u16::from(b'\\') {
            let next = line.get(column + 1);
            let is_octal = |unit: Option<&u16>| {
                unit.is_some_and(|&unit| (b'0'..=b'7').contains(&u8::try_from(unit).unwrap_or(0)))
            };
            column += if next
                .is_some_and(|&unit| b"\"\\tnfr".contains(&u8::try_from(unit).unwrap_or(0)))
            {
                2
            } else if is_octal(next)
                && is_octal(line.get(column + 2))
                && is_octal(line.get(column + 3))
            {
                4
            } else {
                1
            };
            continue;
        }
        column += 1;
    }
    Position { column, ..start }
}

/// Reads the module's text as tlapm's lexer does.
pub fn read_lexical<Line: AsRef<[u16]>>(lines: &[Line]) -> Lexical {
    let mut lexical = Lexical::default();
    let mut opened: Vec<(Position, Option<Position>)> = Vec::new();
    let mut position = find_module_header(lines);
    while let Some(line) = lines.get(position.line) {
        let line = line.as_ref();
        if position.column >= line.len() {
            position = Position {
                line: position.line + 1,
                column: 0,
            };
            continue;
        }
        if starts_with(lines, position, "(*{") {
            opened.push((position, None));
            position.column += 3;
        } else if starts_with(lines, position, "}*)") {
            position.column += 3;
            if let Some(index) = opened.iter().rposition(|(_, close)| close.is_none()) {
                opened[index].1 = Some(position);
            }
        } else if starts_with(lines, position, "\\*") {
            let end = Position {
                column: line.len(),
                ..position
            };
            lexical.comments.push((position, end));
            position = end;
        } else if starts_with(lines, position, "(*") {
            let end = skip_comment(lines, position);
            lexical.comments.push((position, end));
            position = end;
        } else if is_unit(line.get(position.column), b'"') {
            position = skip_string(line, position);
        } else {
            position.column += 1;
        }
    }
    lexical.pragmas = opened
        .into_iter()
        .map(|(open, close)| Pragma { open, close })
        .collect();
    lexical
}

/// Past blanks, line ends and comments.
fn skip_blanks_and_comments<Line: AsRef<[u16]>>(
    lexical: &Lexical,
    lines: &[Line],
    position: &mut Position,
) {
    loop {
        skip_blanks(lines, position);
        match lexical.get_comment_end(*position) {
            Some(end) => *position = end,
            None => return,
        }
    }
}

/// The units from `from` to `to`, comments left out and a line end as a line feed.
fn collect_units<Line: AsRef<[u16]>>(
    lexical: &Lexical,
    lines: &[Line],
    from: Position,
    to: Position,
) -> Vec<u16> {
    let mut units = Vec::new();
    let mut position = from;
    while position < to {
        if let Some(end) = lexical.get_comment_end(position) {
            position = end;
            continue;
        }
        let line = lines.get(position.line).map_or(&[][..], AsRef::as_ref);
        match line.get(position.column) {
            Some(&unit) => {
                units.push(unit);
                position.column += 1;
            }
            None => {
                units.push(u16::from(b'\n'));
                position = Position {
                    line: position.line + 1,
                    column: 0,
                };
            }
        }
    }
    units
}

/// The pragma after `start`, past blanks, line ends and comments.
pub fn find_pragma<Line: AsRef<[u16]>>(
    lexical: &Lexical,
    lines: &[Line],
    start: Position,
) -> Option<Pragma> {
    let mut position = start;
    skip_blanks_and_comments(lexical, lines, &mut position);
    lexical
        .pragmas
        .iter()
        .find(|pragma| pragma.open == position)
        .copied()
}

/// Where the suppression pragma before `keyword` opens, if there is one: Proof.Parser's
/// `suppress`, a pragma holding `_` or `suppress` alone, which the parser reads as tokens, so
/// that only blanks, line ends and comments separate it from the keyword.
pub fn find_suppress_pragma<Line: AsRef<[u16]>>(
    lexical: &Lexical,
    lines: &[Line],
    keyword: Position,
) -> Option<Position> {
    let mut position = keyword;
    // Back over blanks, line ends and comments to the last unit before the keyword.
    loop {
        let line = lines.get(position.line)?.as_ref();
        if position.column > line.len() {
            position.column = line.len();
        }
        if let Some(start) = lexical.get_comment_start(position) {
            position = start;
            continue;
        }
        while position.column > 0 && is_blank(line.get(position.column - 1)) {
            position.column -= 1;
        }
        if position.column > 0 {
            if lexical.get_comment_start(position).is_none() {
                break;
            }
            continue;
        }
        position.line = position.line.checked_sub(1)?;
        position.column = lines.get(position.line)?.as_ref().len();
    }
    let pragma = lexical
        .pragmas
        .iter()
        .find(|pragma| pragma.close == Some(position))?;
    let from = Position {
        column: pragma.open.column + 3,
        ..pragma.open
    };
    let to = Position {
        column: position.column - 3,
        ..position
    };
    let inner = String::from_utf16_lossy(&collect_units(lexical, lines, from, to));
    let inner = inner.trim_matches(|character: char| matches!(character, ' ' | '\t' | '\r' | '\n'));
    (inner == "_" || inner == "suppress").then_some(pragma.open)
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

/// The contents of a literal `match_string` matched, as tlapm's lexer reads a string
/// (alexer.mll:173-197): verbatim. It keeps `\"`, `\\`, `\t`, `\n`, `\f`, `\r` and `\ddd` as
/// they are written (alexer.mll:184-191) and adds every other character as it is
/// (alexer.mll:195-197), so no escape is decoded or refused. tlapm's lexer fails on a TAB or a
/// carriage return in a string (alexer.mll:174-182), as on a TAB anywhere; these keep the
/// TypeScript's SyntaxError, which design/prover.md lists.
fn read_string(literal: &[u16]) -> Result<String> {
    let inner = literal
        .get(1..literal.len().saturating_sub(1))
        .unwrap_or(&[]);
    if inner.iter().any(|&unit| matches!(unit, 0x09 | 0x0d)) {
        return Err(ObligationError::bug(
            "SyntaxError: JSON Parse error: Unterminated string",
        ));
    }
    Ok(String::from_utf16_lossy(inner))
}

fn tokenize_pragma<Line: AsRef<[u16]>>(
    lexical: &Lexical,
    lines: &[Line],
    start: Position,
) -> Result<Option<Vec<Token>>> {
    let Some(pragma) = find_pragma(lexical, lines, start) else {
        return Ok(None);
    };
    let closing = pragma.close.map(|close| Position {
        column: close.column - 3,
        ..close
    });
    let mut position = Position {
        column: pragma.open.column + 3,
        ..pragma.open
    };
    let mut tokens = Vec::new();
    skip_blanks_and_comments(lexical, lines, &mut position);
    while let Some(line) = lines.get(position.line) {
        let rest = line.as_ref().get(position.column..).unwrap_or(&[]);
        if Some(position) == closing {
            return Ok(Some(tokens));
        }
        let length = match_ident(rest)
            .or_else(|| match_number(rest))
            .or_else(|| match_string(rest));
        if let Some(length) = length {
            let text = &rest[..length];
            tokens.push(if is_unit(text.first(), b'"') {
                Token::String(read_string(text)?)
            } else if text.first().is_some_and(|&unit| is_digit(unit)) {
                Token::Number(String::from_utf16_lossy(text))
            } else {
                Token::Ident(String::from_utf16_lossy(text))
            });
            position.column += length;
            skip_blanks_and_comments(lexical, lines, &mut position);
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
        skip_blanks_and_comments(lexical, lines, &mut position);
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
/// The error is `read_string`'s.
pub fn read_old_method<Line: AsRef<[u16]>>(
    lexical: &Lexical,
    lines: &[Line],
    start: Position,
) -> Result<Option<OldMethod>> {
    let Some(tokens) = tokenize_pragma(lexical, lines, start)? else {
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
    lexical: &Lexical,
    lines: &[Line],
    start: Position,
) -> Result<Option<Vec<Vec<PragmaSetting>>>> {
    let Some(tokens) = tokenize_pragma(lexical, lines, start)? else {
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
                "(*{ by (a: \"tab\u{9}here\") }*)",
                (0, 0),
                Some((0, 0)),
                Err(()),
                Err(()),
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
                find_pragma(&read_lexical(&lines), &lines, start).map(|pragma| pragma.open),
                found.map(|(line, column)| Position { line, column }),
                "case {index}"
            );
            assert_eq!(
                read_old_method(&read_lexical(&lines), &lines, start).map_err(|_| ()),
                old_method,
                "case {index}"
            );
            assert_eq!(
                read_new_method(&read_lexical(&lines), &lines, start).map_err(|_| ()),
                new_method,
                "case {index}"
            );
        }
    }

    /// Proof.Parser's `suppress`: the pragma just before the keyword, over blanks and line ends,
    /// holding `_` or `suppress` alone, with only blanks, line ends and comments before the
    /// keyword, and not what looks like one inside a comment or a string.
    #[test]
    fn finds_the_suppression_pragma_before_a_keyword() {
        type Case = (&'static str, (usize, usize), Option<(usize, usize)>);
        let cases: [Case; 16] = [
            ("<1> (*{_}*) WITNESS 1", (0, 12), Some((0, 4))),
            ("  (*{ suppress }*)  BY A", (0, 20), Some((0, 2))),
            ("(*{_}*)\n  USE A", (1, 2), Some((0, 0))),
            ("(*{\n _ \n}*) OBVIOUS", (2, 4), Some((0, 0))),
            ("(*{_}*) (* c *) BY A", (0, 16), Some((0, 0))),
            ("(*{_}*) \\* c\nBY A", (1, 0), Some((0, 0))),
            ("(*{ _ (* c *) }*) BY A", (0, 18), Some((0, 0))),
            ("(*{ _ \\* c\n}*) OBVIOUS", (1, 4), Some((0, 0))),
            ("(*{ by (smt) }*) BY A", (0, 17), None),
            ("\\* (*{_}*)\nOBVIOUS", (1, 0), None),
            ("(* (*{_}*) *)\nOBVIOUS", (1, 0), None),
            ("(* (* (*{_}*) *) *)  \nOBVIOUS", (1, 0), None),
            ("\"(*{_}*)\" OBVIOUS", (0, 10), None),
            ("<1> BY A", (0, 4), None),
            ("(*{suppress_}*) BY", (0, 16), None),
            ("}*) BY", (0, 4), None),
        ];
        for (text, (line, column), expected) in cases {
            assert_eq!(
                find_suppress_pragma(
                    &read_lexical(&get_lines(text)),
                    &get_lines(text),
                    Position { line, column }
                ),
                expected.map(|(line, column)| Position { line, column }),
                "{text:?}"
            );
        }
    }

    /// A string's contents as tlapm's lexer keeps them (alexer.mll:173-197): each escape as it is
    /// written, whether tlapm knows it (`\"` and `\n` at lines 184-187, `\ddd` at 188-191) or
    /// not (`\q`, `\uD800`, `\/`, each character added as it is at 195-197).
    #[test]
    fn reads_strings_as_tlapm_lexes_them() {
        let start = Position { line: 0, column: 0 };
        for (literal, contents) in [
            (r#""\uD800""#, r"\uD800"),
            (r#""\ud83d\ude00""#, r"\ud83d\ude00"),
            (r#""\n""#, r"\n"),
            (r#""\q""#, r"\q"),
            (r#""a\"b""#, r#"a\"b"#),
            (r#""a\\""#, r"a\\"),
            (r#""\101\7""#, r"\101\7"),
            (r#""\t\f\r\/\b\u0041\x""#, r"\t\f\r\/\b\u0041\x"),
            ("\"a\u{1}\u{3b1}\u{1f600}\"", "a\u{1}\u{3b1}\u{1f600}"),
        ] {
            let new_method = format!("(*{{ by (prover: {literal}) }}*)");
            assert_eq!(
                read_new_method(
                    &read_lexical(&get_lines(&new_method)),
                    &get_lines(&new_method),
                    start
                ),
                Ok(Some(vec![vec![set(
                    "prover",
                    PragmaValue::String(contents.to_owned())
                )]])),
                "{literal}"
            );
            let old_method = format!("(*{{ by (isabelle {literal}) }}*)");
            assert_eq!(
                read_old_method(
                    &read_lexical(&get_lines(&old_method)),
                    &get_lines(&old_method),
                    start
                ),
                Ok(Some(old("isabelle", Some(contents), None))),
                "{literal}"
            );
        }
    }

    /// tlapm's lexer fails on a TAB or a carriage return in a string (alexer.mll:174-182).
    #[test]
    fn fails_on_what_tlapm_cannot_lex_in_a_string() {
        let start = Position { line: 0, column: 0 };
        for text in ["(*{ by (a: \"a\u{9}b\") }*)", "(*{ by (a: \"a\u{d}b\") }*)"] {
            assert!(
                read_new_method(&read_lexical(&get_lines(text)), &get_lines(text), start).is_err(),
                "{text:?}"
            );
        }
    }
}

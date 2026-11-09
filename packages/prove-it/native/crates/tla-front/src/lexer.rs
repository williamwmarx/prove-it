//! TLA+'s tokens, as `src/lexer.ts` reads them. Lines count from 1, and columns count UTF-16 code
//! units from 1 with a tab reaching the next multiple of eight, so every position equals the
//! TypeScript one.

use std::rc::Rc;
use std::sync::OnceLock;

use crate::errors::{SyntaxError, SyntaxFailure};
use crate::hash::FastMap;
use crate::json::write_js_string;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Identifier,
    Number,
    Decimal,
    String,
    Operator,
    Keyword,
    Step,
    Separator,
    ModuleEnd,
    End,
}

impl TokenKind {
    pub fn name(self) -> &'static str {
        match self {
            TokenKind::Identifier => "Identifier",
            TokenKind::Number => "Number",
            TokenKind::Decimal => "Decimal",
            TokenKind::String => "String",
            TokenKind::Operator => "Operator",
            TokenKind::Keyword => "Keyword",
            TokenKind::Step => "Step",
            TokenKind::Separator => "Separator",
            TokenKind::ModuleEnd => "ModuleEnd",
            TokenKind::End => "End",
        }
    }
}

/// `spelling` holds the text of an operator written as a synonym, such as `(+)` for `\oplus`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub text: Rc<str>,
    pub spelling: Option<Rc<str>>,
    pub line: u32,
    pub column: u32,
    pub end_column: u32,
}

/// In ASCII order, for a binary search.
const KEYWORDS: &[&str] = &[
    "ACTION",
    "ACTIONS",
    "ASSUME",
    "ASSUMPTION",
    "AXIOM",
    "BY",
    "CASE",
    "CHOOSE",
    "CONSTANT",
    "CONSTANTS",
    "COROLLARY",
    "DEF",
    "DEFINE",
    "DEFS",
    "DOMAIN",
    "ELSE",
    "ENABLED",
    "EXCEPT",
    "EXTENDS",
    "HAVE",
    "HIDE",
    "IF",
    "IN",
    "INSTANCE",
    "LAMBDA",
    "LEMMA",
    "LET",
    "LOCAL",
    "MODULE",
    "NEW",
    "OBVIOUS",
    "OMITTED",
    "ONLY",
    "OTHER",
    "PICK",
    "PROOF",
    "PROPOSITION",
    "PROVE",
    "QED",
    "RECURSIVE",
    "STATE",
    "SUBSET",
    "SUFFICES",
    "TAKE",
    "TEMPORAL",
    "TEMPORALS",
    "THEN",
    "THEOREM",
    "UNCHANGED",
    "UNION",
    "USE",
    "VARIABLE",
    "VARIABLES",
    "WITH",
    "WITNESS",
];

const BACKSLASH_OPERATORS: &[(&str, &str)] = &[
    ("in", "\\in"),
    ("notin", "\\notin"),
    ("subseteq", "\\subseteq"),
    ("subset", "\\subset"),
    ("supseteq", "\\supseteq"),
    ("supset", "\\supset"),
    ("cup", "\\cup"),
    ("union", "\\cup"),
    ("cap", "\\cap"),
    ("intersect", "\\cap"),
    ("X", "\\X"),
    ("times", "\\X"),
    ("o", "\\o"),
    ("circ", "\\o"),
    ("div", "\\div"),
    ("land", "/\\"),
    ("lor", "\\/"),
    ("lnot", "~"),
    ("neg", "~"),
    ("equiv", "<=>"),
    ("leq", "<="),
    ("geq", ">="),
    ("A", "\\A"),
    ("forall", "\\A"),
    ("E", "\\E"),
    ("exists", "\\E"),
    ("AA", "\\AA"),
    ("EE", "\\EE"),
    ("cdot", "\\cdot"),
    ("sqsubseteq", "\\sqsubseteq"),
    ("sqsupseteq", "\\sqsupseteq"),
    ("sqsubset", "\\sqsubset"),
    ("sqsupset", "\\sqsupset"),
    ("sqcap", "\\sqcap"),
    ("sqcup", "\\sqcup"),
    ("oplus", "\\oplus"),
    ("ominus", "\\ominus"),
    ("otimes", "\\otimes"),
    ("oslash", "\\oslash"),
    ("odot", "\\odot"),
    ("uplus", "\\uplus"),
    ("prec", "\\prec"),
    ("preceq", "\\preceq"),
    ("succ", "\\succ"),
    ("succeq", "\\succeq"),
    ("sim", "\\sim"),
    ("simeq", "\\simeq"),
    ("approx", "\\approx"),
    ("cong", "\\cong"),
    ("asymp", "\\asymp"),
    ("doteq", "\\doteq"),
    ("propto", "\\propto"),
    ("wr", "\\wr"),
    ("star", "\\star"),
    ("bullet", "\\bullet"),
    ("bigcirc", "\\bigcirc"),
    ("ll", "\\ll"),
    ("gg", "\\gg"),
];

const SYMBOL_ALIASES: &[(&str, &str)] = &[
    ("/=", "#"),
    ("=<", "<="),
    ("(+)", "\\oplus"),
    ("(-)", "\\ominus"),
    ("(.)", "\\odot"),
    ("(/)", "\\oslash"),
    ("(\\X)", "\\otimes"),
];

/// A longer operator comes before the operators it starts with.
const SYMBOL_OPERATORS: &[&str] = &[
    "-+->", "(\\X)", "<=>", "|->", "...", "::=", ">>_", "(+)", "(-)", "(.)", "(/)", "==", "=>",
    "=<", "=|", "<<", "<=", "<>", "<-", ">>", ">=", "/\\", "\\/", "/=", "[]", "]_", "|-", "|=",
    "||", "->", "-|", "~>", "..", "::", ":=", ":>", "<:", "@@", "++", "--", "-.", "**", "//", "^^",
    "^+", "^*", "^#", "%%", "##", "&&", "$$", "??", "!!", "=", "<", ">", "/", "[", "]", "(", ")",
    "{", "}", "|", "-", "~", ".", ":", "@", ",", "'", "!", "#", "%", "+", "*", "^", "&", "$", "?",
];

/// The symbol operators that start with each ASCII character, in the order above.
static SYMBOL_OPERATORS_BY_START: OnceLock<[Vec<&str>; 128]> = OnceLock::new();

/// The Unicode forms of the operators SANY's grammar, javacc/tla+.jj, reads, as their ASCII forms.
pub(crate) const UNICODE_OPERATORS: &[(&str, &str)] = &[
    ("∃", "\\E"),
    ("∀", "\\A"),
    ("∷", "::"),
    ("≜", "=="),
    ("⟨", "<<"),
    ("⟩_", ">>_"),
    ("⟩", ">>"),
    ("→", "->"),
    ("←", "<-"),
    ("↦", "|->"),
    ("⁺", "^+"),
    ("¬", "~"),
    ("□", "[]"),
    ("◇", "<>"),
    ("∧", "/\\"),
    ("∨", "\\/"),
    ("∈", "\\in"),
    ("≈", "\\approx"),
    ("≔", ":="),
    ("≍", "\\asymp"),
    ("◯", "\\bigcirc"),
    ("⩴", "::="),
    ("●", "\\bullet"),
    ("∩", "\\cap"),
    ("⋅", "\\cdot"),
    ("∘", "\\o"),
    ("≅", "\\cong"),
    ("∪", "\\cup"),
    ("÷", "\\div"),
    ("≐", "\\doteq"),
    ("‥", ".."),
    ("…", "..."),
    ("≡", "<=>"),
    ("‼", "!!"),
    ("≥", ">="),
    ("≫", "\\gg"),
    ("⇔", "<=>"),
    ("⇒", "=>"),
    ("⫤", "=|"),
    ("↝", "~>"),
    ("≤", "<="),
    ("≪", "\\ll"),
    ("⊣", "-|"),
    ("≠", "#"),
    ("∉", "\\notin"),
    ("⊙", "\\odot"),
    ("⊖", "\\ominus"),
    ("⊕", "\\oplus"),
    ("⊘", "\\oslash"),
    ("⊗", "\\otimes"),
    ("⇸", "-+->"),
    ("≺", "\\prec"),
    ("⪯", "\\preceq"),
    ("∝", "\\propto"),
    ("⁇", "??"),
    ("⊨", "|="),
    ("⊢", "|-"),
    ("∼", "\\sim"),
    ("≃", "\\simeq"),
    ("⊓", "\\sqcap"),
    ("⊔", "\\sqcup"),
    ("⊏", "\\sqsubset"),
    ("⊑", "\\sqsubseteq"),
    ("⊐", "\\sqsupset"),
    ("⊒", "\\sqsupseteq"),
    ("⋆", "\\star"),
    ("⊂", "\\subset"),
    ("⊆", "\\subseteq"),
    ("≻", "\\succ"),
    ("⪰", "\\succeq"),
    ("⊃", "\\supset"),
    ("⊇", "\\supseteq"),
    ("×", "\\X"),
    ("⊎", "\\uplus"),
    ("‖", "||"),
    ("≀", "\\wr"),
];

pub(crate) const UNICODE_NAMES: &[&str] = &["ℕ", "ℤ", "ℝ"];

const TAB_SIZE: u32 = 8;

fn lookup<'a>(table: &[(&str, &'a str)], key: &str) -> Option<&'a str> {
    table
        .iter()
        .find(|entry| entry.0 == key)
        .map(|entry| entry.1)
}

fn is_identifier_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn skip_bytes(bytes: &[u8], index: usize, is_match: impl Fn(u8) -> bool) -> usize {
    index
        + bytes[index.min(bytes.len())..]
            .iter()
            .take_while(|byte| is_match(**byte))
            .count()
}

/// An operator at `index`: its text, and its length in bytes.
pub struct OperatorMatch {
    pub text: &'static str,
    pub length: usize,
}

fn match_unicode_operator(source: &str, index: usize) -> Option<(&'static str, usize)> {
    let rest = &source[index..];
    if rest.as_bytes().first().is_none_or(|byte| byte.is_ascii()) {
        return None;
    }
    let first = rest.chars().next()?;
    let second = rest[first.len_utf8()..].chars().next();
    let pair_end = first.len_utf8() + second.map_or(0, char::len_utf8);
    // A pair is two UTF-16 code units: either one character outside the BMP, which no operator
    // is, or two characters.
    let pair = if first.len_utf16() == 1 {
        &rest[..pair_end]
    } else {
        &rest[..first.len_utf8()]
    };
    lookup(UNICODE_OPERATORS, pair)
        .map(|text| (text, pair.len()))
        .or_else(|| {
            let single = &rest[..first.len_utf8()];
            lookup(UNICODE_OPERATORS, single).map(|text| (text, single.len()))
        })
}

pub fn match_operator(source: &str, index: usize) -> Option<OperatorMatch> {
    let bytes = source.as_bytes();
    let code = bytes.get(index).copied();
    if code == Some(b'\\') && bytes.get(index + 1).is_some_and(u8::is_ascii_alphabetic) {
        let word_end = skip_bytes(bytes, index + 1, |byte| byte.is_ascii_alphabetic());
        let word = &source[index + 1..word_end];
        // Like SANY, read the longest operator that the word starts with, so S\used is S \ used.
        return Some(
            (1..=word.len())
                .rev()
                .find_map(|length| {
                    lookup(BACKSLASH_OPERATORS, &word[..length]).map(|text| OperatorMatch {
                        text,
                        length: length + 1,
                    })
                })
                .unwrap_or(OperatorMatch {
                    text: "\\",
                    length: 1,
                }),
        );
    }
    if let Some((text, length)) = match_unicode_operator(source, index) {
        return Some(OperatorMatch { text, length });
    }
    let rest = &source[index..];
    let by_start = SYMBOL_OPERATORS_BY_START.get_or_init(|| {
        let mut table: [Vec<&str>; 128] = std::array::from_fn(|_| Vec::new());
        SYMBOL_OPERATORS
            .iter()
            .for_each(|symbol| table[usize::from(symbol.as_bytes()[0])].push(symbol));
        table
    });
    let candidates = code.and_then(|code| by_start.get(usize::from(code)));
    if let Some(symbol) = candidates
        .and_then(|candidates| candidates.iter().find(|symbol| rest.starts_with(**symbol)))
    {
        return Some(OperatorMatch {
            text: lookup(SYMBOL_ALIASES, symbol).unwrap_or(symbol),
            length: symbol.len(),
        });
    }
    (code == Some(b'\\')).then_some(OperatorMatch {
        text: "\\",
        length: 1,
    })
}

/// TLC's configuration parser reads its tokens with SANY's lexer, so it reads a Unicode operator,
/// or ℕ, ℤ, or ℝ, as one token, which it compares as written with the words it expects.
pub fn match_unicode_token(source: &str, index: usize) -> Option<&str> {
    let rest = &source[index..];
    let first = rest.chars().next()?;
    let single = &rest[..first.len_utf8()];
    let pair = (first.len_utf16() == 1)
        .then(|| rest[single.len()..].chars().next())
        .flatten()
        .map(|second| &rest[..single.len() + second.len_utf8()]);
    [pair, Some(single)]
        .into_iter()
        .flatten()
        .find(|candidate| {
            lookup(UNICODE_OPERATORS, candidate).is_some() || UNICODE_NAMES.contains(candidate)
        })
}

/// The length of a step number such as `<1>a.`, `<+>`, or `<2>*.`, which SANY reads as one token
/// wherever it appears.
fn match_step(bytes: &[u8], index: usize) -> usize {
    let is_implicit = matches!(bytes.get(index + 1), Some(b'+' | b'*'));
    let level_end = if is_implicit {
        index + 2
    } else {
        skip_bytes(bytes, index + 1, |byte| byte.is_ascii_digit())
    };
    if level_end == index + 1 || bytes.get(level_end) != Some(&b'>') {
        return 0;
    }
    let name_end = skip_bytes(bytes, level_end + 1, is_identifier_byte);
    let is_dash = name_end == level_end + 1 && matches!(bytes.get(name_end), Some(b'*' | b'-'));
    skip_bytes(
        bytes,
        if is_dash { name_end + 1 } else { name_end },
        |byte| byte == b'.',
    ) - index
}

/// The length of a based numeral such as `\b01` or `\hFF` at `index`, or 0.
fn match_based_number(bytes: &[u8], index: usize) -> usize {
    if bytes.get(index) != Some(&b'\\') {
        return 0;
    }
    let is_digit: fn(u8) -> bool = match bytes.get(index + 1).map(u8::to_ascii_lowercase) {
        Some(b'b') => |byte| matches!(byte, b'0' | b'1'),
        Some(b'o') => |byte| matches!(byte, b'0'..=b'7'),
        Some(b'h') => |byte| byte.is_ascii_hexdigit(),
        _ => return 0,
    };
    let end = skip_bytes(bytes, index + 2, is_digit);
    if end == index + 2 { 0 } else { end - index }
}

/// The whitespace JavaScript's `trimStart` removes.
pub(crate) fn is_js_whitespace(character: char) -> bool {
    matches!(
        character,
        '\t' | '\n' | '\u{b}' | '\u{c}' | '\r' | ' ' | '\u{a0}' | '\u{1680}' | '\u{2000}'
            ..='\u{200a}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202f}'
                | '\u{205f}'
                | '\u{3000}'
                | '\u{feff}'
    )
}

/// Where `/-{4,}[ \t]*MODULE\b/` first matches.
fn find_module_header(source: &str) -> Option<usize> {
    let bytes = source.as_bytes();
    let mut index = 0;
    while let Some(offset) = source[index..].find("----") {
        let start = index + offset;
        let dashes_end = skip_bytes(bytes, start, |byte| byte == b'-');
        let module = skip_bytes(bytes, dashes_end, |byte| byte == b' ' || byte == b'\t');
        if source[module..].starts_with("MODULE")
            && !bytes
                .get(module + 6)
                .is_some_and(|byte| is_identifier_byte(*byte))
        {
            return Some(start);
        }
        index = dashes_end;
    }
    None
}

fn get_width_after(width: u32, character: Option<char>) -> u32 {
    match character {
        Some('\t') => width + TAB_SIZE - width % TAB_SIZE,
        _ => width + 1,
    }
}

fn utf16_length(text: &str) -> u32 {
    text.chars()
        .map(|character| character.len_utf16() as u32)
        .sum()
}

struct Lexer<'a> {
    source: &'a str,
    bytes: &'a [u8],
    index: usize,
    line: u32,
    line_start: usize,
    module_depth: i32,
    // The column cache: where it last measured up to on which line, and the width there.
    scan_line_start: usize,
    scan_position: usize,
    scan_width: u32,
    names: FastMap<&'a str, Rc<str>>,
    tokens: Vec<Token>,
}

impl<'a> Lexer<'a> {
    fn get_column(&mut self) -> u32 {
        if self.scan_line_start != self.line_start || self.scan_position > self.index {
            self.scan_line_start = self.line_start;
            self.scan_position = self.line_start;
            self.scan_width = 0;
        }
        for character in self.source[self.scan_position..self.index].chars() {
            // A character outside the BMP is two UTF-16 code units, each a column.
            self.scan_width = if character.len_utf16() == 2 {
                self.scan_width + 2
            } else {
                get_width_after(self.scan_width, Some(character))
            };
        }
        self.scan_position = self.index;
        get_width_after(self.scan_width, self.source[self.index..].chars().next())
    }

    fn push(&mut self, kind: TokenKind, text: Rc<str>, length: usize, spelling: Option<Rc<str>>) {
        let column = self.get_column();
        let units = utf16_length(&self.source[self.index..self.index + length]);
        self.tokens.push(Token {
            kind,
            text,
            spelling,
            line: self.line,
            column,
            end_column: column + units - 1,
        });
        self.index += length;
    }

    fn advance(&mut self, length: usize) {
        let end = self.index + length;
        for (offset, byte) in self.bytes[self.index..end].iter().enumerate() {
            if *byte == b'\n' {
                self.line += 1;
                self.line_start = self.index + offset + 1;
            }
        }
        self.index = end;
    }

    fn error(&mut self, reason: &str) -> SyntaxError {
        let column = self.get_column();
        SyntaxError {
            message: format!("{reason} at line {}, column {column}", self.line),
            failure: Some(SyntaxFailure {
                reason: reason.to_string(),
                line: self.line,
                column,
                is_end: self.index >= self.source.len(),
            }),
            sany: None,
        }
    }

    fn name(&mut self, word: &'a str) -> Rc<str> {
        self.names
            .entry(word)
            .or_insert_with(|| Rc::from(word))
            .clone()
    }

    /// Skips a comment, which may nest, a byte at a time: the delimiters and newlines are ASCII,
    /// which no byte of another character's UTF-8 is.
    fn skip_comment(&mut self) -> Result<(), SyntaxError> {
        let mut depth = 0u32;
        loop {
            match (self.bytes.get(self.index), self.bytes.get(self.index + 1)) {
                (None, _) => return Err(self.error("Unterminated comment")),
                (Some(b'('), Some(b'*')) => {
                    depth += 1;
                    self.index += 2;
                }
                (Some(b'*'), Some(b')')) => {
                    depth -= 1;
                    self.index += 2;
                    if depth == 0 {
                        return Ok(());
                    }
                }
                (Some(b'\n'), _) => {
                    self.index += 1;
                    self.line += 1;
                    self.line_start = self.index;
                }
                _ => self.index += 1,
            }
        }
    }

    fn read_string(&mut self) -> Result<(), SyntaxError> {
        let line = self.line;
        let column = self.get_column();
        let mut text = String::new();
        self.advance(1);
        loop {
            match self.bytes.get(self.index) {
                Some(b'"') => break,
                None | Some(b'\n' | b'\r') => return Err(self.error("Unterminated string")),
                Some(b'\\') => {
                    let escaped = match self.bytes.get(self.index + 1) {
                        Some(b'n') => '\n',
                        Some(b't') => '\t',
                        Some(b'r') => '\r',
                        Some(b'f') => '\u{c}',
                        Some(b'\\') => '\\',
                        Some(b'"') => '"',
                        _ => return Err(self.error("Invalid escape in string")),
                    };
                    text.push(escaped);
                    self.advance(2);
                }
                Some(_) => {
                    let character = self.source[self.index..].chars().next().unwrap_or('\0');
                    text.push(character);
                    self.advance(character.len_utf8());
                }
            }
        }
        self.advance(1);
        let end_column = self.get_column() - 1;
        self.tokens.push(Token {
            kind: TokenKind::String,
            text: Rc::from(text),
            spelling: None,
            line,
            column,
            end_column,
        });
        Ok(())
    }

    fn read_word(&mut self) {
        let start = self.index;
        let word_end = skip_bytes(self.bytes, start, is_identifier_byte);
        let word = &self.source[start..word_end];
        let digits_end = skip_bytes(self.bytes, start, |byte| byte.is_ascii_digit());
        if digits_end == word_end {
            let fraction_end = if self.bytes.get(word_end) == Some(&b'.') {
                skip_bytes(self.bytes, word_end + 1, |byte| byte.is_ascii_digit())
            } else {
                word_end
            };
            let is_decimal = fraction_end > word_end + 1;
            let end = if is_decimal { fraction_end } else { word_end };
            let kind = if is_decimal {
                TokenKind::Decimal
            } else {
                TokenKind::Number
            };
            let text = self.name(&self.source[start..end]);
            return self.push(kind, text, end - start, None);
        }
        // A word needs a letter to be a name, so SANY reads one without as underscores and numbers.
        if !word.bytes().any(|byte| byte.is_ascii_alphabetic()) {
            return if self.bytes[start] == b'_' {
                {
                    let name = self.name("_");
                    self.push(TokenKind::Operator, name, 1, None)
                }
            } else {
                let digits = &self.source[start..digits_end];
                {
                    let name = self.name(digits);
                    self.push(TokenKind::Number, name, digits.len(), None)
                }
            };
        }
        if word.starts_with("WF_") || word.starts_with("SF_") {
            let name = self.name(&word[..3]);
            return self.push(TokenKind::Keyword, name, 3, None);
        }
        let kind = if KEYWORDS.binary_search(&word).is_ok() {
            TokenKind::Keyword
        } else {
            TokenKind::Identifier
        };
        let name = self.name(word);
        self.push(kind, name, word.len(), None);
    }

    fn run(&mut self) -> Result<(), SyntaxError> {
        while self.index < self.source.len() {
            let code = self.bytes[self.index];
            let rest = &self.source[self.index..];
            if matches!(code, b'\n' | b' ' | b'\t' | b'\r') {
                self.advance(1);
            } else if code == b'\\' && self.bytes.get(self.index + 1) == Some(&b'*') {
                let length = rest.find('\n').unwrap_or(rest.len());
                self.advance(length);
            } else if code == b'(' && self.bytes.get(self.index + 1) == Some(&b'*') {
                self.skip_comment()?;
            } else if code == b'-' && rest.starts_with("----") {
                let length = skip_bytes(self.bytes, self.index, |byte| byte == b'-') - self.index;
                if rest[length..]
                    .trim_start_matches(is_js_whitespace)
                    .starts_with("MODULE")
                {
                    self.module_depth += 1;
                }
                let name = self.name("----");
                self.push(TokenKind::Separator, name, length, None);
            } else if code == b'=' && rest.starts_with("====") {
                let length = skip_bytes(self.bytes, self.index, |byte| byte == b'=') - self.index;
                let name = self.name("====");
                self.push(TokenKind::ModuleEnd, name, length, None);
                self.module_depth -= 1;
                if self.module_depth <= 0 {
                    break;
                }
            } else if code == b'"' {
                self.read_string()?;
            } else if let length @ 1.. = match_based_number(self.bytes, self.index) {
                let name = self.name(&rest[..length]);
                self.push(TokenKind::Number, name, length, None);
            } else if is_identifier_byte(code) {
                self.read_word();
            } else if !code.is_ascii()
                && let Some(name) = UNICODE_NAMES.iter().find(|name| rest.starts_with(**name))
            {
                let name = self.name(name);
                self.push(TokenKind::Identifier, name.clone(), name.len(), None);
            } else if code == b'<'
                && let length @ 1.. = match_step(self.bytes, self.index)
            {
                let name = self.name(&rest[..length]);
                self.push(TokenKind::Step, name, length, None);
            } else if let Some(operator) = match_operator(self.source, self.index) {
                let spelling = &rest[..operator.length];
                let spelling = (spelling != operator.text).then(|| self.name(spelling));
                let text = self.name(operator.text);
                self.push(TokenKind::Operator, text, operator.length, spelling);
            } else {
                let character = rest.chars().next().unwrap_or('\0');
                // JavaScript reads one UTF-16 code unit, so a character outside the BMP is its
                // first surrogate.
                let mut quoted = String::new();
                if character.len_utf16() == 2 {
                    let mut units = [0; 2];
                    character.encode_utf16(&mut units);
                    quoted.push_str(&format!("\"\\u{:x}\"", units[0]));
                } else {
                    write_js_string(&mut quoted, character.encode_utf8(&mut [0; 4]));
                }
                return Err(self.error(&format!("Unexpected character {quoted}")));
            }
        }
        Ok(())
    }
}

pub fn tokenize(source: &str) -> Result<Vec<Token>, SyntaxError> {
    let header = find_module_header(source).ok_or_else(|| SyntaxError {
        message: "Expected a module header such as ---- MODULE Name ----".to_string(),
        failure: None,
        sany: None,
    })?;
    let prefix = &source[..header];
    let line_start = prefix.rfind('\n').map_or(0, |newline| newline + 1);
    let mut lexer = Lexer {
        source,
        bytes: source.as_bytes(),
        index: header,
        line: prefix.matches('\n').count() as u32 + 1,
        line_start,
        module_depth: 0,
        scan_line_start: usize::MAX,
        scan_position: 0,
        scan_width: 0,
        names: FastMap::default(),
        tokens: Vec::with_capacity(source.len() / 4),
    };
    lexer.run()?;
    let column = lexer.get_column();
    let text = lexer.name("");
    lexer.tokens.push(Token {
        kind: TokenKind::End,
        text,
        spelling: None,
        line: lexer.line,
        column,
        end_column: column,
    });
    Ok(lexer.tokens)
}

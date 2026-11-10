// Ported from Zenon's lexzen.mll and parsezen.mly, as shipped in tlapm. Copyright 2005 INRIA, see
// LICENSE.
//! Reads Zenon's native input format, the .znn files that tlapm writes.

use std::rc::Rc;

use crate::ZenonError;
use crate::expr::{Expr, Expressions, GOAL_NAME, Kind, UNIVERSE, efalse, etrue};

#[derive(Debug)]
pub enum Definition {
    Real {
        name: String,
        symbol: String,
        params: Vec<Expr>,
        body: Expr,
    },
    Pseudo {
        origin: Expr,
        goalness: i64,
        symbol: String,
        params: Vec<Expr>,
        body: Expr,
    },
}

impl Definition {
    pub fn symbol(&self) -> &str {
        match self {
            Definition::Real { symbol, .. } | Definition::Pseudo { symbol, .. } => symbol,
        }
    }

    pub fn params(&self) -> &[Expr] {
        match self {
            Definition::Real { params, .. } | Definition::Pseudo { params, .. } => params,
        }
    }

    pub fn body(&self) -> &Expr {
        match self {
            Definition::Real { body, .. } | Definition::Pseudo { body, .. } => body,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Phrase {
    Hyp {
        name: String,
        formula: Expr,
        goalness: i64,
    },
    Def(Rc<Definition>),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum TokenKind {
    Open,
    Close,
    Ident,
    String,
    Int,
    Keyword,
    Operator,
    End,
}

struct Token {
    kind: TokenKind,
    text: String,
    line: usize,
}

const OPERATORS: [&str; 7] = ["<=>", "-.", "/\\", "\\/", "=>", "<=", "="];

const DOTTED_KEYWORDS: [&str; 5] = ["T.", "F.", "A.", "E.", "t."];

const KEYWORDS: [&str; 12] = [
    "$fixpoint",
    "$include",
    "$indprop",
    "$indset",
    "$match",
    "$goal",
    "$self",
    "$def",
    "$fix",
    "$hyp",
    "$let",
    "$sig",
];

fn is_ident_start(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn is_ident_char(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'\'' | b'.')
}

/// The length of a string escape at the start of `bytes`, which starts with a backslash.
fn get_escape_length(bytes: &[u8]) -> Option<usize> {
    match bytes.get(1)? {
        b'a' | b'b' | b'f' | b'n' | b'r' | b't' | b'v' | b'\'' | b'"' | b'\\' | b'?' => Some(2),
        b'x' if bytes.len() >= 4 && bytes[2..4].iter().all(u8::is_ascii_hexdigit) => Some(4),
        _ => None,
    }
}

fn error(line: usize, message: &str) -> ZenonError {
    ZenonError::new(format!("Zenon: line {line}: {message}"))
}

fn tokenize(text: &str) -> Result<Vec<Token>, ZenonError> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut line = 1;
    let mut index = 0;
    let push = |tokens: &mut Vec<Token>, kind, text: &str, line| {
        tokens.push(Token {
            kind,
            text: text.to_owned(),
            line,
        })
    };
    while index < bytes.len() {
        let byte = bytes[index];
        if byte == b'\n' || byte == b'\r' {
            if !(byte == b'\r' && bytes.get(index + 1) == Some(&b'\n')) {
                line += 1;
            }
            index += 1;
        } else if matches!(byte, b' ' | b'\t' | 0x0c) {
            index += 1;
        } else if byte == b'#' || byte == b';' {
            while index < bytes.len() && bytes[index] != b'\n' && bytes[index] != b'\r' {
                index += 1;
            }
        } else if byte == b'(' || byte == b')' {
            let kind = if byte == b'(' {
                TokenKind::Open
            } else {
                TokenKind::Close
            };
            push(&mut tokens, kind, &text[index..=index], line);
            index += 1;
        } else if byte == b'$' {
            let digits = bytes[index + 1..]
                .iter()
                .take(31)
                .take_while(|byte| byte.is_ascii_digit())
                .count();
            if digits > 0 {
                push(
                    &mut tokens,
                    TokenKind::Int,
                    &text[index + 1..index + 1 + digits],
                    line,
                );
                index += 1 + digits;
            } else if let Some(keyword) = KEYWORDS
                .iter()
                .find(|keyword| text[index..].starts_with(*keyword))
            {
                push(&mut tokens, TokenKind::Keyword, keyword, line);
                index += keyword.len();
            } else {
                return Err(error(line, "bad character '$'"));
            }
        } else if byte == b'"' {
            let mut end = index + 1;
            while end < bytes.len() && bytes[end] != b'"' {
                if bytes[end] == b'\\' {
                    end += get_escape_length(&bytes[end..])
                        .ok_or_else(|| error(line, "bad escape in string"))?;
                } else if bytes[end] < 32 || bytes[end] >= 127 {
                    return Err(error(line, "bad character in string"));
                } else {
                    end += 1;
                }
            }
            if end >= bytes.len() {
                return Err(error(line, "unterminated string"));
            }
            push(&mut tokens, TokenKind::String, &text[index + 1..end], line);
            index = end + 1;
        } else if is_ident_start(byte) {
            let mut end = index + 1;
            while end < bytes.len() && is_ident_char(bytes[end]) {
                end += 1;
            }
            let word = &text[index..end];
            let kind = if DOTTED_KEYWORDS.contains(&word) {
                TokenKind::Keyword
            } else {
                TokenKind::Ident
            };
            push(&mut tokens, kind, word, line);
            index = end;
        } else {
            let Some(operator) = OPERATORS
                .iter()
                .find(|operator| text[index..].starts_with(*operator))
            else {
                // JavaScript names the UTF-16 code unit; a character outside the BMP is a pair.
                let char = text[index..].chars().next().unwrap_or_default();
                let unit = char.encode_utf16(&mut [0; 2])[0];
                let shown = char::from_u32(u32::from(unit)).unwrap_or(char::REPLACEMENT_CHARACTER);
                return Err(error(line, &format!("bad character '{shown}'")));
            };
            push(&mut tokens, TokenKind::Operator, operator, line);
            index += operator.len();
        }
    }
    push(&mut tokens, TokenKind::End, "", line);
    Ok(tokens)
}

/// Zenon's myfold: an n-ary connective nests to the right.
fn fold_right(
    exprs: &Expressions,
    kind: Kind,
    is_reversed: bool,
    first: Expr,
    rest: &[Expr],
) -> Expr {
    match rest.split_first() {
        None => first,
        Some((second, rest)) => {
            let right = fold_right(exprs, kind, is_reversed, second.clone(), rest);
            if is_reversed {
                exprs.binary(kind, &right, &first)
            } else {
                exprs.binary(kind, &first, &right)
            }
        }
    }
}

struct Lambda {
    names: Vec<String>,
    type_name: String,
    body: Expr,
}

struct Parser<'a> {
    exprs: &'a Expressions,
    tokens: Vec<Token>,
    position: usize,
}

impl Parser<'_> {
    fn peek(&self) -> &Token {
        &self.tokens[self.position]
    }

    fn next(&mut self) -> &Token {
        self.position += 1;
        &self.tokens[self.position - 1]
    }

    fn expect(&mut self, kind: TokenKind) -> Result<String, ZenonError> {
        let token = self.next();
        if token.kind != kind {
            return Err(error(token.line, "syntax error"));
        }
        Ok(token.text.clone())
    }

    fn is_at(&self, kind: TokenKind) -> bool {
        self.peek().kind == kind
    }

    /// A lambda after its first parenthesis: ((x y "type") body).
    fn parse_lambda(&mut self) -> Result<Lambda, ZenonError> {
        self.expect(TokenKind::Open)?;
        let mut names = Vec::new();
        while self.is_at(TokenKind::Ident) {
            names.push(self.next().text.clone());
        }
        let type_name = if self.is_at(TokenKind::String) {
            self.next().text.clone()
        } else {
            UNIVERSE.to_owned()
        };
        self.expect(TokenKind::Close)?;
        let body = self.parse_expr()?;
        self.expect(TokenKind::Close)?;
        Ok(Lambda {
            names,
            type_name,
            body,
        })
    }

    fn bind_all(&self, kind: Kind, lambda: Lambda) -> Expr {
        lambda.names.iter().rev().fold(lambda.body, |body, name| {
            self.exprs
                .binder(kind, &self.exprs.evar(name), &lambda.type_name, &body)
        })
    }

    fn parse_list(&mut self) -> Result<Vec<Expr>, ZenonError> {
        let mut expressions = Vec::new();
        while !self.is_at(TokenKind::Close) {
            expressions.push(self.parse_expr()?);
        }
        Ok(expressions)
    }

    fn parse_expr(&mut self) -> Result<Expr, ZenonError> {
        let exprs = self.exprs;
        let token = self.next();
        let (kind, text, line) = (token.kind, token.text.clone(), token.line);
        match (kind, text.as_str()) {
            (TokenKind::Ident, _) => return Ok(exprs.evar(&text)),
            (TokenKind::String, _) => {
                return Ok(exprs.eapp("$string", &[exprs.evar(&format!("\"{text}\""))]));
            }
            (TokenKind::Keyword, "T.") => return Ok(etrue()),
            (TokenKind::Keyword, "F.") => return Ok(efalse()),
            (TokenKind::Open, _) => {}
            _ => return Err(error(line, "syntax error")),
        }
        let head = self.next();
        let (kind, text, line) = (head.kind, head.text.clone(), head.line);
        match (kind, text.as_str()) {
            (TokenKind::Open, _) => {
                self.position -= 1;
                let lambda = self.parse_lambda()?;
                Ok(self.bind_all(Kind::Lam, lambda))
            }
            (TokenKind::Ident, _) => {
                let args = self.parse_list()?;
                self.expect(TokenKind::Close)?;
                Ok(exprs.eapp(&text, &args))
            }
            (TokenKind::Operator, "-.") => {
                let operand = self.parse_expr()?;
                self.expect(TokenKind::Close)?;
                Ok(exprs.enot(&operand))
            }
            (TokenKind::Operator, "=") => {
                let left = self.parse_expr()?;
                let right = self.parse_expr()?;
                self.expect(TokenKind::Close)?;
                Ok(exprs.eapp("=", &[left, right]))
            }
            (TokenKind::Operator, operator) => {
                let first = self.parse_expr()?;
                let rest = self.parse_list()?;
                self.expect(TokenKind::Close)?;
                let (kind, is_reversed) = match operator {
                    "/\\" => (Kind::And, false),
                    "\\/" => (Kind::Or, false),
                    "=>" => (Kind::Imply, false),
                    "<=" => (Kind::Imply, true),
                    _ => (Kind::Equiv, false),
                };
                Ok(fold_right(exprs, kind, is_reversed, first, &rest))
            }
            (TokenKind::Keyword, "T." | "F.") => {
                self.expect(TokenKind::Close)?;
                Ok(if text == "T." { etrue() } else { efalse() })
            }
            (TokenKind::Keyword, "A." | "E.") => {
                self.expect(TokenKind::Open)?;
                let lambda = self.parse_lambda()?;
                self.expect(TokenKind::Close)?;
                let kind = if text == "A." { Kind::All } else { Kind::Ex };
                Ok(self.bind_all(kind, lambda))
            }
            (TokenKind::Keyword, "t.") => {
                self.expect(TokenKind::Open)?;
                let lambda = self.parse_lambda()?;
                self.expect(TokenKind::Close)?;
                if lambda.names.len() != 1 {
                    return Err(error(line, "syntax error"));
                }
                let variable = exprs.evar(&lambda.names[0]);
                Ok(exprs.etau(&variable, &lambda.type_name, &lambda.body))
            }
            _ => Err(error(line, &format!("unsupported construct {text}"))),
        }
    }
}

/// `parseZenon`: the phrases of a .znn file.
pub fn parse_zenon(exprs: &Expressions, text: &str) -> Result<Vec<Phrase>, ZenonError> {
    let mut parser = Parser {
        exprs,
        tokens: tokenize(text)?,
        position: 0,
    };
    let mut phrases = Vec::new();
    while !parser.is_at(TokenKind::End) {
        let token = parser.next();
        let (kind, text, line) = (token.kind, token.text.clone(), token.line);
        match (kind, text.as_str()) {
            (TokenKind::Keyword, "$hyp") => {
                let goalness = if parser.is_at(TokenKind::Int) {
                    parser.next().text.parse::<f64>().unwrap_or(0.0) as i64
                } else {
                    1
                };
                let name = parser.expect(TokenKind::String)?;
                let formula = parser.parse_expr()?;
                phrases.push(Phrase::Hyp {
                    name,
                    formula,
                    goalness,
                });
            }
            (TokenKind::Keyword, "$goal") => {
                let formula = exprs.enot(&parser.parse_expr()?);
                phrases.push(Phrase::Hyp {
                    name: GOAL_NAME.to_owned(),
                    formula,
                    goalness: 0,
                });
            }
            (TokenKind::Keyword, "$def") => {
                let name = parser.expect(TokenKind::String)?;
                parser.expect(TokenKind::Open)?;
                let symbol = parser.expect(TokenKind::Ident)?;
                let mut params = Vec::new();
                while parser.is_at(TokenKind::Ident) {
                    params.push(exprs.evar(&parser.next().text.clone()));
                }
                parser.expect(TokenKind::Close)?;
                let body = parser.parse_expr()?;
                phrases.push(Phrase::Def(Rc::new(Definition::Real {
                    name,
                    symbol,
                    params,
                    body,
                })));
            }
            _ => return Err(error(line, &format!("unsupported phrase {text}"))),
        }
    }
    Ok(phrases)
}

//! Parses Isabelle's inner syntax, the terms inside quotes, as far as tlapm's theory printer
//! (isabelle.ml) uses it. The notation and its priorities come from Isabelle2025's Pure and from
//! the Isabelle/TLA+ theories that declare it: PredicateLogic, SetTheory, Functions, Tuples,
//! Strings and CaseExpressions. The translations those theories declare apply while parsing, so a
//! term comes out as constants, names, applications and abstractions only.

use std::rc::Rc;

use crate::error::{Error, Res, error_exn};
use crate::isar::theory::is_js_whitespace;
use crate::pure::term::{Name, Typ, fun_ts, mk_type, prop_t};

fn tla_type() -> Typ {
    thread_local!(static TLA_TYPE: Typ = mk_type("PredicateLogic.c", Vec::new()));
    TLA_TYPE.with(Clone::clone)
}

/// A parsed term before names resolve and types are inferred. A name is a bound or free variable
/// or a constant; a constant comes from notation.
pub enum Ast {
    Name(Name),
    Const(Name),
    App {
        fun: Rc<Ast>,
        arg: Rc<Ast>,
    },
    Abs {
        name: Name,
        ty: Option<Typ>,
        body: Rc<Ast>,
    },
    Constrain {
        term: Rc<Ast>,
        ty: Typ,
    },
}

enum Token {
    Id(String),
    Delimiter(String),
    String(String),
    End,
}

const DELIMITERS: [&str; 23] = [
    "::", ":>", "<<", ">>", "@@", "=>", "\\", "(", ")", "[", "]", "{", "}", ",", ":", ".", "%",
    "=", "&", "|", "~", "!", "0",
];

const KEYWORDS: [&str; 5] = ["EXCEPT", "DOMAIN", "SUBSET", "UNION", "PROP"];

fn is_letter(byte: Option<&u8>) -> bool {
    byte.is_some_and(u8::is_ascii_alphabetic)
}

fn is_id_char(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'\'')
}

/// `text.slice(0, length)` in UTF-16 code units, without a character that would be cut in half.
fn js_prefix(text: &str, length: usize) -> &str {
    let mut units = 0;
    let end = text
        .char_indices()
        .find(|(_, char)| {
            units += char.len_utf16();
            units > length
        })
        .map_or(text.len(), |(index, _)| index);
    &text[..end]
}

fn tokenize(text: &str) -> Res<Vec<Token>> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut position = 0;
    while let Some(char) = text[position..].chars().next() {
        if is_js_whitespace(char) {
            position += char.len_utf8();
            continue;
        }
        if text[position..].starts_with("''") {
            let Some(offset) = text[position + 2..].find("''") else {
                return Err(error_exn("Inner lexical error: unterminated string"));
            };
            let end = position + 2 + offset;
            tokens.push(Token::String(text[position + 2..end].to_string()));
            position = end + 2;
            continue;
        }
        if text[position..].starts_with("\\<") && is_letter(bytes.get(position + 2)) {
            // Where no > follows, Isabelle reports a lexical error.
            let Some(offset) = text[position..].find('>') else {
                return Err(error_exn(format!(
                    "Inner lexical error at: {}",
                    js_prefix(&text[position..], 20)
                )));
            };
            let end = position + offset;
            tokens.push(Token::Delimiter(text[position..=end].to_string()));
            position = end + 1;
            continue;
        }
        if is_letter(bytes.get(position)) {
            let mut end = position + 1;
            while end < bytes.len()
                && (is_id_char(bytes[end]) || (bytes[end] == b'.' && is_letter(bytes.get(end + 1))))
            {
                end += 1;
            }
            let word = &text[position..end];
            tokens.push(if KEYWORDS.contains(&word) {
                Token::Delimiter(word.to_string())
            } else {
                Token::Id(word.to_string())
            });
            position = end;
            continue;
        }
        let Some(delimiter) = DELIMITERS
            .iter()
            .find(|candidate| text[position..].starts_with(*candidate))
        else {
            return Err(error_exn(format!(
                "Inner lexical error at: {}",
                js_prefix(&text[position..], 20)
            )));
        };
        tokens.push(Token::Delimiter(delimiter.to_string()));
        position += delimiter.len();
    }
    tokens.push(Token::End);
    Ok(tokens)
}

fn constant(name: &str) -> Rc<Ast> {
    Rc::new(Ast::Const(name.into()))
}

fn apply(fun: Rc<Ast>, args: Vec<Rc<Ast>>) -> Rc<Ast> {
    args.into_iter()
        .fold(fun, |result, arg| Rc::new(Ast::App { fun: result, arg }))
}

/// Strings.thy: a string is the tuple of its characters, each a pair of nibbles.
fn nibble(value: u32) -> Rc<Ast> {
    if value == 0 {
        constant("Integers.zero")
    } else {
        apply(
            constant("Functions.fapply"),
            vec![constant("Integers.succ"), nibble(value - 1)],
        )
    }
}

fn string_term(text: &str) -> Res<Rc<Ast>> {
    text.chars()
        .try_fold(constant("Tuples.emptySeq"), |tuple, char| {
            let code = u32::from(char);
            if code >= 128 {
                return Err(error_exn(format!("Non-ASCII symbol: {char}")));
            }
            Ok(apply(
                constant("Tuples.Append"),
                vec![
                    tuple,
                    apply(
                        constant("Strings.char"),
                        vec![nibble(code >> 4), nibble(code & 15)],
                    ),
                ],
            ))
        })
}

fn tuple(elements: Vec<Rc<Ast>>) -> Rc<Ast> {
    elements
        .into_iter()
        .fold(constant("Tuples.emptySeq"), |result, element| {
            apply(constant("Tuples.Append"), vec![result, element])
        })
}

struct Infix {
    constant: &'static str,
    left: i32,
    right: i32,
    priority: i32,
}

fn infixl(name: &'static str, priority: i32) -> Infix {
    Infix {
        constant: name,
        left: priority,
        right: priority + 1,
        priority,
    }
}

fn infixr(name: &'static str, priority: i32) -> Infix {
    Infix {
        constant: name,
        left: priority + 1,
        right: priority,
        priority,
    }
}

/// INFIXES.get(text).
fn get_infix(text: &str) -> Option<Infix> {
    Some(match text {
        "\\<Rightarrow>" | "=>" => infixr("PredicateLogic.imp", 25),
        "\\<Leftrightarrow>" => infixr("PredicateLogic.iff", 25),
        "\\<or>" | "|" => infixr("PredicateLogic.disj", 30),
        "\\<and>" | "&" => infixr("PredicateLogic.conj", 35),
        "=" => infixl("PredicateLogic.eq", 50),
        "\\<noteq>" => infixl("PredicateLogic.not_equal", 50),
        "\\<in>" => infixl("SetTheory.in", 50),
        "\\<notin>" => infixl("SetTheory.notin", 50),
        "\\<subseteq>" => infixl("SetTheory.subset", 50),
        "\\<union>" => infixl("SetTheory.union", 65),
        "\\" => infixl("SetTheory.setminus", 65),
        "\\<inter>" => infixl("SetTheory.inter", 70),
        "@@" => infixl("Functions.extend", 70),
        ":>" => infixl("Functions.oneArg", 75),
        "\\<times>" => infixr("Tuples.prod", 100),
        _ => return None,
    })
}

struct Prefix {
    constant: &'static str,
    argument: i32,
    priority: i32,
}

/// PREFIXES.get(text).
fn get_prefix(text: &str) -> Option<Prefix> {
    let (constant, argument, priority) = match text {
        "~" | "\\<not>" => ("PredicateLogic.not", 40, 40),
        "SUBSET" => ("SetTheory.SUBSET", 100, 90),
        "UNION" => ("SetTheory.UNION", 100, 90),
        "DOMAIN" => ("Functions.DOMAIN", 100, 90),
        _ => return None,
    };
    Some(Prefix {
        constant,
        argument,
        priority,
    })
}

/// A parse result: the term, its priority, and whether it is a proposition rather than an object
/// of the logic, which Isabelle tells apart by syntactic category.
struct Parsed {
    ast: Rc<Ast>,
    priority: i32,
    is_prop: bool,
}

const MAX_PRIORITY: i32 = 1000;

fn term(ast: Rc<Ast>, priority: i32) -> Parsed {
    Parsed {
        ast,
        priority,
        is_prop: false,
    }
}

struct Binder {
    name: Name,
    ty: Option<Typ>,
}

struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    fn peek_at(&self, offset: usize) -> &Token {
        &self.tokens[(self.position + offset).min(self.tokens.len() - 1)]
    }

    fn peek(&self) -> &Token {
        self.peek_at(0)
    }

    fn is_delimiter_at(&self, text: &str, offset: usize) -> bool {
        matches!(self.peek_at(offset), Token::Delimiter(delimiter) if delimiter == text)
    }

    fn is_delimiter(&self, text: &str) -> bool {
        self.is_delimiter_at(text, 0)
    }

    /// The token's index, which next consumes.
    fn next(&mut self) -> usize {
        let index = self.position.min(self.tokens.len() - 1);
        self.position += 1;
        index
    }

    fn expect(&mut self, text: &str) -> Res<()> {
        if !self.is_delimiter(text) {
            return Err(self.syntax_error());
        }
        self.position += 1;
        Ok(())
    }

    fn syntax_error(&self) -> Error {
        error_exn(match self.peek() {
            Token::End => "Inner syntax error at: end of input".to_string(),
            Token::String(text) => format!("Inner syntax error at: ''{text}''"),
            Token::Id(text) | Token::Delimiter(text) => format!("Inner syntax error at: {text}"),
        })
    }

    fn identifier(&mut self) -> Res<Name> {
        let index = self.next();
        match &self.tokens[index] {
            Token::Id(text) => Ok(text.as_str().into()),
            _ => Err(self.syntax_error()),
        }
    }

    fn at_end(&self) -> bool {
        matches!(self.peek(), Token::End)
    }

    /// A type: c, prop, a function type, or [c, c] => c.
    fn ty(&mut self) -> Res<Typ> {
        let domains = if self.is_delimiter("[") {
            Some(self.type_list()?)
        } else {
            None
        };
        let atom = if domains.is_none() {
            Some(self.type_atom()?)
        } else {
            None
        };
        if self.is_delimiter("=>") || self.is_delimiter("\\<Rightarrow>") {
            self.position += 1;
            let range = self.ty()?;
            return Ok(fun_ts(
                &domains.unwrap_or_else(|| vec![atom.unwrap_or_else(tla_type)]),
                range,
            ));
        }
        atom.ok_or_else(|| self.syntax_error())
    }

    fn type_list(&mut self) -> Res<Vec<Typ>> {
        self.expect("[")?;
        let mut types = vec![self.ty()?];
        while self.is_delimiter(",") {
            self.position += 1;
            types.push(self.ty()?);
        }
        self.expect("]")?;
        Ok(types)
    }

    fn type_atom(&mut self) -> Res<Typ> {
        if self.is_delimiter("(") {
            self.position += 1;
            let ty = self.ty()?;
            self.expect(")")?;
            return Ok(ty);
        }
        let name = self.identifier()?;
        match &*name {
            "c" => Ok(tla_type()),
            "prop" => Ok(prop_t()),
            _ => Err(error_exn(format!("Undefined type name: {name}"))),
        }
    }

    /// Binder variables, each optionally constrained: x, x :: c.
    fn binders(&mut self, is_constrainable: bool) -> Res<Vec<Binder>> {
        let mut binders = Vec::new();
        while matches!(self.peek(), Token::Id(_)) {
            let name = self.identifier()?;
            if is_constrainable && self.is_delimiter("::") {
                self.position += 1;
                binders.push(Binder {
                    name,
                    ty: Some(self.ty()?),
                });
            } else {
                binders.push(Binder { name, ty: None });
            }
        }
        if binders.is_empty() {
            return Err(self.syntax_error());
        }
        Ok(binders)
    }

    fn comma_list(&mut self, close: &str) -> Res<Vec<Rc<Ast>>> {
        if self.is_delimiter(close) {
            self.position += 1;
            return Ok(Vec::new());
        }
        let mut items = vec![self.logic(0)?];
        while self.is_delimiter(",") {
            self.position += 1;
            items.push(self.logic(0)?);
        }
        self.expect(close)?;
        Ok(items)
    }

    /// An object-logic term of at least the given priority.
    fn logic(&mut self, minimum: i32) -> Res<Rc<Ast>> {
        let parsed = self.expression(minimum)?;
        if parsed.is_prop {
            return Err(error_exn(
                "Inner syntax error: proposition in term position",
            ));
        }
        Ok(parsed.ast)
    }

    /// A proposition: an object-logic term becomes one through Trueprop, as PredicateLogic's
    /// "(_)" 5 mixfix declares.
    fn prop(&mut self, minimum: i32) -> Res<Rc<Ast>> {
        let parsed = self.expression(minimum)?;
        Ok(if parsed.is_prop {
            parsed.ast
        } else {
            apply(constant("PredicateLogic.Trueprop"), vec![parsed.ast])
        })
    }

    fn expression(&mut self, minimum: i32) -> Res<Parsed> {
        let mut left = self.prefix(minimum)?;
        loop {
            let Token::Delimiter(text) = self.peek() else {
                return Ok(left);
            };
            let text = text.clone();
            if text == "\\<Longrightarrow>" {
                if minimum > 1 || (left.is_prop && left.priority < 2) {
                    return Ok(left);
                }
                self.position += 1;
                let premise = if left.is_prop {
                    left.ast
                } else {
                    apply(constant("PredicateLogic.Trueprop"), vec![left.ast])
                };
                left = Parsed {
                    ast: apply(constant("Pure.imp"), vec![premise, self.prop(1)?]),
                    priority: 1,
                    is_prop: true,
                };
                continue;
            }
            if left.is_prop {
                return Ok(left);
            }
            if text == "::" {
                if minimum > 3 || left.priority < 4 {
                    return Ok(left);
                }
                self.position += 1;
                left = term(
                    Rc::new(Ast::Constrain {
                        term: left.ast,
                        ty: self.ty()?,
                    }),
                    3,
                );
                continue;
            }
            if text == "(" {
                if left.priority < MAX_PRIORITY {
                    return Ok(left);
                }
                self.position += 1;
                let args = self.comma_list(")")?;
                if args.is_empty() {
                    return Err(self.syntax_error());
                }
                left = term(apply(left.ast, args), MAX_PRIORITY);
                continue;
            }
            if text == "[" {
                if minimum > 90 || left.priority < 89 {
                    return Ok(left);
                }
                self.position += 1;
                let index = self.logic(0)?;
                self.expect("]")?;
                left = term(
                    apply(constant("Functions.fapply"), vec![left.ast, index]),
                    90,
                );
                continue;
            }
            let Some(infix) = get_infix(&text) else {
                return Ok(left);
            };
            if infix.priority < minimum || left.priority < infix.left {
                return Ok(left);
            }
            self.position += 1;
            left = term(
                apply(
                    constant(infix.constant),
                    vec![left.ast, self.logic(infix.right)?],
                ),
                infix.priority,
            );
        }
    }

    fn prefix(&mut self, minimum: i32) -> Res<Parsed> {
        let index = self.next();
        let text = match &self.tokens[index] {
            Token::End => {
                self.position -= 1;
                return Err(self.syntax_error());
            }
            Token::Id(text) => {
                return Ok(term(Rc::new(Ast::Name(text.as_str().into())), MAX_PRIORITY));
            }
            Token::String(text) => return Ok(term(string_term(text)?, MAX_PRIORITY)),
            Token::Delimiter(text) => text.clone(),
        };
        match text.as_str() {
            "(" => {
                let inner = self.expression(0)?;
                self.expect(")")?;
                return Ok(Parsed {
                    priority: MAX_PRIORITY,
                    ..inner
                });
            }
            "0" => return Ok(term(constant("Integers.zero"), MAX_PRIORITY)),
            "{" => {
                if self.is_delimiter("}") {
                    self.position += 1;
                    return Ok(term(constant("SetTheory.emptyset"), 100));
                }
                return Ok(term(
                    self.comma_list("}")?
                        .into_iter()
                        .rev()
                        .fold(constant("SetTheory.emptyset"), |set, element| {
                            apply(constant("SetTheory.addElt"), vec![element, set])
                        }),
                    MAX_PRIORITY,
                ));
            }
            "<<" => {
                return Ok(term(
                    if self.is_delimiter(">>") {
                        self.next();
                        constant("Tuples.emptySeq")
                    } else {
                        tuple(self.comma_list(">>")?)
                    },
                    MAX_PRIORITY,
                ));
            }
            "\\<langle>" => {
                return Ok(term(tuple(self.comma_list("\\<rangle>")?), MAX_PRIORITY));
            }
            "[" => return self.bracket(),
            "\\<forall>" | "\\<exists>" => {
                return Ok(term(self.quantifier(text == "\\<forall>")?, 10));
            }
            "%" | "\\<lambda>" => {
                if minimum > 3 {
                    return Err(self.syntax_error());
                }
                let binders = self.binders(true)?;
                self.expect(".")?;
                let body = self.logic(3)?;
                return Ok(term(
                    binders.into_iter().rev().fold(body, |result, binder| {
                        Rc::new(Ast::Abs {
                            name: binder.name,
                            ty: binder.ty,
                            body: result,
                        })
                    }),
                    3,
                ));
            }
            "\\<And>" => {
                if minimum > 0 {
                    return Err(self.syntax_error());
                }
                let binders = self.binders(true)?;
                self.expect(".")?;
                let body = self.prop(0)?;
                return Ok(Parsed {
                    ast: binders.into_iter().rev().fold(body, |result, binder| {
                        apply(
                            constant("Pure.all"),
                            vec![Rc::new(Ast::Abs {
                                name: binder.name,
                                ty: binder.ty,
                                body: result,
                            })],
                        )
                    }),
                    priority: 0,
                    is_prop: true,
                });
            }
            _ => {}
        }
        let prefix = match get_prefix(&text) {
            Some(prefix) if prefix.priority >= minimum => prefix,
            _ => {
                self.position -= 1;
                return Err(self.syntax_error());
            }
        };
        Ok(term(
            apply(
                constant(prefix.constant),
                vec![self.logic(prefix.argument)?],
            ),
            prefix.priority,
        ))
    }

    /// \<forall>x, y : P and \<forall>x, y \<in> S : P, with \<exists> alike.
    fn quantifier(&mut self, is_forall: bool) -> Res<Rc<Ast>> {
        let mut names = vec![self.identifier()?];
        while self.is_delimiter(",") {
            self.position += 1;
            names.push(self.identifier()?);
        }
        if self.is_delimiter(":") {
            self.position += 1;
            let body = self.logic(10)?;
            let quantifier = constant(if is_forall {
                "PredicateLogic.All"
            } else {
                "PredicateLogic.Ex"
            });
            return Ok(names.into_iter().rev().fold(body, |result, name| {
                apply(
                    quantifier.clone(),
                    vec![Rc::new(Ast::Abs {
                        name,
                        ty: None,
                        body: result,
                    })],
                )
            }));
        }
        self.expect("\\<in>")?;
        let domain = self.logic(0)?;
        self.expect(":")?;
        let body = self.logic(0)?;
        let quantifier = constant(if is_forall {
            "SetTheory.bAll"
        } else {
            "SetTheory.bEx"
        });
        Ok(names.into_iter().rev().fold(body, |result, name| {
            apply(
                quantifier.clone(),
                vec![
                    domain.clone(),
                    Rc::new(Ast::Abs {
                        name,
                        ty: None,
                        body: result,
                    }),
                ],
            )
        }))
    }

    /// The bracketed forms: [x \<in> S \<mapsto> e], [S \<rightarrow> T], [f EXCEPT ![x] = e, ...]
    /// and [d : r, ...].
    fn bracket(&mut self) -> Res<Parsed> {
        if matches!(self.peek(), Token::Id(_)) && self.is_delimiter_at("\\<in>", 1) {
            let name = self.identifier()?;
            self.position += 1;
            let domain = self.logic(0)?;
            self.expect("\\<mapsto>")?;
            let body = self.logic(0)?;
            self.expect("]")?;
            return Ok(term(
                apply(
                    constant("Functions.Fcn"),
                    vec![
                        domain,
                        Rc::new(Ast::Abs {
                            name,
                            ty: None,
                            body,
                        }),
                    ],
                ),
                900,
            ));
        }
        let first = self.logic(0)?;
        if self.is_delimiter("\\<rightarrow>") {
            self.position += 1;
            let range = self.logic(0)?;
            self.expect("]")?;
            return Ok(term(
                apply(constant("Functions.FuncSet"), vec![first, range]),
                900,
            ));
        }
        if self.is_delimiter("EXCEPT") {
            self.position += 1;
            let mut result = first;
            loop {
                self.expect("!")?;
                self.expect("[")?;
                let index = self.logic(0)?;
                self.expect("]")?;
                self.expect("=")?;
                result = apply(
                    constant("Functions.except"),
                    vec![result, index, self.logic(0)?],
                );
                if !self.is_delimiter(",") {
                    break;
                }
                self.position += 1;
            }
            self.expect("]")?;
            return Ok(term(result, 900));
        }
        self.expect(":")?;
        let mut domains = vec![first];
        let mut ranges = vec![self.logic(0)?];
        while self.is_delimiter(",") {
            self.position += 1;
            domains.push(self.logic(0)?);
            self.expect(":")?;
            ranges.push(self.logic(0)?);
        }
        self.expect("]")?;
        Ok(term(
            apply(
                constant("Tuples.EnumFuncSet"),
                vec![tuple(domains), tuple(ranges)],
            ),
            MAX_PRIORITY,
        ))
    }
}

fn parse_with<Result>(text: &str, parse: impl FnOnce(&mut Parser) -> Res<Result>) -> Res<Result> {
    let mut parser = Parser {
        tokens: tokenize(text)?,
        position: 0,
    };
    let result = parse(&mut parser)?;
    if !parser.at_end() {
        return Err(error_exn(format!(
            "Inner syntax error: trailing input in {}",
            js_prefix(text, 40)
        )));
    }
    Ok(result)
}

pub fn parse_prop(text: &str) -> Res<Rc<Ast>> {
    parse_with(text, |parser| parser.prop(0))
}

pub fn parse_type(text: &str) -> Res<Typ> {
    parse_with(text, |parser| parser.ty())
}

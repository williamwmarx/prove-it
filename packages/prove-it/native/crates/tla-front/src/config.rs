//! TLC's model configuration, as `src/config.ts` reads it: a port of TLC's `ModelConfig.parse`,
//! which reads its tokens with SANY's lexer and takes any token where it expects a name or a
//! value. Columns count UTF-16 code units, as in TypeScript.

use crate::TlcVersion;
use crate::lexer::{is_js_whitespace, match_operator, match_unicode_token};

#[derive(Clone, Debug, PartialEq)]
pub enum ConfigValue {
    Number(f64),
    String(String),
    Boolean(bool),
    ModelValue(String),
    Set(Vec<ConfigValue>),
    /// A record the constant evaluator builds, its fields in TLC's order of their names. A
    /// configuration has none.
    Record(Vec<(String, ConfigValue)>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct ConstantAssignment {
    pub name: String,
    pub value: ConfigValue,
    pub args: Option<Vec<ConfigValue>>,
    pub module: Option<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Substitution {
    pub name: String,
    pub target: String,
    pub module: Option<String>,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct ModelConfig {
    pub init: Option<String>,
    pub next: Option<String>,
    pub specification: Option<String>,
    pub invariants: Vec<String>,
    pub properties: Vec<String>,
    pub constraints: Vec<String>,
    pub action_constraints: Vec<String>,
    pub constants: Vec<ConstantAssignment>,
    pub substitutions: Vec<Substitution>,
    pub check_deadlock: bool,
    pub symmetry: Option<String>,
    pub view: Option<String>,
    pub alias: Option<String>,
    pub postconditions: Vec<String>,
    pub possible: Vec<String>,
    pub periodic: Option<String>,
    pub rl_reward: Option<String>,
}

/// `TlaConfigError`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigError {
    pub message: String,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Word,
    Number,
    String,
    Symbol,
    End,
    Error,
}

struct ConfigToken {
    kind: Kind,
    text: String,
    line: u32,
}

const SHARED_KEYWORDS: &[&str] = &[
    "CONSTANT",
    "CONSTANTS",
    "INIT",
    "NEXT",
    "SPECIFICATION",
    "INVARIANT",
    "INVARIANTS",
    "PROPERTY",
    "PROPERTIES",
    "CONSTRAINT",
    "CONSTRAINTS",
    "ACTION_CONSTRAINT",
    "ACTION_CONSTRAINTS",
    "SYMMETRY",
    "VIEW",
    "CHECK_DEADLOCK",
];

const MASTER_KEYWORDS: &[&str] = &[
    "ALIAS",
    "POSTCONDITION",
    "POSTCONDITIONS",
    "_POSSIBLE",
    "_PERIODIC",
    "_RL_REWARD",
];

/// TLC 1.7.4 reads a TYPE and a TYPE_CONSTRAINT, which it doesn't check, and none of the keywords
/// that came after it.
const TYPE_KEYWORDS: &[&str] = &["TYPE", "TYPE_CONSTRAINT"];

const SYMBOLS: &[&str] = &[
    "<-", "<<", ">>", "=", "{", "}", ",", "[", "]", "(", ")", "!",
];

fn is_keyword(word: &str, version: TlcVersion) -> bool {
    SHARED_KEYWORDS.contains(&word)
        || match version {
            TlcVersion::Master => MASTER_KEYWORDS.contains(&word),
            TlcVersion::V1_7_4 => TYPE_KEYWORDS.contains(&word),
        }
}

/// JavaCC's `TokenMgrError.addEscapes`, which escapes the characters of a lexical error's
/// message, a UTF-16 code unit at a time.
pub fn escape_lexeme(text: &str) -> String {
    let mut escaped = String::new();
    for unit in text.encode_utf16() {
        match unit {
            0 => {}
            0x08 => escaped.push_str("\\b"),
            0x09 => escaped.push_str("\\t"),
            0x0a => escaped.push_str("\\n"),
            0x0c => escaped.push_str("\\f"),
            0x0d => escaped.push_str("\\r"),
            0x22 => escaped.push_str("\\\""),
            0x27 => escaped.push_str("\\'"),
            0x5c => escaped.push_str("\\\\"),
            0x01..=0x1f | 0x7f.. => escaped.push_str(&format!("\\u{unit:04x}")),
            _ => escaped.push(char::from(unit as u8)),
        }
    }
    escaped
}

/// `TokenMgrError.LexicalError`: the character (a UTF-16 code unit) the lexer stopped at, or the
/// end of the file, and the characters of the token it had read.
pub fn format_lexical_error(line: u32, column: u32, character: Option<u16>, after: &str) -> String {
    let encountered = match character {
        None => "<EOF> ".to_string(),
        Some(unit) => {
            let text = String::from_utf16_lossy(&[unit]);
            let escaped = if (0xd800..0xe000).contains(&unit) {
                format!("\\u{unit:04x}")
            } else {
                escape_lexeme(&text)
            };
            format!("\"{escaped}\" ({unit}), ")
        }
    };
    format!(
        "Lexical error at line {line}, column {column}.  Encountered: {encountered}after : \"{}\"",
        escape_lexeme(after)
    )
}

fn utf16_length(text: &str) -> u32 {
    text.encode_utf16().count() as u32
}

struct Tokenizer<'a> {
    source: &'a str,
    index: usize,
    line: u32,
    line_start: usize,
    tokens: Vec<ConfigToken>,
}

impl Tokenizer<'_> {
    fn skip(&mut self, length: usize) {
        let text = &self.source[self.index..self.index + length];
        if let Some(last) = text.rfind('\n') {
            self.line += text.matches('\n').count() as u32;
            self.line_start = self.index + last + 1;
        }
        self.index += length;
    }

    fn push(&mut self, kind: Kind, text: String, line: u32) {
        self.tokens.push(ConfigToken { kind, text, line });
    }

    fn lexical_error(&mut self, after: &str) {
        let column = utf16_length(&self.source[self.line_start..self.index]) + 1;
        let character = self.source[self.index..].encode_utf16().next();
        let text = format_lexical_error(self.line, column, character, after);
        self.push(Kind::Error, text, self.line);
    }

    /// TLC appends a newline to the file. JavaCC reports a token that the end of the input cuts
    /// off, that newline included, at the start of the line after it.
    fn end_of_input_error(&mut self, after: &str) {
        let text = format_lexical_error(self.line + 1, 0, None, after);
        self.push(Kind::Error, text, self.line);
    }

    /// The length of `/^"((?:[^"\\\n]|\\[^\n])*)("?)/`'s match, and whether it ends in a quote.
    fn match_string(rest: &str) -> (usize, bool) {
        let bytes = rest.as_bytes();
        let mut index = 1;
        loop {
            match bytes.get(index) {
                Some(b'"') => return (index + 1, true),
                Some(b'\\') if bytes.get(index + 1).is_some_and(|next| *next != b'\n') => {
                    let next = rest[index + 1..].chars().next().map_or(1, char::len_utf8);
                    index += 1 + next;
                }
                None | Some(b'\\' | b'\n') => return (index, false),
                Some(_) => index += rest[index..].chars().next().map_or(1, char::len_utf8),
            }
        }
    }

    fn run(mut self) -> Vec<ConfigToken> {
        while self.index < self.source.len() {
            let rest = &self.source[self.index..];
            let whitespace = rest.len() - rest.trim_start_matches(is_js_whitespace).len();
            if whitespace > 0 {
                self.skip(whitespace);
                continue;
            }
            if rest.starts_with("\\*") {
                self.skip(rest.find('\n').unwrap_or(rest.len()));
                continue;
            }
            if rest.starts_with("(*") {
                let Some(end) = rest.find("*)") else {
                    self.skip(rest.len());
                    self.end_of_input_error("");
                    return self.tokens;
                };
                self.skip(end + 2);
                continue;
            }
            let line = self.line;
            let bytes = rest.as_bytes();
            let digits = bytes
                .iter()
                .take_while(|byte| byte.is_ascii_digit())
                .count();
            // `/^\d+(?![A-Za-z_])/` backs off a digit before a letter.
            let is_word_after = bytes
                .get(digits)
                .is_some_and(|byte| byte.is_ascii_alphabetic() || *byte == b'_');
            let number = if is_word_after {
                digits.saturating_sub(1)
            } else {
                digits
            };
            if number > 0 {
                self.push(Kind::Number, rest[..number].to_string(), line);
                self.skip(number);
                continue;
            }
            let word = bytes
                .iter()
                .take_while(|byte| byte.is_ascii_alphanumeric() || **byte == b'_')
                .count();
            if word > 0 {
                self.push(Kind::Word, rest[..word].to_string(), line);
                self.skip(word);
                continue;
            }
            if rest.starts_with('"') {
                let (length, is_closed) = Self::match_string(rest);
                let text = &rest[..length];
                if !is_closed {
                    self.skip(length);
                    if self.index == self.source.len() {
                        self.end_of_input_error(&format!("{text}\n"));
                    } else {
                        self.lexical_error(text);
                    }
                    return self.tokens;
                }
                self.push(Kind::String, text[1..length - 1].to_string(), line);
                self.skip(length);
                continue;
            }
            if let Some(symbol) = SYMBOLS.iter().find(|symbol| rest.starts_with(**symbol)) {
                self.push(Kind::Symbol, symbol.to_string(), line);
                self.skip(symbol.len());
                continue;
            }
            let operator = match_unicode_token(self.source, self.index)
                .map(|token| (token.to_string(), token.len()))
                .or_else(|| {
                    match_operator(self.source, self.index)
                        .map(|operator| (operator.text.to_string(), operator.length))
                });
            let Some((text, length)) = operator else {
                self.lexical_error("");
                return self.tokens;
            };
            self.push(Kind::Word, text, line);
            self.skip(length);
        }
        let line = self.line;
        self.push(Kind::End, String::new(), line);
        self.tokens
    }
}

/// TLC's messages for a configuration file it can't read, from `ModelConfig.parse`.
fn syntax_error(line: u32, problem: &str) -> ConfigError {
    ConfigError {
        message: format!("TLC found an error in the configuration file at line {line}\n{problem}"),
    }
}

fn duplicate_keyword_error(line: u32, keyword: &str) -> ConfigError {
    syntax_error(line, &format!("The keyword {keyword} appeared twice."))
}

type Parsed<T> = Result<T, ConfigError>;

struct Parser {
    tokens: Vec<ConfigToken>,
    index: usize,
    version: TlcVersion,
    config: ModelConfig,
}

impl Parser {
    fn advance(&mut self) -> Parsed<(Kind, String, u32)> {
        let token = &self.tokens[self.index.min(self.tokens.len() - 1)];
        self.index += 1;
        if token.kind == Kind::Error {
            return Err(ConfigError {
                message: format!(
                    "TLC found an error in the configuration file:\n{}",
                    token.text
                ),
            });
        }
        Ok((token.kind, token.text.clone(), token.line))
    }

    fn is_keyword(&self, word: &str) -> bool {
        is_keyword(word, self.version)
    }

    fn parse_value(&mut self, token: (Kind, String, u32)) -> Parsed<ConfigValue> {
        let (kind, text, line) = token;
        if kind == Kind::Number {
            return Ok(ConfigValue::Number(text.parse().unwrap_or(f64::NAN)));
        }
        if kind == Kind::String {
            return Ok(ConfigValue::String(text));
        }
        if text == "TRUE" || text == "FALSE" {
            return Ok(ConfigValue::Boolean(text == "TRUE"));
        }
        if text == "{" {
            let mut elements = Vec::new();
            let mut current = self.advance()?;
            if current.1 != "}" {
                loop {
                    elements.push(self.parse_value(current)?);
                    current = self.advance()?;
                    if current.1 != "," {
                        break;
                    }
                    current = self.advance()?;
                }
            }
            if current.1 != "}" {
                return Err(syntax_error(
                    current.2,
                    "It was expecting }, but did not find it.",
                ));
            }
            return Ok(ConfigValue::Set(elements));
        }
        if kind != Kind::End {
            return Ok(ConfigValue::ModelValue(text));
        }
        Err(syntax_error(
            line,
            "It was expecting a value, but did not find it.",
        ))
    }

    /// A module name in brackets after `=` or `<-`, which applies the assignment in that module.
    fn parse_module_scope(&mut self, operator: &str) -> Parsed<String> {
        let name = self.advance()?;
        if name.0 == Kind::End {
            return Err(syntax_error(
                name.2,
                &format!("Expected an identifier after {operator}[."),
            ));
        }
        let close = self.advance()?;
        if close.1 != "]" {
            return Err(syntax_error(
                close.2,
                "It was expecting ], but did not find it.",
            ));
        }
        Ok(name.1)
    }

    /// TLC reports a malformed argument list at the line of the CONSTANT keyword.
    fn parse_constants(&mut self, keyword_line: u32) -> Parsed<(Kind, String, u32)> {
        loop {
            let first = self.advance()?;
            if first.0 == Kind::End || self.is_keyword(&first.1) {
                return Ok(first);
            }
            let mut current = self.advance()?;
            let mut name = first.1;
            while current.1 == "!" {
                name = format!("{name}!{}", self.advance()?.1);
                current = self.advance()?;
            }
            if current.1 == "<-" {
                current = self.advance()?;
                if current.1 == "[" {
                    let module = self.parse_module_scope("<-")?;
                    let target = self.advance()?;
                    if target.0 == Kind::End {
                        return Err(syntax_error(
                            target.2,
                            "Expected an identifier after <-[mod].",
                        ));
                    }
                    self.config.substitutions.push(Substitution {
                        name,
                        target: target.1,
                        module: Some(module),
                    });
                    continue;
                }
                if current.0 == Kind::End {
                    return Err(syntax_error(current.2, "Expected an identifier after <-."));
                }
                self.config.substitutions.push(Substitution {
                    name,
                    target: current.1,
                    module: None,
                });
                continue;
            }
            let mut args = Vec::new();
            let has_args = current.1 == "(";
            if has_args {
                loop {
                    let token = self.advance()?;
                    args.push(self.parse_value(token)?);
                    current = self.advance()?;
                    if current.1 != "," {
                        break;
                    }
                }
                if current.1 != ")" {
                    return Err(syntax_error(keyword_line, ""));
                }
                current = self.advance()?;
            }
            if current.1 != "=" {
                return Err(syntax_error(
                    current.2,
                    "It was expecting = or <-, but did not find it.",
                ));
            }
            current = self.advance()?;
            let module = if current.1 == "[" {
                Some(self.parse_module_scope("=")?)
            } else {
                None
            };
            let token = if module.is_none() {
                current
            } else {
                self.advance()?
            };
            let value = self.parse_value(token)?;
            self.config.constants.push(ConstantAssignment {
                name,
                value,
                args: has_args.then_some(args),
                module,
            });
        }
    }

    fn parse_names(
        &mut self,
        list: fn(&mut ModelConfig) -> &mut Vec<String>,
    ) -> Parsed<(Kind, String, u32)> {
        loop {
            let token = self.advance()?;
            if token.0 == Kind::End || self.is_keyword(&token.1) {
                return Ok(token);
            }
            list(&mut self.config).push(token.1);
        }
    }
}

fn get_single(keyword: &str) -> Option<fn(&mut ModelConfig) -> &mut Option<String>> {
    Some(match keyword {
        "INIT" => |config| &mut config.init,
        "NEXT" => |config| &mut config.next,
        "SPECIFICATION" => |config| &mut config.specification,
        "VIEW" => |config| &mut config.view,
        "SYMMETRY" => |config| &mut config.symmetry,
        "ALIAS" => |config| &mut config.alias,
        "_PERIODIC" => |config| &mut config.periodic,
        "_RL_REWARD" => |config| &mut config.rl_reward,
        _ => return None,
    })
}

fn get_list(keyword: &str) -> Option<fn(&mut ModelConfig) -> &mut Vec<String>> {
    Some(match keyword {
        "INVARIANT" | "INVARIANTS" => |config| &mut config.invariants,
        "PROPERTY" | "PROPERTIES" => |config| &mut config.properties,
        "CONSTRAINT" | "CONSTRAINTS" => |config| &mut config.constraints,
        "ACTION_CONSTRAINT" | "ACTION_CONSTRAINTS" => |config| &mut config.action_constraints,
        "POSTCONDITION" | "POSTCONDITIONS" => |config| &mut config.postconditions,
        "_POSSIBLE" => |config| &mut config.possible,
        _ => return None,
    })
}

/// `parseConfig`.
pub fn parse_config(source: &str, version: TlcVersion) -> Result<ModelConfig, ConfigError> {
    let tokens = Tokenizer {
        source,
        index: 0,
        line: 1,
        line_start: 0,
        tokens: Vec::new(),
    }
    .run();
    let mut parser = Parser {
        tokens,
        index: 0,
        version,
        config: ModelConfig {
            check_deadlock: true,
            ..ModelConfig::default()
        },
    };
    let mut is_deadlock_set = false;
    let mut type_keywords: Vec<String> = Vec::new();
    let mut current = parser.advance()?;
    while current.0 != Kind::End {
        let keyword = current.1.clone();
        let line = current.2;
        let is_known = parser.is_keyword(&keyword);
        let advance_to_argument = |parser: &mut Parser| {
            let argument = parser.advance()?;
            if argument.0 == Kind::End {
                return Err(syntax_error(
                    line,
                    &format!("The keyword {keyword} was not followed by an identifier."),
                ));
            }
            Ok(argument)
        };
        if let Some(single) = get_single(&keyword).filter(|_| is_known) {
            let name = advance_to_argument(&mut parser)?;
            let slot = single(&mut parser.config);
            if slot.is_some() {
                return Err(duplicate_keyword_error(line, &keyword));
            }
            *slot = Some(name.1);
            current = parser.advance()?;
            continue;
        }
        if let Some(list) = get_list(&keyword).filter(|_| is_known) {
            current = parser.parse_names(list)?;
            continue;
        }
        if keyword == "CONSTANT" || keyword == "CONSTANTS" {
            current = parser.parse_constants(line)?;
            continue;
        }
        if keyword == "CHECK_DEADLOCK" {
            let value = advance_to_argument(&mut parser)?;
            if value.1 != "TRUE" && value.1 != "FALSE" {
                return Err(syntax_error(
                    value.2,
                    "It was expecting TRUE or FALSE, but did not find it.",
                ));
            }
            if is_deadlock_set {
                return Err(duplicate_keyword_error(line, &keyword));
            }
            is_deadlock_set = true;
            parser.config.check_deadlock = value.1 == "TRUE";
            current = parser.advance()?;
            continue;
        }
        if !is_known || !TYPE_KEYWORDS.contains(&keyword.as_str()) {
            return Err(syntax_error(
                line,
                "It was expecting a keyword, but did not find it.",
            ));
        }
        advance_to_argument(&mut parser)?;
        if type_keywords.contains(&keyword) {
            return Err(duplicate_keyword_error(line, &keyword));
        }
        type_keywords.push(keyword);
        current = parser.advance()?;
    }
    Ok(parser.config)
}

//! TLA+'s parser, as `src/parser.ts` parses in its `tlc` and `sany` modes: the same AST, with the
//! same locations and ranges, and the same errors. The `tlapm` mode, which reads proof obligations
//! as tlapm does, is not ported, since the model checker never uses it.

use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::*;
use crate::errors::{SanyError, SyntaxError, SyntaxFailure, format_range};
use crate::hash::FastSet;
use crate::json::write_js_string;
use crate::lexer::{Token, TokenKind, read_at_as_identifier, tokenize};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Precedence {
    low: u32,
    high: u32,
}

#[derive(Clone, Copy)]
struct InfixOperator {
    low: u32,
    high: u32,
    is_associative: bool,
}

/// SANY's precedences of a postfix operator and of the `[` of a function application.
const POSTFIX_PRECEDENCE: Precedence = Precedence { low: 15, high: 15 };
const FUNCTION_PRECEDENCE: Precedence = Precedence { low: 16, high: 16 };

const NEGATION_PRECEDENCE: u32 = 12;

fn get_infix(text: &str) -> Option<InfixOperator> {
    let infix = |low, high, is_associative| {
        Some(InfixOperator {
            low,
            high,
            is_associative,
        })
    };
    match text {
        "=" | "#" | "<" | ">" | "<=" | ">=" | "\\in" | "\\notin" | "\\subseteq" | "\\subset"
        | "\\supseteq" | "\\supset" | "\\sqsubseteq" | "\\sqsupseteq" | "\\sqsubset"
        | "\\sqsupset" | "\\prec" | "\\preceq" | "\\succ" | "\\succeq" | "\\sim" | "\\simeq"
        | "\\approx" | "\\cong" | "\\asymp" | "\\doteq" | "\\propto" | "\\ll" | "\\gg" | "|-"
        | "-|" | "|=" | "=|" | ":=" | "::=" => infix(5, 5, false),
        "=>" => infix(1, 1, false),
        "<=>" | "~>" | "-+->" => infix(2, 2, false),
        "/\\" | "\\/" => infix(3, 3, true),
        "\\cdot" => infix(5, 14, true),
        "@@" => infix(6, 6, true),
        ":>" | "<:" => infix(7, 7, false),
        "\\cup" | "\\cap" => infix(8, 8, true),
        "\\" => infix(8, 8, false),
        ".." | "..." => infix(9, 9, false),
        "##" | "$" | "$$" | "??" | "\\sqcap" | "\\sqcup" | "\\uplus" => infix(9, 13, true),
        "!!" => infix(9, 13, false),
        "\\wr" => infix(9, 14, false),
        "+" | "++" | "(+)" | "\\oplus" => infix(10, 10, true),
        "%" => infix(10, 11, false),
        "%%" | "|" | "||" => infix(10, 11, true),
        "\\X" => infix(10, 13, false),
        "-" | "--" | "(-)" | "\\ominus" => infix(11, 11, true),
        "*" | "**" | "\\o" | "(.)" | "\\odot" | "(\\X)" | "\\otimes" | "&" | "&&" | "\\star"
        | "\\bullet" | "\\bigcirc" => infix(13, 13, true),
        "/" | "//" | "\\div" | "(/)" | "\\oslash" => infix(13, 13, false),
        "^" | "^^" => infix(14, 14, false),
        _ => None,
    }
}

pub fn is_infix(text: &str) -> bool {
    get_infix(text).is_some()
}

fn is_postfix(text: &str) -> bool {
    matches!(text, "^+" | "^*" | "^#")
}

fn is_prefix_operator_reference(text: &str) -> bool {
    matches!(text, "-" | "~" | "-.")
}

/// The prefix operators SANY reads in a definition's left-hand side, built-in ones included.
fn is_definable_prefix(text: &str) -> bool {
    matches!(
        text,
        "-." | "~" | "[]" | "<>" | "ENABLED" | "UNCHANGED" | "SUBSET" | "UNION" | "DOMAIN"
    )
}

fn is_expression_prefix(text: &str) -> bool {
    matches!(
        text,
        "-" | "~"
            | "/\\"
            | "\\/"
            | "SUBSET"
            | "UNION"
            | "DOMAIN"
            | "ENABLED"
            | "UNCHANGED"
            | "[]"
            | "<>"
    )
}

fn is_operator_argument(text: &str) -> bool {
    matches!(
        text,
        "SUBSET" | "UNION" | "DOMAIN" | "ENABLED" | "UNCHANGED" | "[]" | "<>" | "'"
    ) || is_postfix(text)
}

fn is_unit_keyword(text: &str) -> bool {
    matches!(
        text,
        "ASSUME"
            | "ASSUMPTION"
            | "AXIOM"
            | "CONSTANT"
            | "CONSTANTS"
            | "COROLLARY"
            | "INSTANCE"
            | "LEMMA"
            | "LOCAL"
            | "PROPOSITION"
            | "RECURSIVE"
            | "THEOREM"
            | "VARIABLE"
            | "VARIABLES"
    )
}

fn is_fact_keyword(text: &str) -> bool {
    matches!(
        text,
        "CASE"
            | "CHOOSE"
            | "DOMAIN"
            | "ENABLED"
            | "IF"
            | "LAMBDA"
            | "LET"
            | "MODULE"
            | "SF_"
            | "SUBSET"
            | "UNCHANGED"
            | "UNION"
            | "WF_"
    )
}

fn get_new_symbol_level(text: &str) -> Option<SymbolLevel> {
    match text {
        "CONSTANT" | "CONSTANTS" => Some(SymbolLevel::Constant),
        "VARIABLE" | "VARIABLES" => Some(SymbolLevel::Variable),
        "STATE" => Some(SymbolLevel::State),
        "ACTION" | "ACTIONS" => Some(SymbolLevel::Action),
        "TEMPORAL" | "TEMPORALS" => Some(SymbolLevel::Temporal),
        _ => None,
    }
}

fn is_builtin_constant(text: &str) -> bool {
    matches!(text, "TRUE" | "FALSE" | "BOOLEAN" | "STRING")
}

fn is_operator_name(text: &str) -> bool {
    is_infix(text) || is_postfix(text) || text == "-."
}

fn is_unnamed_step_label(label: &str) -> bool {
    matches!(label, "" | "*" | "-")
}

/// A SANY InfixExpr or PostfixExpr.
fn is_operator_expression(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Prime(_) | ExpressionKind::Product(_) => true,
        ExpressionKind::Junction { is_bulleted, .. } => !is_bulleted,
        ExpressionKind::Apply { operator, args, .. } => {
            if args.len() == 2 {
                is_infix(operator)
            } else {
                is_postfix(operator)
            }
        }
        _ => false,
    }
}

/// The value of a numeral as typed, such as `\hFF`, as JavaScript's `Number` and `parseInt` give it.
pub fn get_numeral_value(text: &str) -> f64 {
    let Some(based) = text.strip_prefix('\\') else {
        return text.parse().unwrap_or(f64::NAN);
    };
    let radix = match based.as_bytes()[0].to_ascii_lowercase() {
        b'b' => 2,
        b'o' => 8,
        _ => 16,
    };
    let digits = &based[1..];
    u128::from_str_radix(digits, radix).map_or_else(
        |_| {
            digits.chars().fold(0.0, |value, digit| {
                value * f64::from(radix) + f64::from(digit.to_digit(radix).unwrap_or(0))
            })
        },
        |value| value as f64,
    )
}

/// `MonolithSpecExtractor.module`: a module that no file defines can follow the root module in the
/// root module's file, from its `---- MODULE` line to the next `====` line.
pub fn extract_module(source: &str, name: &str) -> Option<String> {
    // JavaScript's split(/\r?\n/).
    let mut lines: Vec<&str> = source.split('\n').collect();
    let last = lines.len() - 1;
    lines[..last]
        .iter_mut()
        .for_each(|line| *line = line.strip_suffix('\r').unwrap_or(line));
    let is_header = |line: &str| {
        let after_dashes = line.trim_start_matches('-');
        if line.len() - after_dashes.len() < 4 {
            return false;
        }
        let Some(rest) = after_dashes
            .trim_start_matches(crate::lexer::is_js_whitespace)
            .strip_prefix("MODULE")
        else {
            return false;
        };
        let after_space = rest.trim_start_matches(crate::lexer::is_js_whitespace);
        if after_space.len() == rest.len() {
            return false;
        }
        let Some(rest) = after_space.strip_prefix(name) else {
            return false;
        };
        let rest = rest.trim_start_matches(crate::lexer::is_js_whitespace);
        rest.len() >= 3 && rest.bytes().all(|byte| byte == b'-')
    };
    let start = lines.iter().position(|line| is_header(line))?;
    let end = lines
        .iter()
        .enumerate()
        .position(|(index, line)| index > start && line.starts_with("===="));
    let selected = &lines[start..end.map_or(lines.len(), |end| end + 1)];
    Some(format!("{}\n", selected.join("\n")))
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Tlc,
    Sany,
}

type Parsed<T> = Result<T, SyntaxError>;

/// A token as `peek` gives it: past the column a junction list's bullet sets, a token reads as the
/// end.
#[derive(Clone)]
struct Peeked {
    kind: TokenKind,
    text: Rc<str>,
    line: u32,
    column: u32,
}

const NO_OFFSIDE: i64 = -1;

struct Parser {
    tokens: Vec<Token>,
    index: usize,
    offside_columns: Vec<i64>,
    last: Option<Precedence>,
    preceding: Option<Precedence>,
    recursive_scopes: Vec<FastSet<Name>>,
    fact_names: FastSet<Name>,
    proof_scopes: Vec<FastSet<Name>>,
    open_modules: Vec<Module>,
    root_name: Name,
    end: Rc<str>,
    is_keyword_module_name: bool,
    proof_levels: Vec<i64>,
    mode: Mode,
    version: TlcVersion,
    /// The errors of SANY's semantic analysis that the parser finds, when it collects them
    /// rather than failing at the first: a DEF clause entry that isn't a definition, which SANY
    /// leaves out, and a HIDE of what isn't a fact.
    sany_errors: Option<Vec<SanyError>>,
}

fn location_of(token: &Token) -> Location {
    Location {
        line: token.line,
        column: token.column,
        range: None,
    }
}

fn located(kind: ExpressionKind, location: Location) -> Expression {
    Expression::new(kind, location)
}

impl Parser {
    fn raw(&self, offset: usize) -> &Token {
        &self.tokens[(self.index + offset).min(self.tokens.len() - 1)]
    }

    fn peek(&self, offset: usize) -> Peeked {
        let token = self.raw(offset);
        let is_offside = self.is_offside(token);
        Peeked {
            kind: if is_offside {
                TokenKind::End
            } else {
                token.kind
            },
            text: if is_offside {
                self.end.clone()
            } else {
                token.text.clone()
            },
            line: token.line,
            column: token.column,
        }
    }

    fn peek_location(&self) -> Location {
        let token = self.raw(0);
        Location {
            line: token.line,
            column: token.column,
            range: None,
        }
    }

    fn get_range_between(&self, start: usize, end: usize) -> Range {
        let first = &self.tokens[start];
        let last = &self.tokens[end];
        SourceRange {
            module: self.root_name.clone(),
            start: Position {
                line: first.line,
                column: first.column,
            },
            end: Position {
                line: last.line,
                column: last.end_column,
            },
        }
    }

    fn get_range(&self, start: usize) -> Range {
        self.get_range_between(start, self.index - 1)
    }

    fn with_range(&self, mut expression: Expression, start: usize) -> Expression {
        expression.location.range = Some(self.get_range(start));
        expression
    }

    fn error_at(&self, message: &str, line: u32, column: u32) -> SyntaxError {
        let end = &self.tokens[self.tokens.len() - 1];
        SyntaxError {
            message: format!("{message} at line {line}, column {column}"),
            failure: Some(SyntaxFailure {
                reason: message.to_string(),
                line,
                column,
                is_end: line == end.line && column == end.column,
            }),
            sany: None,
        }
    }

    fn error(&self, message: &str) -> SyntaxError {
        let token = self.raw(0);
        self.error_at(message, token.line, token.column)
    }

    fn describe(&self, token: &Peeked) -> String {
        if token.kind == TokenKind::End {
            return "end of input".to_string();
        }
        let mut quoted = String::new();
        write_js_string(&mut quoted, &token.text);
        quoted
    }

    fn quoted(text: &str) -> String {
        let mut quoted = String::new();
        write_js_string(&mut quoted, text);
        quoted
    }

    fn is_recursive_name(&self, name: &str) -> bool {
        self.recursive_scopes
            .last()
            .is_some_and(|scope| scope.contains(name))
    }

    /// `TLAplusParser.isFieldNameToken`: a keyword or an underscore names a field or a module too.
    fn is_field_name(token: &Peeked) -> bool {
        matches!(token.kind, TokenKind::Identifier | TokenKind::Keyword)
            || (token.kind == TokenKind::Operator && &*token.text == "_")
    }

    fn is_offside(&self, token: &Token) -> bool {
        match self.offside_columns.last() {
            Some(&column) if column != NO_OFFSIDE && token.kind != TokenKind::End => {
                i64::from(token.column) <= column
            }
            _ => false,
        }
    }

    /// The kind `peek` gives the token at `offset`, without the rest.
    fn peek_kind(&self, offset: usize) -> TokenKind {
        let token = self.raw(offset);
        if self.is_offside(token) {
            TokenKind::End
        } else {
            token.kind
        }
    }

    fn is_at(&self, text: &str, offset: usize) -> bool {
        let token = self.raw(offset);
        &*token.text == text
            && token.kind != TokenKind::String
            && token.kind != TokenKind::End
            && !self.is_offside(token)
    }

    fn advance(&mut self) -> Parsed<Token> {
        if self.peek_kind(0) == TokenKind::End {
            return Err(self.error("Unexpected end of expression"));
        }
        self.index += 1;
        Ok(self.tokens[self.index - 1].clone())
    }

    fn accept(&mut self, text: &str) -> bool {
        if !self.is_at(text, 0) {
            return false;
        }
        self.index += 1;
        true
    }

    fn expect(&mut self, text: &str) -> Parsed<Token> {
        if !self.is_at(text, 0) {
            return Err(self.error(&format!(
                "Expected {} but found {}",
                Self::quoted(text),
                self.describe(&self.peek(0))
            )));
        }
        self.advance()
    }

    fn expect_identifier(&mut self) -> Parsed<Name> {
        let token = self.peek(0);
        if token.kind != TokenKind::Identifier {
            return Err(self.error(&format!(
                "Expected an identifier but found {}",
                self.describe(&token)
            )));
        }
        self.index += 1;
        Ok(token.text)
    }

    fn expect_name(&mut self) -> Parsed<(Name, Range)> {
        let start = self.index;
        let name = self.expect_identifier()?;
        Ok((name, self.get_range(start)))
    }

    fn separated<T>(&mut self, mut item: impl FnMut(&mut Self) -> Parsed<T>) -> Parsed<Vec<T>> {
        let mut items = vec![item(self)?];
        while self.accept(",") {
            items.push(item(self)?);
        }
        Ok(items)
    }

    fn names(&mut self) -> Parsed<(Vec<Name>, Vec<Range>)> {
        Ok(self.separated(Self::expect_name)?.into_iter().unzip())
    }

    /// `TLAplusParser.Substitution`: an identifier, or a prefix, infix or postfix operator.
    fn expect_substitution_target(&mut self) -> Parsed<Name> {
        let token = self.peek(0);
        let is_operator = token.kind != TokenKind::String
            && (is_definable_prefix(&token.text)
                || is_infix(&token.text)
                || is_postfix(&token.text)
                || &*token.text == "'");
        if !is_operator {
            return self.expect_identifier();
        }
        self.index += 1;
        Ok(token.text)
    }

    /// SANY takes a keyword for the name of a module, as it does for a field.
    fn expect_module_name(&mut self) -> Parsed<Name> {
        let token = self.peek(0);
        if token.kind == TokenKind::Identifier || !Self::is_field_name(&token) {
            return self.expect_identifier();
        }
        self.is_keyword_module_name = true;
        Ok(self.advance()?.text)
    }

    fn is_bound_ahead(&self) -> bool {
        if self.is_at("<<", 0) {
            let mut offset = 1;
            while self.peek_kind(offset) == TokenKind::Identifier || self.is_at(",", offset) {
                offset += 1;
            }
            return self.is_at(">>", offset) && self.is_at("\\in", offset + 1);
        }
        let mut offset = 0;
        while self.peek_kind(offset) == TokenKind::Identifier {
            if self.is_at("\\in", offset + 1) {
                return true;
            }
            if !self.is_at(",", offset + 1) {
                return false;
            }
            offset += 2;
        }
        false
    }

    fn is_label_ahead(&self) -> bool {
        if self.is_at("::", 0) {
            return true;
        }
        if !self.is_at("(", 0) {
            return false;
        }
        let mut offset = 1;
        while self.peek_kind(offset) == TokenKind::Identifier && self.is_at(",", offset + 1) {
            offset += 2;
        }
        self.peek_kind(offset) == TokenKind::Identifier
            && self.is_at(")", offset + 1)
            && self.is_at("::", offset + 2)
    }

    fn parse_pattern(&mut self) -> Parsed<BoundPattern> {
        if !self.accept("<<") {
            let (name, range) = self.expect_name()?;
            return Ok(BoundPattern::Name {
                name,
                ranges: vec![range],
            });
        }
        let (names, ranges) = self.names()?;
        self.expect(">>")?;
        Ok(BoundPattern::Tuple { names, ranges })
    }

    fn parse_bounds(&mut self) -> Parsed<Vec<Bound>> {
        let groups = self.separated(|parser| {
            let patterns = parser.separated(Self::parse_pattern)?;
            parser.expect("\\in")?;
            let set = Rc::new(parser.parse_expression(0)?);
            Ok(patterns
                .into_iter()
                .map(|pattern| Bound {
                    pattern,
                    set: set.clone(),
                })
                .collect::<Vec<_>>())
        })?;
        Ok(groups.into_iter().flatten().collect())
    }

    fn parse_subscript(&mut self) -> Parsed<Expression> {
        let token = self.peek(0);
        // SANY's FairnessExpr reads WF_B(A)(Act) with the subscript B(A).
        if token.kind == TokenKind::Identifier && self.is_application_subscript_ahead() {
            let start = self.index;
            let application = self.parse_primary(None)?;
            return Ok(self.with_range(application, start));
        }
        if token.kind == TokenKind::Identifier {
            let start = self.index;
            let location = self.peek_location();
            let mut names = vec![self.advance()?.text];
            while self.is_at("!", 0) && self.peek_kind(1) == TokenKind::Identifier {
                self.advance()?;
                names.push(self.expect_identifier()?);
            }
            let name: Name = Rc::from(names.join("!"));
            let identifier = located(
                ExpressionKind::Identifier {
                    name,
                    spelling: None,
                    selector_ranges: None,
                },
                location,
            );
            return Ok(self.with_range(identifier, start));
        }
        if self.is_at("<<", 0) || self.is_at("(", 0) {
            return self.parse_primary(None);
        }
        Err(self.error(&format!(
            "Expected a subscript but found {}",
            self.describe(&token)
        )))
    }

    fn is_application_subscript_ahead(&self) -> bool {
        let mut offset = 1;
        while self.is_at("!", offset) && self.peek_kind(offset + 1) == TokenKind::Identifier {
            offset += 2;
        }
        if !self.is_at("(", offset) {
            return false;
        }
        let mut depth = 0;
        loop {
            if self.peek_kind(offset) == TokenKind::End {
                return false;
            }
            depth += usize::from(self.is_at("(", offset));
            if self.is_at(")", offset) {
                depth -= 1;
                if depth == 0 {
                    return self.is_at("(", offset + 1);
                }
            }
            offset += 1;
        }
    }

    fn is_definition_ahead(&self, operator_line: u32) -> bool {
        let token = self.peek(1);
        let next = self.peek(2);
        if token.kind == TokenKind::Identifier && &*next.text == "==" {
            return true;
        }
        if token.line == operator_line {
            return false;
        }
        if &*token.text == "-." {
            return true;
        }
        token.kind == TokenKind::Identifier
            && (&*next.text == "("
                || &*next.text == "["
                || (next.kind == TokenKind::Operator
                    && self.is_at("==", if is_postfix(&next.text) { 3 } else { 4 })))
    }

    /// SANY's OpOrExpr reads an operator as an argument only before what ends the argument, and as
    /// the start of an expression, such as `-.(1)`, otherwise.
    fn is_standalone(&self, operator_line: u32) -> bool {
        let token = self.peek(1);
        matches!(
            token.kind,
            TokenKind::End | TokenKind::ModuleEnd | TokenKind::Separator
        ) || self.is_at(",", 1)
            || self.is_at(")", 1)
            || (token.kind == TokenKind::Keyword && is_unit_keyword(&token.text))
            || self.is_definition_ahead(operator_line)
    }

    fn parse_argument(&mut self) -> Parsed<Expression> {
        let token = self.peek(0);
        let raw = self.raw(0).clone();
        let is_operator_alone = token.kind == TokenKind::Operator
            && (is_infix(&token.text) || is_prefix_operator_reference(&token.text))
            && self.is_standalone(token.line);
        if is_operator_alone {
            self.index += 1;
            let reference = located(
                ExpressionKind::OperatorReference {
                    operator: token.text,
                    spelling: raw.spelling.clone(),
                },
                location_of(&raw),
            );
            return Ok(self.with_range(reference, self.index - 1));
        }
        let is_prefix_alone = token.kind != TokenKind::String
            && is_operator_argument(&token.text)
            && self.is_standalone(token.line);
        if is_prefix_alone {
            self.index += 1;
            let location = location_of(&raw);
            if is_postfix(&token.text) {
                let reference = located(
                    ExpressionKind::OperatorReference {
                        operator: token.text,
                        spelling: raw.spelling.clone(),
                    },
                    location,
                );
                return Ok(self.with_range(reference, self.index - 1));
            }
            let argument_name: Name = Rc::from("argument");
            let argument = Rc::new(located(
                ExpressionKind::Identifier {
                    name: argument_name.clone(),
                    spelling: None,
                    selector_ranges: None,
                },
                location.clone(),
            ));
            let body = match &*token.text {
                "ENABLED" => ExpressionKind::Enabled(argument),
                "UNCHANGED" => ExpressionKind::Unchanged(argument),
                "[]" => ExpressionKind::Always(argument),
                "<>" => ExpressionKind::Eventually(argument),
                "'" => ExpressionKind::Prime(argument),
                _ => ExpressionKind::Apply {
                    operator: token.text.clone(),
                    spelling: None,
                    args: vec![argument],
                    argument_counts: None,
                    arguments_range: None,
                    selector_ranges: None,
                    argument_ranges: None,
                },
            };
            let lambda = located(
                ExpressionKind::Lambda {
                    params: vec![argument_name],
                    param_ranges: None,
                    body: Rc::new(located(body, location.clone())),
                    operator: Some(token.text),
                },
                location,
            );
            return Ok(self.with_range(lambda, self.index - 1));
        }
        if self.is_at("LAMBDA", 0) {
            let start = self.index;
            self.advance()?;
            let (params, ranges) = self.names()?;
            self.expect(":")?;
            let body = Rc::new(self.parse_expression(0)?);
            let lambda = located(
                ExpressionKind::Lambda {
                    params,
                    param_ranges: Some(ranges),
                    body,
                    operator: None,
                },
                location_of(&raw),
            );
            return Ok(self.with_range(lambda, start));
        }
        self.parse_expression(0)
    }

    fn parse_arguments(&mut self) -> Parsed<(Vec<Expr>, Range)> {
        let start = self.index;
        self.expect("(")?;
        let args = self.separated(|parser| parser.parse_argument().map(Rc::new))?;
        self.expect(")")?;
        Ok((args, self.get_range(start)))
    }

    fn parse_junction_list(&mut self) -> Parsed<Expression> {
        let bullet = self.advance()?;
        self.offside_columns.push(i64::from(bullet.column));
        let mut operands = vec![Rc::new(self.parse_expression(0)?)];
        while self.raw(0).text == bullet.text && self.raw(0).column == bullet.column {
            self.index += 1;
            operands.push(Rc::new(self.parse_expression(0)?));
        }
        self.offside_columns.pop();
        Ok(located(
            ExpressionKind::Junction {
                is_and: &*bullet.text == "/\\",
                operands,
                is_bulleted: true,
                prefix_ends: None,
            },
            location_of(&bullet),
        ))
    }

    fn parse_record_field(&mut self, is_record: bool, is_first: bool) -> Parsed<RecordField> {
        let start = self.index;
        let mut location = self.peek_location();
        let name = if is_first && self.peek_kind(0) != TokenKind::Identifier {
            self.advance()?.text
        } else {
            self.expect_identifier()?
        };
        location.range = Some(self.get_range(start));
        self.expect(if is_record { "|->" } else { ":" })?;
        let value = Rc::new(self.parse_expression(0)?);
        Ok(RecordField {
            name,
            value,
            location,
        })
    }

    fn parse_bracket(&mut self, start: &Token) -> Parsed<Expression> {
        let location = location_of(start);
        // SANY takes a keyword for the first field of a record, as it does for a selected field.
        let is_identifier = self.peek_kind(0) == TokenKind::Identifier;
        let is_record =
            self.is_at("|->", 1) && (is_identifier || Self::is_field_name(&self.peek(0)));
        if is_record || (is_identifier && self.is_at(":", 1)) {
            let mut fields = vec![self.parse_record_field(is_record, true)?];
            if self.accept(",") {
                fields
                    .extend(self.separated(|parser| parser.parse_record_field(is_record, false))?);
            }
            self.expect("]")?;
            return Ok(located(
                ExpressionKind::Record {
                    is_set: !is_record,
                    fields,
                },
                location,
            ));
        }
        if self.is_bound_ahead() {
            let bounds = self.parse_bounds()?;
            self.expect("|->")?;
            let body = Rc::new(self.parse_expression(0)?);
            self.expect("]")?;
            return Ok(located(
                ExpressionKind::FunctionConstruction { bounds, body },
                location,
            ));
        }
        let expression = Rc::new(self.parse_expression(0)?);
        if self.accept("->") {
            let range = Rc::new(self.parse_expression(0)?);
            self.expect("]")?;
            return Ok(located(
                ExpressionKind::FunctionSet {
                    domain: expression,
                    range,
                },
                location,
            ));
        }
        if self.accept("EXCEPT") {
            let updates = self.separated(|parser| {
                parser.expect("!")?;
                let mut path = Vec::new();
                while parser.is_at(".", 0) || parser.is_at("[", 0) {
                    if parser.accept(".") {
                        let token = parser.peek(0);
                        if !Self::is_field_name(&token) {
                            return Err(parser.error(&format!(
                                "Expected a field name but found {}",
                                parser.describe(&token)
                            )));
                        }
                        path.push(ExceptPathStep::Field(parser.advance()?.text));
                        continue;
                    }
                    parser.expect("[")?;
                    let args =
                        parser.separated(|parser| parser.parse_expression(0).map(Rc::new))?;
                    path.push(ExceptPathStep::Index(args));
                    parser.expect("]")?;
                }
                parser.expect("=")?;
                let value = Rc::new(parser.parse_expression(0)?);
                Ok(ExceptUpdate { path, value })
            })?;
            self.expect("]")?;
            return Ok(located(
                ExpressionKind::Except {
                    function: expression,
                    updates,
                },
                location,
            ));
        }
        if !self.is_at("]_", 0) {
            let mut args = vec![expression];
            while self.accept(",") {
                args.push(Rc::new(self.parse_expression(0)?));
            }
            self.expect("]")?;
            return Ok(located(ExpressionKind::Bracket(args), location));
        }
        self.expect("]_")?;
        let subscript = Rc::new(self.parse_subscript()?);
        Ok(located(
            ExpressionKind::Action {
                is_box: true,
                action: expression,
                subscript,
            },
            location,
        ))
    }

    /// SANY reads the set after the `\in` of `{x \in S}` as a whole expression, whatever operators
    /// it has.
    fn parse_set_membership(&mut self) -> Parsed<Expression> {
        let start = self.index;
        let prefix = self.parse_prefix()?;
        let element = Rc::new(self.with_range(prefix, start));
        let location = location_of(&self.advance()?);
        let set = Rc::new(self.parse_expression(0)?);
        let membership = located(
            ExpressionKind::Apply {
                operator: Rc::from("\\in"),
                spelling: None,
                args: vec![element, set],
                argument_counts: None,
                arguments_range: None,
                selector_ranges: None,
                argument_ranges: None,
            },
            location,
        );
        Ok(self.with_range(membership, start))
    }

    fn parse_brace(&mut self, start: &Token) -> Parsed<Expression> {
        let location = location_of(start);
        if self.accept("}") {
            return Ok(located(
                ExpressionKind::SetEnumeration(Vec::new()),
                location,
            ));
        }
        if self.is_bound_ahead() && (&*self.peek(1).text == "\\in" || self.is_at("<<", 0)) {
            let checkpoint = self.index;
            let pattern = self.parse_pattern()?;
            self.expect("\\in")?;
            let set = Rc::new(self.parse_expression(0)?);
            if self.accept(":") {
                let predicate = Rc::new(self.parse_expression(0)?);
                self.expect("}")?;
                return Ok(located(
                    ExpressionKind::SetFilter {
                        bound: Bound { pattern, set },
                        predicate,
                    },
                    location,
                ));
            }
            self.index = checkpoint;
        }
        let first = if self.peek_kind(0) == TokenKind::Identifier && self.is_at("\\in", 1) {
            self.parse_set_membership()?
        } else {
            self.parse_expression(0)?
        };
        let first = Rc::new(first);
        if self.accept(":") {
            let bounds = self.parse_bounds()?;
            self.expect("}")?;
            return Ok(located(
                ExpressionKind::SetMap {
                    expression: first,
                    bounds,
                },
                location,
            ));
        }
        let mut elements = vec![first];
        while self.accept(",") {
            elements.push(Rc::new(self.parse_expression(0)?));
        }
        self.expect("}")?;
        Ok(located(ExpressionKind::SetEnumeration(elements), location))
    }

    fn parse_tuple(&mut self, start: &Token) -> Parsed<Expression> {
        let location = location_of(start);
        let mut elements = if self.is_at(">>", 0) || self.is_at(">>_", 0) {
            Vec::new()
        } else {
            self.separated(|parser| parser.parse_expression(0).map(Rc::new))?
        };
        if self.accept(">>_") {
            if elements.len() != 1 {
                return Err(self.error_at(
                    "Expected a single action inside <<A>>_v",
                    start.line,
                    start.column,
                ));
            }
            let subscript = Rc::new(self.parse_subscript()?);
            return Ok(located(
                ExpressionKind::Action {
                    is_box: false,
                    action: elements.remove(0),
                    subscript,
                },
                location,
            ));
        }
        self.expect(">>")?;
        Ok(located(ExpressionKind::Tuple(elements), location))
    }

    fn parse_quantifier(&mut self, start: &Token) -> Parsed<Expression> {
        let location = location_of(start);
        let is_temporal = &*start.text == "\\AA" || &*start.text == "\\EE";
        if !is_temporal && self.is_bound_ahead() {
            let bounds = self.parse_bounds()?;
            self.expect(":")?;
            let body = Rc::new(self.parse_expression(0)?);
            let quantifier = if &*start.text == "\\A" {
                Quantifier::Forall
            } else {
                Quantifier::Exists
            };
            return Ok(located(
                ExpressionKind::Quantified {
                    quantifier,
                    bounds,
                    body,
                },
                location,
            ));
        }
        let (names, name_ranges) = self.names()?;
        self.expect(":")?;
        let body = Rc::new(self.parse_expression(0)?);
        let quantifier = if &*start.text == "\\A" || &*start.text == "\\AA" {
            Quantifier::Forall
        } else {
            Quantifier::Exists
        };
        Ok(located(
            ExpressionKind::UnboundedQuantifier {
                quantifier,
                names,
                name_ranges,
                is_temporal,
                body,
            },
            location,
        ))
    }

    fn parse_case(&mut self, start: &Token) -> Parsed<Expression> {
        let mut arms = Vec::new();
        loop {
            if self.accept("OTHER") {
                self.expect("->")?;
                let other = Some(Rc::new(self.parse_expression(0)?));
                return Ok(located(
                    ExpressionKind::Case { arms, other },
                    location_of(start),
                ));
            }
            let condition = Rc::new(self.parse_expression(0)?);
            self.expect("->")?;
            let body = Rc::new(self.parse_expression(0)?);
            arms.push(CaseArm { condition, body });
            if !self.accept("[]") {
                break;
            }
        }
        Ok(located(
            ExpressionKind::Case { arms, other: None },
            location_of(start),
        ))
    }

    fn is_selector_ahead(&self) -> bool {
        let next = self.peek(1);
        self.is_at("!", 0)
            && (matches!(next.kind, TokenKind::Identifier | TokenKind::Number)
                || matches!(&*next.text, "<<" | ">>" | ":" | "@" | "(")
                || (next.kind == TokenKind::Operator
                    && (is_infix(&next.text)
                        || is_postfix(&next.text)
                        || is_prefix_operator_reference(&next.text))))
    }

    fn parse_selector(&mut self) -> Parsed<(Selector, Option<Range>)> {
        let token = self.advance()?;
        if token.kind == TokenKind::Number {
            let value = get_numeral_value(&token.text);
            return Ok((Selector::Operand(Operand::Index(value)), None));
        }
        Ok(match &*token.text {
            "<<" => (Selector::Operand(Operand::First), None),
            ">>" => (Selector::Operand(Operand::Last), None),
            ":" => (Selector::Colon, None),
            "@" => (Selector::At, None),
            "(" => {
                self.index -= 1;
                let (args, range) = self.parse_arguments()?;
                (Selector::Bound(args), Some(range))
            }
            _ => {
                let (args, range) = if self.is_at("(", 0) {
                    let (args, range) = self.parse_arguments()?;
                    (args, Some(range))
                } else {
                    (Vec::new(), None)
                };
                (
                    Selector::Name {
                        name: token.text,
                        args,
                    },
                    range,
                )
            }
        })
    }

    fn get_proof_level(&self) -> i64 {
        self.proof_levels.last().copied().unwrap_or(-1)
    }

    fn get_step_level(text: &str) -> i64 {
        match text.as_bytes()[1] {
            b'*' => -1,
            b'+' => -2,
            _ => text[1..text.find('>').unwrap_or(text.len())]
                .parse()
                .unwrap_or(0),
        }
    }

    fn get_step_label(text: &str) -> &str {
        text[text.find('>').map_or(0, |end| end + 1)..].trim_end_matches('.')
    }

    fn is_step_reference(text: &str) -> bool {
        !text.ends_with('.') && !is_unnamed_step_label(Self::get_step_label(text))
    }

    fn get_step_name(&self, text: &str) -> Option<Name> {
        let label = Self::get_step_label(text);
        if is_unnamed_step_label(label) {
            return None;
        }
        let level = Self::get_step_level(text);
        if level >= 0 {
            return Some(Rc::from(format!("<{level}>{label}")));
        }
        let current = self.get_proof_level();
        let outer = self
            .proof_levels
            .len()
            .checked_sub(2)
            .map(|index| self.proof_levels[index]);
        let level = match outer {
            Some(outer) if current < 0 => outer,
            _ => current,
        };
        Some(Rc::from(format!("<{level}>{label}")))
    }

    fn parse_primary(&mut self, preceding: Option<Precedence>) -> Parsed<Expression> {
        let start = self.index;
        let token = self.advance()?;
        let location = location_of(&token);
        match token.kind {
            TokenKind::Number => {
                let value = get_numeral_value(&token.text);
                return Ok(located(
                    ExpressionKind::Number {
                        value,
                        text: token.text,
                    },
                    location,
                ));
            }
            TokenKind::Decimal => {
                return Ok(located(
                    ExpressionKind::Decimal { text: token.text },
                    location,
                ));
            }
            TokenKind::String => {
                return Ok(located(
                    ExpressionKind::String { value: token.text },
                    location,
                ));
            }
            _ => {}
        }
        let is_step = token.kind == TokenKind::Step && Self::is_step_reference(&token.text);
        if is_step && self.get_proof_level() < 0 && self.proof_levels.len() <= 1 {
            return Err(self.error_at("Step number used outside proof", token.line, token.column));
        }
        if is_step && token.text.as_bytes()[1] == b'+' {
            return Err(self.error_at(
                "<+> step number used in an expression",
                token.line,
                token.column,
            ));
        }
        if token.kind == TokenKind::Identifier || is_step {
            let name = if is_step {
                self.get_step_name(&token.text)
                    .unwrap_or_else(|| token.text.clone())
            } else {
                token.text.clone()
            };
            if self.is_label_ahead() {
                let (params, param_ranges) = if self.accept("(") {
                    self.names()?
                } else {
                    (Vec::new(), Vec::new())
                };
                if !params.is_empty() {
                    self.expect(")")?;
                }
                self.expect("::")?;
                let body = self.parse_expression(0)?;
                // TLAplusParser.labelDoesNotChangeParse.
                if let (Some(preceding), Some(last)) = (preceding, self.last)
                    && is_operator_expression(&body)
                    && preceding.high >= last.low
                {
                    return Err(self.error_at(
                        "Removing the label would change expression parsing",
                        token.line,
                        token.column,
                    ));
                }
                return Ok(located(
                    ExpressionKind::Label {
                        name,
                        params,
                        param_ranges,
                        body: Rc::new(body),
                    },
                    location,
                ));
            }
            let has_arguments = self.is_at("(", 0);
            if &*name == "@" && !has_arguments && !self.is_selector_ahead() {
                return Ok(located(ExpressionKind::ExceptAt, location));
            }
            let (args, arguments_range) = if has_arguments {
                let (args, range) = self.parse_arguments()?;
                (args, Some(range))
            } else {
                (Vec::new(), None)
            };
            if !self.is_selector_ahead() {
                return Ok(located(
                    if has_arguments {
                        ExpressionKind::Apply {
                            operator: name,
                            spelling: None,
                            args,
                            argument_counts: None,
                            arguments_range,
                            selector_ranges: None,
                            argument_ranges: None,
                        }
                    } else {
                        ExpressionKind::Identifier {
                            name,
                            spelling: None,
                            selector_ranges: None,
                        }
                    },
                    location,
                ));
            }
            let mut argument_ranges = vec![arguments_range];
            let mut selectors = vec![Selector::Name { name, args }];
            let mut selector_ranges = vec![self.get_range_between(start, start)];
            while self.is_selector_ahead() {
                self.advance()?;
                selector_ranges.push(self.get_range_between(self.index, self.index));
                let (selector, range) = self.parse_selector()?;
                selectors.push(selector);
                argument_ranges.push(range);
            }
            let names: Vec<&str> = selectors
                .iter()
                .filter_map(|selector| match selector {
                    Selector::Name { name, .. } => Some(&**name),
                    _ => None,
                })
                .collect();
            if names.len() < selectors.len() {
                return Ok(located(
                    ExpressionKind::Subexpression {
                        selectors,
                        selector_ranges,
                        argument_ranges,
                    },
                    location,
                ));
            }
            let operator: Name = Rc::from(names.join("!"));
            let qualified_args: Vec<Expr> = selectors
                .iter()
                .flat_map(|selector| selector.args().iter().cloned())
                .collect();
            if qualified_args.is_empty() {
                return Ok(located(
                    ExpressionKind::Identifier {
                        name: operator,
                        spelling: None,
                        selector_ranges: Some(selector_ranges),
                    },
                    location,
                ));
            }
            let argument_counts: Vec<usize> = selectors
                .iter()
                .map(|selector| selector.args().len())
                .collect();
            let has_inner_arguments = argument_counts[..argument_counts.len() - 1]
                .iter()
                .any(|count| *count > 0);
            let arguments_range = argument_ranges
                .last()
                .cloned()
                .flatten()
                .unwrap_or_else(|| self.get_range(start));
            return Ok(located(
                ExpressionKind::Apply {
                    operator,
                    spelling: None,
                    args: qualified_args,
                    argument_counts: has_inner_arguments.then_some(argument_counts),
                    arguments_range: Some(arguments_range),
                    selector_ranges: Some(selector_ranges),
                    argument_ranges: Some(argument_ranges),
                },
                location,
            ));
        }
        // SANY reads an infix or postfix operator as a primary expression, with or without
        // arguments.
        if token.kind == TokenKind::Operator && is_operator_name(&token.text) {
            if self.is_at("(", 0) {
                let (args, _) = self.parse_arguments()?;
                return Ok(located(
                    ExpressionKind::Apply {
                        operator: token.text,
                        spelling: token.spelling,
                        args,
                        argument_counts: None,
                        arguments_range: None,
                        selector_ranges: None,
                        argument_ranges: None,
                    },
                    location,
                ));
            }
            return Ok(located(
                ExpressionKind::Identifier {
                    name: token.text,
                    spelling: token.spelling,
                    selector_ranges: None,
                },
                location,
            ));
        }
        match &*token.text {
            "(" => {
                let expression = self.parse_expression(0)?;
                self.expect(")")?;
                Ok(expression)
            }
            "[" => self.parse_bracket(&token),
            "{" => self.parse_brace(&token),
            "<<" => self.parse_tuple(&token),
            "@" => Ok(located(ExpressionKind::ExceptAt, location)),
            "\\A" | "\\E" | "\\AA" | "\\EE" => self.parse_quantifier(&token),
            "IF" => {
                let condition = Rc::new(self.parse_expression(0)?);
                self.expect("THEN")?;
                let consequent = Rc::new(self.parse_expression(0)?);
                self.expect("ELSE")?;
                let alternative = Rc::new(self.parse_expression(0)?);
                Ok(located(
                    ExpressionKind::If {
                        condition,
                        consequent,
                        alternative,
                    },
                    location,
                ))
            }
            "CASE" => self.parse_case(&token),
            "LET" => {
                let mut definitions = Vec::new();
                let mut instances = Vec::new();
                let mut recursive = Vec::new();
                self.recursive_scopes.push(FastSet::default());
                while !self.accept("IN") {
                    if self.accept("RECURSIVE") {
                        recursive.extend(self.declare_recursive()?.into_iter().map(Rc::new));
                        continue;
                    }
                    match self.parse_definition(false)? {
                        DefinitionUnit::Instance(instance) => instances.push(instance),
                        DefinitionUnit::Definition(definition) => definitions.push(definition),
                    }
                }
                self.recursive_scopes.pop();
                let body = Rc::new(self.parse_expression(0)?);
                Ok(located(
                    ExpressionKind::Let {
                        definitions,
                        instances: (!instances.is_empty()).then_some(instances),
                        recursive,
                        body,
                    },
                    location,
                ))
            }
            "CHOOSE" => {
                let pattern = self.parse_pattern()?;
                let set = if self.accept("\\in") {
                    Some(Rc::new(self.parse_expression(0)?))
                } else {
                    None
                };
                self.expect(":")?;
                let body = Rc::new(self.parse_expression(0)?);
                Ok(located(
                    ExpressionKind::Choose { pattern, set, body },
                    location,
                ))
            }
            "WF_" | "SF_" => {
                let subscript = Rc::new(self.parse_subscript()?);
                self.expect("(")?;
                let action = Rc::new(self.parse_expression(0)?);
                self.expect(")")?;
                Ok(located(
                    ExpressionKind::Fairness {
                        is_strong: &*token.text == "SF_",
                        subscript,
                        action,
                        enabled: None,
                    },
                    location,
                ))
            }
            _ => {
                let mut quoted = String::new();
                write_js_string(&mut quoted, &token.text);
                Err(self.error_at(&format!("Unexpected {quoted}"), token.line, token.column))
            }
        }
    }

    /// SANY rejects the operator after a prefix operator's operand unless it binds looser than the
    /// prefix operator.
    fn parse_prefix_operand(&mut self, operator: &str, low: u32, high: u32) -> Parsed<Expr> {
        self.last = Some(Precedence { low, high });
        self.preceding = self.last;
        let operand = self.parse_expression(high + 1)?;
        let next = self.peek(0);
        let next_high = if &*next.text == "'" || is_postfix(&next.text) {
            Some(POSTFIX_PRECEDENCE.high)
        } else {
            get_infix(&next.text).map(|infix| infix.high)
        };
        if next.kind == TokenKind::Operator && next_high.is_some_and(|next_high| next_high >= low) {
            return Err(self.error_at(
                &format!("Precedence conflict between {operator} and {}", next.text),
                next.line,
                next.column,
            ));
        }
        Ok(Rc::new(operand))
    }

    fn prefix_apply(operator: &str, operand: Expr, location: Location) -> Expression {
        located(
            ExpressionKind::Apply {
                operator: Rc::from(operator),
                spelling: None,
                args: vec![operand],
                argument_counts: None,
                arguments_range: None,
                selector_ranges: None,
                argument_ranges: None,
            },
            location,
        )
    }

    fn parse_prefix(&mut self) -> Parsed<Expression> {
        let preceding = self.preceding.take();
        let token = self.peek(0);
        let location = self.peek_location();
        if token.kind == TokenKind::Operator && matches!(&*token.text, "/\\" | "\\/") {
            return self.parse_junction_list();
        }
        if matches!(token.kind, TokenKind::Operator | TokenKind::Keyword) {
            let text = &*token.text;
            let wrap = |kind: fn(Expr) -> ExpressionKind, operand| {
                located(kind(operand), location.clone())
            };
            match text {
                "~" => {
                    self.advance()?;
                    let operand = self.parse_prefix_operand(text, 4, 4)?;
                    return Ok(Self::prefix_apply("~", operand, location));
                }
                "-" => {
                    self.advance()?;
                    let operand =
                        self.parse_prefix_operand(text, NEGATION_PRECEDENCE, NEGATION_PRECEDENCE)?;
                    return Ok(Self::prefix_apply("-.", operand, location));
                }
                "[]" | "<>" | "ENABLED" | "UNCHANGED" => {
                    self.advance()?;
                    let operand = self.parse_prefix_operand(text, 4, 15)?;
                    let kind: fn(Expr) -> ExpressionKind = match text {
                        "[]" => ExpressionKind::Always,
                        "<>" => ExpressionKind::Eventually,
                        "ENABLED" => ExpressionKind::Enabled,
                        _ => ExpressionKind::Unchanged,
                    };
                    return Ok(wrap(kind, operand));
                }
                "SUBSET" | "UNION" | "DOMAIN" => {
                    self.advance()?;
                    // SANY gives SUBSET and UNION precedence 8 and DOMAIN 9, and in TLC 1.7.4 gave
                    // all three 10-13.
                    let is_174 = self.version == TlcVersion::V1_7_4;
                    let low = if is_174 {
                        10
                    } else if text == "DOMAIN" {
                        9
                    } else {
                        8
                    };
                    let operand =
                        self.parse_prefix_operand(text, low, if is_174 { 13 } else { low })?;
                    return Ok(Self::prefix_apply(text, operand, location));
                }
                _ => {}
            }
        }
        self.parse_primary(preceding)
    }

    fn parse_expression(&mut self, minimum: u32) -> Parsed<Expression> {
        let start = self.index;
        let prefix = self.parse_prefix()?;
        let mut left = if prefix.location.range.is_some() {
            prefix
        } else {
            self.with_range(prefix, start)
        };
        let mut previous: Option<(InfixOperator, Name)> = None;
        loop {
            let token = self.peek(0);
            if token.kind != TokenKind::Operator {
                break;
            }
            let raw = self.raw(0).clone();
            let location = location_of(&raw);
            if &*token.text == "'" && minimum <= 15 {
                self.advance()?;
                self.last = Some(POSTFIX_PRECEDENCE);
                left = self.with_range(
                    located(ExpressionKind::Prime(Rc::new(left)), location),
                    start,
                );
                continue;
            }
            if is_postfix(&token.text) && minimum <= 15 {
                self.advance()?;
                self.last = Some(POSTFIX_PRECEDENCE);
                let apply = ExpressionKind::Apply {
                    operator: token.text.clone(),
                    spelling: raw.spelling.clone(),
                    args: vec![Rc::new(left)],
                    argument_counts: None,
                    arguments_range: None,
                    selector_ranges: None,
                    argument_ranges: None,
                };
                left = self.with_range(located(apply, location), start);
                continue;
            }
            if &*token.text == "[" {
                self.advance()?;
                let args = self.separated(|parser| parser.parse_expression(0).map(Rc::new))?;
                self.expect("]")?;
                self.last = Some(FUNCTION_PRECEDENCE);
                let application = ExpressionKind::FunctionApplication {
                    function: Rc::new(left),
                    args,
                };
                left = self.with_range(located(application, location), start);
                continue;
            }
            if &*token.text == "." && Self::is_field_name(&self.peek(1)) {
                self.advance()?;
                let field = self.advance()?.text;
                let access = ExpressionKind::FieldAccess {
                    record: Rc::new(left),
                    field,
                };
                left = self.with_range(located(access, location), start);
                continue;
            }
            let Some(infix) = get_infix(&token.text) else {
                break;
            };
            if infix.low < minimum {
                break;
            }
            if let Some((previous_infix, previous_text)) = &previous {
                let is_overlapping =
                    !(previous_infix.low > infix.high || previous_infix.high < infix.low);
                let is_chain = *previous_text == token.text && infix.is_associative;
                let is_product = &**previous_text == "\\X" && &*token.text == "\\X";
                if is_overlapping && !is_chain && !is_product {
                    return Err(self.error_at(
                        &format!(
                            "Precedence conflict between {previous_text} and {}",
                            token.text
                        ),
                        token.line,
                        token.column,
                    ));
                }
            }
            self.advance()?;
            // SANY reads - after an infix operator as prefix -, and rejects it after one that binds
            // tighter.
            if infix.low > NEGATION_PRECEDENCE && self.is_at("-", 0) {
                return Err(
                    self.error(&format!("Precedence conflict between {} and -", token.text))
                );
            }
            self.last = Some(Precedence {
                low: infix.low,
                high: infix.high,
            });
            self.preceding = self.last;
            let right = Rc::new(self.parse_expression(infix.high + 1)?);
            let is_same = previous
                .as_ref()
                .is_some_and(|(_, previous_text)| *previous_text == token.text);
            left = match &*token.text {
                "/\\" | "\\/" => {
                    let is_and = &*token.text == "/\\";
                    let end = self.get_range(start).end;
                    match left.kind {
                        ExpressionKind::Junction {
                            is_and: left_is_and,
                            mut operands,
                            is_bulleted,
                            prefix_ends,
                        } if left_is_and == is_and && is_same => {
                            operands.push(right);
                            let mut ends = prefix_ends.unwrap_or_default();
                            ends.push(end);
                            located(
                                ExpressionKind::Junction {
                                    is_and,
                                    operands,
                                    is_bulleted,
                                    prefix_ends: Some(ends),
                                },
                                left.location,
                            )
                        }
                        kind => located(
                            ExpressionKind::Junction {
                                is_and,
                                operands: vec![Rc::new(located(kind, left.location)), right],
                                is_bulleted: false,
                                prefix_ends: Some(vec![end]),
                            },
                            location,
                        ),
                    }
                }
                "\\X" => match left.kind {
                    ExpressionKind::Product(mut factors) if is_same => {
                        factors.push(right);
                        located(ExpressionKind::Product(factors), left.location)
                    }
                    kind => located(
                        ExpressionKind::Product(vec![Rc::new(located(kind, left.location)), right]),
                        location,
                    ),
                },
                _ => located(
                    ExpressionKind::Apply {
                        operator: token.text.clone(),
                        spelling: raw.spelling.clone(),
                        args: vec![Rc::new(left), right],
                        argument_counts: None,
                        arguments_range: None,
                        selector_ranges: None,
                        argument_ranges: None,
                    },
                    location,
                ),
            };
            left = self.with_range(left, start);
            previous = Some((infix, token.text));
        }
        Ok(left)
    }

    fn parse_params(&mut self) -> Parsed<Vec<OperatorParam>> {
        if !self.accept("(") {
            return Ok(Vec::new());
        }
        let params = self.parse_declarations()?;
        self.expect(")")?;
        Ok(params
            .into_iter()
            .map(|declaration| OperatorParam {
                name: declaration.name,
                arity: declaration.arity,
                location: Some(declaration.location),
            })
            .collect())
    }

    fn parse_definition(&mut self, is_local: bool) -> Parsed<DefinitionUnit> {
        let start = self.index;
        let unit = self.parse_definition_unit(is_local)?;
        Ok(self.with_unit_range(unit, start))
    }

    fn with_unit_range(&self, unit: DefinitionUnit, start: usize) -> DefinitionUnit {
        let range = Some(self.get_range(start));
        match unit {
            DefinitionUnit::Definition(definition) => {
                let mut definition = Rc::unwrap_or_clone(definition);
                definition.location.range = range;
                DefinitionUnit::Definition(Rc::new(definition))
            }
            DefinitionUnit::Instance(instance) => {
                let mut instance = Rc::unwrap_or_clone(instance);
                instance.location.range = range;
                DefinitionUnit::Instance(Rc::new(instance))
            }
        }
    }

    fn to_param(name: Name, range: Range) -> OperatorParam {
        OperatorParam {
            name,
            arity: 0,
            location: Some(Location {
                line: range.start.line,
                column: range.start.column,
                range: Some(range),
            }),
        }
    }

    fn parse_operator(
        &mut self,
        name: Name,
        params: Vec<OperatorParam>,
        is_local: bool,
        location: Location,
    ) -> Parsed<DefinitionUnit> {
        let body_start = self.peek_location().position();
        let body = Rc::new(self.parse_expression(0)?);
        let last = &self.tokens[self.index - 1];
        let body_range = SourceRange {
            module: self.root_name.clone(),
            start: body_start,
            end: Position {
                line: last.line,
                column: last.end_column,
            },
        };
        let is_recursive = self.is_recursive_name(&name);
        Ok(DefinitionUnit::Definition(Rc::new(Definition {
            name,
            kind: DefinitionKind::Operator {
                params,
                body_range: Some(body_range),
            },
            body,
            is_local,
            is_recursive,
            location,
            is_self_referential: Default::default(),
        })))
    }

    fn parse_definition_unit(&mut self, is_local: bool) -> Parsed<DefinitionUnit> {
        let token = self.peek(0);
        let location = self.peek_location();
        let next = self.peek(1);
        if token.kind == TokenKind::Identifier
            && next.kind == TokenKind::Operator
            && is_infix(&next.text)
            && self.peek_kind(2) == TokenKind::Identifier
            && self.is_at("==", 3)
        {
            let (left, left_range) = self.expect_name()?;
            let operator = self.advance()?.text;
            let (right, right_range) = self.expect_name()?;
            self.expect("==")?;
            let params = vec![
                Self::to_param(left, left_range),
                Self::to_param(right, right_range),
            ];
            return self.parse_operator(operator, params, is_local, location);
        }
        let is_prefix_definition =
            token.kind != TokenKind::String && is_definable_prefix(&token.text);
        let is_postfix_definition =
            token.kind == TokenKind::Identifier && is_postfix(&next.text) && self.is_at("==", 2);
        if is_prefix_definition || is_postfix_definition {
            let operator = if is_prefix_definition {
                token.text.clone()
            } else {
                next.text.clone()
            };
            if is_prefix_definition {
                self.advance()?;
            }
            let (param, range) = self.expect_name()?;
            if is_postfix_definition {
                self.advance()?;
            }
            self.expect("==")?;
            return self.parse_operator(
                operator,
                vec![Self::to_param(param, range)],
                is_local,
                location,
            );
        }
        let name = self.expect_identifier()?;
        if self.accept("[") {
            let bounds = self.parse_bounds()?;
            self.expect("]")?;
            self.expect("==")?;
            let body = Rc::new(self.parse_expression(0)?);
            let is_recursive = self.is_recursive_name(&name);
            return Ok(DefinitionUnit::Definition(Rc::new(Definition {
                name,
                kind: DefinitionKind::Function { bounds },
                body,
                is_local,
                is_recursive,
                location,
                is_self_referential: Default::default(),
            })));
        }
        let definition_start = self.index;
        let params = self.parse_params()?;
        self.expect("==")?;
        if self.is_at("INSTANCE", 0) {
            let mut instance = self.parse_instance(Some(name), params, is_local, location)?;
            instance.definition_range = Some(self.get_range(definition_start));
            return Ok(DefinitionUnit::Instance(Rc::new(instance)));
        }
        self.parse_operator(name, params, is_local, location)
    }

    fn parse_instance(
        &mut self,
        name: Option<Name>,
        params: Vec<OperatorParam>,
        is_local: bool,
        location: Location,
    ) -> Parsed<Instance> {
        let start = self.index;
        self.expect("INSTANCE")?;
        let module = self.expect_module_name()?;
        let substitutions = if self.accept("WITH") {
            self.separated(|parser| {
                let target_start = parser.index;
                let name = parser.expect_substitution_target()?;
                let name_range = parser.get_range(target_start);
                parser.expect("<-")?;
                let expression = Rc::new(parser.parse_argument()?);
                Ok(InstanceSubstitution {
                    name,
                    name_range,
                    expression,
                })
            })?
        } else {
            Vec::new()
        };
        Ok(Instance {
            name,
            params,
            module,
            substitutions,
            is_local,
            location,
            instance_range: self.get_range(start),
            definition_range: None,
        })
    }

    fn parse_declaration(&mut self) -> Parsed<Declaration> {
        let start = self.index;
        let mut declaration = self.parse_declaration_unit()?;
        declaration.location.range = Some(self.get_range(start));
        Ok(declaration)
    }

    fn parse_declaration_unit(&mut self) -> Parsed<Declaration> {
        let location = self.peek_location();
        if self.is_at("_", 0) && self.peek_kind(1) == TokenKind::Operator {
            self.advance()?;
            let name = self.advance()?.text;
            let arity = if self.accept("_") { 2 } else { 1 };
            return Ok(Declaration {
                name,
                arity,
                location,
            });
        }
        if self.peek_kind(0) == TokenKind::Operator && self.is_at("_", 1) {
            let operator = self.advance()?.text;
            self.advance()?;
            let name = if &*operator == "-" {
                Rc::from("-.")
            } else {
                operator
            };
            return Ok(Declaration {
                name,
                arity: 1,
                location,
            });
        }
        let name = self.expect_identifier()?;
        if !self.accept("(") {
            return Ok(Declaration {
                name,
                arity: 0,
                location,
            });
        }
        let placeholders = self.separated(|parser| parser.expect("_"))?;
        self.expect(")")?;
        Ok(Declaration {
            name,
            arity: placeholders.len(),
            location,
        })
    }

    fn parse_declarations(&mut self) -> Parsed<Vec<Declaration>> {
        self.separated(Self::parse_declaration)
    }

    fn declare_recursive(&mut self) -> Parsed<Vec<Declaration>> {
        let declarations = self.parse_declarations()?;
        if let Some(scope) = self.recursive_scopes.last_mut() {
            scope.extend(
                declarations
                    .iter()
                    .map(|declaration| declaration.name.clone()),
            );
        }
        Ok(declarations)
    }

    fn get_closing_offset(&self, offset: usize) -> usize {
        let mut depth = 0i64;
        let mut offset = offset;
        loop {
            let token = self.peek(offset);
            if token.kind == TokenKind::End {
                return offset;
            }
            if token.kind == TokenKind::Operator && matches!(&*token.text, "(" | "[" | "{" | "<<") {
                depth += 1;
            }
            if token.kind == TokenKind::Operator
                && matches!(&*token.text, ")" | "]" | "}" | ">>" | "]_" | ">>_")
            {
                depth -= 1;
            }
            offset += 1;
            if depth <= 0 {
                return offset;
            }
        }
    }

    /// SANY inserts a break before each definition, which ends the fact list or step before it.
    fn is_definition_start(&self) -> bool {
        let token = self.peek(0);
        let next = self.peek(1);
        if token.kind != TokenKind::Identifier {
            return token.kind != TokenKind::String
                && is_definable_prefix(&token.text)
                && next.kind == TokenKind::Identifier
                && self.is_at("==", 2);
        }
        if self.is_at("(", 1) || self.is_at("[", 1) {
            return self.is_at("==", self.get_closing_offset(1));
        }
        if next.kind == TokenKind::Operator && is_postfix(&next.text) {
            return self.is_at("==", 2);
        }
        if next.kind == TokenKind::Operator && is_infix(&next.text) {
            return self.peek_kind(2) == TokenKind::Identifier && self.is_at("==", 3);
        }
        self.is_at("==", 1)
    }

    fn is_proof_start(&self, token: &Peeked) -> bool {
        if token.kind == TokenKind::Keyword {
            return matches!(&*token.text, "BY" | "PROOF" | "OBVIOUS" | "OMITTED");
        }
        if token.kind != TokenKind::Step {
            return false;
        }
        match token.text.as_bytes()[1] {
            b'*' => return self.proof_levels.is_empty(),
            b'+' => return true,
            _ if self.proof_levels.is_empty() => return true,
            _ => {}
        }
        let level = self.get_proof_level();
        level >= 0 && Self::get_step_level(&token.text) > level
    }

    fn is_correct_level(&mut self, text: &str) -> bool {
        let level = Self::get_step_level(text);
        let top = self.proof_levels.len() - 1;
        let outer = top
            .checked_sub(1)
            .map_or(-1, |index| self.proof_levels[index]);
        let is_first = self.proof_levels[top] < 0;
        if is_first {
            self.proof_levels[top] = if level < 0 { outer + 1 } else { level };
        }
        match level {
            -1 => true,
            -2 => is_first,
            _ if is_first => level > outer,
            _ => self.proof_levels[top] == level,
        }
    }

    fn is_module_symbol(&self, name: &str, with_definitions: bool) -> bool {
        self.open_modules.iter().any(|module| {
            module
                .constants
                .iter()
                .any(|constant| &*constant.name == name)
                || module
                    .variables
                    .iter()
                    .any(|variable| &*variable.name == name)
                || (with_definitions
                    && module
                        .definitions
                        .iter()
                        .any(|definition| &*definition.name == name))
        })
    }

    fn is_hide_fact(&self, fact: &Fact) -> bool {
        let Fact::Expression(expression) = fact else {
            return true;
        };
        match &expression.kind {
            ExpressionKind::Subexpression { .. } => true,
            ExpressionKind::Apply { operator, .. } => operator.contains('!'),
            ExpressionKind::Identifier { name, .. } => {
                name.starts_with('<')
                    || name.contains('!')
                    || (!is_builtin_constant(name)
                        && (self.fact_names.contains(&**name)
                            || !self.is_module_symbol(name, true)))
            }
            _ => false,
        }
    }

    fn is_fact_ahead(&self) -> bool {
        let token = self.peek(0);
        match token.kind {
            TokenKind::Step => Self::is_step_reference(&token.text),
            TokenKind::Keyword => is_fact_keyword(&token.text),
            TokenKind::End | TokenKind::ModuleEnd | TokenKind::Separator => false,
            _ => !self.is_definition_start(),
        }
    }

    /// SANY reads an infix or postfix operator alone as its name, but a prefix operator such as `-`
    /// as the start of an expression.
    fn parse_fact(&mut self) -> Parsed<Fact> {
        let start = self.index;
        let token = self.raw(0).clone();
        let peeked = self.peek(0);
        if peeked.kind == TokenKind::Operator
            && !is_expression_prefix(&peeked.text)
            && is_operator_name(&peeked.text)
        {
            self.index += 1;
            let reference = located(
                ExpressionKind::OperatorReference {
                    operator: token.text.clone(),
                    spelling: token.spelling.clone(),
                },
                location_of(&token),
            );
            return Ok(Fact::Expression(Rc::new(self.with_range(reference, start))));
        }
        if !self.accept("MODULE") {
            return Ok(Fact::Expression(Rc::new(self.parse_expression(0)?)));
        }
        let name = self.expect_identifier()?;
        let mut location = location_of(&token);
        location.range = Some(self.get_range(start));
        Ok(Fact::Module { name, location })
    }

    fn declare_proof_symbol(&mut self, name: &Name) {
        if let Some(scope) = self.proof_scopes.last_mut() {
            scope.insert(name.clone());
        }
    }

    fn with_proof_scope<T>(&mut self, parse: impl FnOnce(&mut Self) -> Parsed<T>) -> Parsed<T> {
        self.proof_scopes.push(FastSet::default());
        let result = parse(self)?;
        self.proof_scopes.pop();
        Ok(result)
    }

    fn parse_defs(&mut self) -> Parsed<Vec<Fact>> {
        // A DEF entry in parentheses keeps them in its range, as SANY's parser rejects them.
        let defs = self.separated(|parser| {
            let start = parser.index;
            let is_parenthesized = parser.is_at("(", 0);
            Ok(match parser.parse_fact()? {
                Fact::Expression(expression) if is_parenthesized => {
                    Fact::Expression(Rc::new(parser.with_range((*expression).clone(), start)))
                }
                fact => fact,
            })
        })?;
        if self.mode != Mode::Tlc {
            return Ok(defs);
        }
        let is_invalid = |def: &Fact| match def {
            Fact::Expression(expression) => match &expression.kind {
                ExpressionKind::Identifier { name, .. } => {
                    self.proof_scopes
                        .iter()
                        .any(|scope| scope.contains(&**name))
                        || self.is_module_symbol(name, false)
                }
                _ => false,
            },
            Fact::Module { .. } => false,
        };
        // SANY's report words them where its generator meets them (`resolve.rs`).
        if self.sany_errors.is_some() {
            return Ok(defs);
        }
        let Some(Fact::Expression(first)) = defs.iter().find(|def| is_invalid(def)) else {
            return Ok(defs);
        };
        Err(self.error_at(
            "DEF clause entry should describe a defined operator",
            first.location.line,
            first.location.column,
        ))
    }

    fn parse_facts(&mut self) -> Parsed<(Vec<Fact>, Vec<Fact>)> {
        let facts = if self.is_fact_ahead() {
            self.separated(Self::parse_fact)?
        } else {
            Vec::new()
        };
        let defs = if self.accept("DEF") || self.accept("DEFS") {
            self.parse_defs()?
        } else {
            Vec::new()
        };
        Ok((facts, defs))
    }

    fn parse_use_or_hide(&mut self) -> Parsed<UseOrHide> {
        let start = self.index;
        let keyword = self.advance()?;
        let is_hide = &*keyword.text != "USE";
        let is_only = !is_hide && self.accept("ONLY");
        let keyword_range = self.get_range(start);
        let (facts, defs) = self.parse_facts()?;
        if is_hide && self.mode == Mode::Tlc {
            let errors: Vec<SanyError> = facts
                .iter()
                .filter(|fact| !self.is_hide_fact(fact))
                .map(|fact| {
                    let location = match fact {
                        Fact::Expression(expression) => &expression.location,
                        Fact::Module { location, .. } => location,
                    };
                    let range = location
                        .range
                        .clone()
                        .unwrap_or_else(|| self.get_range(start));
                    SanyError {
                        location: format_range(&range),
                        message: "The only expression allowed as a fact in a HIDE is \nthe name of a theorem, assumption, or step.".to_string(),
                    }
                })
                .collect();
            match &mut self.sany_errors {
                Some(collected) => collected.extend(errors),
                None if !errors.is_empty() => return Err(SyntaxError::sany(errors)),
                None => {}
            }
        }
        let mut location = location_of(&keyword);
        location.range = Some(self.get_range(start));
        Ok(UseOrHide {
            is_hide,
            is_only,
            facts,
            defs,
            keyword: keyword_range,
            location,
        })
    }

    fn parse_new_symbol(&mut self) -> Parsed<NewSymbol> {
        let start = self.index;
        let mut location = self.peek_location();
        let is_new = self.accept("NEW");
        let token = self.peek(0);
        let level = if token.kind == TokenKind::Keyword {
            get_new_symbol_level(&token.text)
        } else {
            None
        };
        if !is_new && level.is_none() {
            return Err(self.error(&format!(
                "Expected a declaration but found {}",
                self.describe(&token)
            )));
        }
        if level.is_some() {
            self.advance()?;
        }
        if level == Some(SymbolLevel::Variable) {
            let (name, range) = self.expect_name()?;
            self.declare_proof_symbol(&name);
            location.range = Some(self.get_range(start));
            return Ok(NewSymbol {
                name,
                arity: 0,
                level: SymbolLevel::Variable,
                set: None,
                name_range: Some(range),
                location,
            });
        }
        let declaration = self.parse_declaration()?;
        self.declare_proof_symbol(&declaration.name);
        let level = level.unwrap_or(SymbolLevel::Constant);
        let is_bounded = level == SymbolLevel::Constant && self.is_at("\\in", 0);
        if is_bounded && declaration.arity > 0 {
            return Err(self.error("declared symbol with arguments before \\in"));
        }
        if is_bounded {
            self.advance()?;
        }
        let set = if is_bounded {
            Some(Rc::new(self.parse_expression(0)?))
        } else {
            None
        };
        location.range = Some(self.get_range(start));
        Ok(NewSymbol {
            name: declaration.name,
            arity: declaration.arity,
            level,
            set,
            name_range: declaration.location.range,
            location,
        })
    }

    fn parse_assume_prove(&mut self) -> Parsed<AssumeProve> {
        let start = self.index;
        let mut location = location_of(&self.expect("ASSUME")?);
        let assumptions = self.separated(|parser| {
            if parser.is_at("ASSUME", 0) {
                return Ok(Assumed::AssumeProve(
                    parser.with_proof_scope(Self::parse_assume_prove)?,
                ));
            }
            let token = parser.peek(0);
            if token.kind == TokenKind::Keyword
                && (&*token.text == "NEW" || get_new_symbol_level(&token.text).is_some())
            {
                return Ok(Assumed::NewSymbol(parser.parse_new_symbol()?));
            }
            Ok(Assumed::Expression(Rc::new(parser.parse_expression(0)?)))
        })?;
        self.expect("PROVE")?;
        let conclusion = Rc::new(self.parse_expression(0)?);
        location.range = Some(self.get_range(start));
        Ok(AssumeProve {
            assumptions,
            conclusion,
            location,
        })
    }

    fn is_name_list_ahead(&self, terminator: &str) -> bool {
        let mut offset = 0;
        while self.peek_kind(offset) == TokenKind::Identifier && self.is_at(",", offset + 1) {
            offset += 2;
        }
        self.peek_kind(offset) == TokenKind::Identifier && self.is_at(terminator, offset + 1)
    }

    fn declare_proof_symbols(&mut self, names: &[Name], bounds: &[Bound]) {
        names
            .iter()
            .chain(bounds.iter().flat_map(|bound| bound.pattern.names()))
            .cloned()
            .collect::<Vec<_>>()
            .iter()
            .for_each(|name| self.declare_proof_symbol(name));
    }

    fn parse_step_body(&mut self) -> Parsed<StepBody> {
        let location = self.peek_location();
        if self.is_at("USE", 0) || self.is_at("HIDE", 0) {
            return Ok(StepBody::UseOrHide(self.parse_use_or_hide()?));
        }
        if self.is_at("INSTANCE", 0) {
            let start = self.index;
            let mut instance = self.parse_instance(None, Vec::new(), false, location)?;
            instance.location.range = Some(self.get_range(start));
            return Ok(StepBody::Instance(Rc::new(instance)));
        }
        if self.is_at("DEFINE", 0) || self.is_definition_start() {
            let start = self.index;
            self.accept("DEFINE");
            let mut definitions = vec![self.parse_definition(false)?];
            while self.is_definition_start() {
                definitions.push(self.parse_definition(false)?);
            }
            let mut location = location;
            location.range = Some(self.get_range(start));
            return Ok(StepBody::Define {
                definitions,
                location,
            });
        }
        if self.accept("HAVE") {
            return Ok(StepBody::Have(Rc::new(self.parse_expression(0)?)));
        }
        if self.accept("TAKE") {
            let is_bounded = self.is_bound_ahead();
            let (names, name_ranges) = if is_bounded {
                (Vec::new(), Vec::new())
            } else {
                self.names()?
            };
            let bounds = if is_bounded {
                self.parse_bounds()?
            } else {
                Vec::new()
            };
            self.declare_proof_symbols(&names, &bounds);
            return Ok(StepBody::Take {
                names,
                name_ranges,
                bounds,
            });
        }
        if self.accept("WITNESS") {
            let expressions = self.separated(|parser| parser.parse_expression(0).map(Rc::new))?;
            return Ok(StepBody::Witness(expressions));
        }
        if self.accept("PICK") {
            let is_names = self.is_name_list_ahead(":");
            let (names, name_ranges) = if is_names {
                self.names()?
            } else {
                (Vec::new(), Vec::new())
            };
            let bounds = if is_names {
                Vec::new()
            } else {
                self.parse_bounds()?
            };
            self.declare_proof_symbols(&names, &bounds);
            self.expect(":")?;
            let body = Rc::new(self.parse_expression(0)?);
            return Ok(StepBody::Pick {
                names,
                name_ranges,
                bounds,
                body,
            });
        }
        if self.accept("CASE") {
            return Ok(StepBody::Case(Rc::new(self.parse_expression(0)?)));
        }
        let is_suffices = self.accept("SUFFICES");
        let statement = if self.is_at("ASSUME", 0) {
            Statement::AssumeProve(self.parse_assume_prove()?)
        } else {
            Statement::Expression(Rc::new(self.parse_expression(0)?))
        };
        Ok(StepBody::Assert {
            is_suffices,
            statement,
        })
    }

    /// The names an assertion assumes stay in its own proof, and other steps declare theirs for the
    /// rest of the enclosing proof.
    fn parse_step(&mut self) -> Parsed<ProofStep> {
        let start = self.index;
        let is_qed = self.is_at("QED", 1);
        let step = self.peek(0);
        if step.kind != TokenKind::Step {
            return Err(self.error(&format!(
                "Expected a step number but found {}",
                self.describe(&step)
            )));
        }
        if !self.is_correct_level(&step.text) {
            let message = if is_qed {
                "QED step's number has bad level"
            } else {
                "step's number has bad level"
            };
            return Err(self.error_at(message, step.line, step.column));
        }
        let is_named_unnumbered =
            Self::get_step_level(&step.text) < 0 && self.get_step_name(&step.text).is_some();
        self.index += 1;
        // SANY's generator rejects it at the step, a semantic error.
        if is_named_unnumbered && self.mode == Mode::Tlc {
            let error = SanyError {
                location: format_range(&self.get_range(start)),
                message: "<*> and <+> cannot be used for a named step.".to_owned(),
            };
            match &mut self.sany_errors {
                Some(errors) => errors.push(error),
                None => return Err(SyntaxError::sany(vec![error])),
            }
        }
        let name = self.get_step_name(&step.text);
        let mut location = location_of(&self.tokens[start]);
        let statement_start = self.index;
        self.proof_scopes.push(FastSet::default());
        let body = if self.accept("QED") {
            StepBody::Qed
        } else {
            self.parse_step_body()?
        };
        let head = self.get_range(start);
        let statement = self.get_range(statement_start);
        let has_proof = self.is_proof_start(&self.peek(0));
        let is_provable = matches!(
            body,
            StepBody::Qed | StepBody::Pick { .. } | StepBody::Case(_) | StepBody::Assert { .. }
        );
        if has_proof && !is_provable {
            return Err(self.error("Proof of a step that does not take a proof"));
        }
        let proof = if has_proof {
            Some(Box::new(self.parse_proof()?))
        } else {
            None
        };
        let scope = self.proof_scopes.pop().unwrap_or_default();
        let is_assertion = matches!(
            body,
            StepBody::Assert {
                is_suffices: false,
                ..
            }
        );
        if !is_assertion {
            scope
                .iter()
                .for_each(|name| self.declare_proof_symbol(name));
        }
        location.range = Some(self.get_range(start));
        Ok(ProofStep {
            name,
            token: step.text,
            body,
            head,
            statement,
            proof,
            location,
        })
    }

    fn parse_proof_body(&mut self) -> Parsed<Proof> {
        let location = self.peek_location();
        if self.is_at("BY", 0) || (self.is_at("PROOF", 0) && self.is_at("BY", 1)) {
            self.accept("PROOF");
            self.advance()?;
            let keyword = self.get_range(self.index - 1);
            let is_only = self.accept("ONLY");
            let (facts, defs) = self.parse_facts()?;
            return Ok(Proof {
                kind: ProofKind::By {
                    is_only,
                    facts,
                    defs,
                    keyword,
                },
                location,
            });
        }
        let terminal = self.peek(if self.is_at("PROOF", 0) { 1 } else { 0 });
        if terminal.kind == TokenKind::Keyword && matches!(&*terminal.text, "OBVIOUS" | "OMITTED") {
            self.accept("PROOF");
            self.advance()?;
            let keyword = self.get_range(self.index - 1);
            let kind = if &*terminal.text == "OBVIOUS" {
                ProofKind::Obvious { keyword }
            } else {
                ProofKind::Omitted { keyword }
            };
            return Ok(Proof { kind, location });
        }
        self.accept("PROOF");
        let mut steps = vec![self.parse_step()?];
        while !matches!(steps[steps.len() - 1].body, StepBody::Qed) {
            steps.push(self.parse_step()?);
        }
        Ok(Proof {
            kind: ProofKind::Steps {
                level: self.get_proof_level(),
                steps,
            },
            location,
        })
    }

    fn parse_proof(&mut self) -> Parsed<Proof> {
        let start = self.index;
        self.proof_levels.push(-1);
        let mut proof = self.with_proof_scope(Self::parse_proof_body)?;
        self.proof_levels.pop();
        proof.location.range = Some(self.get_range(start));
        Ok(proof)
    }

    /// SANY binds the name of a theorem or assumption that a module already defines to the first
    /// definition, warning of the second.
    fn add_fact_definition(&mut self, definition: Definition) {
        let module = self.open_modules.last_mut().expect("an open module");
        if module
            .definitions
            .iter()
            .any(|other| other.name == definition.name)
        {
            return;
        }
        module.definitions.push(Rc::new(definition));
    }

    fn parse_fact_name(&mut self) -> Parsed<Option<Name>> {
        let is_named = self.peek_kind(0) == TokenKind::Identifier && self.is_at("==", 1);
        if !is_named {
            return Ok(None);
        }
        let name = self.expect_identifier()?;
        self.fact_names.insert(name.clone());
        self.advance()?;
        Ok(Some(name))
    }

    fn parse_theorem(&mut self) -> Parsed<()> {
        let start = self.index;
        let keyword = self.advance()?;
        let name = self.parse_fact_name()?;
        let (statement, proof) = self.with_proof_scope(|parser| {
            let statement = if parser.is_at("ASSUME", 0) {
                Statement::AssumeProve(parser.parse_assume_prove()?)
            } else {
                Statement::Expression(Rc::new(parser.parse_expression(0)?))
            };
            let proof = if parser.is_proof_start(&parser.peek(0)) {
                Some(parser.parse_proof()?)
            } else {
                None
            };
            Ok((statement, proof))
        })?;
        let mut location = location_of(&keyword);
        location.range = Some(self.get_range(start));
        let body = match &statement {
            Statement::Expression(expression) => Some(expression.clone()),
            Statement::AssumeProve(_) => None,
        };
        let theorem = Rc::new(Theorem {
            name: name.clone(),
            statement,
            proof,
            location: location.clone(),
        });
        let module = self.open_modules.last_mut().expect("an open module");
        module.theorems.push(theorem.clone());
        module.units.push(ModuleUnit::Theorem(theorem));
        if let (Some(name), Some(body)) = (name, body) {
            self.add_fact_definition(Definition {
                name,
                kind: DefinitionKind::Operator {
                    params: Vec::new(),
                    body_range: None,
                },
                body,
                is_local: false,
                is_recursive: false,
                location,
                is_self_referential: Default::default(),
            });
        }
        Ok(())
    }

    fn parse_assumption(&mut self) -> Parsed<Assumption> {
        let start = self.index;
        let keyword = self.advance()?;
        let name = self.parse_fact_name()?;
        let expression = Rc::new(self.parse_expression(0)?);
        let mut location = location_of(&keyword);
        location.range = Some(self.get_range(start));
        Ok(Assumption {
            name,
            expression,
            is_axiom: &*keyword.text == "AXIOM",
            location,
        })
    }

    fn current_module(&mut self) -> &mut Module {
        self.open_modules.last_mut().expect("an open module")
    }

    fn add_definition_unit(&mut self, unit: DefinitionUnit) {
        let module = self.current_module();
        match unit {
            DefinitionUnit::Instance(instance) => {
                module.instances.push(instance.clone());
                module.units.push(ModuleUnit::Instance(instance));
            }
            DefinitionUnit::Definition(definition) => {
                module.definitions.push(definition.clone());
                module.units.push(ModuleUnit::Definition(definition));
            }
        }
    }

    fn parse_module_body(&mut self) -> Parsed<Module> {
        let mut location = location_of(&self.expect("----")?);
        self.expect("MODULE")?;
        let name = self.expect_module_name()?;
        self.expect("----")?;
        if self.open_modules.is_empty() {
            self.root_name = name.clone();
        }
        self.open_modules.push(Module {
            name,
            modules: Vec::new(),
            extends: Vec::new(),
            extends_ranges: Vec::new(),
            constants: Vec::new(),
            variables: Vec::new(),
            definitions: Vec::new(),
            instances: Vec::new(),
            assumptions: Vec::new(),
            location: location.clone(),
            theorems: Vec::new(),
            uses: Vec::new(),
            units: Vec::new(),
        });
        self.recursive_scopes.push(FastSet::default());
        if self.accept("EXTENDS") {
            self.separated(|parser| {
                let start = parser.index;
                let extendee = parser.expect_module_name()?;
                let range = parser.get_range(start);
                let module = parser.current_module();
                module.extends.push(extendee);
                module.extends_ranges.push(range);
                Ok(())
            })?;
        }
        loop {
            let token_index = self.index;
            let token = self.peek(0);
            if token.kind == TokenKind::ModuleEnd {
                let raw = self.raw(0);
                location.range = Some(SourceRange {
                    module: self.root_name.clone(),
                    start: location.position(),
                    end: Position {
                        line: raw.line,
                        column: raw.end_column,
                    },
                });
                let mut module = self.open_modules.pop().expect("an open module");
                module.location = location;
                self.recursive_scopes.pop();
                return Ok(module);
            }
            if token.kind == TokenKind::Separator {
                if self.is_at("MODULE", 1) {
                    let submodule = Rc::new(self.parse_module_body()?);
                    let module = self.current_module();
                    module.modules.push(submodule.clone());
                    module.units.push(ModuleUnit::Module(submodule));
                    self.expect("====")?;
                    continue;
                }
                self.advance()?;
                continue;
            }
            match &*token.text {
                "CONSTANT" | "CONSTANTS" => {
                    let mut unit_location = location_of(&self.advance()?);
                    let declarations: Vec<Rc<Declaration>> = self
                        .parse_declarations()?
                        .into_iter()
                        .map(Rc::new)
                        .collect();
                    unit_location.range = Some(self.get_range(token_index));
                    let module = self.current_module();
                    module.constants.extend(declarations.iter().cloned());
                    module.units.push(ModuleUnit::Constants {
                        declarations,
                        location: unit_location,
                    });
                    continue;
                }
                "VARIABLE" | "VARIABLES" => {
                    let mut unit_location = location_of(&self.advance()?);
                    let declarations = self.separated(|parser| {
                        let start = parser.index;
                        let mut location = parser.peek_location();
                        let name = parser.expect_identifier()?;
                        location.range = Some(parser.get_range(start));
                        Ok(Rc::new(Declaration {
                            name,
                            arity: 0,
                            location,
                        }))
                    })?;
                    unit_location.range = Some(self.get_range(token_index));
                    let module = self.current_module();
                    module.variables.extend(declarations.iter().cloned());
                    module.units.push(ModuleUnit::Variables {
                        declarations,
                        location: unit_location,
                    });
                    continue;
                }
                "ASSUME" | "ASSUMPTION" | "AXIOM" => {
                    let assumption = Rc::new(self.parse_assumption()?);
                    let module = self.current_module();
                    module.assumptions.push(assumption.clone());
                    module
                        .units
                        .push(ModuleUnit::Assumption(assumption.clone()));
                    if let Some(name) = &assumption.name {
                        self.add_fact_definition(Definition {
                            name: name.clone(),
                            kind: DefinitionKind::Operator {
                                params: Vec::new(),
                                body_range: None,
                            },
                            body: assumption.expression.clone(),
                            is_local: false,
                            is_recursive: false,
                            location: assumption.location.clone(),
                            is_self_referential: Default::default(),
                        });
                    }
                    continue;
                }
                "USE" | "HIDE" => {
                    // SANY's module body takes a USE only when ONLY doesn't follow it.
                    if self.is_at("USE", 0) && self.is_at("ONLY", 1) {
                        return Err(self.error(&format!(
                            "Expected a module unit but found {}",
                            self.describe(&token)
                        )));
                    }
                    let use_or_hide = Rc::new(self.parse_use_or_hide()?);
                    let module = self.current_module();
                    module.uses.push(use_or_hide.clone());
                    module.units.push(ModuleUnit::Use(use_or_hide));
                    continue;
                }
                "RECURSIVE" => {
                    self.advance()?;
                    let declarations = self.declare_recursive()?.into_iter().map(Rc::new).collect();
                    self.current_module()
                        .units
                        .push(ModuleUnit::Recursive(declarations));
                    continue;
                }
                "INSTANCE" => {
                    let location = self.peek_location();
                    let mut instance = self.parse_instance(None, Vec::new(), false, location)?;
                    instance.location.range = Some(self.get_range(token_index));
                    self.add_definition_unit(DefinitionUnit::Instance(Rc::new(instance)));
                    continue;
                }
                "LOCAL" => {
                    let location = self.peek_location();
                    self.advance()?;
                    if self.is_at("INSTANCE", 0) {
                        let mut instance = self.parse_instance(None, Vec::new(), true, location)?;
                        instance.location.range = Some(self.get_range(token_index));
                        self.add_definition_unit(DefinitionUnit::Instance(Rc::new(instance)));
                        continue;
                    }
                    let unit = self.parse_definition_unit(true)?;
                    let unit = self.with_unit_range(unit, token_index);
                    self.add_definition_unit(unit);
                    continue;
                }
                _ => {}
            }
            if token.kind == TokenKind::Keyword
                && matches!(
                    &*token.text,
                    "THEOREM" | "LEMMA" | "COROLLARY" | "PROPOSITION"
                )
            {
                self.parse_theorem()?;
                continue;
            }
            let unit = self.parse_definition(false)?;
            self.add_definition_unit(unit);
        }
    }
}

fn parse(
    source: &str,
    mode: Mode,
    tokens: Option<&[Token]>,
    version: TlcVersion,
) -> Parsed<Module> {
    parse_collecting(source, mode, tokens, version, false).map(|parsed| parsed.0)
}

fn parse_collecting(
    source: &str,
    mode: Mode,
    tokens: Option<&[Token]>,
    version: TlcVersion,
    is_collecting: bool,
) -> Parsed<(Module, Vec<SanyError>)> {
    let tokens = match tokens {
        Some(tokens) => tokens.to_vec(),
        None => tokenize(source)?,
    };
    let end: Rc<str> = Rc::from("");
    let tokens = tokens.into_iter().map(read_at_as_identifier).collect();
    let mut parser = Parser {
        tokens,
        index: 0,
        offside_columns: Vec::new(),
        last: None,
        preceding: None,
        recursive_scopes: Vec::new(),
        fact_names: FastSet::default(),
        proof_scopes: Vec::new(),
        open_modules: Vec::new(),
        root_name: end.clone(),
        end,
        is_keyword_module_name: false,
        proof_levels: Vec::new(),
        mode,
        version,
        sany_errors: is_collecting.then(Vec::new),
    };
    let module = parser.parse_module_body()?;
    // SANY's lexer marks where each definition begins before its parser runs, which can split a
    // module's name from a keyword that the parser would take for one. That check is SANY's own
    // parser, which a later milestone ports.
    if parser.is_keyword_module_name {
        return Err(SyntaxError {
            message: "unsupported: a keyword names a module".to_string(),
            failure: None,
            sany: None,
        });
    }
    Ok((module, parser.sany_errors.unwrap_or_default()))
}

pub fn parse_module(source: &str) -> Parsed<Module> {
    parse(source, Mode::Tlc, None, TlcVersion::Master)
}

/// Parses a module as `parse_module_tokens` does, and collects the errors of SANY's semantic
/// analysis that the parser finds, for SANY's messages.
pub fn parse_module_for_sany(
    source: &str,
    tokens: &[Token],
    version: TlcVersion,
) -> Parsed<(Module, Vec<SanyError>)> {
    parse_collecting(source, Mode::Tlc, Some(tokens), version, true)
}

/// Parses a module the caller has tokenized already, as SANY in a version of TLC does.
pub fn parse_module_tokens(source: &str, tokens: &[Token], version: TlcVersion) -> Parsed<Module> {
    parse(source, Mode::Tlc, Some(tokens), version)
}

pub fn parse_sany_module(
    source: &str,
    tokens: Option<&[Token]>,
    version: TlcVersion,
) -> Parsed<Module> {
    parse(source, Mode::Sany, tokens, version)
}

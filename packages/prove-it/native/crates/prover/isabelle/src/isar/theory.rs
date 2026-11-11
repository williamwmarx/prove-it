//! Reads the outer syntax of the theories tlapm writes (Isabelle.thy_temp in isabelle.ml): the
//! header, the constants it declares, and one lemma with its proof.
//!
//! ```text
//!   theory NAME imports Constant Zenon begin
//!   consts "name" :: type ...
//!   lemma NAME: fixes ... assumes NAME: "prop" ... shows "prop" (is "PROP ?NAME")
//!   proof - show "PROP ?NAME" [using assms] by METHOD [METHOD] qed
//!   end
//! ```

use crate::error::{Error, Res, error_exn};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OuterTokenKind {
    Word,
    String,
    Symbol,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OuterToken {
    pub kind: OuterTokenKind,
    pub text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementElement {
    Fixes { names: Vec<String> },
    Assumes { name: String, prop: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoryConst {
    pub name: String,
    pub ty: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoryText {
    pub name: String,
    pub consts: Vec<TheoryConst>,
    pub elements: Vec<StatementElement>,
    pub shows: String,
    pub is_using_assms: bool,
    /// The method of by, then the terminal method if there is one, as outer tokens.
    pub method: Vec<OuterToken>,
}

/// JavaScript's `\s`: its WhiteSpace and LineTerminator characters.
pub(crate) fn is_js_whitespace(char: char) -> bool {
    matches!(
        char,
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

fn is_word_char(char: char) -> bool {
    char.is_ascii_alphanumeric() || matches!(char, '_' | '\'' | '.')
}

/// The character at a byte position of text, which is always on a character boundary.
fn char_at(text: &str, position: usize) -> Option<char> {
    text.get(position..).and_then(|rest| rest.chars().next())
}

/// Outer strings unescape \" and \\; symbols such as \<in> stay as they are.
fn read_string(text: &str, start: usize) -> Res<(String, usize)> {
    let bytes = text.as_bytes();
    let mut result = String::new();
    let mut position = start + 1;
    while position < bytes.len() && bytes[position] != b'"' {
        if bytes[position] == b'\\' && matches!(bytes.get(position + 1), Some(b'"' | b'\\')) {
            result.push(char::from(bytes[position + 1]));
            position += 2;
        } else {
            let char = char_at(text, position).unwrap_or_default();
            result.push(char);
            position += char.len_utf8();
        }
    }
    if position >= bytes.len() {
        return Err(error_exn("Outer lexical error: unterminated string"));
    }
    Ok((result, position + 1))
}

fn skip_comment(text: &str, start: usize) -> Res<usize> {
    let bytes = text.as_bytes();
    let mut depth = 0;
    let mut position = start;
    loop {
        if bytes[position..].starts_with(b"(*") {
            depth += 1;
            position += 2;
        } else if bytes[position..].starts_with(b"*)") {
            depth -= 1;
            position += 2;
        } else if position >= bytes.len() {
            return Err(error_exn("Outer lexical error: unterminated comment"));
        } else {
            position += 1;
        }
        if depth <= 0 {
            return Ok(position);
        }
    }
}

fn tokenize(text: &str) -> Res<Vec<OuterToken>> {
    let mut tokens = Vec::new();
    let mut position = 0;
    while let Some(char) = char_at(text, position) {
        if is_js_whitespace(char) {
            position += char.len_utf8();
        } else if text[position..].starts_with("(*") {
            position = skip_comment(text, position)?;
        } else if char == '"' {
            let (string, end) = read_string(text, position)?;
            tokens.push(OuterToken {
                kind: OuterTokenKind::String,
                text: string,
            });
            position = end;
        } else if is_word_char(char) {
            let end = text[position..]
                .find(|char| !is_word_char(char))
                .map_or(text.len(), |offset| position + offset);
            tokens.push(OuterToken {
                kind: OuterTokenKind::Word,
                text: text[position..end].to_string(),
            });
            position = end;
        } else {
            tokens.push(OuterToken {
                kind: OuterTokenKind::Symbol,
                text: char.to_string(),
            });
            position += char.len_utf8();
        }
    }
    Ok(tokens)
}

const KEYWORDS: [&str; 11] = [
    "fixes", "assumes", "shows", "lemma", "proof", "show", "using", "by", "qed", "end", "consts",
];

struct OuterParser {
    tokens: Vec<OuterToken>,
    position: usize,
}

impl OuterParser {
    fn peek(&self) -> Option<&OuterToken> {
        self.tokens.get(self.position)
    }

    fn is_kind(&self, kind: OuterTokenKind) -> bool {
        self.peek().is_some_and(|token| token.kind == kind)
    }

    fn is_word(&self, word: &str) -> bool {
        self.peek()
            .is_some_and(|token| token.kind == OuterTokenKind::Word && token.text == word)
    }

    fn syntax_error(&self) -> Error {
        error_exn(format!(
            "Outer syntax error at: {}",
            self.peek()
                .map_or("end of input", |token| token.text.as_str())
        ))
    }

    fn expect_word(&mut self, word: &str) -> Res<()> {
        if !self.is_word(word) {
            return Err(self.syntax_error());
        }
        self.position += 1;
        Ok(())
    }

    fn expect_symbol(&mut self, symbol: &str) -> Res<()> {
        if !self
            .peek()
            .is_some_and(|token| token.kind == OuterTokenKind::Symbol && token.text == symbol)
        {
            return Err(self.syntax_error());
        }
        self.position += 1;
        Ok(())
    }

    fn is_name(&self) -> bool {
        self.peek().is_some_and(|token| {
            token.kind == OuterTokenKind::Word && !KEYWORDS.contains(&token.text.as_str())
        })
    }

    fn name(&mut self) -> Res<String> {
        if !self.is_name() {
            return Err(self.syntax_error());
        }
        self.position += 1;
        Ok(self.tokens[self.position - 1].text.clone())
    }

    fn string(&mut self) -> Res<String> {
        if !self.is_kind(OuterTokenKind::String) {
            return Err(self.syntax_error());
        }
        self.position += 1;
        Ok(self.tokens[self.position - 1].text.clone())
    }

    fn name_or_string(&mut self) -> Res<String> {
        if self.is_kind(OuterTokenKind::String) {
            self.string()
        } else {
            self.name()
        }
    }
}

pub fn parse_theory(text: &str) -> Res<TheoryText> {
    let mut parser = OuterParser {
        tokens: tokenize(text)?,
        position: 0,
    };
    parser.expect_word("theory")?;
    let theory_name = parser.name()?;
    parser.expect_word("imports")?;
    while !parser.is_word("begin") {
        parser.name()?;
    }
    parser.expect_word("begin")?;
    let mut consts = Vec::new();
    if parser.is_word("consts") {
        parser.position += 1;
        while parser.is_kind(OuterTokenKind::String) {
            let const_name = parser.string()?;
            parser.expect_symbol(":")?;
            parser.expect_symbol(":")?;
            consts.push(TheoryConst {
                name: const_name,
                ty: parser.name_or_string()?,
            });
        }
    }
    parser.expect_word("lemma")?;
    parser.name()?;
    parser.expect_symbol(":")?;
    let mut elements = Vec::new();
    while parser.is_word("fixes") || parser.is_word("assumes") {
        if parser.is_word("fixes") {
            parser.position += 1;
            let mut names = vec![parser.name()?];
            while parser.is_name() {
                names.push(parser.name()?);
            }
            elements.push(StatementElement::Fixes { names });
        } else {
            parser.position += 1;
            let assumption = parser.name()?;
            parser.expect_symbol(":")?;
            elements.push(StatementElement::Assumes {
                name: assumption,
                prop: parser.string()?,
            });
        }
    }
    parser.expect_word("shows")?;
    let shows = parser.string()?;
    parser.expect_symbol("(")?;
    parser.expect_word("is")?;
    parser.string()?;
    parser.expect_symbol(")")?;
    parser.expect_word("proof")?;
    parser.expect_symbol("-")?;
    parser.expect_word("show")?;
    parser.string()?;
    let is_using_assms = parser.is_word("using");
    if is_using_assms {
        parser.position += 1;
        parser.expect_word("assms")?;
    }
    parser.expect_word("by")?;
    let method_start = parser.position;
    while parser.position < parser.tokens.len() && !parser.is_word("qed") {
        parser.position += 1;
    }
    let method = parser.tokens[method_start..parser.position].to_vec();
    parser.expect_word("qed")?;
    parser.expect_word("end")?;
    if parser.position != parser.tokens.len() {
        return Err(parser.syntax_error());
    }
    Ok(TheoryText {
        name: theory_name,
        consts,
        elements,
        shows,
        is_using_assms,
        method,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isar::inner_syntax::{Ast, parse_prop, parse_type};
    use crate::pure::term::{Typ, TypNode};

    // The expectations in testdata/isar are what the TypeScript parsers produce, rendered alike.

    macro_rules! fixtures {
        ($($name:literal),* $(,)?) => {
            [$((
                $name,
                include_str!(concat!("../../../../../../tests/fixtures/isabelle/", $name, ".thy")),
                include_str!(concat!("../../testdata/isar/", $name, ".dump")),
            )),*]
        };
    }

    fn escape(text: &str) -> String {
        text.replace('\\', "\\\\")
            .replace('\n', "\\n")
            .replace('\t', "\\t")
            .replace('\r', "\\r")
    }

    fn unescape(text: &str) -> String {
        let mut result = String::new();
        let mut chars = text.chars();
        while let Some(char) = chars.next() {
            result.push(if char == '\\' {
                match chars.next() {
                    Some('n') => '\n',
                    Some('t') => '\t',
                    Some('r') => '\r',
                    Some(other) => other,
                    None => panic!("escape at end of {text}"),
                }
            } else {
                char
            });
        }
        result
    }

    fn render_typ(ty: &Typ) -> String {
        match &**ty {
            TypNode::Type { name, args, .. } if &**name == "fun" => {
                format!("({} => {})", render_typ(&args[0]), render_typ(&args[1]))
            }
            TypNode::Type { name, args, .. } if args.is_empty() => name.to_string(),
            TypNode::Type { name, args, .. } => format!(
                "{name}({})",
                args.iter().map(render_typ).collect::<Vec<_>>().join(", ")
            ),
            TypNode::TFree { .. } => "?TFree".to_string(),
            TypNode::TVar { .. } => "?TVar".to_string(),
        }
    }

    fn render_ast(ast: &Ast) -> String {
        match ast {
            Ast::Name(name) => name.to_string(),
            Ast::Const(name) => format!("'{name}"),
            Ast::App { fun, arg } => format!("({} {})", render_ast(fun), render_ast(arg)),
            Ast::Abs { name, ty, body } => format!(
                "(%{name}{}. {})",
                ty.as_ref()
                    .map_or(String::new(), |ty| format!("::{}", render_typ(ty))),
                render_ast(body)
            ),
            Ast::Constrain { term, ty } => {
                format!("({} :: {})", render_ast(term), render_typ(ty))
            }
        }
    }

    fn attempt(result: Res<String>) -> String {
        match result {
            Ok(text) => text,
            Err(Error::Isabelle(exception, message)) => format!("{}: {message}", exception.name()),
            Err(error) => panic!("unexpected {error:?}"),
        }
    }

    fn dump_theory(text: &str) -> Res<String> {
        let theory = parse_theory(text)?;
        let mut lines = vec![format!("theory {}", theory.name)];
        for constant in &theory.consts {
            lines.push(format!(
                "const {} :: {} = {}",
                escape(&constant.name),
                escape(&constant.ty),
                attempt(parse_type(&constant.ty).map(|ty| render_typ(&ty)))
            ));
        }
        for element in &theory.elements {
            match element {
                StatementElement::Fixes { names } => {
                    lines.push(format!("fixes {}", names.join(" ")))
                }
                StatementElement::Assumes { name, prop } => {
                    lines.push(format!("assumes {name}: {}", escape(prop)));
                    lines.push(format!(
                        "  = {}",
                        attempt(parse_prop(prop).map(|ast| render_ast(&ast)))
                    ));
                }
            }
        }
        lines.push(format!("shows {}", escape(&theory.shows)));
        lines.push(format!(
            "  = {}",
            attempt(parse_prop(&theory.shows).map(|ast| render_ast(&ast)))
        ));
        lines.push(format!("using assms {}", theory.is_using_assms));
        lines.push(format!(
            "method {}",
            theory
                .method
                .iter()
                .map(|token| {
                    let kind = match token.kind {
                        OuterTokenKind::Word => "word",
                        OuterTokenKind::String => "string",
                        OuterTokenKind::Symbol => "symbol",
                    };
                    format!("{kind}:{}", escape(&token.text))
                })
                .collect::<Vec<_>>()
                .join(" ")
        ));
        Ok(format!("{}\n", lines.join("\n")))
    }

    #[test]
    fn parses_the_fixtures_as_the_typescript_does() {
        for (name, text, expected) in fixtures![
            "AllocatorImplementation_proof-127",
            "AllocatorImplementation_proof-33",
            "AtomicBakeryWithoutSMT-465",
            "AtomicBakeryWithoutSMT-6",
            "FiniteSetTheorems_proofs-453",
            "Level_test-1",
            "NaturalsInduction_proofs-1",
            "Paxos-109",
            "Sets-183",
            "TLAPS-2",
            "constantfcn_test-1",
            "function_except_tuple_soundness_gh201_test-1",
        ] {
            assert_eq!(attempt(dump_theory(text)), expected, "{name}");
        }
    }

    #[test]
    fn parses_the_cases_as_the_typescript_does() {
        let mut cases: Vec<(&str, String, Vec<&str>)> = Vec::new();
        for line in include_str!("../../testdata/isar/cases.txt").lines() {
            match line.split_once('\t') {
                Some((kind @ ("theory" | "prop" | "type"), input)) => {
                    cases.push((kind, unescape(input), Vec::new()));
                }
                _ => cases.last_mut().expect("a case").2.push(line),
            }
        }
        assert!(cases.len() > 100);
        for (kind, input, expected) in cases {
            let actual = attempt(match kind {
                "theory" => dump_theory(&input).map(|dump| dump.trim_end().replace('\n', "\n  ")),
                "prop" => parse_prop(&input).map(|ast| render_ast(&ast)),
                _ => parse_type(&input).map(|ty| render_typ(&ty)),
            });
            assert_eq!(actual, expected.join("\n"), "{kind} {input:?}");
        }
    }

    #[test]
    fn reads_a_character_beyond_the_basic_plane_as_one_symbol() {
        // The TypeScript reads UTF-16 code units, so it makes a symbol of each surrogate.
        let theory = parse_theory(
            "theory T imports Constant begin lemma L: shows \"x\" (is \"PROP ?G\") proof - show \
             \"PROP ?G\" by auto \u{1F600} qed end",
        )
        .unwrap();
        assert_eq!(theory.method[1].kind, OuterTokenKind::Symbol);
        assert_eq!(theory.method[1].text, "\u{1F600}");
    }

    #[test]
    fn reports_a_symbol_without_its_closing_bracket() {
        // The TypeScript starts tokenizing over forever here.
        assert_eq!(
            attempt(parse_prop("a = \\<foo b").map(|ast| render_ast(&ast))),
            "ERROR: Inner lexical error at: \\<foo b"
        );
        assert_eq!(
            attempt(parse_prop("\\<f\u{1F600}").map(|ast| render_ast(&ast))),
            "ERROR: Inner lexical error at: \\<f\u{1F600}"
        );
    }
}

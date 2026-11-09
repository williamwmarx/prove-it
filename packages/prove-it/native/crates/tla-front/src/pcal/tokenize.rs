//! The translator's tokenizer, as `src/pcal/tokenize.ts` ports `pcal.PcalCharReader` and
//! `pcal.Tokenize`.

use std::collections::HashSet;
use std::sync::OnceLock;

use super::ast::{
    BUILTIN, Expr, IDENT, NUMBER, STRING, Token, create_normalized_expr, create_token,
};
use super::{PcalError, bug, error};

/// PcalCharReader: reads the algorithm's characters from a start position to the end of the
/// lines, returning '\n' at the end of each line and '\t' at the end of the input. Columns count
/// code points. The lines come without tabs, as trans.removeTabs replaced them.
pub struct Reader {
    lines: Vec<Vec<char>>,
    has_current: bool,
    pub line: usize,
    pub column: usize,
    pub vcolumn: usize,
}

impl Reader {
    /// The first column is the Java string index of the first line, which the reader then uses as
    /// an index of its code points, as the Java does.
    pub fn new(
        lines: Vec<Vec<char>>,
        first_line: usize,
        first_column: usize,
        vcolumn: usize,
    ) -> Self {
        Reader {
            has_current: first_line < lines.len(),
            lines,
            line: first_line,
            column: first_column,
            vcolumn,
        }
    }

    fn get_next_char(&mut self) -> char {
        if !self.has_current {
            return '\t';
        }
        let current = &self.lines[self.line];
        if current.len() <= self.column {
            self.line += 1;
            self.column = 0;
            self.vcolumn = 0;
            self.has_current = self.line < self.lines.len();
            return '\n';
        }
        let char = current[self.column];
        self.column += 1;
        self.vcolumn += 1;
        char
    }

    fn backspace(&mut self) -> Result<(), PcalError> {
        if self.column > 0 {
            self.column -= 1;
            self.vcolumn = self.vcolumn.saturating_sub(1);
            return Ok(());
        }
        if self.line == 0 {
            return Err(bug(
                "PcalCharReader.backspace trying to move past beginning of reader",
            ));
        }
        self.line -= 1;
        self.has_current = true;
        self.column = self.lines[self.line].len().saturating_sub(1);
        self.vcolumn = self.column;
        Ok(())
    }

    /// PcalCharReader.peek: the rest of the line from the next character that is not white space,
    /// with its '\n', or "\t" at the end of the input.
    pub fn peek(&mut self) -> Result<String, PcalError> {
        loop {
            let next = self.get_next_char();
            if next == '\t' {
                return Ok("\t".to_owned());
            }
            if next != ' ' && next != '\n' {
                break;
            }
        }
        self.backspace()?;
        let mut rest: String = if self.has_current {
            self.lines[self.line].iter().skip(self.column).collect()
        } else {
            String::new()
        };
        rest.push('\n');
        Ok(rest)
    }
}

/// Symbol.LEFT_PAREN and RIGHT_PAREN of PcalBuiltInSymbols' table.
const LEFT_PARENS: [&str; 5] = ["(", "[", "{", "<<", "⟨"];
const RIGHT_PARENS: [&str; 8] = [">>_", "⟩_", "]_", ")", "}", "]", ">>", "⟩"];

const SYMBOLS: [&str; 6] = [
    "_ ASSUME ASSUMPTION AXIOM BOOLEAN CASE CONSTANT CONSTANTS EXCEPT EXTENDS FALSE IF INSTANCE LOCAL MODULE OTHER STRING THEOREM TRUE VARIABLE VARIABLES WITH WF_ SF_",
    "\\A ∀ \\forall \\E ∃ \\exists \\AA \\EE ~ ¬ \\lnot \\neg <> ◇ CHOOSE ENABLED UNCHANGED SUBSET UNION DOMAIN ' ^+ ⁺ ^* ^#",
    "=> ⇒ \\cdot ⋅ <=> ⇔ \\equiv ≡ ~> ↝ -+-> ⇸ \\subseteq ⊆ \\subset ⊂ \\supset ⊃ \\supseteq ⊇ \\ll ≪ \\gg ≫ \\ \\cap \\intersect ∩ \\cup \\union ∪ /\\ ∧ \\/ ∨ \\land \\lor \\X × - + * / ^ | || ‖ & && ++ -- ** // ^^ |- ⊢ |= ⊨ -| ⊣ =| ⫤ <: :> := ≔ ::= ⩴",
    "(+) ⊕ (-) ⊖ \\oplus \\ominus (.) ⊙ \\odot (/) ⊘ \\oslash (\\X) ⊗ \\otimes \\uplus ⊎ \\sqcap ⊓ \\sqcup ⊔ \\div ÷ \\star ⋆ \\o ∘ \\circ \\bigcirc ◯ \\bullet ●",
    "\\in ∈ \\notin ∉ = # /= ≠ < > =< <= ≤ >= ≥ \\prec ≺ \\succ ≻ \\preceq ⪯ \\succeq ⪰ \\sim ∼ \\simeq ≃ \\approx ≈ \\doteq ≐ \\asymp ≍ \\sqsubset ⊏ \\sqsupset ⊐ \\sqsubseteq ⊑ \\sqsupseteq ⊒ \\propto ∝",
    ": -> → |-> ↦ <- ← == ≜ ELSE THEN LET IN [] □ .. ‥ ... … $ $$ ? ?? ⁇ % %% ## @@ !! ‼ \\times \\leq \\geq \\mod \\wr ≀ ≅ ! ; , . -. @",
];

struct BuiltIns {
    symbols: HashSet<String>,
    prefixes: HashSet<String>,
}

/// PcalBuiltInSymbols.buildHashTable, and buildPrefixHashTable: the prefixes of the symbols that
/// are not words.
fn get_built_ins() -> &'static BuiltIns {
    static BUILT_INS: OnceLock<BuiltIns> = OnceLock::new();
    BUILT_INS.get_or_init(|| {
        let symbols: HashSet<String> = LEFT_PARENS
            .into_iter()
            .chain(RIGHT_PARENS)
            .chain(SYMBOLS.iter().flat_map(|group| group.split(' ')))
            .map(str::to_owned)
            .collect();
        let prefixes = symbols
            .iter()
            .filter(|symbol| {
                let mut chars = symbol.chars();
                let first = chars.next().unwrap_or(' ');
                !is_letter(first) && !(first == '\\' && chars.next().is_some_and(is_letter))
            })
            .flat_map(|symbol| {
                let chars: Vec<char> = symbol.chars().collect();
                (1..=chars.len())
                    .map(|length| chars[..length].iter().collect::<String>())
                    .collect::<Vec<_>>()
            })
            .collect();
        BuiltIns { symbols, prefixes }
    })
}

/// tla2tex.Misc.IsLetter, IsDigit and IsSpace, which only accept ASCII.
fn is_letter(char: char) -> bool {
    char.is_ascii_alphabetic() || char == '_'
}

fn is_digit(char: char) -> bool {
    char.is_ascii_digit()
}

fn is_space(char: char) -> bool {
    char == ' ' || char == '\u{c}' || char == '\r'
}

/// PcalBuiltInSymbols.buildStringCharTable.
fn is_string_char(char: char) -> bool {
    char.is_ascii_alphanumeric() || " ~!@#$%^&*()_-+={}[]|:;<,>.?/`'".contains(char)
}

/// Tokenize.IsDelimiter: the words and symbols that end an expression of the algorithm.
const DELIMITERS: &[&str] = &[
    ";",
    "do",
    "then",
    ":=",
    "≔",
    "begin",
    "variable",
    "variables",
    "||",
    "‖",
    "end",
    "else",
    "elsif",
    "if",
    "either",
    "or",
    "while",
    "with",
    "call",
    "return",
    "goto",
    "print",
    "assert",
    "skip",
    "procedure",
    "define",
    "process",
    "fair",
];

fn is_delimiter(token: &str) -> bool {
    DELIMITERS.contains(&token)
}

/// tla2tex.Token's types beyond those TLAToken shares.
const DASHES: u8 = 6;
const END_MODULE: u8 = 7;

/// Tokenize's static Delimiter fields, the delimiter its last call ended at, and its comment
/// depth, which an error in a comment leaves set for the next call.
#[derive(Debug, Default)]
pub struct TokenizerState {
    pub delimiter: String,
    pub delimiter_line: i64,
    pub delimiter_col: i64,
    pub comment_depth: i64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum State {
    Start,
    Id,
    NumOrId,
    Bs,
    NumOrBi,
    Num,
    BsBuiltIn,
    BuiltIn,
    Dash1,
    Dash2,
    Dash3,
    Dashes,
    Eq1,
    Eq2,
    Eq3,
    Eqs,
    LeftParen,
    String,
    EscString,
    LineComment,
    LineComParen,
    LineComStar,
    Comment,
    OrComment,
    CommentStar,
    OrCommentStar,
    CommentParen,
    OrCommentParen,
    Done,
}

struct Scan<'a> {
    state_: &'a mut TokenizerState,
    reader: &'a mut Reader,
    is_expr: bool,
    is_in_define_block: bool,
    lines: Vec<Vec<Token>>,
    line: Vec<Token>,
    token: String,
    state: State,
    column: i64,
    next_column: i64,
    next_char: char,
    paren_depth: i64,
    is_in_quantifier: bool,
    is_expr_end: bool,
    previous_token: String,
}

impl Scan<'_> {
    fn skip_next_char(&mut self) {
        self.next_column = self.reader.vcolumn as i64;
        self.next_char = self.reader.get_next_char();
    }

    fn add_next_char(&mut self) {
        self.token.push(self.next_char);
        self.skip_next_char();
    }

    fn goto_start(&mut self) {
        self.state = State::Start;
        self.column = self.next_column;
    }

    fn start_new_line(&mut self) {
        self.lines.push(std::mem::take(&mut self.line));
        self.column = 0;
    }

    fn tokenizing_error(&self, message: &str) -> PcalError {
        error(&format!(
            "{message} `{}' found at\n    line {}, column {}",
            self.token,
            self.reader.line + 1,
            self.column + 1
        ))
    }

    fn end_expression(&mut self) {
        self.is_expr_end = true;
        self.state_.delimiter = self.token.clone();
        self.state_.delimiter_col = self.column;
        self.state_.delimiter_line = self.reader.line as i64 - i64::from(self.next_char == '\n');
    }

    /// Tokenize.TokenOut.
    fn token_out(&mut self, kind: u8) -> Result<(), PcalError> {
        if !self.is_expr {
            self.end_expression();
            self.token.clear();
            return Ok(());
        }
        if kind > IDENT {
            return Err(self.tokenizing_error("Illegal token in an expression"));
        }
        let token = self.token.as_str();
        let is_delimiter = kind != STRING
            && ((is_delimiter(token)
                && !(kind == IDENT && [".", "[", ","].contains(&self.previous_token.as_str())))
                || (((token == "," && !self.is_in_quantifier && !self.is_in_define_block)
                    || token == ")"
                    || token == "}")
                    && self.paren_depth == 0));
        if is_delimiter {
            if self.paren_depth != 0 {
                return Err(self
                    .tokenizing_error("Expression with an unmatched (, [, {, or << followed by"));
            }
            if self.is_in_quantifier {
                return Err(self.tokenizing_error(
                    "Expression with \\A or \\E but no following `:` followed by",
                ));
            }
            self.end_expression();
            if !self.line.is_empty() {
                self.start_new_line();
            }
            return Ok(());
        }
        if kind == BUILTIN && LEFT_PARENS.contains(&token) {
            self.paren_depth += 1;
        }
        if kind == BUILTIN && RIGHT_PARENS.contains(&token) {
            self.paren_depth -= 1;
            if self.paren_depth < 0 {
                return Err(self.tokenizing_error("Extra (unmatching)"));
            }
        }
        let token = self.token.clone();
        self.previous_token = if kind == STRING {
            " ".to_owned()
        } else {
            token.clone()
        };
        if ["\\A", "∀", "\\E", "∃"].contains(&token.as_str()) && self.paren_depth == 0 {
            self.is_in_quantifier = true;
        }
        if self.is_in_quantifier && token == ":" && self.paren_depth == 0 {
            self.is_in_quantifier = false;
        }
        if !token.is_empty() || kind == STRING {
            self.line.push(create_token(&token, self.column, kind));
        }
        self.token.clear();
        Ok(())
    }

    fn output_token(&mut self, kind: u8) -> Result<(), PcalError> {
        self.token_out(kind)?;
        self.goto_start();
        Ok(())
    }

    fn add_and_goto(&mut self, state: State) {
        self.add_next_char();
        self.state = state;
    }

    fn skip_and_goto(&mut self, state: State) {
        self.skip_next_char();
        self.state = state;
    }

    /// One transition of the state machine on the next character.
    fn step(&mut self, next: char) -> Result<(), PcalError> {
        let built_ins = get_built_ins();
        match self.state {
            State::Start => {
                if is_space(next) {
                    self.skip_next_char();
                    self.goto_start();
                } else if is_letter(next) {
                    self.add_and_goto(State::Id);
                } else if next == 'ℕ' || next == 'ℤ' || next == 'ℝ' {
                    self.add_next_char();
                    self.output_token(IDENT)?;
                } else if is_digit(next) {
                    self.add_and_goto(State::NumOrId);
                } else if next == '\\' {
                    self.add_and_goto(State::Bs);
                } else if next == '-' {
                    self.add_and_goto(State::Dash1);
                } else if next == '=' {
                    self.add_and_goto(State::Eq1);
                } else if next == '(' {
                    self.skip_and_goto(State::LeftParen);
                } else if next == '"' {
                    self.skip_and_goto(State::String);
                } else if next == '\n' {
                    self.skip_next_char();
                    self.start_new_line();
                    self.goto_start();
                } else if built_ins
                    .prefixes
                    .contains(next.encode_utf8(&mut [0; 4]) as &str)
                {
                    self.add_and_goto(State::BuiltIn);
                } else if next == '\t' {
                    self.state = State::Done;
                } else {
                    self.add_next_char();
                    return Err(self.tokenizing_error("Illegal lexeme"));
                }
            }
            State::Id => {
                if self.token == "WF_" || self.token == "SF_" {
                    self.output_token(BUILTIN)?;
                } else if is_letter(next) || is_digit(next) {
                    self.add_next_char();
                } else {
                    let kind = if built_ins.symbols.contains(&self.token) {
                        BUILTIN
                    } else {
                        IDENT
                    };
                    self.output_token(kind)?;
                }
            }
            State::NumOrId => {
                if is_digit(next) {
                    self.add_next_char();
                } else if is_letter(next) {
                    self.add_and_goto(State::Id);
                } else {
                    self.output_token(NUMBER)?;
                }
            }
            State::Bs => {
                if "bBoOhH".contains(next) {
                    self.add_and_goto(State::NumOrBi);
                } else if is_letter(next) {
                    self.state = State::BsBuiltIn;
                } else if next == '*' {
                    self.skip_next_char();
                    self.token.clear();
                    self.state = State::LineComment;
                } else {
                    self.state = State::BuiltIn;
                }
            }
            State::NumOrBi => {
                self.state = if is_digit(next) {
                    State::Num
                } else {
                    State::BsBuiltIn
                };
            }
            State::Num => {
                if is_digit(next) {
                    self.add_next_char();
                } else if !is_letter(next) {
                    self.output_token(NUMBER)?;
                } else {
                    self.add_next_char();
                    if self.token.starts_with('\\') {
                        return Err(self.tokenizing_error("Illegal lexeme"));
                    }
                    self.state = State::Id;
                }
            }
            State::BsBuiltIn => {
                if is_letter(next) && next != '_' {
                    self.add_next_char();
                } else if built_ins.symbols.contains(&self.token) {
                    self.output_token(BUILTIN)?;
                } else {
                    return Err(self.tokenizing_error("Illegal lexeme "));
                }
            }
            State::BuiltIn => {
                let mut extended = self.token.clone();
                extended.push(next);
                if built_ins.prefixes.contains(&extended) {
                    self.add_next_char();
                    return Ok(());
                }
                // A prefix that is no symbol backs up to its longest symbol.
                if !built_ins.symbols.contains(&self.token) {
                    self.reader.backspace()?;
                    while !built_ins.symbols.contains(&self.token) {
                        self.reader.backspace()?;
                        if self.token.is_empty() {
                            return Err(self.tokenizing_error("Illegal lexeme"));
                        }
                        self.token.pop();
                    }
                    self.skip_next_char();
                }
                self.output_token(BUILTIN)?;
            }
            State::Dash1 | State::Dash2 => {
                if next == '-' {
                    let state = if self.state == State::Dash1 {
                        State::Dash2
                    } else {
                        State::Dash3
                    };
                    self.add_and_goto(state);
                } else {
                    self.state = State::BuiltIn;
                }
            }
            State::Dash3 => {
                if next != '-' {
                    return Err(self.tokenizing_error("Illegal lexeme"));
                }
                self.add_and_goto(State::Dashes);
            }
            State::Dashes => {
                if next == '-' {
                    self.add_next_char();
                } else {
                    self.output_token(DASHES)?;
                }
            }
            State::Eq1 | State::Eq2 => {
                if next == '=' {
                    let state = if self.state == State::Eq1 {
                        State::Eq2
                    } else {
                        State::Eq3
                    };
                    self.add_and_goto(state);
                } else {
                    self.state = State::BuiltIn;
                }
            }
            State::Eq3 => {
                if next != '=' {
                    return Err(self.tokenizing_error("Illegal lexeme"));
                }
                self.add_and_goto(State::Eqs);
            }
            State::Eqs => {
                if next == '=' {
                    self.add_next_char();
                } else {
                    self.output_token(END_MODULE)?;
                }
            }
            State::LeftParen => {
                if next == '*' {
                    self.state_.comment_depth = 1;
                    self.skip_and_goto(State::Comment);
                } else {
                    self.token = "(".to_owned();
                    self.state = State::BuiltIn;
                }
            }
            State::String => {
                if next == '\\' {
                    self.add_and_goto(State::EscString);
                } else if next == '"' {
                    self.skip_next_char();
                    self.output_token(STRING)?;
                } else {
                    self.add_next_char();
                    if !is_string_char(next) {
                        return Err(self.tokenizing_error("Illegal character in string"));
                    }
                }
            }
            State::EscString => {
                self.add_next_char();
                if !"\"\\tnfr".contains(next) {
                    return Err(self.tokenizing_error("Illegal character following \\ in string"));
                }
                self.state = State::String;
            }
            State::LineComment => {
                if next == '(' {
                    self.skip_and_goto(State::LineComParen);
                } else if next == '*' && self.state_.comment_depth > 0 {
                    self.skip_and_goto(State::LineComStar);
                } else if next == '\n' || next == '\t' {
                    self.token.clear();
                    self.state_.comment_depth = 0;
                    self.goto_start();
                } else if self.state_.comment_depth == 0 {
                    self.add_next_char();
                } else {
                    self.skip_next_char();
                }
            }
            State::LineComParen => {
                if next == '*' {
                    self.state_.comment_depth += 1;
                    self.skip_and_goto(State::LineComment);
                } else {
                    if self.state_.comment_depth == 0 {
                        self.token.push('(');
                    }
                    self.state = State::LineComment;
                }
            }
            State::LineComStar => {
                if next == ')' {
                    self.state_.comment_depth -= 1;
                    if self.state_.comment_depth < 0 {
                        return Err(bug("Failure of assertion: case LINE_COM_STAR"));
                    }
                    self.skip_and_goto(State::LineComment);
                } else {
                    if self.state_.comment_depth == 0 {
                        self.token.push('*');
                    }
                    self.state = State::LineComment;
                }
            }
            // A comment that continues past its first line is an "or comment".
            State::Comment | State::OrComment => {
                let is_first_line = self.state == State::Comment;
                if next == '*' {
                    self.skip_and_goto(if is_first_line {
                        State::CommentStar
                    } else {
                        State::OrCommentStar
                    });
                } else if next == '(' {
                    self.skip_and_goto(if is_first_line {
                        State::CommentParen
                    } else {
                        State::OrCommentParen
                    });
                } else if next == '\n' {
                    self.token.clear();
                    self.skip_next_char();
                    self.start_new_line();
                    self.state = State::OrComment;
                } else if next == '\t' {
                    return Err(error(if is_first_line {
                        "Input ended in the middle of a comment"
                    } else {
                        "Input ended in the middle of a multi-line comment"
                    }));
                } else if self.state_.comment_depth == 1 {
                    self.add_next_char();
                } else {
                    self.skip_next_char();
                }
            }
            State::CommentStar | State::OrCommentStar => {
                let comment_state = if self.state == State::CommentStar {
                    State::Comment
                } else {
                    State::OrComment
                };
                if next != ')' {
                    if self.state_.comment_depth == 1 {
                        self.token.push('*');
                    }
                    self.state = comment_state;
                    return Ok(());
                }
                self.skip_next_char();
                self.state_.comment_depth -= 1;
                if comment_state == State::OrComment && self.state_.comment_depth < 0 {
                    return Err(bug("Assertion failure"));
                }
                if self.state_.comment_depth != 0 {
                    self.state = comment_state;
                    return Ok(());
                }
                self.token.clear();
                self.goto_start();
            }
            State::CommentParen | State::OrCommentParen => {
                let comment_state = if self.state == State::CommentParen {
                    State::Comment
                } else {
                    State::OrComment
                };
                if next == '*' {
                    self.state_.comment_depth += 1;
                    self.skip_and_goto(comment_state);
                } else {
                    if self.state_.comment_depth == 1 {
                        self.token.push('(');
                    }
                    self.state = comment_state;
                }
            }
            State::Done => {}
        }
        Ok(())
    }
}

/// Tokenize.InnerTokenize in TLA mode: reads an expression up to the delimiter that ends it when
/// is_expr, and otherwise a single token of the algorithm, which becomes state.delimiter. A define
/// block's commas at the top level don't end it.
fn tokenize(
    state: &mut TokenizerState,
    reader: &mut Reader,
    is_expr: bool,
    is_in_define_block: bool,
) -> Result<Expr, PcalError> {
    let column = reader.vcolumn as i64;
    let next_char = reader.get_next_char();
    let mut scan = Scan {
        state_: state,
        reader,
        is_expr,
        is_in_define_block,
        lines: Vec::new(),
        line: Vec::new(),
        token: String::new(),
        state: State::Start,
        column,
        next_column: column,
        next_char,
        paren_depth: 0,
        is_in_quantifier: false,
        is_expr_end: false,
        previous_token: " ".to_owned(),
    };
    while scan.state != State::Done && !scan.is_expr_end {
        scan.step(scan.next_char)?;
    }
    if scan.next_char != '\n' {
        scan.reader.backspace()?;
    }
    Ok(create_normalized_expr(scan.lines))
}

/// Tokenize.TokenizeExpr and TokenizeDefineBlock.
pub fn tokenize_expr(
    state: &mut TokenizerState,
    reader: &mut Reader,
    is_in_define_block: bool,
) -> Result<Expr, PcalError> {
    tokenize(state, reader, true, is_in_define_block)
}

/// Tokenize.GetAlgorithmToken.
pub fn get_algorithm_token(
    state: &mut TokenizerState,
    reader: &mut Reader,
) -> Result<String, PcalError> {
    tokenize(state, reader, false, false)?;
    Ok(state.delimiter.clone())
}

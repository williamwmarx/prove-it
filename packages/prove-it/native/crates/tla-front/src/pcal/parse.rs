//! The translator's parser, as `src/pcal/parse.ts` ports `pcal.ParseAlgorithm`.

use std::collections::HashSet;

use super::ast::{
    Algorithm, AlgorithmBody, Clause, Coord, Expr, IDENT, Macro, Position, Procedure, Process,
    SingleAssign, StmtKind, StmtRef, VarDecl, clone_expr, create_expr, create_normalized_expr,
    create_stmt, create_token, get_element, get_labeled_stmts, get_substituted_expr, get_token_at,
    is_one_token_expr, normalize_expr, prepend_expr, step_coord,
};
use super::tokenize::{Reader, get_algorithm_token, tokenize_expr};
use super::{PcalError, PcalSession, bug, error, error_at};

pub struct ParseResult {
    pub ast: Algorithm,
    pub omit_pc: bool,
    pub has_default_initialization: bool,
}

/// ParseAlgorithm's static fields that Init resets for each algorithm.
struct Parser<'a> {
    session: &'a mut PcalSession,
    reader: Reader,
    lookahead_size: usize,
    added_labels: Vec<String>,
    added_labels_locs: Vec<String>,
    next_label_num: i64,
    all_labels: HashSet<String>,
    has_label: bool,
    has_default_initialization: bool,
    current_procedure: Option<String>,
    procedures: Vec<Procedure>,
    c_syntax: bool,
    plus_labels: Vec<String>,
    minus_labels: Vec<String>,
    procedures_called: Vec<String>,
    goto_used: bool,
    goto_done_used: bool,
    omit_pc: bool,
}

/// PcalParams.DefaultVarInit: the value of a variable declared without one.
fn create_default_var_init() -> Expr {
    create_normalized_expr(vec![vec![create_token("defaultInitValue", 0, 0)]])
}

/// ParseAlgorithm.Union.
fn get_union(first: &[String], second: &[String]) -> Vec<String> {
    let mut result = first.to_vec();
    for (index, name) in second.iter().enumerate() {
        if !first.contains(name) && second.iter().position(|other| other == name) == Some(index) {
            result.push(name.clone());
        }
    }
    result
}

/// ParseAlgorithm.HasEmptyIntersection.
fn is_disjoint(first: &[String], second: &[String]) -> bool {
    !second.iter().any(|name| first.contains(name))
}

fn is_kind(stmt: &StmtRef, name: &str) -> bool {
    stmt.borrow().kind.name() == name
}

fn get_pos(stmt: &StmtRef) -> Position {
    stmt.borrow().pos
}

/// The statements of a labeled statement, taken out to be changed and put back.
fn take_labeled(stmt: &StmtRef) -> Vec<StmtRef> {
    match &mut stmt.borrow_mut().kind {
        StmtKind::LabeledStmt { stmts, .. } => std::mem::take(stmts),
        _ => Vec::new(),
    }
}

fn put_labeled(stmt: &StmtRef, new_stmts: Vec<StmtRef>) {
    if let StmtKind::LabeledStmt { stmts, .. } = &mut stmt.borrow_mut().kind {
        *stmts = new_stmts;
    }
}

fn get_first_label(stmts: &[StmtRef]) -> Option<usize> {
    stmts.iter().position(|stmt| !stmt.borrow().lbl.is_empty())
}

impl Parser<'_> {
    /// ParseAlgorithm.ParsingError.
    fn parsing_error(&self, message: &str) -> PcalError {
        let last = &self.session.last_token;
        error(&format!(
            "{message}\n    line {}, column {}",
            last.line, last.column
        ))
    }

    fn get_alg_token(&mut self) -> Result<String, PcalError> {
        if self.lookahead_size == 0 {
            self.reader.peek()?;
            self.session.last_token.column = self.reader.vcolumn as i64 + 1;
            self.session.last_token.line = self.reader.line as i64 + 1;
            let text = get_algorithm_token(&mut self.session.tokenizer, &mut self.reader)?;
            self.session.last_token.text = text.clone();
            return Ok(text);
        }
        let lookahead = &mut self.session.lookahead;
        self.session.last_token.column = lookahead.columns[0] + 1;
        self.session.last_token.line = lookahead.lines[0] + 1;
        let result = lookahead.tokens[0].clone();
        for index in 1..self.lookahead_size {
            lookahead.tokens[index - 1] = lookahead.tokens[index].clone();
            lookahead.columns[index - 1] = lookahead.columns[index];
            lookahead.lines[index - 1] = lookahead.lines[index];
        }
        self.lookahead_size -= 1;
        self.session.last_token.text = result.clone();
        Ok(result)
    }

    fn peek_at_alg_token(&mut self, token_number: usize) -> Result<String, PcalError> {
        while self.lookahead_size < token_number {
            let size = self.lookahead_size;
            if self.reader.peek()? == "\t" {
                let lookahead = &self.session.lookahead;
                return Err(error(&format!(
                    "Premature end of file, perhaps because of unclosed comment, near\n    line {}, column {}",
                    lookahead.lines[size] + 1,
                    lookahead.columns[size] + 1
                )));
            }
            self.session.lookahead.columns[size] = self.reader.vcolumn as i64;
            self.session.lookahead.lines[size] = self.reader.line as i64;
            self.session.lookahead.tokens[size] =
                get_algorithm_token(&mut self.session.tokenizer, &mut self.reader)?;
            self.lookahead_size += 1;
        }
        Ok(self.session.lookahead.tokens[token_number - 1].clone())
    }

    fn peek_is(&mut self, token: &str) -> Result<bool, PcalError> {
        Ok(self.peek_at_alg_token(1)? == token)
    }

    /// ParseAlgorithm.PeekPastAlgToken: the rest of the line after the next token_number tokens.
    fn peek_past_alg_token(&mut self, token_number: usize) -> Result<String, PcalError> {
        if token_number < self.lookahead_size {
            return Err(bug(
                "ParseAlgorithm.PeekPastAlgToken called to peek after a token\n    it has already peeked at",
            ));
        }
        while token_number > self.lookahead_size {
            self.session.lookahead.tokens[self.lookahead_size] =
                get_algorithm_token(&mut self.session.tokenizer, &mut self.reader)?;
            self.lookahead_size += 1;
        }
        self.reader.peek()
    }

    /// ParseAlgorithm.getExprInternal: an expression's delimiter becomes the next token.
    fn get_expr(&mut self, is_define_block: bool) -> Result<Expr, PcalError> {
        if self.lookahead_size != 0 {
            return Err(bug("ParseAlgorithm: GetExpr called after lookahead"));
        }
        let result = tokenize_expr(
            &mut self.session.tokenizer,
            &mut self.reader,
            is_define_block,
        )?;
        let tokenizer = &self.session.tokenizer;
        self.session.lookahead.tokens[0] = tokenizer.delimiter.clone();
        self.session.lookahead.columns[0] = tokenizer.delimiter_col;
        self.session.lookahead.lines[0] = tokenizer.delimiter_line;
        self.lookahead_size = 1;
        Ok(result)
    }

    /// ParseAlgorithm.GobbleThis: a missing ";" is fine before a token that can't start a
    /// statement.
    fn gobble_this_or(&mut self, expected: &str, alternate: Option<&str>) -> Result<(), PcalError> {
        if expected == ";" {
            let next = self.peek_at_alg_token(1)?;
            let endings = "end begin else elsif or do macro procedure process fair define } {";
            if endings.split(' ').any(|ending| ending == next) {
                return Ok(());
            }
            let statements = "if either while with call return goto print assert skip";
            if statements.split(' ').any(|statement| statement == next) {
                let lookahead = &self.session.lookahead;
                return Err(error(&format!(
                    "Missing `;' before line {}, column {}",
                    lookahead.lines[0] + 1,
                    lookahead.columns[0] + 1
                )));
            }
        }
        let token = self.get_alg_token()?;
        if token != expected && Some(token.as_str()) != alternate {
            return Err(
                self.parsing_error(&format!("Expected \"{expected}\" but found \"{token}\""))
            );
        }
        Ok(())
    }

    fn gobble_this(&mut self, expected: &str) -> Result<(), PcalError> {
        self.gobble_this_or(expected, None)
    }

    fn must_gobble_this(&mut self, expected: &str) -> Result<(), PcalError> {
        let token = self.get_alg_token()?;
        if token != expected {
            return Err(
                self.parsing_error(&format!("Expected \"{expected}\" but found \"{token}\""))
            );
        }
        Ok(())
    }

    fn gobble_equal_or_if(&mut self) -> Result<bool, PcalError> {
        let token = self.get_alg_token()?;
        match token.as_str() {
            "=" => Ok(true),
            "\\in" | "∈" => Ok(false),
            _ => Err(self.parsing_error(&format!(
                "Expected \"=\" or \"\\in\"  but found \"{token}\""
            ))),
        }
    }

    fn gobble_comma_or_semicolon(&mut self) -> Result<(), PcalError> {
        let expected = if self.peek_is(",")? { "," } else { ";" };
        self.gobble_this(expected)
    }

    fn gobble_begin_or_left_brace(&mut self) -> Result<(), PcalError> {
        self.gobble_this(if self.c_syntax { "{" } else { "begin" })
    }

    fn gobble_end_or_right_brace(&mut self, name: &str) -> Result<(), PcalError> {
        if self.c_syntax {
            return self.gobble_this("}");
        }
        self.gobble_this("end")?;
        self.gobble_this(name)
    }

    fn gobble_variables(&mut self) -> Result<(), PcalError> {
        if self.peek_is("variables")? {
            self.must_gobble_this("variables")
        } else {
            self.gobble_this("variable")
        }
    }

    fn get_last_position(&self) -> Position {
        Position::at(self.session.last_token.line, self.session.last_token.column)
    }

    fn get_var_decl(&mut self) -> Result<VarDecl, PcalError> {
        let var = self.get_alg_token()?;
        let mut decl = VarDecl {
            pos: self.get_last_position(),
            var,
            is_eq: true,
            val: create_default_var_init(),
        };
        let next = self.peek_at_alg_token(1)?;
        if !["=", "\\in", "∈"].contains(&next.as_str()) {
            self.has_default_initialization = true;
            return Ok(decl);
        }
        decl.is_eq = self.gobble_equal_or_if()?;
        decl.val = self.get_expr(false)?;
        // ParseAlgorithm.GetVarDecl takes the end of the value's origin, which an empty value
        // lacks, before checking for one.
        if decl.val.tokens.is_empty() {
            return Err(super::runtime("NullPointerException".to_owned()));
        }
        Ok(decl)
    }

    fn get_var_decls(&mut self) -> Result<Vec<VarDecl>, PcalError> {
        self.gobble_variables()?;
        let mut result = Vec::new();
        let ends = [
            "begin",
            "{",
            "procedure",
            "process",
            "fair",
            "define",
            "macro",
        ];
        while !ends.contains(&self.peek_at_alg_token(1)?.as_str()) {
            result.push(self.get_var_decl()?);
            self.gobble_comma_or_semicolon()?;
        }
        Ok(result)
    }

    fn get_pvar_decl(&mut self) -> Result<VarDecl, PcalError> {
        let var = self.get_alg_token()?;
        let mut decl = VarDecl {
            pos: self.get_last_position(),
            var,
            is_eq: true,
            val: create_default_var_init(),
        };
        if !self.peek_is("=")? {
            self.has_default_initialization = true;
            return Ok(decl);
        }
        self.gobble_this("=")?;
        decl.val = self.get_expr(false)?;
        if decl.val.tokens.is_empty() {
            return Err(super::runtime("NullPointerException".to_owned()));
        }
        Ok(decl)
    }

    fn get_pvar_decls(&mut self) -> Result<Vec<VarDecl>, PcalError> {
        self.gobble_variables()?;
        let mut result = Vec::new();
        while !(self.peek_is("begin")? || self.peek_is("{")?) {
            result.push(self.get_pvar_decl()?);
            self.gobble_comma_or_semicolon()?;
        }
        Ok(result)
    }

    /// ParseAlgorithm.IsLabelNext: an identifier followed by ":" but not ":=".
    fn is_label_next(&mut self) -> Result<bool, PcalError> {
        let keywords =
            "while if assert print else elsif either or end with when await skip call return goto";
        let next = self.peek_at_alg_token(1)?;
        if keywords.split(' ').any(|keyword| keyword == next) {
            return Ok(false);
        }
        let rest = self.reader.peek()?;
        let mut chars = rest.chars();
        Ok(chars.next() == Some(':') && chars.next() != Some('='))
    }

    fn get_label(&mut self) -> Result<String, PcalError> {
        if !self.is_label_next()? {
            return Ok(String::new());
        }
        let label = self.get_alg_token()?;
        if self.session.is_in_macro {
            return Err(self.parsing_error("A label may not appear in a macro."));
        }
        if label == "Done" {
            return Err(self.parsing_error("Cannot use `Done' as a label."));
        }
        if label == "Error" {
            return Err(self.parsing_error("Cannot use `Error' as a label."));
        }
        self.gobble_this(":")?;
        self.has_label = true;
        self.all_labels.insert(label.clone());
        let modifier = self.peek_at_alg_token(1)?;
        if modifier != "+" && modifier != "-" {
            return Ok(label);
        }
        self.gobble_this(&modifier)?;
        if modifier == "+" {
            self.plus_labels.push(label.clone());
        } else {
            self.minus_labels.push(label.clone());
        }
        self.omit_pc = false;
        Ok(label)
    }

    fn get_stmt_seq(&mut self) -> Result<Vec<StmtRef>, PcalError> {
        let mut result = Vec::new();
        loop {
            let token = self.peek_at_alg_token(1)?;
            let is_end = if self.c_syntax {
                token == "}"
            } else {
                ["end", "else", "elsif", "or"].contains(&token.as_str())
            };
            if is_end {
                break;
            }
            result.extend(self.get_c_stmt()?);
        }
        if self.c_syntax && result.is_empty() {
            return Err(self.parsing_error("Empty statement list"));
        }
        Ok(result)
    }

    fn get_c_stmt_seq(&mut self, label: String) -> Result<Vec<StmtRef>, PcalError> {
        self.must_gobble_this("{")?;
        let result = self.get_stmt_seq()?;
        self.gobble_this("}")?;
        self.gobble_this(";")?;
        if !label.is_empty() {
            let mut first = result[0].borrow_mut();
            if !first.lbl.is_empty() {
                return Err(error_at("Duplicate labeling of statement", first.pos));
            }
            first.lbl = label;
        }
        Ok(result)
    }

    fn get_c_stmt(&mut self) -> Result<Vec<StmtRef>, PcalError> {
        let label = self.get_label()?;
        if self.c_syntax && self.peek_is("{")? {
            return self.get_c_stmt_seq(label);
        }
        let stmt = self.get_stmt()?;
        stmt.borrow_mut().lbl = label;
        Ok(vec![stmt])
    }

    fn get_stmt(&mut self) -> Result<StmtRef, PcalError> {
        let next = self.peek_at_alg_token(1)?;
        match next.as_str() {
            "if" => return self.get_if(0),
            "either" => return self.get_either(),
            "with" => return self.get_with(0),
            "when" | "await" => {
                self.must_gobble_this(&next)?;
                let pos = self.get_last_position();
                let exp = self.get_expr(false)?;
                // ParseAlgorithm.GetWhen takes the end of the expression's origin, which an empty
                // expression lacks, before checking for one.
                if exp.tokens.is_empty() {
                    return Err(super::runtime("NullPointerException".to_owned()));
                }
                self.gobble_this(";")?;
                return Ok(create_stmt(pos, StmtKind::When(exp)));
            }
            "print" | "assert" => {
                self.must_gobble_this(&next)?;
                let pos = self.get_last_position();
                let exp = self.get_expr(false)?;
                if exp.tokens.is_empty() {
                    return Err(
                        self.parsing_error(&format!("Empty expression in {next} statement at "))
                    );
                }
                self.gobble_this(";")?;
                let kind = if next == "print" {
                    StmtKind::PrintS(exp)
                } else {
                    StmtKind::Assert(exp)
                };
                return Ok(create_stmt(pos, kind));
            }
            "skip" => {
                self.must_gobble_this("skip")?;
                let skip = create_stmt(self.get_last_position(), StmtKind::Skip);
                self.gobble_this(";")?;
                return Ok(skip);
            }
            "call" => return self.get_call_or_call_return_or_call_goto(),
            "return" => {
                self.must_gobble_this("return")?;
                let result = create_stmt(
                    self.get_last_position(),
                    StmtKind::Return {
                        from: self.current_procedure.clone(),
                    },
                );
                self.gobble_this(";")?;
                return Ok(result);
            }
            "goto" => {
                self.must_gobble_this("goto")?;
                let pos = self.get_last_position();
                let to = self.get_alg_token()?;
                self.goto_used = true;
                if to == "Done" || to == "\"Done\"" {
                    self.goto_done_used = true;
                }
                self.gobble_this(";")?;
                return Ok(create_stmt(pos, StmtKind::Goto { to }));
            }
            "while" => return self.get_while(),
            _ => {}
        }
        if self.peek_past_alg_token(1)?.starts_with('(') {
            return self.get_macro_call();
        }
        self.get_assign()
    }

    fn get_while(&mut self) -> Result<StmtRef, PcalError> {
        self.must_gobble_this("while")?;
        let pos = self.get_last_position();
        if self.c_syntax {
            self.gobble_this("(")?;
        }
        let test = self.get_expr(false)?;
        if self.c_syntax {
            self.gobble_this(")")?;
        }
        if test.tokens.is_empty() {
            return Err(self.parsing_error("Empty while test at "));
        }
        if !self.c_syntax {
            self.gobble_this("do")?;
        }
        let unlab_do = if self.c_syntax {
            self.get_c_stmt()?
        } else {
            self.get_stmt_seq()?
        };
        if !self.c_syntax {
            self.gobble_this("end")?;
            self.gobble_this("while")?;
            self.gobble_this(";")?;
        }
        if unlab_do.is_empty() {
            return Err(self.parsing_error("Missing body of while statement at"));
        }
        Ok(create_stmt(
            pos,
            StmtKind::While {
                test,
                unlab_do,
                lab_do: Vec::new(),
            },
        ))
    }

    fn get_if(&mut self, depth: usize) -> Result<StmtRef, PcalError> {
        self.must_gobble_this(if depth == 0 { "if" } else { "elsif" })?;
        let pos = self.get_last_position();
        if self.c_syntax {
            self.gobble_this("(")?;
        }
        let test = self.get_expr(false)?;
        if self.c_syntax {
            self.gobble_this(")")?;
        }
        if test.tokens.is_empty() {
            return Err(self.parsing_error("Empty if test at "));
        }
        if !self.c_syntax {
            self.gobble_this("then")?;
        }
        let unlab_then = if self.c_syntax {
            self.get_c_stmt()?
        } else {
            self.get_stmt_seq()?
        };
        let next = self.peek_at_alg_token(1)?;
        let mut unlab_else = Vec::new();
        if next == "else" {
            self.must_gobble_this("else")?;
            unlab_else = if self.c_syntax {
                self.get_c_stmt()?
            } else {
                self.get_stmt_seq()?
            };
        }
        if !self.c_syntax && next == "elsif" {
            unlab_else = vec![self.get_if(depth + 1)?];
        }
        if !self.c_syntax && !["else", "elsif", "end"].contains(&next.as_str()) {
            return Err(self.parsing_error("Expecting \"else\", \"elsif\", or \"end\""));
        }
        if !self.c_syntax && depth == 0 {
            self.gobble_this("end")?;
            self.gobble_this("if")?;
            self.gobble_this(";")?;
        }
        // ParseAlgorithm.GetIf takes the origin of the last statement, which an empty then clause
        // with no else clause doesn't have.
        if unlab_else.is_empty() {
            get_element(&unlab_then, unlab_then.len() as i64 - 1)?;
        }
        Ok(create_stmt(
            pos,
            StmtKind::LabelIf {
                test,
                unlab_then,
                lab_then: Vec::new(),
                unlab_else,
                lab_else: Vec::new(),
            },
        ))
    }

    fn get_either(&mut self) -> Result<StmtRef, PcalError> {
        self.must_gobble_this("either")?;
        let pos = self.get_last_position();
        let mut clauses = Vec::new();
        loop {
            let unlab_or = if self.c_syntax {
                self.get_c_stmt()?
            } else {
                self.get_stmt_seq()?
            };
            if unlab_or.is_empty() {
                return Err(error_at("`either' statement with empty `or' clause", pos));
            }
            clauses.push(Clause {
                unlab_or,
                lab_or: Vec::new(),
            });
            if !self.peek_is("or")? {
                break;
            }
            self.must_gobble_this("or")?;
        }
        if !self.c_syntax {
            self.must_gobble_this("end")?;
            self.gobble_this("either")?;
            self.gobble_this(";")?;
        }
        if clauses.len() == 1 {
            return Err(error_at("`either' statement has no `or'", pos));
        }
        Ok(create_stmt(pos, StmtKind::LabelEither { clauses }))
    }

    /// ParseAlgorithm.InnerGetWith: "with x = e, y \in f" nests a with for each variable.
    fn get_with(&mut self, depth: usize) -> Result<StmtRef, PcalError> {
        if depth == 0 {
            self.gobble_this("with")?;
            if self.c_syntax {
                self.gobble_this("(")?;
            }
        }
        let pos = self.get_last_position();
        let var = self.get_alg_token()?;
        let is_eq = self.gobble_equal_or_if()?;
        let exp = self.get_expr(false)?;
        if !self.c_syntax || !self.peek_is(")")? {
            self.gobble_comma_or_semicolon()?;
        }
        if exp.tokens.is_empty() {
            return Err(self.parsing_error("Empty with expression at "));
        }
        let is_block_body = !self.c_syntax && self.peek_is("do")?;
        let is_brace_body = self.c_syntax && self.peek_is(")")?;
        if is_block_body {
            self.gobble_this("do")?;
        }
        if is_brace_body {
            self.must_gobble_this(")")?;
        }
        let body = if is_block_body {
            self.get_stmt_seq()?
        } else if is_brace_body {
            self.get_c_stmt()?
        } else {
            vec![self.get_with(depth + 1)?]
        };
        if is_block_body {
            self.gobble_this("end")?;
            self.gobble_this("with")?;
            self.gobble_this(";")?;
        }
        if body.is_empty() {
            return Err(error_at("Missing body of with statement", pos));
        }
        Ok(create_stmt(
            pos,
            StmtKind::With {
                var,
                is_eq,
                exp,
                body,
            },
        ))
    }

    fn get_lookahead_position(&self) -> Position {
        let lookahead = &self.session.lookahead;
        Position::at(lookahead.lines[0] + 1, lookahead.columns[0] + 1)
    }

    fn get_single_assign(&mut self) -> Result<SingleAssign, PcalError> {
        let pos = self.get_lookahead_position();
        let var = self.get_alg_token()?;
        let sub = self.get_expr(false)?;
        self.gobble_this_or(":=", Some("≔"))?;
        let rhs = self.get_expr(false)?;
        if rhs.tokens.is_empty() {
            return Err(self.parsing_error("Empty right-hand side of assignment at "));
        }
        Ok(SingleAssign { pos, var, sub, rhs })
    }

    fn get_assign(&mut self) -> Result<StmtRef, PcalError> {
        let pos = self.get_lookahead_position();
        let mut ass = vec![self.get_single_assign()?];
        while self.peek_is("||")? || self.peek_is("‖")? {
            self.get_alg_token()?;
            // HACK: ParseAlgorithm.GetAssign replaces the error of an assignment after the first
            // with its own.
            match self.get_single_assign() {
                Ok(assign) => ass.push(assign),
                Err(PcalError::Error { .. }) => {
                    return Err(self.parsing_error("Bad assignment statement at "));
                }
                Err(other) => return Err(other),
            }
        }
        self.gobble_this(";")?;
        Ok(create_stmt(pos, StmtKind::Assign { ass }))
    }

    /// The arguments of a call or macro call, through its ")" and ";".
    fn get_call_args(&mut self) -> Result<Vec<Expr>, PcalError> {
        let mut args = Vec::new();
        if !self.peek_past_alg_token(0)?.starts_with(')') {
            loop {
                let arg = self.get_expr(false)?;
                let is_empty = arg.tokens.is_empty();
                args.push(arg);
                if is_empty {
                    return Err(self.parsing_error("Empty argument in call statement at "));
                }
                if self.peek_is(")")? {
                    break;
                }
                self.gobble_this(",")?;
            }
        }
        self.gobble_this(")")?;
        self.gobble_this(";")?;
        Ok(args)
    }

    fn get_call(&mut self) -> Result<(Position, String, Vec<Expr>), PcalError> {
        self.must_gobble_this("call")?;
        let pos = self.get_last_position();
        let to = self.get_alg_token()?;
        self.gobble_this("(")?;
        let args = self.get_call_args()?;
        if !self.procedures_called.contains(&to) {
            self.procedures_called.push(to.clone());
        }
        Ok((pos, to, args))
    }

    fn get_call_or_call_return_or_call_goto(&mut self) -> Result<StmtRef, PcalError> {
        let (pos, to, args) = self.get_call()?;
        if self.peek_is("return")? {
            self.must_gobble_this("return")?;
            self.gobble_this(";")?;
            return Ok(create_stmt(
                pos,
                StmtKind::CallReturn {
                    from: self.current_procedure.clone(),
                    to,
                    args,
                },
            ));
        }
        if !self.peek_is("goto")? {
            return Ok(create_stmt(
                pos,
                StmtKind::Call {
                    return_to: String::new(),
                    to,
                    args,
                },
            ));
        }
        self.must_gobble_this("goto")?;
        let after = self.get_alg_token()?;
        self.goto_used = true;
        if to == "Done" || to == "\"Done\"" {
            self.goto_done_used = true;
        }
        self.gobble_this(";")?;
        Ok(create_stmt(pos, StmtKind::CallGoto { after, to, args }))
    }

    fn get_macro_call(&mut self) -> Result<StmtRef, PcalError> {
        let name = self.get_alg_token()?;
        let pos = self.get_last_position();
        self.must_gobble_this("(")?;
        let args = self.get_call_args()?;
        Ok(create_stmt(pos, StmtKind::MacroCall { name, args }))
    }

    fn get_macro(&mut self, macros: &[Macro]) -> Result<Macro, PcalError> {
        self.session.is_in_macro = true;
        self.must_gobble_this("macro")?;
        let name = self.get_alg_token()?;
        self.gobble_this("(")?;
        let mut params = Vec::new();
        while !self.peek_is(")")? {
            if !params.is_empty() {
                self.gobble_this(",")?;
            }
            params.push(self.get_alg_token()?);
        }
        self.must_gobble_this(")")?;
        self.gobble_begin_or_left_brace()?;
        let mut body = self.get_stmt_seq()?;
        self.gobble_end_or_right_brace("macro")?;
        if self.peek_is(";")? {
            self.get_alg_token()?;
        }
        self.expand_macros_in_stmt_seq(&mut body, macros)?;
        self.session.is_in_macro = false;
        Ok(Macro { name, params, body })
    }

    fn get_procedure(&mut self) -> Result<Procedure, PcalError> {
        self.gobble_this("procedure")?;
        let pos = self.get_last_position();
        let name = self.get_alg_token()?;
        self.current_procedure = Some(name.clone());
        self.plus_labels = Vec::new();
        self.minus_labels = Vec::new();
        self.procedures_called = Vec::new();
        self.gobble_this("(")?;
        let mut params = Vec::new();
        while !self.peek_is(")")? {
            if !params.is_empty() {
                self.gobble_this(",")?;
            }
            params.push(self.get_pvar_decl()?);
        }
        self.must_gobble_this(")")?;
        let decls = if self.peek_is("begin")? || self.peek_is("{")? {
            Vec::new()
        } else {
            self.get_pvar_decls()?
        };
        self.gobble_begin_or_left_brace()?;
        let body = self.get_stmt_seq()?;
        self.gobble_end_or_right_brace("procedure")?;
        if self.peek_is(";")? {
            self.get_alg_token()?;
        }
        self.current_procedure = None;
        Ok(Procedure {
            pos,
            name,
            minus_labels: std::mem::take(&mut self.minus_labels),
            plus_labels: std::mem::take(&mut self.plus_labels),
            procedures_called: std::mem::take(&mut self.procedures_called),
            params,
            decls,
            body,
        })
    }

    fn get_process(&mut self, fairness: usize) -> Result<Process, PcalError> {
        self.gobble_this("process")?;
        let pos = self.get_last_position();
        if self.c_syntax {
            self.gobble_this("(")?;
        }
        let name = self.get_alg_token()?;
        let is_eq = self.gobble_equal_or_if()?;
        let id = self.get_expr(false)?;
        self.plus_labels = Vec::new();
        self.minus_labels = Vec::new();
        self.procedures_called = Vec::new();
        if self.c_syntax {
            self.gobble_this(")")?;
        }
        if id.tokens.is_empty() {
            return Err(self.parsing_error("Empty process id at "));
        }
        let decls = if self.peek_is("begin")? || self.peek_is("{")? {
            Vec::new()
        } else {
            self.get_var_decls()?
        };
        self.gobble_begin_or_left_brace()?;
        let body = self.get_stmt_seq()?;
        self.gobble_end_or_right_brace("process")?;
        if self.peek_is(";")? {
            self.get_alg_token()?;
        }
        Ok(Process {
            pos,
            name,
            fairness,
            minus_labels: std::mem::take(&mut self.minus_labels),
            plus_labels: std::mem::take(&mut self.plus_labels),
            procedures_called: std::mem::take(&mut self.procedures_called),
            is_eq,
            id,
            decls,
            body,
        })
    }

    /// ParseAlgorithm.NeedsLabel: the label root and the next number no label of the algorithm
    /// has.
    fn needs_label(&mut self, stmt: &StmtRef) {
        if !stmt.borrow().lbl.is_empty() {
            return;
        }
        let label = loop {
            let label = format!("{}{}", self.session.params.label_root, self.next_label_num);
            self.next_label_num += 1;
            if !self.all_labels.contains(&label) {
                break label;
            }
        };
        let mut stmt = stmt.borrow_mut();
        stmt.lbl = label.clone();
        self.added_labels.push(label);
        self.added_labels_locs.push(stmt.pos.location());
    }

    /// The variables a return, or a call of the procedure being labeled, assigns: those of every
    /// procedure.
    fn get_procedure_vars(&self) -> Vec<String> {
        self.procedures
            .iter()
            .flat_map(|procedure| procedure.params.iter().chain(&procedure.decls))
            .map(|decl| decl.var.clone())
            .collect()
    }

    /// ParseAlgorithm.InnerAddLabels: labels the statements that must start a step, tracking the
    /// variables assigned since the last label in out_assigned. True when the statement after the
    /// sequence needs a label.
    fn add_labels(
        &mut self,
        stmts: &[StmtRef],
        is_first_labeled: bool,
        is_in_with: bool,
        in_assigned: &[String],
        out_assigned: &mut Vec<String>,
    ) -> Result<bool, PcalError> {
        *out_assigned = in_assigned.to_vec();
        let mut is_next_labeled = is_first_labeled;
        let mut has_label = false;
        for stmt in stmts {
            if !stmt.borrow().lbl.is_empty() {
                has_label = true;
                out_assigned.clear();
                if is_in_with {
                    return Err(error_at("Label in `with' statement", get_pos(stmt)));
                }
            }
            if is_next_labeled {
                if is_in_with {
                    return Err(error_at(
                        "Statement follows `call' or `return' inside a `with' statement.",
                        get_pos(stmt),
                    ));
                }
                self.needs_label(stmt);
                has_label = true;
                out_assigned.clear();
                is_next_labeled = false;
            }
            enum Compound {
                LabelIf(Vec<StmtRef>, Vec<StmtRef>),
                LabelEither(Vec<Vec<StmtRef>>),
                While(Vec<StmtRef>),
                With(Vec<StmtRef>),
                Simple,
            }
            let compound = match &stmt.borrow().kind {
                StmtKind::LabelIf {
                    unlab_then,
                    unlab_else,
                    ..
                } => Compound::LabelIf(unlab_then.clone(), unlab_else.clone()),
                StmtKind::LabelEither { clauses } => Compound::LabelEither(
                    clauses
                        .iter()
                        .map(|clause| clause.unlab_or.clone())
                        .collect(),
                ),
                StmtKind::While { unlab_do, .. } => Compound::While(unlab_do.clone()),
                StmtKind::With { body, .. } => Compound::With(body.clone()),
                _ => Compound::Simple,
            };
            match compound {
                Compound::LabelIf(unlab_then, unlab_else) => {
                    let mut then_assigned = Vec::new();
                    let mut else_assigned = Vec::new();
                    let is_then_labeled = self.add_labels(
                        &unlab_then,
                        false,
                        is_in_with,
                        out_assigned,
                        &mut then_assigned,
                    )?;
                    is_next_labeled = self.add_labels(
                        &unlab_else,
                        false,
                        is_in_with,
                        out_assigned,
                        &mut else_assigned,
                    )? || is_then_labeled;
                    *out_assigned = get_union(&then_assigned, &else_assigned);
                    continue;
                }
                Compound::LabelEither(ors) => {
                    let mut either_assigned: Vec<String> = Vec::new();
                    for unlab_or in ors {
                        let mut or_assigned = Vec::new();
                        is_next_labeled = self.add_labels(
                            &unlab_or,
                            false,
                            is_in_with,
                            out_assigned,
                            &mut or_assigned,
                        )? || is_next_labeled;
                        either_assigned = get_union(&or_assigned, &either_assigned);
                    }
                    *out_assigned = either_assigned;
                    continue;
                }
                Compound::While(unlab_do) => {
                    if is_in_with {
                        return Err(error_at("`while' inside a `with' statement", get_pos(stmt)));
                    }
                    self.needs_label(stmt);
                    has_label = true;
                    out_assigned.clear();
                    self.add_labels(&unlab_do, false, false, out_assigned, &mut Vec::new())?;
                    is_next_labeled = false;
                    continue;
                }
                Compound::With(body) => {
                    let mut with_assigned = Vec::new();
                    let inner_in = if is_in_with {
                        in_assigned.to_vec()
                    } else {
                        Vec::new()
                    };
                    is_next_labeled =
                        self.add_labels(&body, false, true, &inner_in, &mut with_assigned)?;
                    *out_assigned = with_assigned;
                    if !is_in_with && !is_disjoint(in_assigned, out_assigned) {
                        self.needs_label(stmt);
                        has_label = true;
                        out_assigned.clear();
                    }
                    continue;
                }
                Compound::Simple => {}
            }
            // A call or return assigns the stack, and a return or a recursive call the
            // parameters and variables of every procedure. A statement that assigns a variable
            // assigned since the last label starts a new step.
            let (is_call, is_return, is_goto, assigned) = {
                let borrowed = stmt.borrow();
                match &borrowed.kind {
                    StmtKind::Assign { ass } => {
                        let vars: Vec<String> =
                            ass.iter().map(|assign| assign.var.clone()).collect();
                        (false, false, false, get_union(&[], &vars))
                    }
                    StmtKind::Call { to, .. } | StmtKind::CallGoto { to, .. } => {
                        let mut assigned = vec!["stack".to_owned()];
                        if Some(to) == self.current_procedure.as_ref() {
                            assigned.extend(self.get_procedure_vars());
                        }
                        (true, false, false, assigned)
                    }
                    StmtKind::Return { .. } | StmtKind::CallReturn { .. } => {
                        let mut assigned = vec!["stack".to_owned()];
                        assigned.extend(self.get_procedure_vars());
                        (false, true, false, assigned)
                    }
                    StmtKind::Goto { .. } => (false, false, true, Vec::new()),
                    _ => (false, false, false, Vec::new()),
                }
            };
            is_next_labeled = is_call || is_return || is_goto;
            if is_disjoint(out_assigned, &assigned) {
                *out_assigned = get_union(out_assigned, &assigned);
                continue;
            }
            if is_in_with {
                let message = if is_kind(stmt, "Assign") {
                    "Second assignment to same variable inside a `with' statement"
                } else {
                    "Call or return makes second assignment to a variable inside a `with' statement"
                };
                return Err(error_at(message, get_pos(stmt)));
            }
            self.needs_label(stmt);
            has_label = true;
            *out_assigned = assigned;
        }
        Ok(has_label || is_next_labeled)
    }

    /// Splits a sequence into the statements before its first label and the labeled statements
    /// from it on.
    fn split(
        &mut self,
        mut sequence: Vec<StmtRef>,
    ) -> Result<(Vec<StmtRef>, Vec<StmtRef>), PcalError> {
        let labeled = match get_first_label(&sequence) {
            None => Vec::new(),
            Some(index) => sequence.split_off(index),
        };
        self.fix_stmt_seq(&sequence)?;
        let labeled = self.make_labeled_stmts(labeled)?;
        Ok((sequence, labeled))
    }

    /// ParseAlgorithm.FixStmtSeq: splits each compound statement's sequences into the statements
    /// before their first label and the labeled statements from it on.
    fn fix_stmt_seq(&mut self, stmts: &[StmtRef]) -> Result<(), PcalError> {
        for stmt in stmts {
            let kind = stmt.borrow().kind.name();
            match kind {
                "LabelIf" => {
                    let (unlab_then, unlab_else) = match &mut stmt.borrow_mut().kind {
                        StmtKind::LabelIf {
                            unlab_then,
                            unlab_else,
                            ..
                        } => (std::mem::take(unlab_then), std::mem::take(unlab_else)),
                        _ => continue,
                    };
                    let then_parts = self.split(unlab_then)?;
                    let else_parts = self.split(unlab_else)?;
                    if let StmtKind::LabelIf {
                        unlab_then,
                        lab_then,
                        unlab_else,
                        lab_else,
                        ..
                    } = &mut stmt.borrow_mut().kind
                    {
                        *unlab_then = then_parts.0;
                        *lab_then = then_parts.1;
                        *unlab_else = else_parts.0;
                        *lab_else = else_parts.1;
                    }
                }
                "LabelEither" => {
                    let ors: Vec<Vec<StmtRef>> = match &mut stmt.borrow_mut().kind {
                        StmtKind::LabelEither { clauses } => clauses
                            .iter_mut()
                            .map(|clause| std::mem::take(&mut clause.unlab_or))
                            .collect(),
                        _ => continue,
                    };
                    let mut parts = Vec::new();
                    for unlab_or in ors {
                        parts.push(self.split(unlab_or)?);
                    }
                    if let StmtKind::LabelEither { clauses } = &mut stmt.borrow_mut().kind {
                        for (clause, part) in clauses.iter_mut().zip(parts) {
                            clause.unlab_or = part.0;
                            clause.lab_or = part.1;
                        }
                    }
                }
                "While" => {
                    let unlab_do = match &mut stmt.borrow_mut().kind {
                        StmtKind::While { unlab_do, .. } => std::mem::take(unlab_do),
                        _ => continue,
                    };
                    let parts = self.split(unlab_do)?;
                    if let StmtKind::While {
                        unlab_do, lab_do, ..
                    } = &mut stmt.borrow_mut().kind
                    {
                        *unlab_do = parts.0;
                        *lab_do = parts.1;
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// ParseAlgorithm.InnerMakeLabeledStmtSeq: groups the statements into labeled statements.
    fn make_labeled_stmts(&mut self, stmts: Vec<StmtRef>) -> Result<Vec<StmtRef>, PcalError> {
        let mut result: Vec<StmtRef> = Vec::new();
        for stmt in stmts {
            let (lbl, pos) = {
                let borrowed = stmt.borrow();
                (borrowed.lbl.clone(), borrowed.pos)
            };
            if lbl.is_empty() {
                let Some(last) = result.last() else {
                    return Err(bug(
                        "Failure of assertion: Missing Label in MakeLabeledStmtSeq",
                    ));
                };
                if let StmtKind::LabeledStmt { stmts, .. } = &mut last.borrow_mut().kind {
                    stmts.push(stmt);
                }
                continue;
            }
            result.push(create_stmt(
                pos,
                StmtKind::LabeledStmt {
                    label: lbl,
                    stmts: vec![stmt],
                },
            ));
        }
        for labeled in &result {
            self.fix_stmt_seq(&get_labeled_stmts(labeled))?;
        }
        Ok(result)
    }

    fn classify_labeled(&mut self, labeled: &StmtRef) -> Result<(), PcalError> {
        let mut stmts = take_labeled(labeled);
        let result = self.classify_stmt_seq(&mut stmts);
        put_labeled(labeled, stmts);
        result.map(|_| ())
    }

    /// ParseAlgorithm.ClassifyStmtSeq for one statement: 0 for one that may have a statement
    /// after it in the step, 1 for a call, return or goto, which ends a step, and 2 for one with a
    /// labeled statement inside. An if or either without labels inside becomes an If or Either.
    fn classify_stmt(&mut self, stmts: &mut [StmtRef], index: usize) -> Result<i32, PcalError> {
        let node = stmts[index].clone();
        let kind = node.borrow().kind.name();
        match kind {
            "LabelIf" => {
                let (mut unlab_then, lab_then, mut unlab_else, lab_else) =
                    match &mut node.borrow_mut().kind {
                        StmtKind::LabelIf {
                            unlab_then,
                            lab_then,
                            unlab_else,
                            lab_else,
                            ..
                        } => (
                            std::mem::take(unlab_then),
                            lab_then.clone(),
                            std::mem::take(unlab_else),
                            lab_else.clone(),
                        ),
                        _ => return Ok(0),
                    };
                let then_class = self.classify_stmt_seq(&mut unlab_then)?;
                for labeled in &lab_then {
                    self.classify_labeled(labeled)?;
                }
                let else_class = self.classify_stmt_seq(&mut unlab_else)?;
                for labeled in &lab_else {
                    self.classify_labeled(labeled)?;
                }
                let is_labeled = !lab_then.is_empty() || !lab_else.is_empty();
                let mut borrowed = node.borrow_mut();
                let StmtKind::LabelIf {
                    test,
                    unlab_then: then_slot,
                    unlab_else: else_slot,
                    ..
                } = &mut borrowed.kind
                else {
                    return Ok(0);
                };
                if is_labeled || then_class == 2 || else_class == 2 {
                    *then_slot = unlab_then;
                    *else_slot = unlab_else;
                    return Ok(2);
                }
                let test = std::mem::take(test);
                drop(borrowed);
                stmts[index] = create_stmt(
                    Position::NONE,
                    StmtKind::If {
                        test,
                        then: unlab_then,
                        els: unlab_else,
                    },
                );
                Ok(if then_class + else_class > 0 { 1 } else { 0 })
            }
            "LabelEither" => {
                let clauses = match &mut node.borrow_mut().kind {
                    StmtKind::LabelEither { clauses } => std::mem::take(clauses),
                    _ => return Ok(0),
                };
                let mut clauses = clauses;
                let mut either_class = 0;
                for clause in &mut clauses {
                    let unlabeled_class =
                        either_class.max(self.classify_stmt_seq(&mut clause.unlab_or)?);
                    for labeled in &clause.lab_or {
                        self.classify_labeled(labeled)?;
                    }
                    either_class = if clause.lab_or.is_empty() {
                        unlabeled_class
                    } else {
                        2
                    };
                }
                if either_class == 2 {
                    if let StmtKind::LabelEither { clauses: slot } = &mut node.borrow_mut().kind {
                        *slot = clauses;
                    }
                    return Ok(2);
                }
                stmts[index] = create_stmt(
                    Position::NONE,
                    StmtKind::Either {
                        ors: clauses.into_iter().map(|clause| clause.unlab_or).collect(),
                    },
                );
                Ok(either_class)
            }
            "With" => {
                let mut body = match &mut node.borrow_mut().kind {
                    StmtKind::With { body, .. } => std::mem::take(body),
                    _ => return Ok(0),
                };
                let with_class = self.classify_stmt_seq(&mut body);
                if let StmtKind::With { body: slot, .. } = &mut node.borrow_mut().kind {
                    *slot = body;
                }
                let with_class = with_class?;
                if with_class == 2 {
                    return Err(error(&format!(
                        "with statement at {} contains a labeled statement",
                        get_pos(&node).location()
                    )));
                }
                Ok(with_class)
            }
            "While" => {
                if index != 0 {
                    return Err(bug(
                        "ParseAlgorithm.ClassifyStmtSeq encountered `while' not at beginning of StmtSeq.",
                    ));
                }
                let (mut unlab_do, lab_do) = match &mut node.borrow_mut().kind {
                    StmtKind::While {
                        unlab_do, lab_do, ..
                    } => (std::mem::take(unlab_do), lab_do.clone()),
                    _ => return Ok(0),
                };
                let result = self.classify_stmt_seq(&mut unlab_do);
                if let StmtKind::While { unlab_do: slot, .. } = &mut node.borrow_mut().kind {
                    *slot = unlab_do;
                }
                result?;
                for labeled in &lab_do {
                    self.classify_labeled(labeled)?;
                }
                Ok(0)
            }
            "Call" => Ok(
                if stmts
                    .get(index + 1)
                    .is_some_and(|next| is_kind(next, "Return"))
                {
                    0
                } else {
                    1
                },
            ),
            "Return" | "CallReturn" => {
                if self.current_procedure.is_none() {
                    return Err(error(&format!(
                        "return statement not in a procedure at {}",
                        get_pos(&node).location()
                    )));
                }
                Ok(1)
            }
            "Goto" | "CallGoto" => Ok(1),
            "Assign" | "When" | "PrintS" | "Assert" | "Skip" | "MacroCall" => Ok(0),
            _ => Err(bug(&format!(
                "ParseAlgorithm.ClassifyStmtSeq encountered the unexpected statement type {kind}"
            ))),
        }
    }

    /// ParseAlgorithm.ClassifyStmtSeq: a statement that ends a step can only end its sequence.
    fn classify_stmt_seq(&mut self, stmts: &mut [StmtRef]) -> Result<i32, PcalError> {
        for index in 0..stmts.len() {
            let stmt_class = self.classify_stmt(stmts, index)?;
            if stmt_class == 0 {
                continue;
            }
            if index == stmts.len() - 1 {
                return Ok(stmt_class);
            }
            return Err(bug(&format!(
                "Translator discovered later than it should have  that\n  Statement at {} must have a label",
                get_pos(&stmts[index + 1]).location()
            )));
        }
        Ok(0)
    }

    /// ParseAlgorithm.AddLabelsToStmtSeq followed by MakeLabeledStmtSeq.
    fn make_labeled_stmt_seq(&mut self, stmts: Vec<StmtRef>) -> Result<Vec<StmtRef>, PcalError> {
        self.add_labels(&stmts, true, false, &[], &mut Vec::new())?;
        let result = self.make_labeled_stmts(stmts)?;
        for labeled in &result {
            self.classify_labeled(labeled)?;
        }
        Ok(result)
    }

    /// ParseAlgorithm.ExpandMacrosInStmtSeq: replaces each macro call with the macro's body.
    fn expand_macros_in_stmt_seq(
        &mut self,
        stmts: &mut Vec<StmtRef>,
        macros: &[Macro],
    ) -> Result<(), PcalError> {
        let mut expanded = Vec::new();
        for node in std::mem::take(stmts) {
            let mut borrowed = node.borrow_mut();
            match &mut borrowed.kind {
                StmtKind::LabelIf {
                    unlab_then,
                    unlab_else,
                    ..
                } => {
                    self.expand_macros_in_stmt_seq(unlab_then, macros)?;
                    self.expand_macros_in_stmt_seq(unlab_else, macros)?;
                }
                StmtKind::LabelEither { clauses } => {
                    for clause in clauses {
                        self.expand_macros_in_stmt_seq(&mut clause.unlab_or, macros)?;
                    }
                }
                StmtKind::With { body, .. } => self.expand_macros_in_stmt_seq(body, macros)?,
                StmtKind::While { unlab_do, .. } => {
                    self.expand_macros_in_stmt_seq(unlab_do, macros)?;
                }
                StmtKind::MacroCall { name, args } => {
                    let (name, args) = (name.clone(), args.clone());
                    let (pos, lbl) = (borrowed.pos, borrowed.lbl.clone());
                    expanded.extend(expand_macro_call(pos, lbl, &name, &args, macros)?);
                    continue;
                }
                _ => {}
            }
            drop(borrowed);
            expanded.push(node);
        }
        *stmts = expanded;
        Ok(())
    }

    fn fix_procedures(&mut self, macros: &[Macro]) -> Result<(), PcalError> {
        for index in 0..self.procedures.len() {
            self.current_procedure = Some(self.procedures[index].name.clone());
            let mut body = std::mem::take(&mut self.procedures[index].body);
            self.expand_macros_in_stmt_seq(&mut body, macros)?;
            self.procedures[index].body = self.make_labeled_stmt_seq(body)?;
        }
        Ok(())
    }

    /// ParseAlgorithm.checkBody: a body that is a single labeled "while TRUE" without labels
    /// inside lets the translation omit pc.
    fn check_body(&mut self, body: &[StmtRef]) {
        let Some(labeled) = body.first() else {
            return;
        };
        if body.len() > 1 || !is_kind(labeled, "LabeledStmt") {
            self.omit_pc = false;
            return;
        }
        let stmts = get_labeled_stmts(labeled);
        let Some(first) = stmts.first() else {
            return;
        };
        let borrowed = first.borrow();
        let StmtKind::While {
            test,
            unlab_do,
            lab_do,
        } = &borrowed.kind
        else {
            self.omit_pc = false;
            return;
        };
        if stmts.len() > 1 {
            self.omit_pc = false;
            return;
        }
        if !is_one_token_expr(test) || test.tokens[0][0].borrow().string != "TRUE" {
            self.omit_pc = false;
            return;
        }
        if !lab_do.is_empty() {
            self.omit_pc = false;
        }
        let has_labeled = unlab_do.iter().any(|stmt| {
            ["LabelIf", "LabelEither", "LabeledStmt"].contains(&stmt.borrow().kind.name())
        });
        if has_labeled {
            self.omit_pc = false;
        }
    }

    /// ParseAlgorithm.AddedMessagesError.
    fn added_labels_error(&self) -> PcalError {
        let header = if self.added_labels.len() > 1 {
            "Missing labels at the following locations:"
        } else {
            "Missing label at the following location:"
        };
        let mut parts = vec![header.to_owned()];
        parts.extend(self.added_labels_locs.iter().cloned());
        error(&parts.join("\n     "))
    }

    fn check_for_duplicate_macros(macros: &[Macro]) -> Result<(), PcalError> {
        for (index, definition) in macros.iter().enumerate() {
            if macros[index + 1..]
                .iter()
                .any(|other| other.name == definition.name)
            {
                return Err(error(&format!(
                    "Multiple definitions of macro name `{}'",
                    definition.name
                )));
            }
        }
        Ok(())
    }

    fn parse(&mut self, is_fair_algorithm: bool) -> Result<Algorithm, PcalError> {
        if is_fair_algorithm && self.get_alg_token()? != "algorithm" {
            return Err(self.parsing_error("`--fair' not followed by `algorithm'"));
        }
        let name = self.get_alg_token()?;
        self.c_syntax = self.peek_is("{")?;
        if self.c_syntax {
            self.must_gobble_this("{")?;
        }
        let decls = if self.peek_is("variable")? || self.peek_is("variables")? {
            self.get_var_decls()?
        } else {
            Vec::new()
        };
        let mut defs = create_expr(Vec::new());
        if self.peek_is("define")? {
            self.must_gobble_this("define")?;
            if self.c_syntax {
                self.gobble_this("{")?;
            }
            defs = self.get_expr(true)?;
            self.gobble_end_or_right_brace("define")?;
            self.gobble_this(";")?;
        }
        let mut macros = Vec::new();
        while self.peek_is("macro")? {
            let definition = self.get_macro(&macros)?;
            macros.push(definition);
        }
        while self.peek_is("procedure")? {
            let procedure = self.get_procedure()?;
            self.procedures.push(procedure);
            self.omit_pc = false;
        }
        let is_multiprocess = (self.peek_is("fair")?
            && (self.peek_at_alg_token(2)? == "process"
                || (self.peek_at_alg_token(2)? == "+" && self.peek_at_alg_token(3)? == "process")))
            || self.peek_is("process")?;
        if is_multiprocess {
            let mut procs = Vec::new();
            while self.peek_is("fair")? || self.peek_is("process")? {
                let is_fair = self.peek_is("fair")?;
                if is_fair {
                    self.must_gobble_this("fair")?;
                }
                let is_strongly_fair = is_fair && self.peek_is("+")?;
                if is_strongly_fair {
                    self.must_gobble_this("+")?;
                }
                let option = self.session.params.fairness_option.as_str();
                let fairness = if is_strongly_fair || (!is_fair && option == "sf") {
                    2
                } else if is_fair || option == "wf" {
                    1
                } else {
                    0
                };
                procs.push(self.get_process(fairness)?);
            }
            self.gobble_end_or_right_brace("algorithm")?;
            Self::check_for_duplicate_macros(&macros)?;
            for proc in &mut procs {
                let mut body = std::mem::take(&mut proc.body);
                self.expand_macros_in_stmt_seq(&mut body, &macros)?;
                proc.body = self.make_labeled_stmt_seq(body)?;
                self.check_body(&proc.body);
            }
            self.fix_procedures(&macros)?;
            if !self.added_labels.is_empty() {
                if !self.session.params.label_flag {
                    return Err(self.added_labels_error());
                }
                self.session.log.push("Labels added.".to_owned());
            }
            if self.goto_done_used || self.goto_used {
                self.omit_pc = false;
            }
            return Ok(Algorithm {
                name,
                decls,
                defs,
                prcds: std::mem::take(&mut self.procedures),
                body: AlgorithmBody::Multiprocess(procs),
            });
        }
        if self.session.params.input_version_number == 1500.0 && self.peek_is("fair")? {
            self.gobble_this("fair")?;
            if self.peek_is("+")? {
                self.gobble_this("+")?;
            }
            self.session.params.fairness_option = "wf".to_owned();
        }
        if is_fair_algorithm {
            let option = &self.session.params.fairness_option;
            if !["", "wf", "wfNext"].contains(&option.as_str()) {
                let warning = format!("Warning: Option `{option}' specified for --fair algorithm.");
                self.session.log.push(warning);
            }
            self.session.params.fairness_option = "wf".to_owned();
        }
        // The Java's labels and called procedures of the last procedure are the parser's own,
        // which the body's labels and calls add to.
        if let Some(last) = self.procedures.last_mut() {
            self.plus_labels = std::mem::take(&mut last.plus_labels);
            self.minus_labels = std::mem::take(&mut last.minus_labels);
            self.procedures_called = std::mem::take(&mut last.procedures_called);
        }
        self.gobble_begin_or_left_brace()?;
        let mut body = self.get_stmt_seq()?;
        Self::check_for_duplicate_macros(&macros)?;
        self.expand_macros_in_stmt_seq(&mut body, &macros)?;
        self.fix_procedures(&macros)?;
        // The first brace ends the body that gobble_begin_or_left_brace began.
        if self.c_syntax {
            self.gobble_this("}")?;
        }
        self.gobble_end_or_right_brace("algorithm")?;
        let labeled_body = self.make_labeled_stmt_seq(body)?;
        if !self.added_labels.is_empty() {
            if self.has_label && !self.session.params.label_flag {
                return Err(self.added_labels_error());
            }
            self.session.log.push("Labels added.".to_owned());
        }
        if self.goto_used || self.goto_done_used {
            self.omit_pc = false;
        }
        self.check_body(&labeled_body);
        if let Some(last) = self.procedures.last_mut() {
            last.plus_labels = std::mem::take(&mut self.plus_labels);
            last.minus_labels = std::mem::take(&mut self.minus_labels);
            last.procedures_called = std::mem::take(&mut self.procedures_called);
        }
        Ok(Algorithm {
            name,
            decls,
            defs,
            prcds: std::mem::take(&mut self.procedures),
            body: AlgorithmBody::Uniprocess(labeled_body),
        })
    }
}

/// ParseAlgorithm.ExpandMacroCall: the last macro of the name wins.
fn expand_macro_call(
    pos: Position,
    lbl: String,
    name: &str,
    args: &[Expr],
    macros: &[Macro],
) -> Result<Vec<StmtRef>, PcalError> {
    let Some(definition) = macros
        .iter()
        .rev()
        .find(|definition| definition.name == name)
    else {
        return Err(error(&format!(
            "Macro {name} undefined,\n    at {}",
            pos.location()
        )));
    };
    if definition.params.len() != args.len() {
        return Err(error(&format!(
            "Macro {name} called with wrong number of arguments at \n    {}",
            pos.location()
        )));
    }
    let mut result = Vec::new();
    for stmt in &definition.body {
        result.push(substitute_in_stmt(
            stmt,
            args,
            &definition.params,
            pos.line,
            pos.col,
        )?);
    }
    if let Some(first) = result.first() {
        first.borrow_mut().lbl = lbl;
    }
    Ok(result)
}

/// ParseAlgorithm.SubstituteInStmt: a copy of a macro's statement with the macro's arguments for
/// its parameters, which records the position of the macro call.
fn substitute_in_stmt(
    stmt: &StmtRef,
    args: &[Expr],
    names: &[String],
    macro_line: i64,
    macro_col: i64,
) -> Result<StmtRef, PcalError> {
    let substitute = |expr: &Expr| get_substituted_expr(expr, args, names);
    let substitute_all = |stmts: &[StmtRef]| -> Result<Vec<StmtRef>, PcalError> {
        stmts
            .iter()
            .map(|inner| substitute_in_stmt(inner, args, names, macro_line, macro_col))
            .collect()
    };
    let substitute_labeled = |stmts: &[StmtRef]| -> Result<Vec<StmtRef>, PcalError> {
        stmts
            .iter()
            .map(|inner| {
                let inner_stmts = get_labeled_stmts(inner)
                    .iter()
                    .map(|labeled| substitute_in_stmt(labeled, args, names, -1, 0))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(create_stmt(
                    Position::NONE,
                    StmtKind::LabeledStmt {
                        label: super::ast::get_label(inner),
                        stmts: inner_stmts,
                    },
                ))
            })
            .collect()
    };
    let stmt = stmt.borrow();
    let pos = if macro_line > 0 {
        Position {
            macro_line,
            macro_col,
            ..stmt.pos
        }
    } else {
        stmt.pos
    };
    let kind = match &stmt.kind {
        StmtKind::Assign { ass } => StmtKind::Assign {
            ass: ass
                .iter()
                .map(|assign| {
                    substitute_in_single_assign(assign, args, names, macro_line, macro_col)
                })
                .collect::<Result<_, _>>()?,
        },
        StmtKind::If { test, then, els } => StmtKind::If {
            test: substitute(test)?,
            then: substitute_all(then)?,
            els: substitute_all(els)?,
        },
        StmtKind::Either { ors } => StmtKind::Either {
            ors: ors
                .iter()
                .map(|or| substitute_all(or))
                .collect::<Result<_, _>>()?,
        },
        StmtKind::With {
            var,
            is_eq,
            exp,
            body,
        } => StmtKind::With {
            var: var.clone(),
            is_eq: *is_eq,
            exp: substitute(exp)?,
            body: substitute_all(body)?,
        },
        StmtKind::When(exp) => StmtKind::When(substitute(exp)?),
        StmtKind::Assert(exp) => StmtKind::Assert(substitute(exp)?),
        StmtKind::PrintS(exp) => StmtKind::PrintS(substitute(exp)?),
        // SubstituteInStmt doesn't copy a skip's macro position.
        StmtKind::Skip => {
            let pos = if macro_line > 0 {
                pos
            } else {
                Position {
                    macro_line: -1,
                    macro_col: 0,
                    ..stmt.pos
                }
            };
            return Ok(create_stmt(pos, StmtKind::Skip));
        }
        StmtKind::While {
            test,
            unlab_do,
            lab_do,
        } => StmtKind::While {
            test: substitute(test)?,
            unlab_do: substitute_all(unlab_do)?,
            lab_do: substitute_labeled(lab_do)?,
        },
        StmtKind::LabelIf {
            test,
            unlab_then,
            lab_then,
            unlab_else,
            lab_else,
        } => StmtKind::LabelIf {
            test: substitute(test)?,
            unlab_then: substitute_all(unlab_then)?,
            lab_then: substitute_labeled(lab_then)?,
            unlab_else: substitute_all(unlab_else)?,
            lab_else: substitute_labeled(lab_else)?,
        },
        StmtKind::LabelEither { clauses } => StmtKind::LabelEither {
            clauses: clauses
                .iter()
                .map(|clause| {
                    let lab_or = substitute_labeled(&clause.lab_or)?;
                    let unlab_or = substitute_all(&clause.unlab_or)?;
                    Ok(Clause { unlab_or, lab_or })
                })
                .collect::<Result<_, PcalError>>()?,
        },
        StmtKind::Call {
            return_to,
            to,
            args: call_args,
        } => StmtKind::Call {
            return_to: return_to.clone(),
            to: to.clone(),
            args: substitute_exprs(call_args, args, names)?,
        },
        StmtKind::Return { from } => StmtKind::Return { from: from.clone() },
        StmtKind::CallReturn {
            from,
            to,
            args: call_args,
        } => StmtKind::CallReturn {
            from: from.clone(),
            to: to.clone(),
            args: substitute_exprs(call_args, args, names)?,
        },
        StmtKind::CallGoto {
            after,
            to,
            args: call_args,
        } => StmtKind::CallGoto {
            after: after.clone(),
            to: to.clone(),
            args: substitute_exprs(call_args, args, names)?,
        },
        StmtKind::Goto { to } => StmtKind::Goto { to: to.clone() },
        StmtKind::LabeledStmt { .. } | StmtKind::MacroCall { .. } => {
            return Err(bug(&format!(
                "Found unexpected statement type in macro at{}",
                stmt.pos.location()
            )));
        }
    };
    Ok(create_stmt(pos, kind))
}

/// TLAExpr.SeqSubstituteForAll.
fn substitute_exprs(
    exprs: &[Expr],
    args: &[Expr],
    params: &[String],
) -> Result<Vec<Expr>, PcalError> {
    exprs
        .iter()
        .map(|expr| get_substituted_expr(expr, args, params))
        .collect()
}

/// ParseAlgorithm.SubstituteInSingleAssign: a parameter assigned to becomes the variable its
/// argument starts with, and the rest of the argument goes before the subscript.
fn substitute_in_single_assign(
    assign: &SingleAssign,
    args: &[Expr],
    names: &[String],
    macro_line: i64,
    macro_col: i64,
) -> Result<SingleAssign, PcalError> {
    let rhs = get_substituted_expr(&assign.rhs, args, names)?;
    let sub = if assign.sub.tokens.is_empty() {
        assign.sub.clone()
    } else {
        get_substituted_expr(&assign.sub, args, names)?
    };
    let pos = if macro_line > 0 {
        Position {
            macro_line,
            macro_col,
            ..assign.pos
        }
    } else {
        assign.pos
    };
    let mut result = SingleAssign {
        pos,
        var: assign.var.clone(),
        sub,
        rhs,
    };
    let Some(index) = names.iter().position(|name| *name == result.var) else {
        return Ok(result);
    };
    let argument = &args[index];
    let first = Coord { line: 0, item: 0 };
    let var_token = get_token_at(argument, first)?;
    let (kind, string) = {
        let token = var_token.borrow();
        (token.kind, token.string.clone())
    };
    if kind != IDENT {
        return Err(error(&format!(
            "Macro expansion substitutes `{string}' for assignment variable\n    at {}",
            result.pos.location()
        )));
    }
    result.var = string;
    if step_coord(argument, first, 1)?.is_none() {
        return Ok(result);
    }
    let mut copy = clone_expr(argument);
    copy.tokens[0].remove(0);
    normalize_expr(&mut copy);
    if result.sub.tokens.is_empty() {
        result.sub = copy;
    } else {
        prepend_expr(&mut result.sub, &copy, 0)?;
    }
    Ok(result)
}

/// ParseAlgorithm.getAlgorithm: parses the algorithm the reader is at, just after "--algorithm"
/// or "--fair", adds the labels it needs, and expands its macros.
pub fn parse_algorithm(
    session: &mut PcalSession,
    reader: Reader,
    is_fair_algorithm: bool,
) -> Result<ParseResult, PcalError> {
    let omit_pc = session.params.input_version_number >= 1500.0;
    let mut parser = Parser {
        session,
        reader,
        lookahead_size: 0,
        added_labels: Vec::new(),
        added_labels_locs: Vec::new(),
        next_label_num: 1,
        all_labels: HashSet::new(),
        has_label: false,
        has_default_initialization: false,
        current_procedure: None,
        procedures: Vec::new(),
        c_syntax: false,
        plus_labels: Vec::new(),
        minus_labels: Vec::new(),
        procedures_called: Vec::new(),
        goto_used: false,
        goto_done_used: false,
        omit_pc,
    };
    // HACK: ParseAlgorithm.getAlgorithm turns any RuntimeException, such as an index out of bounds
    // on input it doesn't expect, into a parsing error at the last token.
    match parser.parse(is_fair_algorithm) {
        Ok(ast) => Ok(ParseResult {
            ast,
            omit_pc: parser.omit_pc,
            has_default_initialization: parser.has_default_initialization,
        }),
        Err(PcalError::Runtime(_)) => Err(parser.parsing_error("Unknown error at or before")),
        Err(other) => Err(other),
    }
}

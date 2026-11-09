//! The translator's AST and expressions, as `src/pcal/ast.ts` ports them from the Java of
//! `pcal.AST` and `pcal.TLAExpr`. Statements and tokens are shared and changed in place, as the
//! Java's objects are: the translation changes the AST that SANY then checksums.

use std::cell::RefCell;
use std::rc::Rc;

use super::{PcalError, bug, error, runtime};
use crate::TlcVersion;

/// TLAToken's types.
pub const BUILTIN: u8 = 1;
pub const NUMBER: u8 = 2;
pub const STRING: u8 = 3;
pub const IDENT: u8 = 4;
pub const ADDED: u8 = 5;

#[derive(Debug)]
pub struct TokenData {
    pub string: String,
    pub column: i64,
    pub kind: u8,
}

pub type Token = Rc<RefCell<TokenData>>;

pub fn create_token(string: &str, column: i64, kind: u8) -> Token {
    Rc::new(RefCell::new(TokenData {
        string: string.to_owned(),
        column,
        kind,
    }))
}

/// The length of a Java string: its UTF-16 code units.
pub fn get_java_length(text: &str) -> i64 {
    text.encode_utf16().count() as i64
}

/// TLAToken.getWidth: a string token's width counts its quotes.
pub fn get_token_width(token: &Token) -> i64 {
    let token = token.borrow();
    get_java_length(&token.string) + if token.kind == STRING { 2 } else { 0 }
}

/// TLAExpr: the tokens of an expression, line by line, and for each line the token of an earlier
/// line it is aligned under, with that token's column when the expression was normalized.
/// `Clone` shares the tokens, as the Java shares an expression; `clone_expr` copies them.
#[derive(Clone, Debug, Default)]
pub struct Expr {
    pub tokens: Vec<Vec<Token>>,
    pub anchor_tokens: Option<Vec<Option<Token>>>,
    pub anchor_tok_col: Option<Vec<i64>>,
}

/// IntPair, as the "Java coordinates" of a token in an expression.
#[derive(Clone, Copy, Debug)]
pub struct Coord {
    pub line: i64,
    pub item: i64,
}

/// PcalParams: the translator's options, which the Java keeps in static fields that SANY never
/// resets, so options one module sets carry over to the modules SANY validates after it.
#[derive(Debug)]
pub struct Params {
    pub label_flag: bool,
    pub label_root: String,
    pub fairness_option: String,
    pub check_termination: bool,
    pub spec_option: bool,
    pub myspec_option: bool,
    pub input_version_number: f64,
}

/// PcalParams.versionWeight.
pub const VERSION_WEIGHT: f64 = 1903.0;

impl Default for Params {
    fn default() -> Self {
        Params {
            label_flag: false,
            label_root: "Lbl_".to_owned(),
            fairness_option: String::new(),
            check_termination: false,
            spec_option: false,
            myspec_option: false,
            input_version_number: VERSION_WEIGHT,
        }
    }
}

/// PcalParams.VersionToNumber: "1.5" is 1500, and -1 means a malformed version.
pub fn get_version_number(text: &str) -> f64 {
    let mut result = 0.0;
    let mut digits_after_decimal = 0;
    let mut is_after_decimal = false;
    for char in text.chars() {
        if char == '.' {
            is_after_decimal = true;
            continue;
        }
        let Some(digit) = char.to_digit(10).filter(|_| char.is_ascii_digit()) else {
            return -1.0;
        };
        result = 10.0 * result + f64::from(digit);
        if is_after_decimal {
            digits_after_decimal += 1;
        }
        if digits_after_decimal > 3 {
            return -1.0;
        }
    }
    result * 10f64.powi((3 - digits_after_decimal).max(0))
}

/// The line and column of a node, and of the macro call it was expanded from.
#[derive(Clone, Copy, Debug)]
pub struct Position {
    pub line: i64,
    pub col: i64,
    pub macro_line: i64,
    pub macro_col: i64,
}

impl Position {
    pub const NONE: Position = Position {
        line: 0,
        col: 0,
        macro_line: -1,
        macro_col: 0,
    };

    pub fn at(line: i64, col: i64) -> Position {
        Position {
            line,
            col,
            ..Position::NONE
        }
    }

    /// AST.location.
    pub fn location(&self) -> String {
        if self.macro_line < 0 {
            format!("line {}, column {}", self.line, self.col)
        } else {
            format!(
                "line {}, column {} of macro called at line {}, column {}",
                self.line, self.col, self.macro_line, self.macro_col
            )
        }
    }
}

pub type StmtRef = Rc<RefCell<Stmt>>;

#[derive(Debug)]
pub struct Stmt {
    pub pos: Position,
    pub lbl: String,
    pub kind: StmtKind,
}

pub fn create_stmt(pos: Position, kind: StmtKind) -> StmtRef {
    Rc::new(RefCell::new(Stmt {
        pos,
        lbl: String::new(),
        kind,
    }))
}

#[derive(Debug)]
pub struct SingleAssign {
    pub pos: Position,
    pub var: String,
    pub sub: Expr,
    pub rhs: Expr,
}

#[derive(Debug, Default)]
pub struct Clause {
    pub unlab_or: Vec<StmtRef>,
    pub lab_or: Vec<StmtRef>,
}

#[derive(Debug)]
pub enum StmtKind {
    LabeledStmt {
        label: String,
        stmts: Vec<StmtRef>,
    },
    While {
        test: Expr,
        unlab_do: Vec<StmtRef>,
        lab_do: Vec<StmtRef>,
    },
    Assign {
        ass: Vec<SingleAssign>,
    },
    If {
        test: Expr,
        then: Vec<StmtRef>,
        els: Vec<StmtRef>,
    },
    Either {
        ors: Vec<Vec<StmtRef>>,
    },
    With {
        var: String,
        is_eq: bool,
        exp: Expr,
        body: Vec<StmtRef>,
    },
    When(Expr),
    PrintS(Expr),
    Assert(Expr),
    Skip,
    LabelIf {
        test: Expr,
        unlab_then: Vec<StmtRef>,
        lab_then: Vec<StmtRef>,
        unlab_else: Vec<StmtRef>,
        lab_else: Vec<StmtRef>,
    },
    LabelEither {
        clauses: Vec<Clause>,
    },
    Call {
        return_to: String,
        to: String,
        args: Vec<Expr>,
    },
    /// A return outside a procedure has a null from, which Java prints as "null".
    Return {
        from: Option<String>,
    },
    CallReturn {
        from: Option<String>,
        to: String,
        args: Vec<Expr>,
    },
    CallGoto {
        after: String,
        to: String,
        args: Vec<Expr>,
    },
    Goto {
        to: String,
    },
    MacroCall {
        name: String,
        args: Vec<Expr>,
    },
}

impl StmtKind {
    pub fn name(&self) -> &'static str {
        match self {
            StmtKind::LabeledStmt { .. } => "LabeledStmt",
            StmtKind::While { .. } => "While",
            StmtKind::Assign { .. } => "Assign",
            StmtKind::If { .. } => "If",
            StmtKind::Either { .. } => "Either",
            StmtKind::With { .. } => "With",
            StmtKind::When(_) => "When",
            StmtKind::PrintS(_) => "PrintS",
            StmtKind::Assert(_) => "Assert",
            StmtKind::Skip => "Skip",
            StmtKind::LabelIf { .. } => "LabelIf",
            StmtKind::LabelEither { .. } => "LabelEither",
            StmtKind::Call { .. } => "Call",
            StmtKind::Return { .. } => "Return",
            StmtKind::CallReturn { .. } => "CallReturn",
            StmtKind::CallGoto { .. } => "CallGoto",
            StmtKind::Goto { .. } => "Goto",
            StmtKind::MacroCall { .. } => "MacroCall",
        }
    }
}

/// A VarDecl, or with `is_eq` true a PVarDecl.
#[derive(Debug)]
pub struct VarDecl {
    pub pos: Position,
    pub var: String,
    pub is_eq: bool,
    pub val: Expr,
}

#[derive(Debug)]
pub struct Procedure {
    pub pos: Position,
    pub name: String,
    pub minus_labels: Vec<String>,
    pub plus_labels: Vec<String>,
    pub procedures_called: Vec<String>,
    pub params: Vec<VarDecl>,
    pub decls: Vec<VarDecl>,
    pub body: Vec<StmtRef>,
}

/// AST.UNFAIR_PROC, WF_PROC and SF_PROC index FairnessString.
const FAIRNESS: [&str; 3] = ["unfair", "wf", "sf"];

#[derive(Debug)]
pub struct Process {
    pub pos: Position,
    pub name: String,
    pub fairness: usize,
    pub minus_labels: Vec<String>,
    pub plus_labels: Vec<String>,
    pub procedures_called: Vec<String>,
    pub is_eq: bool,
    pub id: Expr,
    pub decls: Vec<VarDecl>,
    pub body: Vec<StmtRef>,
}

#[derive(Debug)]
pub struct Macro {
    pub name: String,
    pub params: Vec<String>,
    pub body: Vec<StmtRef>,
}

#[derive(Debug)]
pub enum AlgorithmBody {
    Uniprocess(Vec<StmtRef>),
    Multiprocess(Vec<Process>),
}

#[derive(Debug)]
pub struct Algorithm {
    pub name: String,
    pub decls: Vec<VarDecl>,
    pub defs: Expr,
    pub prcds: Vec<Procedure>,
    pub body: AlgorithmBody,
}

/// A Java cast of a statement to AST.LabeledStmt.
pub fn check_labeled(stmt: &StmtRef) -> Result<(), PcalError> {
    let stmt = stmt.borrow();
    match stmt.kind {
        StmtKind::LabeledStmt { .. } => Ok(()),
        _ => Err(runtime(format!("ClassCastException: {}", stmt.kind.name()))),
    }
}

/// The label of a labeled statement.
pub fn get_label(stmt: &StmtRef) -> String {
    match &stmt.borrow().kind {
        StmtKind::LabeledStmt { label, .. } => label.clone(),
        _ => String::new(),
    }
}

/// The statements of a labeled statement, shared.
pub fn get_labeled_stmts(stmt: &StmtRef) -> Vec<StmtRef> {
    match &stmt.borrow().kind {
        StmtKind::LabeledStmt { stmts, .. } => stmts.clone(),
        _ => Vec::new(),
    }
}

/// Vector.elementAt, which throws for an index out of bounds.
pub fn get_element<T>(vector: &[T], index: i64) -> Result<&T, PcalError> {
    usize::try_from(index)
        .ok()
        .and_then(|position| vector.get(position))
        .ok_or_else(|| runtime(format!("ArrayIndexOutOfBoundsException: {index}")))
}

pub fn create_expr(tokens: Vec<Vec<Token>>) -> Expr {
    Expr {
        tokens,
        anchor_tokens: None,
        anchor_tok_col: None,
    }
}

/// TLAExpr.normalize: drops empty first and last lines, shifts the tokens left as far as they go,
/// and records the token each line is aligned under.
pub fn normalize_expr(expr: &mut Expr) {
    while expr.tokens.first().is_some_and(Vec::is_empty) {
        expr.tokens.remove(0);
    }
    while expr.tokens.last().is_some_and(Vec::is_empty) {
        expr.tokens.pop();
    }
    let min_column = expr
        .tokens
        .iter()
        .filter_map(|line| line.first())
        .map(|token| token.borrow().column)
        .fold(999_999, i64::min);
    for token in expr.tokens.iter().flatten() {
        token.borrow_mut().column -= min_column;
    }
    let mut anchor_tokens = Vec::new();
    let mut anchor_tok_col = Vec::new();
    for (index, line) in expr.tokens.iter().enumerate() {
        anchor_tok_col.push(0);
        anchor_tokens.push(None);
        let Some(first) = line.first() else {
            continue;
        };
        let first_column = first.borrow().column;
        let Some(anchor_line) = expr.tokens[..index].iter().rev().find(|candidate| {
            candidate
                .first()
                .is_some_and(|token| token.borrow().column <= first_column)
        }) else {
            continue;
        };
        let stop = anchor_line
            .iter()
            .enumerate()
            .position(|(item, token)| item > 0 && token.borrow().column > first_column)
            .unwrap_or(anchor_line.len());
        let anchor = &anchor_line[stop - 1];
        anchor_tok_col[index] = anchor.borrow().column;
        anchor_tokens[index] = Some(anchor.clone());
    }
    expr.anchor_tokens = Some(anchor_tokens);
    expr.anchor_tok_col = Some(anchor_tok_col);
}

pub fn create_normalized_expr(tokens: Vec<Vec<Token>>) -> Expr {
    let mut expr = create_expr(tokens);
    normalize_expr(&mut expr);
    expr
}

/// TLAExpr.renormalize: shifts each line right by as much as its anchor token has moved.
fn renormalize_expr(expr: &mut Expr) -> Result<(), PcalError> {
    let (Some(anchor_tokens), Some(anchor_tok_col)) =
        (&expr.anchor_tokens, &mut expr.anchor_tok_col)
    else {
        return Err(runtime(
            "NullPointerException: TLAExpr.renormalize".to_owned(),
        ));
    };
    for (index, line) in expr.tokens.iter().enumerate() {
        let Some(Some(anchor)) = anchor_tokens.get(index) else {
            continue;
        };
        let column = anchor.borrow().column;
        let previous = anchor_tok_col.get(index).copied().unwrap_or(0);
        let shift = column - previous;
        if let Some(slot) = anchor_tok_col.get_mut(index) {
            *slot = column;
        }
        if shift < 0 {
            return Err(error(
                "TLAExpr.renormalize() found anchor has moved to left.",
            ));
        }
        for token in line {
            token.borrow_mut().column += shift;
        }
    }
    Ok(())
}

/// TLAExpr.cloneAndNormalize: a copy of the expression with tokens of its own.
pub fn clone_expr(expr: &Expr) -> Expr {
    create_normalized_expr(
        expr.tokens
            .iter()
            .map(|line| {
                line.iter()
                    .map(|token| {
                        let token = token.borrow();
                        create_token(&token.string, token.column, token.kind)
                    })
                    .collect()
            })
            .collect(),
    )
}

/// TLAExpr.prepend: puts prefix in front of the expression, spaces columns before its first token.
pub fn prepend_expr(expr: &mut Expr, prefix: &Expr, spaces: i64) -> Result<(), PcalError> {
    let prefix_lines = prefix.tokens.len();
    let (Some(prefix_line), true) = (prefix.tokens.last(), prefix_lines <= expr.tokens.len())
    else {
        return Err(runtime("NullPointerException: TLAExpr.prepend".to_owned()));
    };
    let inserted = prefix.tokens[..prefix_lines - 1].iter().cloned();
    expr.tokens.splice(0..0, inserted);
    let Some(last) = prefix_line.last() else {
        return Err(runtime("ArrayIndexOutOfBoundsException: -1".to_owned()));
    };
    let shift = last.borrow().column + get_token_width(last) + spaces;
    let expr_line = &mut expr.tokens[prefix_lines - 1];
    for token in expr_line.iter() {
        token.borrow_mut().column += shift;
    }
    expr_line.splice(0..0, prefix_line.iter().cloned());
    let mut anchor_tokens = prefix.anchor_tokens.clone().unwrap_or_default();
    let mut anchor_tok_col = prefix.anchor_tok_col.clone().unwrap_or_default();
    for index in prefix_lines..expr.tokens.len() {
        let old = index - prefix_lines + 1;
        anchor_tokens.push(
            expr.anchor_tokens
                .as_ref()
                .and_then(|anchors| anchors.get(old).cloned().flatten()),
        );
        anchor_tok_col.push(
            expr.anchor_tok_col
                .as_ref()
                .and_then(|columns| columns.get(old).copied())
                .unwrap_or(0),
        );
    }
    expr.anchor_tokens = Some(anchor_tokens);
    expr.anchor_tok_col = Some(anchor_tok_col);
    renormalize_expr(expr)
}

pub fn is_one_token_expr(expr: &Expr) -> bool {
    expr.tokens.len() == 1 && expr.tokens[0].len() == 1
}

pub fn get_token_at(expr: &Expr, coord: Coord) -> Result<Token, PcalError> {
    Ok(get_element(get_element(&expr.tokens, coord.line)?, coord.item)?.clone())
}

fn get_line_length(expr: &Expr, line: i64) -> i64 {
    usize::try_from(line)
        .ok()
        .and_then(|line| expr.tokens.get(line))
        .map_or(0, |line| line.len() as i64)
}

/// TLAExpr.stepCoord: the coordinates steps tokens after coord, or none past the end.
pub fn step_coord(expr: &Expr, coord: Coord, steps: i64) -> Result<Option<Coord>, PcalError> {
    let lines = expr.tokens.len() as i64;
    if lines <= coord.line {
        return Err(bug("TLAExpr.StepCoord called with line too big"));
    }
    if get_line_length(expr, coord.line) <= coord.item {
        return Err(bug("TLAExpr.StepCoord called with col too big"));
    }
    let mut result = coord;
    for _ in 0..steps {
        result.item += 1;
        if get_line_length(expr, result.line) == result.item {
            result.item = 0;
            result.line += 1;
            while result.line < lines && get_line_length(expr, result.line) == 0 {
                result.line += 1;
            }
            if result.line == lines {
                return Ok(None);
            }
        }
    }
    Ok(Some(result))
}

/// TLAExpr.findNextInstanceIn: the next token id at or after start that is not a record field
/// name, such as the a in r.a, [a |-> 1] or [a : S].
fn find_next_instance(expr: &Expr, id: &str, start: Coord) -> Result<Option<Coord>, PcalError> {
    let mut coord = if expr.tokens.is_empty() {
        None
    } else {
        Some(start)
    };
    while let Some(current) = coord {
        let token = get_token_at(expr, current)?;
        let (is_string, string) = {
            let token = token.borrow();
            (token.kind == STRING, token.string.clone())
        };
        if !is_string && string == id {
            return Ok(Some(current));
        }
        let after_next = if !is_string && (string == "[" || string == ",") {
            step_coord(expr, current, 2)?
        } else {
            None
        };
        let is_field_name = match after_next {
            None => false,
            Some(after_next) => {
                let field_end = get_token_at(expr, after_next)?;
                let field_end = field_end.borrow();
                field_end.kind != STRING && [":", "|->", "↦"].contains(&field_end.string.as_str())
            }
        };
        let steps = if is_string {
            1
        } else if string == "." {
            2
        } else if is_field_name {
            3
        } else {
            1
        };
        coord = step_coord(expr, current, steps)?;
    }
    Ok(None)
}

fn get_line_mut(expr: &mut Expr, line: i64) -> Result<&mut Vec<Token>, PcalError> {
    usize::try_from(line)
        .ok()
        .and_then(|position| expr.tokens.get_mut(position))
        .ok_or_else(|| runtime(format!("ArrayIndexOutOfBoundsException: {line}")))
}

/// TLAExpr.substituteAt: replaces the token at coord with a copy of replacement, parenthesized
/// when is_parenthesized and replacement has more than one token, and returns the coordinates of
/// the token after it.
fn substitute_at(
    expr: &mut Expr,
    replacement: &Expr,
    coord: Coord,
    is_parenthesized: bool,
) -> Result<Option<Coord>, PcalError> {
    let token = get_token_at(expr, coord)?;
    if is_one_token_expr(expr) {
        let cloned = clone_expr(replacement);
        *expr = cloned;
        return Ok(None);
    }
    let item = coord.item as usize;
    let token_line = get_line_mut(expr, coord.line)?;
    let spaces = match token_line.get(item + 1) {
        Some(next) => next.borrow().column - (token.borrow().column + get_token_width(&token)),
        None => 0,
    };
    let rest_of_line: Vec<Token> = token_line.split_off(item + 1);
    let mut line_index = coord.line;
    let mut indent = i64::from(is_parenthesized) + token.borrow().column;
    let mut is_inserting = !is_parenthesized;
    if is_one_token_expr(replacement) {
        let replacement_token = replacement.tokens[0][0].borrow();
        let mut token = token.borrow_mut();
        token.string = replacement_token.string.clone();
        token.kind = replacement_token.kind;
    } else {
        if is_parenthesized {
            let mut token = token.borrow_mut();
            token.string = "(".to_owned();
            token.kind = BUILTIN;
        }
        let new_expr = clone_expr(replacement);
        for (index, replacement_line) in new_expr.tokens.iter().enumerate() {
            for next_token in replacement_line {
                next_token.borrow_mut().column += indent;
                if !is_inserting {
                    get_line_mut(expr, line_index)?.push(next_token.clone());
                    continue;
                }
                let next_token = next_token.borrow();
                let mut token = token.borrow_mut();
                token.string = next_token.string.clone();
                token.kind = next_token.kind;
                is_inserting = false;
            }
            if index + 1 >= new_expr.tokens.len() {
                continue;
            }
            indent = 0;
            line_index += 1;
            let current_line = line_index as usize;
            if current_line > expr.tokens.len() {
                return Err(runtime(format!(
                    "ArrayIndexOutOfBoundsException: {current_line}"
                )));
            }
            expr.tokens.insert(current_line, Vec::new());
            let old_anchors = expr.anchor_tokens.take().unwrap_or_default();
            let old_columns = expr.anchor_tok_col.take().unwrap_or_default();
            let count = expr.tokens.len();
            let new_anchor = new_expr
                .anchor_tokens
                .as_ref()
                .and_then(|anchors| anchors.get(index + 1).cloned().flatten());
            let new_column = new_expr
                .anchor_tok_col
                .as_ref()
                .and_then(|columns| columns.get(index + 1).copied())
                .unwrap_or(0);
            expr.anchor_tokens = Some(
                (0..count)
                    .map(|item| match item.cmp(&current_line) {
                        std::cmp::Ordering::Less => old_anchors.get(item).cloned().flatten(),
                        std::cmp::Ordering::Equal => new_anchor.clone(),
                        std::cmp::Ordering::Greater => old_anchors.get(item - 1).cloned().flatten(),
                    })
                    .collect(),
            );
            expr.anchor_tok_col = Some(
                (0..count)
                    .map(|item| match item.cmp(&current_line) {
                        std::cmp::Ordering::Less => old_columns.get(item).copied().unwrap_or(0),
                        std::cmp::Ordering::Equal => new_column,
                        std::cmp::Ordering::Greater => {
                            old_columns.get(item - 1).copied().unwrap_or(0)
                        }
                    })
                    .collect(),
            );
        }
        if is_parenthesized {
            let line = get_line_mut(expr, line_index)?;
            let column = match line.last() {
                Some(last) => last.borrow().column + get_token_width(last),
                None => return Err(runtime("ArrayIndexOutOfBoundsException: -1".to_owned())),
            };
            line.push(create_token(")", column, BUILTIN));
        }
    }
    let line = get_line_mut(expr, line_index)?;
    let result = Coord {
        line: line_index,
        item: line.len() as i64 - 1,
    };
    if let (Some(first), Some(previous)) = (rest_of_line.first(), line.last()) {
        let shift =
            previous.borrow().column + get_token_width(previous) + spaces - first.borrow().column;
        for old_token in rest_of_line {
            old_token.borrow_mut().column += shift;
            line.push(old_token);
        }
    }
    renormalize_expr(expr)?;
    step_coord(expr, result, 1)
}

/// TLAExpr.substituteForAll: replaces each instance of names[i] with exprs[i], in the order the
/// instances appear.
pub fn substitute_expr(
    expr: &mut Expr,
    exprs: &[Expr],
    names: &[String],
    is_parenthesized: bool,
) -> Result<(), PcalError> {
    let mut next = Vec::new();
    for name in names {
        next.push(find_next_instance(expr, name, Coord { line: 0, item: 0 })?);
    }
    loop {
        let mut nearest: Option<(usize, Coord)> = None;
        for (index, position) in next.iter().enumerate() {
            let Some(position) = *position else {
                continue;
            };
            let is_nearer = match nearest {
                None => true,
                Some((_, best)) => {
                    position.line < best.line
                        || (position.line == best.line && position.item < best.item)
                }
            };
            if is_nearer {
                nearest = Some((index, position));
            }
        }
        let Some((nearest_index, nearest_position)) = nearest else {
            return Ok(());
        };
        let after_next = step_coord(expr, nearest_position, 1)?;
        let new_position = substitute_at(
            expr,
            &exprs[nearest_index],
            nearest_position,
            is_parenthesized,
        )?;
        next[nearest_index] = match new_position {
            None => None,
            Some(new_position) => find_next_instance(expr, &names[nearest_index], new_position)?,
        };
        for (index, position) in next.iter_mut().enumerate() {
            let (Some(position), Some(new_position)) = (position.as_mut(), new_position) else {
                continue;
            };
            if index == nearest_index {
                continue;
            }
            // HACK: TLAExpr.substituteForAll dereferences afterNextPos without checking for null,
            // which throws a NullPointerException when the substituted token ends the expression.
            let Some(after_next) = after_next else {
                return Err(runtime(
                    "NullPointerException: TLAExpr.substituteForAll".to_owned(),
                ));
            };
            if position.line == nearest_position.line {
                position.item += new_position.item - after_next.item;
            }
            position.line += new_position.line - after_next.line;
        }
    }
}

pub fn get_substituted_expr(
    expr: &Expr,
    args: &[Expr],
    params: &[String],
) -> Result<Expr, PcalError> {
    let mut result = clone_expr(expr);
    substitute_expr(&mut result, args, params, true)?;
    Ok(result)
}

/// TLAExpr.toString, which names the column of a junction except in TLC 1.7.4.
fn format_expr(out: &mut String, expr: &Expr, version: TlcVersion) {
    let first_token_line = expr.tokens.iter().position(|line| !line.is_empty());
    out.push_str("<< ");
    for (index, line) in expr.tokens.iter().enumerate() {
        if index > 0 {
            out.push('\n');
        }
        let is_after_token = first_token_line.is_some_and(|first| index > first);
        for (item, token) in line.iter().enumerate() {
            if is_after_token || item > 0 {
                out.push_str(", ");
            }
            let token = token.borrow();
            let column = if version == TlcVersion::V1_7_4 {
                String::new()
            } else {
                format!("(col{}) ", token.column)
            };
            if token.kind == STRING {
                out.push_str("\"\\\"\", \"");
                out.push_str(&token.string);
                out.push_str("\", \"\\\"\"");
            } else if token.string == "\\/" {
                out.push_str(&format!("\"{column}\\\\/\""));
            } else if token.string.starts_with('\\') {
                out.push_str(&format!("\"\\{}\"", token.string));
            } else if token.string == "/\\" {
                out.push_str(&format!("\"{column}/\\\\\""));
            } else {
                out.push_str(&format!("\"{}\"", token.string));
            }
        }
    }
    out.push_str(" >>");
}

/// AST.toString's Indent, EndIndent and NewLine, which keep a stack of indentation columns as
/// the Java concatenates a record's text left to right.
struct Formatter {
    out: String,
    columns: Vec<i64>,
    depth: usize,
    is_old_version: bool,
    version: TlcVersion,
}

impl Formatter {
    fn text(&mut self, text: &str) {
        self.out.push_str(text);
    }

    fn indent(&mut self, text: &str) {
        let column = self.columns[self.depth] + get_java_length(text);
        self.columns.truncate(self.depth + 1);
        self.columns.push(column);
        self.depth += 1;
        self.out.push_str(text);
    }

    fn end_indent(&mut self) {
        self.depth -= 1;
    }

    fn new_line(&mut self) {
        let column = self.columns[self.depth].max(0) as usize;
        self.out.push('\n');
        self.out.push_str(&" ".repeat(column));
    }

    fn expr(&mut self, expr: &Expr) {
        format_expr(&mut self.out, expr, self.version);
    }

    fn quoted(&mut self, text: &str) {
        self.out.push('"');
        self.out.push_str(text);
        self.out.push('"');
    }

    /// The separators' new lines take the indentation the elements before them leave.
    fn seq<T>(&mut self, items: &[T], each: impl Fn(&mut Self, &T)) {
        self.indent("<<");
        for (index, item) in items.iter().enumerate() {
            if index > 0 {
                self.text(", ");
                self.new_line();
            }
            each(self, item);
        }
        self.text(">>");
        self.end_indent();
    }

    fn stmts(&mut self, stmts: &[StmtRef]) {
        self.seq(stmts, |this, stmt| this.stmt(stmt));
    }

    fn exprs(&mut self, exprs: &[Expr]) {
        self.seq(exprs, |this, expr| this.expr(expr));
    }

    fn quoted_seq(&mut self, items: &[String]) {
        self.indent("<<");
        let text = items
            .iter()
            .map(|item| format!("\"{item}\""))
            .collect::<Vec<_>>()
            .join(", ");
        self.text(&text);
        self.text(">>");
        self.end_indent();
    }

    fn eq_or_in(&mut self, is_eq: bool) {
        self.text(if is_eq { "\"=\"" } else { "\"\\\\in\"" });
    }

    fn labels(&mut self, minus: &[String], plus: &[String], called: &[String]) {
        self.text("minusLabels |-> ");
        self.quoted_seq(minus);
        self.text(", plusLabels |->");
        self.quoted_seq(plus);
        self.text(", proceduresCalled |->");
        self.quoted_seq(called);
    }

    fn var_decl(&mut self, decl: &VarDecl) {
        self.indent("");
        self.text("[var |-> ");
        self.quoted(&decl.var);
        self.text(", eqOrIn |-> ");
        self.eq_or_in(decl.is_eq);
        self.text(", val |-> ");
        self.expr(&decl.val);
        self.text("]");
        self.end_indent();
    }

    fn pvar_decl(&mut self, decl: &VarDecl) {
        self.indent("");
        self.text("[var |-> ");
        self.quoted(&decl.var);
        self.text(", eqOrIn |-> \"=\", val |-> ");
        self.expr(&decl.val);
        self.text("]");
        self.end_indent();
    }

    fn procedure(&mut self, procedure: &Procedure) {
        self.indent("");
        self.text("[name   |-> ");
        self.quoted(&procedure.name);
        self.text(", ");
        self.new_line();
        if !self.is_old_version {
            self.labels(
                &procedure.minus_labels,
                &procedure.plus_labels,
                &procedure.procedures_called,
            );
            self.text(",");
            self.new_line();
        }
        self.indent(" params |-> ");
        self.seq(&procedure.params, Self::pvar_decl);
        self.text(",");
        self.end_indent();
        self.new_line();
        self.indent(" decls  |-> ");
        self.seq(&procedure.decls, Self::pvar_decl);
        self.text(",");
        self.end_indent();
        self.new_line();
        self.indent(" body   |-> ");
        self.stmts(&procedure.body);
        self.text("]");
        self.end_indent();
        self.end_indent();
    }

    fn process(&mut self, process: &Process) {
        self.indent("");
        self.text("[name   |-> ");
        self.quoted(&process.name);
        if self.is_old_version {
            self.text(", ");
        } else {
            self.text(",");
            self.new_line();
            self.text(" fairness |-> ");
            self.quoted(FAIRNESS[process.fairness]);
            self.text(", ");
            self.labels(
                &process.minus_labels,
                &process.plus_labels,
                &process.procedures_called,
            );
            self.text(",");
        }
        self.new_line();
        self.text(" eqOrIn |-> ");
        self.eq_or_in(process.is_eq);
        self.text(",");
        self.new_line();
        self.text(" id     |-> ");
        self.expr(&process.id);
        self.text(",");
        self.new_line();
        self.indent(" decls  |-> ");
        self.seq(&process.decls, Self::var_decl);
        self.text(",");
        self.end_indent();
        self.new_line();
        self.indent(" body   |-> ");
        self.stmts(&process.body);
        self.text("]");
        self.end_indent();
        self.end_indent();
    }

    fn single_assign(&mut self, assign: &SingleAssign) {
        self.indent("");
        self.text("[lhs |-> [var |-> ");
        self.quoted(&assign.var);
        self.text(", sub |-> ");
        self.expr(&assign.sub);
        self.text("],");
        self.new_line();
        self.text(" rhs |-> ");
        self.expr(&assign.rhs);
        self.text("]");
        self.end_indent();
    }

    fn call_args(&mut self, args: &[Expr]) {
        self.indent("args     |-> ");
        self.exprs(args);
        self.text("]");
        self.new_line();
        self.end_indent();
        self.end_indent();
    }

    fn stmt(&mut self, stmt: &StmtRef) {
        let stmt = stmt.borrow();
        match &stmt.kind {
            StmtKind::LabeledStmt { label, stmts } => {
                self.indent("");
                self.text("[label |-> ");
                self.quoted(label);
                self.text(",");
                self.new_line();
                self.indent(" stmts |-> ");
                self.stmts(stmts);
                self.text("]");
                self.end_indent();
                self.end_indent();
            }
            StmtKind::While {
                test,
                unlab_do,
                lab_do,
            } => {
                self.indent("");
                self.text("[type    |-> \"while\", ");
                self.new_line();
                self.text(" test    |-> ");
                self.expr(test);
                self.text(",");
                self.new_line();
                self.indent(" labDo   |-> ");
                self.stmts(lab_do);
                self.text(",");
                self.end_indent();
                self.new_line();
                self.indent(" unlabDo |-> ");
                self.stmts(unlab_do);
                self.text("]");
                self.end_indent();
                self.end_indent();
            }
            StmtKind::Assign { ass } => {
                self.indent("");
                self.text("[type |-> \"assignment\",");
                self.new_line();
                self.indent(" ass  |-> ");
                self.seq(ass, Self::single_assign);
                self.text("]");
                self.end_indent();
                self.end_indent();
            }
            StmtKind::If { test, then, els } => {
                self.indent("");
                self.text("[type    |-> \"if\", ");
                self.new_line();
                self.text(" test    |-> ");
                self.expr(test);
                self.text(",");
                self.new_line();
                self.indent(" then |-> ");
                self.stmts(then);
                self.text(",");
                self.end_indent();
                self.new_line();
                self.indent(" else |-> ");
                self.stmts(els);
                self.text("]");
                self.end_indent();
                self.end_indent();
            }
            StmtKind::Either { ors } => {
                self.indent("");
                self.text("[type |-> \"either\", ");
                self.new_line();
                self.indent(" ors  |-> ");
                self.indent("<< ");
                for (index, or) in ors.iter().enumerate() {
                    if index > 0 {
                        self.text(", ");
                        self.new_line();
                    }
                    self.stmts(or);
                }
                self.text(" >>");
                self.end_indent();
                self.text("]");
                self.end_indent();
                self.end_indent();
            }
            StmtKind::With {
                var,
                is_eq,
                exp,
                body,
            } => {
                self.indent("");
                self.text("[type   |-> \"with\", ");
                self.new_line();
                self.text(" var    |-> ");
                self.quoted(var);
                self.text(",");
                self.new_line();
                self.text(" eqOrIn |-> ");
                self.eq_or_in(*is_eq);
                self.text(",");
                self.new_line();
                self.text(" exp    |-> ");
                self.expr(exp);
                self.text(",");
                self.new_line();
                self.indent(" do     |-> ");
                self.stmts(body);
                self.text("]");
                self.end_indent();
                self.end_indent();
            }
            StmtKind::When(exp) | StmtKind::PrintS(exp) | StmtKind::Assert(exp) => {
                let name = match &stmt.kind {
                    StmtKind::When(_) => "when",
                    StmtKind::PrintS(_) => "print",
                    _ => "assert",
                };
                self.indent("");
                self.text(&format!("[type |-> \"{name}\", "));
                self.new_line();
                self.text(" exp |-> ");
                self.expr(exp);
                self.text("]");
                self.end_indent();
            }
            StmtKind::Skip => self.text("[type |-> \"skip\"]"),
            StmtKind::LabelIf {
                test,
                unlab_then,
                lab_then,
                unlab_else,
                lab_else,
            } => {
                self.indent("");
                self.text("[type      |-> \"labelIf\",");
                self.new_line();
                self.text(" test      |-> ");
                self.expr(test);
                self.text(",");
                self.new_line();
                self.indent(" unlabThen |-> ");
                self.stmts(unlab_then);
                self.text(",");
                self.end_indent();
                self.new_line();
                self.indent(" labThen   |-> ");
                self.stmts(lab_then);
                self.text(",");
                self.end_indent();
                self.new_line();
                self.indent(" unlabElse |-> ");
                self.stmts(unlab_else);
                self.text(",");
                self.end_indent();
                self.new_line();
                self.indent(" labElse   |-> ");
                self.stmts(lab_else);
                self.text("]");
                self.end_indent();
                self.new_line();
                self.end_indent();
            }
            StmtKind::LabelEither { clauses } => {
                self.indent("");
                self.text("[type    |-> \"labelEither\",");
                self.new_line();
                self.indent(" clauses |-> ");
                self.seq(clauses, |this, clause| {
                    this.indent("");
                    this.indent("[unlabOr |-> ");
                    this.stmts(&clause.unlab_or);
                    this.text(",");
                    this.end_indent();
                    this.new_line();
                    this.indent(" labOr   |-> ");
                    this.stmts(&clause.lab_or);
                    this.text("]");
                    this.end_indent();
                    this.new_line();
                    this.end_indent();
                });
                self.text("]");
                self.end_indent();
                self.new_line();
                self.end_indent();
            }
            StmtKind::Call {
                return_to,
                to,
                args,
            } => {
                self.indent("");
                self.text("[type     |-> \"call\",");
                self.new_line();
                self.text(" returnTo |-> ");
                self.quoted(return_to);
                self.text(",");
                self.new_line();
                self.text(" to       |-> ");
                self.quoted(to);
                self.text(",");
                self.new_line();
                self.indent(" args     |-> ");
                self.exprs(args);
                self.text("]");
                self.end_indent();
                self.end_indent();
            }
            StmtKind::Return { from } => {
                self.text("[type |-> \"return\", from |-> ");
                self.quoted(from.as_deref().unwrap_or("null"));
                self.text("]");
            }
            StmtKind::CallReturn { from, to, args } => {
                self.indent("");
                self.text("[type     |-> \"callReturn\",");
                self.new_line();
                self.text(" from     |-> ");
                self.quoted(from.as_deref().unwrap_or("null"));
                self.text(",");
                self.new_line();
                self.text(" to       |-> ");
                self.quoted(to);
                self.text(",");
                self.new_line();
                self.call_args(args);
            }
            StmtKind::CallGoto { after, to, args } => {
                self.indent("");
                self.text("[type     |-> \"callGoto\",");
                self.new_line();
                self.text(" after    |-> ");
                self.quoted(after);
                self.text(",");
                self.new_line();
                self.text(" to       |-> ");
                self.quoted(to);
                self.text(",");
                self.new_line();
                self.call_args(args);
            }
            StmtKind::Goto { to } => {
                self.text("[type |-> \"goto\",  to |-> ");
                self.quoted(to);
                self.text("]");
            }
            StmtKind::MacroCall { name, args } => {
                self.indent("");
                self.text("[type |-> \"macrocall\",");
                self.new_line();
                self.text(" name |-> ");
                self.quoted(name);
                self.text(",");
                self.new_line();
                self.indent(" args     |-> ");
                self.exprs(args);
                self.text("]");
                self.end_indent();
                self.end_indent();
            }
        }
    }

    fn algorithm(&mut self, algorithm: &Algorithm) {
        self.indent("");
        let (kind, decls, defs, prcds, last) = match &algorithm.body {
            AlgorithmBody::Uniprocess(_) => (
                "[type     |-> \"uniprocess\", ",
                " decls  |-> ",
                " defs   |-> ",
                " prcds  |-> ",
                " body  |-> ",
            ),
            AlgorithmBody::Multiprocess(_) => (
                "[type    |-> \"multiprocess\", ",
                " decls |-> ",
                " defs  |-> ",
                " prcds |-> ",
                " procs |-> ",
            ),
        };
        self.text(kind);
        self.new_line();
        self.text(" name  |-> ");
        self.quoted(&algorithm.name);
        self.text(", ");
        self.new_line();
        self.indent(decls);
        self.seq(&algorithm.decls, Self::var_decl);
        self.text(",");
        self.end_indent();
        self.new_line();
        self.indent(defs);
        self.expr(&algorithm.defs);
        self.text(",");
        self.end_indent();
        self.new_line();
        self.indent(prcds);
        self.seq(&algorithm.prcds, Self::procedure);
        self.text(",");
        self.end_indent();
        self.new_line();
        self.indent(last);
        match &algorithm.body {
            AlgorithmBody::Uniprocess(body) => self.stmts(body),
            AlgorithmBody::Multiprocess(procs) => self.seq(procs, Self::process),
        }
        self.text("]");
        self.end_indent();
        self.end_indent();
    }
}

/// AST.toString: the TLA+ record that PlusCal.tla uses for the algorithm.
pub fn format_algorithm(
    algorithm: &Algorithm,
    input_version_number: f64,
    version: TlcVersion,
) -> String {
    let mut formatter = Formatter {
        out: String::new(),
        columns: vec![0],
        depth: 0,
        is_old_version: input_version_number < 1500.0,
        version,
    };
    formatter.algorithm(algorithm);
    formatter.out
}

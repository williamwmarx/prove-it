//! What the translation does to the AST and the errors it reports, as `src/pcal/translate.ts`
//! ports `pcal.PcalSymTab`, `PcalFixIDs`, `PcalTranslate.Explode` and the checks of `PcalTLAGen`.

use std::cmp::Ordering;

use super::ast::{
    ADDED, Algorithm, AlgorithmBody, BUILTIN, Expr, IDENT, Position, Procedure, Process, STRING,
    SingleAssign, StmtKind, StmtRef, Token, VarDecl, check_labeled, create_expr,
    create_normalized_expr, create_stmt, create_token, get_element, get_label, get_labeled_stmts,
    get_token_width, normalize_expr, substitute_expr,
};
use super::{PcalError, bug, error, error_at};

/// PcalSymTab's symbol types, which index TYPE_NAMES.
const GLOBAL: usize = 0;
const LABEL: usize = 1;
const PROCEDURE: usize = 2;
const PROCESS: usize = 3;
const PROCESS_VAR: usize = 4;
const PROCEDURE_VAR: usize = 5;
const PARAMETER: usize = 6;

/// PcalSymTab.Disambiguate loops one type past the last, as num_vtypes is 7.
const TYPE_COUNT: usize = 7;

const TYPE_NAMES: [&str; 7] = [
    "Global variable",
    "Label",
    "Procedure",
    "Process",
    "Process variable",
    "Procedure variable",
    "Parameter",
];

fn is_variable_symbol(kind: usize) -> bool {
    [GLOBAL, PROCESS_VAR, PROCEDURE_VAR, PARAMETER].contains(&kind)
}

struct Symbol {
    kind: usize,
    id: String,
    context: String,
    use_this: String,
}

/// PcalSymTab.ProcedureEntry, whose parameters and variables are those of the procedure at
/// index. initial_pc is the first label, which a body with no statements lacks.
struct ProcedureEntry {
    name: String,
    index: usize,
    initial_pc: Option<String>,
}

#[derive(Default)]
struct SymbolTable {
    symbols: Vec<Symbol>,
    procedures: Vec<ProcedureEntry>,
    process_names: Vec<String>,
    error_report: String,
}

impl SymbolTable {
    fn find_symbol(&self, kind: usize, id: &str, context: &str) -> Option<&Symbol> {
        self.symbols
            .iter()
            .find(|symbol| symbol.id == id && symbol.context == context && symbol.kind == kind)
    }

    fn find_symbol_in_context(&self, id: &str, context: &str) -> Option<&Symbol> {
        self.symbols
            .iter()
            .find(|symbol| symbol.id == id && symbol.context == context)
    }

    /// PcalSymTab.FindProc returns the number of procedures when it finds none.
    fn find_procedure_index(&self, name: &str) -> usize {
        self.procedures
            .iter()
            .position(|procedure| procedure.name == name)
            .unwrap_or(self.procedures.len())
    }

    fn insert_symbol(&mut self, kind: usize, id: &str, context: &str) -> bool {
        let is_variable = [PROCEDURE_VAR, PROCESS_VAR, PARAMETER].contains(&kind);
        let is_defined = if is_variable {
            self.find_symbol(GLOBAL, id, "").is_some()
                || self.find_symbol_in_context(id, context).is_some()
        } else {
            self.find_symbol(kind, id, context).is_some()
        };
        if is_defined {
            return false;
        }
        self.symbols.push(Symbol {
            kind,
            id: id.to_owned(),
            context: context.to_owned(),
            use_this: id.to_owned(),
        });
        true
    }

    fn use_this(&self, kind: usize, id: &str, context: &str) -> String {
        self.find_symbol(kind, id, context)
            .map_or(id, |symbol| symbol.use_this.as_str())
            .to_owned()
    }

    fn use_this_var(&self, id: &str, context: &str) -> String {
        match self.find_symbol_in_context(id, context) {
            Some(symbol) if is_variable_symbol(symbol.kind) => symbol.use_this.clone(),
            _ => id.to_owned(),
        }
    }

    fn extract_labeled_stmt(&mut self, labeled: &StmtRef, context: &str) -> Result<(), PcalError> {
        let (label, pos) = {
            let borrowed = labeled.borrow();
            (get_label(labeled), borrowed.pos)
        };
        if !self.insert_symbol(LABEL, &label, context) {
            self.error_report.push_str(&format!(
                "\nLabel {label} redefined at line {}, column {}",
                pos.line, pos.col
            ));
        }
        for stmt in get_labeled_stmts(labeled) {
            self.extract_stmt(&stmt, context)?;
        }
        Ok(())
    }

    fn extract_stmt(&mut self, stmt: &StmtRef, context: &str) -> Result<(), PcalError> {
        let (stmts, labeled): (Vec<StmtRef>, Vec<StmtRef>) = match &stmt.borrow().kind {
            StmtKind::While {
                unlab_do, lab_do, ..
            } => (unlab_do.clone(), lab_do.clone()),
            StmtKind::If { then, els, .. } => {
                (then.iter().chain(els).cloned().collect(), Vec::new())
            }
            StmtKind::With { body, .. } => (body.clone(), Vec::new()),
            StmtKind::Either { ors } => (ors.iter().flatten().cloned().collect(), Vec::new()),
            StmtKind::LabelIf {
                unlab_then,
                lab_then,
                unlab_else,
                lab_else,
                ..
            } => {
                // The Java extracts the then clause's statements and labeled statements before
                // the else clause's.
                for inner in unlab_then {
                    self.extract_stmt(inner, context)?;
                }
                for inner in lab_then {
                    self.extract_labeled_stmt(inner, context)?;
                }
                (unlab_else.clone(), lab_else.clone())
            }
            StmtKind::LabelEither { clauses } => {
                for clause in clauses {
                    for inner in &clause.unlab_or {
                        self.extract_stmt(inner, context)?;
                    }
                    for inner in &clause.lab_or {
                        self.extract_labeled_stmt(inner, context)?;
                    }
                }
                (Vec::new(), Vec::new())
            }
            StmtKind::Assign { .. }
            | StmtKind::When(_)
            | StmtKind::PrintS(_)
            | StmtKind::Assert(_)
            | StmtKind::Skip
            | StmtKind::Call { .. }
            | StmtKind::Return { .. }
            | StmtKind::CallReturn { .. }
            | StmtKind::CallGoto { .. }
            | StmtKind::Goto { .. } => (Vec::new(), Vec::new()),
            other => return Err(bug(&format!("Unexpected AST type {}", other.name()))),
        };
        for inner in &stmts {
            self.extract_stmt(inner, context)?;
        }
        for inner in &labeled {
            self.extract_labeled_stmt(inner, context)?;
        }
        Ok(())
    }

    fn extract_var_decl(&mut self, decl: &VarDecl, context: &str, kind: usize) {
        if !self.insert_symbol(kind, &decl.var, context) {
            self.error_report.push_str(&format!(
                "\n{} {} redefined at line {}, column {}",
                TYPE_NAMES[kind], decl.var, decl.pos.line, decl.pos.col
            ));
        }
    }

    fn extract_body(&mut self, body: &[StmtRef], context: &str) -> Result<(), PcalError> {
        for stmt in body {
            check_labeled(stmt)?;
            self.extract_labeled_stmt(stmt, context)?;
        }
        Ok(())
    }

    fn extract_procedure(&mut self, procedure: &Procedure, index: usize) -> Result<(), PcalError> {
        let is_redefined = self.find_procedure_index(&procedure.name) < self.procedures.len();
        if is_redefined {
            self.error_report.push_str(&format!(
                "\nProcedure {} redefined at line {}, column {}",
                procedure.name, procedure.pos.line, procedure.pos.col
            ));
        } else {
            let initial_pc = match procedure.body.first() {
                None => None,
                Some(first) => {
                    check_labeled(first)?;
                    Some(get_label(first))
                }
            };
            self.procedures.push(ProcedureEntry {
                name: procedure.name.clone(),
                index,
                initial_pc,
            });
        }
        self.insert_symbol(PROCEDURE, &procedure.name, "");
        for decl in &procedure.decls {
            self.extract_var_decl(decl, &procedure.name, PROCEDURE_VAR);
        }
        for param in &procedure.params {
            self.extract_var_decl(param, &procedure.name, PARAMETER);
        }
        self.extract_body(&procedure.body, &procedure.name)
    }

    fn extract_process(&mut self, process: &Process) -> Result<(), PcalError> {
        if self.process_names.contains(&process.name) {
            self.error_report.push_str(&format!(
                "\nProcess {} redefined at line {}, column {}",
                process.name, process.pos.line, process.pos.col
            ));
        } else {
            self.process_names.push(process.name.clone());
        }
        self.insert_symbol(PROCESS, &process.name, "");
        for decl in &process.decls {
            self.extract_var_decl(decl, &process.name, PROCESS_VAR);
        }
        self.extract_body(&process.body, &process.name)
    }

    /// The PcalSymTab constructor: collects the algorithm's variables, labels, procedures and
    /// processes, reporting every redefinition at once.
    fn create(ast: &Algorithm) -> Result<SymbolTable, PcalError> {
        let mut table = SymbolTable::default();
        table.insert_symbol(GLOBAL, "pc", "");
        if !ast.prcds.is_empty() {
            table.insert_symbol(GLOBAL, "stack", "");
        }
        for decl in &ast.decls {
            table.extract_var_decl(decl, "", GLOBAL);
        }
        for (index, procedure) in ast.prcds.iter().enumerate() {
            table.extract_procedure(procedure, index)?;
        }
        match &ast.body {
            AlgorithmBody::Multiprocess(procs) => {
                for process in procs {
                    table.extract_process(process)?;
                }
            }
            AlgorithmBody::Uniprocess(body) => table.extract_body(body, "")?,
        }
        if !table.error_report.is_empty() {
            return Err(error(&table.error_report));
        }
        Ok(table)
    }

    /// PcalSymTab.Disambiguate: renames each symbol whose name another symbol already uses, by
    /// appending "_", then the letters of its context, then its type. Returns whether it renamed
    /// any.
    fn disambiguate(&mut self) -> bool {
        let mut is_any = false;
        for kind in 0..=TYPE_COUNT {
            for index in 0..self.symbols.len() {
                if self.symbols[index].kind != kind {
                    continue;
                }
                let mut use_this = self.symbols[index].id.clone();
                self.symbols[index].use_this = use_this.clone();
                let context: Vec<char> = self.symbols[index].context.chars().collect();
                let mut suffix_length = 1;
                while kind > 0
                    && self
                        .symbols
                        .iter()
                        .filter(|symbol| symbol.use_this == use_this)
                        .count()
                        > 1
                {
                    if suffix_length == 1 {
                        use_this.push('_');
                    } else {
                        match context.get(suffix_length - 2) {
                            Some(char) => use_this.push(*char),
                            None => use_this.push_str(&kind.to_string()),
                        }
                    }
                    self.symbols[index].use_this = use_this.clone();
                    suffix_length += 1;
                }
                if self.symbols[index].id != use_this {
                    is_any = true;
                }
            }
        }
        is_any
    }

    /// PcalSymTab.CheckForDefaultInitValue.
    fn check_for_default_init_value(&self) -> Result<(), PcalError> {
        let uses: Vec<String> = self
            .symbols
            .iter()
            .filter(|symbol| symbol.id == "defaultInitValue")
            .map(|symbol| format!("{} name", TYPE_NAMES[symbol.kind]))
            .collect();
        if uses.is_empty() {
            return Ok(());
        }
        Err(error(&format!(
            "Cannot use `defaultInitValue' as {}",
            uses.join(" or ")
        )))
    }
}

/// PcalTranslate's token constructors, which leave the column 0.
fn string_token(string: &str) -> Token {
    create_token(string, 0, STRING)
}

fn added_token(string: &str) -> Token {
    create_token(string, 0, ADDED)
}

fn built_in_token(string: &str) -> Token {
    create_token(string, 0, BUILTIN)
}

fn ident_token(string: &str) -> Token {
    create_token(string, 0, IDENT)
}

/// PcalFixIDs.Fix: replaces every identifier with the name PcalSymTab.Disambiguate chose for it,
/// and closes each process's set of called procedures over the procedures they call.
struct Fixer<'a> {
    table: &'a mut SymbolTable,
    log: &'a mut Vec<String>,
}

impl Fixer<'_> {
    fn fix_expr(&self, expr: &mut Expr, context: &str) -> Result<(), PcalError> {
        let mut names: Vec<String> = Vec::new();
        let mut replacements = Vec::new();
        for token in expr.tokens.iter().flatten() {
            let token = token.borrow();
            if token.kind != IDENT {
                continue;
            }
            let use_me = self.table.use_this_var(&token.string, context);
            if names.contains(&token.string) || use_me == token.string {
                continue;
            }
            names.push(token.string.clone());
            replacements.push(create_normalized_expr(vec![vec![ident_token(&use_me)]]));
        }
        if replacements.is_empty() {
            return Ok(());
        }
        substitute_expr(expr, &replacements, &names, false)
    }

    fn fix_var_decl(&self, decl: &mut VarDecl, context: &str) -> Result<(), PcalError> {
        decl.var = self.table.use_this_var(&decl.var, context);
        self.fix_expr(&mut decl.val, context)
    }

    fn fix_labels(&self, labels: &mut [String], context: &str) {
        for label in labels {
            *label = self.table.use_this(LABEL, label, context);
        }
    }

    fn fix_stmts(&self, stmts: &[StmtRef], context: &str) -> Result<(), PcalError> {
        stmts
            .iter()
            .try_for_each(|stmt| self.fix_stmt(stmt, context))
    }

    fn fix_stmt(&self, stmt: &StmtRef, context: &str) -> Result<(), PcalError> {
        let mut borrowed = stmt.borrow_mut();
        let pos = borrowed.pos;
        let table = &*self.table;
        let use_procedure = |name: &str| table.use_this(PROCEDURE, name, context);
        match &mut borrowed.kind {
            StmtKind::LabeledStmt { label, stmts } => {
                *label = table.use_this(LABEL, label, context);
                self.fix_stmts(stmts, context)?;
            }
            StmtKind::While {
                test,
                unlab_do,
                lab_do,
            } => {
                self.fix_stmts(unlab_do, context)?;
                self.fix_stmts(lab_do, context)?;
                self.fix_expr(test, context)?;
            }
            StmtKind::Assign { ass } => {
                for assign in ass {
                    assign.var = table.use_this_var(&assign.var, context);
                    self.fix_expr(&mut assign.sub, context)?;
                    self.fix_expr(&mut assign.rhs, context)?;
                }
            }
            StmtKind::If { test, then, els } => {
                self.fix_stmts(then, context)?;
                self.fix_stmts(els, context)?;
                self.fix_expr(test, context)?;
            }
            StmtKind::With { exp, body, .. } => {
                self.fix_expr(exp, context)?;
                self.fix_stmts(body, context)?;
            }
            StmtKind::When(exp) | StmtKind::PrintS(exp) | StmtKind::Assert(exp) => {
                self.fix_expr(exp, context)?;
            }
            StmtKind::Skip => {}
            StmtKind::LabelIf {
                test,
                unlab_then,
                lab_then,
                unlab_else,
                lab_else,
            } => {
                self.fix_expr(test, context)?;
                self.fix_stmts(unlab_then, context)?;
                self.fix_stmts(lab_then, context)?;
                self.fix_stmts(unlab_else, context)?;
                self.fix_stmts(lab_else, context)?;
            }
            StmtKind::Call {
                return_to,
                to,
                args,
            } => {
                *return_to = use_procedure(return_to);
                *to = use_procedure(to);
                for arg in args {
                    self.fix_expr(arg, context)?;
                }
            }
            StmtKind::Return { from } => {
                *from = from.as_deref().map(use_procedure);
            }
            StmtKind::CallReturn { from, to, args } => {
                *from = from.as_deref().map(use_procedure);
                *to = use_procedure(to);
                for arg in args {
                    self.fix_expr(arg, context)?;
                }
            }
            StmtKind::CallGoto { after, to, args } => {
                *after = use_procedure(after);
                *to = use_procedure(to);
                for arg in args {
                    self.fix_expr(arg, context)?;
                }
            }
            StmtKind::Goto { to } => {
                if table.find_symbol(LABEL, to, context).is_none() && to != "Done" {
                    return Err(error(&format!(
                        "goto to non-existent label `{to}' at line {}, column {}",
                        pos.line, pos.col
                    )));
                }
                *to = table.use_this(LABEL, to, context);
            }
            StmtKind::Either { ors } => {
                for or in ors {
                    self.fix_stmts(or, context)?;
                }
            }
            StmtKind::LabelEither { clauses } => {
                for clause in clauses {
                    self.fix_stmts(&clause.unlab_or, context)?;
                    self.fix_stmts(&clause.lab_or, context)?;
                }
            }
            StmtKind::MacroCall { .. } => {
                return Err(bug("Unexpected AST typeMacroCall"));
            }
        }
        Ok(())
    }

    fn fix_body(&self, body: &[StmtRef], context: &str) -> Result<(), PcalError> {
        for stmt in body {
            check_labeled(stmt)?;
            self.fix_stmt(stmt, context)?;
        }
        Ok(())
    }

    fn fix_procedure(&mut self, procedure: &mut Procedure) -> Result<(), PcalError> {
        let context = procedure.name.clone();
        for decl in &mut procedure.decls {
            self.fix_var_decl(decl, &context)?;
        }
        for param in &mut procedure.params {
            self.fix_var_decl(param, &context)?;
        }
        self.fix_body(&procedure.body, &context)?;
        let index = self.table.find_procedure_index(&context) as i64;
        get_element(&self.table.procedures, index)?;
        self.fix_labels(&mut procedure.plus_labels, &context);
        self.fix_labels(&mut procedure.minus_labels, &context);
        let initial_pc = self.table.procedures[index as usize]
            .initial_pc
            .as_deref()
            .map(|label| self.table.use_this(LABEL, label, &context));
        procedure.name = self.table.use_this(PROCEDURE, &procedure.name, "");
        let entry = &mut self.table.procedures[index as usize];
        entry.initial_pc = initial_pc;
        entry.name = procedure.name.clone();
        Ok(())
    }

    fn fix_process(&self, process: &mut Process) -> Result<(), PcalError> {
        let context = process.name.clone();
        for decl in &mut process.decls {
            self.fix_var_decl(decl, &context)?;
        }
        self.fix_body(&process.body, &context)?;
        self.fix_labels(&mut process.plus_labels, &context);
        self.fix_labels(&mut process.minus_labels, &context);
        process.name = self.table.use_this(PROCESS, &process.name, "");
        Ok(())
    }

    /// PcalFixIDs.FixMultiprocess: a process calling an unknown procedure stops the fixing of
    /// the remaining processes with an error message, but not the translation.
    fn fix_multiprocess(
        &mut self,
        procedures: &mut [Procedure],
        processes: &mut [Process],
    ) -> Result<(), PcalError> {
        for procedure in procedures.iter_mut() {
            self.fix_procedure(procedure)?;
        }
        let names: Vec<String> = procedures
            .iter()
            .map(|procedure| procedure.name.clone())
            .collect();
        let mut is_called: Vec<Vec<bool>> = procedures
            .iter()
            .map(|procedure| {
                names
                    .iter()
                    .map(|name| procedure.procedures_called.contains(name))
                    .collect()
            })
            .collect();
        for middle in 0..names.len() {
            for row in 0..is_called.len() {
                for end in 0..names.len() {
                    is_called[row][end] =
                        is_called[row][end] || (is_called[row][middle] && is_called[middle][end]);
                }
            }
        }
        for (index, procedure) in procedures.iter_mut().enumerate() {
            procedure.procedures_called = names
                .iter()
                .enumerate()
                .filter(|(callee, _)| is_called[index][*callee])
                .map(|(_, name)| name.clone())
                .collect();
        }
        for process in processes {
            self.fix_process(process)?;
            // Callees appended below are themselves visited, as the Java loop rereads the size.
            let mut called_index = 0;
            while called_index < process.procedures_called.len() {
                let called = &process.procedures_called[called_index];
                let Some(procedure_index) = names.iter().position(|name| name == called) else {
                    self.log.push(format!(
                        "\nUnrecoverable error:\n -- Could not find procedure name `{called}'.\n"
                    ));
                    return Ok(());
                };
                for (callee_index, callee) in names.iter().enumerate() {
                    if is_called[procedure_index][callee_index]
                        && !process.procedures_called.contains(callee)
                    {
                        process.procedures_called.push(callee.clone());
                    }
                }
                called_index += 1;
            }
        }
        Ok(())
    }

    fn fix(&mut self, ast: &mut Algorithm) -> Result<(), PcalError> {
        for decl in &mut ast.decls {
            self.fix_var_decl(decl, "")?;
        }
        match &mut ast.body {
            AlgorithmBody::Multiprocess(procs) => self.fix_multiprocess(&mut ast.prcds, procs),
            AlgorithmBody::Uniprocess(body) => {
                for procedure in &mut ast.prcds {
                    self.fix_procedure(procedure)?;
                }
                self.fix_body(body, "")
            }
        }
    }
}

/// PcalTranslate.TokVectorToExpr: copies the tokens onto one line, spaces columns apart.
fn tokens_to_expr(tokens: &[Token], spaces: i64) -> Expr {
    let mut line: Vec<Token> = Vec::new();
    for token in tokens {
        let column = match line.last() {
            None => 0,
            Some(previous) => previous.borrow().column + get_token_width(previous) + spaces,
        };
        let token = token.borrow();
        line.push(create_token(&token.string, column, token.kind));
    }
    create_normalized_expr(vec![line])
}

/// PcalTranslate.MakeNewStackTopExprPretty: lays out a pushed stack frame one field per line
/// with the "|->" aligned.
fn prettify_stack_top_expr(expr: &Expr) {
    let count = expr.tokens.len();
    for (line_index, line) in expr.tokens.iter().enumerate() {
        let mut cursor = if line_index == 0 || line_index == count - 1 {
            1
        } else {
            6
        };
        for token in line {
            let width = get_token_width(token);
            let mut token = token.borrow_mut();
            token.column = cursor;
            cursor += width;
            if token.kind != BUILTIN {
                continue;
            }
            match token.string.as_str() {
                "|->" | "↦" => {
                    token.column = (token.column + 1).max(16);
                    cursor = token.column + 5;
                }
                "[" | "<<" => cursor += 1,
                "]" | ">>" => {
                    token.column += 1;
                    cursor += 1;
                }
                "\\o" => {
                    token.column += 1;
                    cursor += 2;
                }
                _ => {}
            }
        }
    }
}

fn create_single_assign(var: &str, sub: Expr, rhs: Expr, line: i64, col: i64) -> SingleAssign {
    SingleAssign {
        pos: Position::at(line, col),
        var: var.to_owned(),
        sub,
        rhs,
    }
}

fn create_assign(ass: Vec<SingleAssign>, line: i64, col: i64) -> StmtRef {
    create_stmt(Position::at(line, col), StmtKind::Assign { ass })
}

fn make_assign(var: &str, expr: Expr, line: i64, col: i64) -> StmtRef {
    create_assign(
        vec![create_single_assign(
            var,
            create_normalized_expr(Vec::new()),
            expr,
            line,
            col,
        )],
        line,
        col,
    )
}

/// PcalTranslate.IsTRUE, which indexes the first line of an expression without checking it has
/// one.
fn is_true(expr: &Expr) -> Result<bool, PcalError> {
    if expr.tokens.len() > 1 {
        return Ok(false);
    }
    let line = get_element(&expr.tokens, 0)?;
    let strings: Vec<String> = line
        .iter()
        .map(|token| token.borrow().string.clone())
        .collect();
    Ok(match strings.len() {
        1 => strings[0] == "TRUE",
        3 => strings[0] == "(" && strings[1] == "TRUE" && strings[2] == ")",
        _ => false,
    })
}

fn check_pc(label: &str) -> StmtRef {
    create_stmt(
        Position::NONE,
        StmtKind::When(tokens_to_expr(
            &[added_token("pc"), built_in_token("="), string_token(label)],
            1,
        )),
    )
}

/// HACK: PcalSymTab.ProcedureEntry leaves iPC null for a procedure with no statements, which
/// StringToken keeps and AST.toString prints as "null".
fn update_pc(next: Option<&str>) -> StmtRef {
    make_assign(
        "pc",
        create_normalized_expr(vec![vec![string_token(next.unwrap_or("null"))]]),
        0,
        0,
    )
}

/// `Head(stack).field`.
fn get_stack_head_tokens(field: &str) -> Vec<Token> {
    vec![
        ident_token("Head"),
        built_in_token("("),
        added_token("stack"),
        built_in_token(")"),
        built_in_token("."),
        ident_token(field),
    ]
}

/// `Tail(stack)`.
fn get_stack_tail_tokens() -> Vec<Token> {
    vec![
        ident_token("Tail"),
        built_in_token("("),
        added_token("stack"),
        built_in_token(")"),
    ]
}

fn create_stack_head_expr(field: &str) -> Expr {
    create_normalized_expr(vec![get_stack_head_tokens(field)])
}

/// The `<< [ procedure |-> "name", pc |-> ..., var |-> var ] >> \o ...` that ExplodeCall and
/// ExplodeCallReturn push onto the stack.
fn create_stack_push_expr(
    procedure: &str,
    pc_tokens: Vec<Token>,
    variables: &[&VarDecl],
    tail_tokens: Vec<Token>,
) -> Expr {
    let mut tokens = vec![
        vec![
            built_in_token("<<"),
            built_in_token("["),
            ident_token("procedure"),
            built_in_token("|->"),
            string_token(procedure),
            built_in_token(","),
        ],
        [vec![ident_token("pc"), built_in_token("|->")], pc_tokens].concat(),
    ];
    for variable in variables {
        if let Some(last) = tokens.last_mut() {
            last.push(built_in_token(","));
        }
        tokens.push(vec![
            ident_token(&variable.var),
            built_in_token("|->"),
            ident_token(&variable.var),
        ]);
    }
    if let Some(last) = tokens.last_mut() {
        last.push(built_in_token("]"));
        last.push(built_in_token(">>"));
    }
    tokens.push(tail_tokens);
    let mut expr = create_expr(tokens);
    prettify_stack_top_expr(&expr);
    normalize_expr(&mut expr);
    expr
}

/// CopyAndExplodeLastStmt's triple: the statements with their last one exploded, which are the
/// statements given unless they were empty, the labeled statements the explosion split off, and
/// whether control falls off the end needing a pc update.
struct Exploded {
    stmts: Option<Vec<StmtRef>>,
    labeled: Vec<StmtRef>,
    needs_goto: bool,
}

/// A statement list of a node that the explosion changes in place.
#[derive(Clone, Copy)]
enum Field {
    Then,
    Else,
    Or(usize),
    Do,
    UnlabThen,
    UnlabElse,
    UnlabOr(usize),
}

fn get_field(kind: &mut StmtKind, field: Field) -> Option<&mut Vec<StmtRef>> {
    match (kind, field) {
        (StmtKind::If { then, .. }, Field::Then) => Some(then),
        (StmtKind::If { els, .. }, Field::Else) => Some(els),
        (StmtKind::Either { ors }, Field::Or(index)) => ors.get_mut(index),
        (StmtKind::With { body, .. }, Field::Do) => Some(body),
        (StmtKind::LabelIf { unlab_then, .. }, Field::UnlabThen) => Some(unlab_then),
        (StmtKind::LabelIf { unlab_else, .. }, Field::UnlabElse) => Some(unlab_else),
        (StmtKind::LabelEither { clauses }, Field::UnlabOr(index)) => {
            clauses.get_mut(index).map(|clause| &mut clause.unlab_or)
        }
        _ => None,
    }
}

fn set_field(node: &StmtRef, field: Field, stmts: Vec<StmtRef>) {
    if let Some(slot) = get_field(&mut node.borrow_mut().kind, field) {
        *slot = stmts;
    }
}

fn push_field(node: &StmtRef, field: Field, stmt: StmtRef) {
    if let Some(slot) = get_field(&mut node.borrow_mut().kind, field) {
        slot.push(stmt);
    }
}

/// PcalTranslate.Explode: turns each labeled statement into an atomic action that checks and
/// sets pc, and calls, returns and gotos into stack and pc assignments. Statement lists nested in
/// the original AST are exploded in place, as the Java does, so the original AST changes too.
struct Exploder<'a> {
    table: &'a SymbolTable,
    ast: &'a Algorithm,
    omit_pc: bool,
    /// The procedure being exploded, which a return comes from.
    procedure: Option<String>,
}

impl Exploder<'_> {
    fn get_entry(&self, index: usize) -> (&ProcedureEntry, &Procedure) {
        let entry = &self.table.procedures[index];
        (entry, &self.ast.prcds[entry.index])
    }

    /// The statements a call explodes into after its stack push: the parameters' and the
    /// procedure variables' initial values and the jump to the procedure's first label.
    fn create_call_stmts(
        &self,
        assign: StmtRef,
        index: usize,
        pos: Position,
        to: &str,
        args: &[Expr],
    ) -> Result<Vec<StmtRef>, PcalError> {
        let (entry, procedure) = self.get_entry(index);
        if procedure.params.len() != args.len() {
            return Err(error_at(
                &format!("Procedure {to} called with wrong number of arguments"),
                pos,
            ));
        }
        if let StmtKind::Assign { ass } = &mut assign.borrow_mut().kind {
            for (param, arg) in procedure.params.iter().zip(args) {
                ass.push(create_single_assign(
                    &param.var,
                    create_normalized_expr(Vec::new()),
                    arg.clone(),
                    pos.line,
                    pos.col,
                ));
            }
        }
        let mut result = vec![assign];
        for decl in &procedure.decls {
            result.push(make_assign(&decl.var, decl.val.clone(), pos.line, pos.col));
        }
        result.push(update_pc(entry.initial_pc.as_deref()));
        Ok(result)
    }

    fn explode_call(
        &self,
        pos: Position,
        to: &str,
        args: &[Expr],
        next: &str,
    ) -> Result<Vec<StmtRef>, PcalError> {
        let index = self.table.find_procedure_index(to);
        if index == self.table.procedures.len() {
            return Err(error_at(
                &format!("Call of non-existent procedure {to}"),
                pos,
            ));
        }
        let procedure = self.get_entry(index).1;
        let variables: Vec<&VarDecl> = procedure.decls.iter().chain(&procedure.params).collect();
        let stack_push = create_stack_push_expr(
            to,
            vec![string_token(next)],
            &variables,
            vec![built_in_token("\\o"), added_token("stack")],
        );
        let assign = make_assign("stack", stack_push, pos.line, pos.col);
        self.create_call_stmts(assign, index, pos, to, args)
    }

    fn explode_return(&self, stmt: &StmtRef) -> Result<Vec<StmtRef>, PcalError> {
        let (pos, from) = {
            let mut borrowed = stmt.borrow_mut();
            let pos = borrowed.pos;
            let StmtKind::Return { from } = &mut borrowed.kind else {
                return Ok(Vec::new());
            };
            if from.is_none() {
                from.clone_from(&self.procedure);
            }
            (pos, from.clone())
        };
        let Some(from) = from else {
            return Err(error_at("`return' statement not in procedure", pos));
        };
        let index = self.table.find_procedure_index(&from);
        if index >= self.table.procedures.len() {
            return Err(error_at(
                "Error in procedure (perhaps name used elsewhere)",
                pos,
            ));
        }
        let procedure = self.get_entry(index).1;
        let restore = |variable: &str, rhs: Expr| {
            create_assign(
                vec![create_single_assign(
                    variable,
                    create_expr(Vec::new()),
                    rhs,
                    pos.line,
                    pos.col,
                )],
                pos.line,
                pos.col,
            )
        };
        let mut result = vec![restore("pc", create_stack_head_expr("pc"))];
        for decl in procedure.decls.iter().chain(&procedure.params) {
            result.push(restore(&decl.var, create_stack_head_expr(&decl.var)));
        }
        result.push(restore(
            "stack",
            create_normalized_expr(vec![get_stack_tail_tokens()]),
        ));
        Ok(result)
    }

    fn explode_call_return(&self, stmt: &StmtRef) -> Result<Vec<StmtRef>, PcalError> {
        let borrowed = stmt.borrow();
        let pos = borrowed.pos;
        let StmtKind::CallReturn { from, to, args } = &borrowed.kind else {
            return Ok(Vec::new());
        };
        let Some(from) = from else {
            return Err(error(&format!(
                "`return' statement following `call' at {} not in a procedure",
                pos.location()
            )));
        };
        let from_index = self.table.find_procedure_index(from);
        get_element(&self.table.procedures, from_index as i64)?;
        let to_index = self.table.find_procedure_index(to);
        if to_index == self.table.procedures.len() {
            return Err(error_at(
                &format!("Call of non-existent procedure {to}"),
                pos,
            ));
        }
        let assign = create_assign(Vec::new(), pos.line, pos.col);
        // A tail call to the procedure itself reuses its stack frame.
        if from != to {
            let from_procedure = self.get_entry(from_index).1;
            let to_procedure = self.get_entry(to_index).1;
            let mut ass = Vec::new();
            for decl in &from_procedure.decls {
                ass.push(create_single_assign(
                    &decl.var,
                    create_expr(Vec::new()),
                    create_stack_head_expr(&decl.var),
                    pos.line,
                    pos.col,
                ));
            }
            let variables: Vec<&VarDecl> = to_procedure
                .decls
                .iter()
                .chain(&to_procedure.params)
                .collect();
            let stack_push = create_stack_push_expr(
                to,
                get_stack_head_tokens("pc"),
                &variables,
                [vec![built_in_token("\\o")], get_stack_tail_tokens()].concat(),
            );
            ass.push(create_single_assign(
                "stack",
                create_normalized_expr(Vec::new()),
                stack_push,
                pos.line,
                pos.col,
            ));
            if let StmtKind::Assign { ass: slot } = &mut assign.borrow_mut().kind {
                *slot = ass;
            }
        }
        self.create_call_stmts(assign, to_index, pos, to, args)
    }

    /// Explodes a statement list of node in place, as the Java passes the node's own list.
    fn explode_field(
        &mut self,
        node: &StmtRef,
        field: Field,
        next: &str,
        is_goto_added: bool,
    ) -> Result<(Vec<StmtRef>, Vec<StmtRef>, bool), PcalError> {
        let mut stmts = get_field(&mut node.borrow_mut().kind, field)
            .map(std::mem::take)
            .unwrap_or_default();
        let result = if is_goto_added {
            self.copy_and_explode_last_stmt_with_goto(&mut stmts, next)
        } else {
            self.copy_and_explode_last_stmt(&mut stmts, next)
        };
        set_field(node, field, stmts.clone());
        let exploded = result?;
        Ok((
            exploded.stmts.unwrap_or(stmts),
            exploded.labeled,
            exploded.needs_goto,
        ))
    }

    /// PcalTranslate.CopyAndExplodeLastStmt: explodes the last statement of stmts in place,
    /// recursing into the branches of a trailing if, either or with.
    fn copy_and_explode_last_stmt(
        &mut self,
        stmts: &mut Vec<StmtRef>,
        next: &str,
    ) -> Result<Exploded, PcalError> {
        let Some(last) = stmts.last().cloned() else {
            return Ok(Exploded {
                stmts: Some(Vec::new()),
                labeled: Vec::new(),
                needs_goto: !self.omit_pc,
            });
        };
        let mut labeled = Vec::new();
        let mut needs_goto = false;
        let kind = last.borrow().kind.name();
        match kind {
            "LabelIf" | "LabelEither" => {
                let (stmt, split) = if kind == "LabelIf" {
                    self.explode_label_if(&last, next)?
                } else {
                    self.explode_label_either(&last, next)?
                };
                stmts.pop();
                stmts.push(stmt);
                labeled = split;
            }
            "Goto" => {
                let to = match &last.borrow().kind {
                    StmtKind::Goto { to } => to.clone(),
                    _ => String::new(),
                };
                stmts.pop();
                stmts.push(update_pc(Some(&to)));
            }
            "Call" | "CallGoto" => {
                stmts.pop();
                let (pos, to, args, after) = {
                    let borrowed = last.borrow();
                    match &borrowed.kind {
                        StmtKind::Call { to, args, .. } => {
                            (borrowed.pos, to.clone(), args.clone(), next.to_owned())
                        }
                        StmtKind::CallGoto { to, args, after } => (
                            Position::at(borrowed.pos.line, borrowed.pos.col),
                            to.clone(),
                            args.clone(),
                            after.clone(),
                        ),
                        _ => return Err(bug("Unexpected call")),
                    }
                };
                stmts.extend(self.explode_call(pos, &to, &args, &after)?);
            }
            "Return" => {
                stmts.pop();
                stmts.extend(self.explode_return(&last)?);
            }
            "CallReturn" => {
                stmts.pop();
                stmts.extend(self.explode_call_return(&last)?);
            }
            "If" => {
                let (then_stmts, then_labeled, then_goto) =
                    self.explode_field(&last, Field::Then, next, false)?;
                let (else_stmts, else_labeled, else_goto) =
                    self.explode_field(&last, Field::Else, next, false)?;
                labeled.extend(then_labeled);
                labeled.extend(else_labeled);
                set_field(&last, Field::Then, then_stmts);
                set_field(&last, Field::Else, else_stmts);
                if !self.omit_pc {
                    needs_goto = then_goto && else_goto;
                    if !needs_goto {
                        if then_goto {
                            push_field(&last, Field::Then, update_pc(Some(next)));
                        }
                        if else_goto {
                            push_field(&last, Field::Else, update_pc(Some(next)));
                        }
                    }
                }
            }
            "Either" => {
                let count = match &last.borrow().kind {
                    StmtKind::Either { ors } => ors.len(),
                    _ => 0,
                };
                let mut goto_flags = Vec::new();
                for index in 0..count {
                    let (or_stmts, or_labeled, or_goto) =
                        self.explode_field(&last, Field::Or(index), next, false)?;
                    set_field(&last, Field::Or(index), or_stmts);
                    labeled.extend(or_labeled);
                    goto_flags.push(or_goto);
                }
                needs_goto = goto_flags.iter().all(|flag| *flag);
                if !self.omit_pc && !needs_goto {
                    for (index, flag) in goto_flags.iter().enumerate() {
                        if *flag {
                            push_field(&last, Field::Or(index), update_pc(Some(next)));
                        }
                    }
                }
            }
            "With" => {
                let (do_stmts, do_labeled, do_goto) =
                    self.explode_field(&last, Field::Do, next, false)?;
                set_field(&last, Field::Do, do_stmts);
                labeled.extend(do_labeled);
                needs_goto = do_goto;
            }
            _ => needs_goto = true,
        }
        if self.omit_pc {
            needs_goto = false;
        }
        Ok(Exploded {
            stmts: None,
            labeled,
            needs_goto,
        })
    }

    fn copy_and_explode_last_stmt_with_goto(
        &mut self,
        stmts: &mut Vec<StmtRef>,
        next: &str,
    ) -> Result<Exploded, PcalError> {
        let mut exploded = self.copy_and_explode_last_stmt(stmts, next)?;
        if exploded.needs_goto {
            match &mut exploded.stmts {
                Some(own) => own.push(update_pc(Some(next))),
                None => stmts.push(update_pc(Some(next))),
            }
        }
        Ok(exploded)
    }

    /// Explodes a copy of the statements, whose last statement it changes in place.
    fn explode_copy(
        &mut self,
        stmts: &[StmtRef],
        next: &str,
    ) -> Result<(Vec<StmtRef>, Vec<StmtRef>), PcalError> {
        let mut copy = stmts.to_vec();
        let exploded = self.copy_and_explode_last_stmt_with_goto(&mut copy, next)?;
        Ok((exploded.stmts.unwrap_or(copy), exploded.labeled))
    }

    fn explode_labeled_stmt(
        &mut self,
        labeled: &StmtRef,
        next: &str,
    ) -> Result<Vec<StmtRef>, PcalError> {
        let stmts = get_labeled_stmts(labeled);
        let label = get_label(labeled);
        let pos = labeled.borrow().pos;
        if let Some(first) = stmts
            .first()
            .filter(|first| first.borrow().kind.name() == "While")
        {
            return self.explode_while(labeled, first, next);
        }
        let (mut exploded_stmts, split) = self.explode_copy(&stmts, next)?;
        let mut result = Vec::new();
        // With omit_pc, PcalTranslate.ExplodeLabeledStmt drops the labeled statement itself.
        if !self.omit_pc {
            exploded_stmts.insert(0, check_pc(&label));
            result.push(create_stmt(
                Position::at(pos.line, pos.col),
                StmtKind::LabeledStmt {
                    label,
                    stmts: exploded_stmts,
                },
            ));
        }
        result.extend(split);
        Ok(result)
    }

    fn explode_labeled_stmt_seq(
        &mut self,
        seq: &[StmtRef],
        next: &str,
    ) -> Result<Vec<StmtRef>, PcalError> {
        let mut result = Vec::new();
        for (index, labeled) in seq.iter().enumerate() {
            let following = match seq.get(index + 1) {
                Some(following) => get_label(following),
                None => next.to_owned(),
            };
            result.extend(self.explode_labeled_stmt(labeled, &following)?);
        }
        Ok(result)
    }

    /// PcalTranslate.ExplodeWhile: the loop's label tests the condition, running the unlabeled
    /// body or the statements after the loop.
    fn explode_while(
        &mut self,
        labeled: &StmtRef,
        loop_stmt: &StmtRef,
        next: &str,
    ) -> Result<Vec<StmtRef>, PcalError> {
        let label = get_label(labeled);
        let pos = labeled.borrow().pos;
        let rest: Vec<StmtRef> = get_labeled_stmts(labeled).into_iter().skip(1).collect();
        let (test, unlab_do, lab_do) = match &loop_stmt.borrow().kind {
            StmtKind::While {
                test,
                unlab_do,
                lab_do,
            } => (test.clone(), unlab_do.clone(), lab_do.clone()),
            _ => return Ok(Vec::new()),
        };
        let unlab_do_next = lab_do.first().map_or_else(|| label.clone(), get_label);
        let (body_stmts, body_labeled) = self.explode_copy(&unlab_do, &unlab_do_next)?;
        let (rest_stmts, rest_labeled) = self.explode_copy(&rest, next)?;
        let is_forever = is_true(&test)?;
        let loop_stmts = if is_forever {
            body_stmts
        } else {
            vec![create_stmt(
                Position::NONE,
                StmtKind::If {
                    test,
                    then: body_stmts,
                    els: rest_stmts,
                },
            )]
        };
        let mut stmts = if self.omit_pc {
            Vec::new()
        } else {
            vec![check_pc(&label)]
        };
        stmts.extend(loop_stmts);
        let mut result = vec![create_stmt(
            Position::at(pos.line, pos.col),
            StmtKind::LabeledStmt {
                label: label.clone(),
                stmts,
            },
        )];
        result.extend(self.explode_labeled_stmt_seq(&lab_do, &label)?);
        result.extend(body_labeled);
        if !is_forever {
            result.extend(rest_labeled);
        }
        Ok(result)
    }

    fn explode_label_if(
        &mut self,
        stmt: &StmtRef,
        next: &str,
    ) -> Result<(StmtRef, Vec<StmtRef>), PcalError> {
        let (pos, test, lab_then, lab_else) = match &stmt.borrow().kind {
            StmtKind::LabelIf {
                test,
                lab_then,
                lab_else,
                ..
            } => (
                stmt.borrow().pos,
                test.clone(),
                lab_then.clone(),
                lab_else.clone(),
            ),
            _ => return Err(bug("Unexpected labelIf")),
        };
        let then_next = lab_then.first().map_or_else(|| next.to_owned(), get_label);
        let else_next = lab_else.first().map_or_else(|| next.to_owned(), get_label);
        let (then_stmts, then_labeled, _) =
            self.explode_field(stmt, Field::UnlabThen, &then_next, true)?;
        let (else_stmts, else_labeled, _) =
            self.explode_field(stmt, Field::UnlabElse, &else_next, true)?;
        let mut labeled = self.explode_labeled_stmt_seq(&lab_then, next)?;
        labeled.extend(self.explode_labeled_stmt_seq(&lab_else, next)?);
        labeled.extend(then_labeled);
        labeled.extend(else_labeled);
        let new_if = create_stmt(
            Position::at(pos.line, pos.col),
            StmtKind::If {
                test,
                then: then_stmts,
                els: else_stmts,
            },
        );
        Ok((new_if, labeled))
    }

    fn explode_label_either(
        &mut self,
        stmt: &StmtRef,
        next: &str,
    ) -> Result<(StmtRef, Vec<StmtRef>), PcalError> {
        let (pos, lab_ors) = match &stmt.borrow().kind {
            StmtKind::LabelEither { clauses } => (
                stmt.borrow().pos,
                clauses
                    .iter()
                    .map(|clause| clause.lab_or.clone())
                    .collect::<Vec<_>>(),
            ),
            _ => return Err(bug("Unexpected labelEither")),
        };
        let mut ors = Vec::new();
        let mut labeled = Vec::new();
        for (index, lab_or) in lab_ors.iter().enumerate() {
            let or_next = lab_or.first().map_or_else(|| next.to_owned(), get_label);
            let (or_stmts, or_labeled, _) =
                self.explode_field(stmt, Field::UnlabOr(index), &or_next, true)?;
            ors.push(or_stmts);
            labeled.extend(or_labeled);
            labeled.extend(self.explode_labeled_stmt_seq(lab_or, next)?);
        }
        Ok((
            create_stmt(Position::at(pos.line, pos.col), StmtKind::Either { ors }),
            labeled,
        ))
    }

    fn explode_body(&mut self, body: &[StmtRef], next: &str) -> Result<Vec<StmtRef>, PcalError> {
        for stmt in body {
            check_labeled(stmt)?;
        }
        self.explode_labeled_stmt_seq(body, next)
    }
}

/// The parts of PcalTLAGen.generate that change the AST or throw: GenVarsAndDefs's check that
/// there are variables, and GenAssign's sorting of multiple assignments and its checks that each
/// variable is declared and assigned at most once per step. Changed counts the assignments to
/// each variable along the paths through a labeled statement.
struct Generator {
    vars: Vec<String>,
}

/// String.compareTo, which compares UTF-16 code units.
fn compare_java(left: &str, right: &str) -> Ordering {
    left.encode_utf16().cmp(right.encode_utf16())
}

fn merge_changed(changed: &mut [i64], other: &[i64]) {
    for (count, other) in changed.iter_mut().zip(other) {
        *count = (*count).max(*other);
    }
}

impl Generator {
    /// Changed.Set, which counts only the first of duplicate variable names.
    fn set_changed(&self, changed: &mut [i64], variable: &str) -> i64 {
        match self.vars.iter().position(|var| var == variable) {
            None => 0,
            Some(index) => {
                changed[index] += 1;
                changed[index]
            }
        }
    }

    fn gen_assign(&self, assign: &StmtRef, changed: &mut [i64]) -> Result<(), PcalError> {
        let mut this_changed = changed.to_vec();
        let mut borrowed = assign.borrow_mut();
        let pos = borrowed.pos;
        let StmtKind::Assign { ass } = &mut borrowed.kind else {
            return Ok(());
        };
        // PcalTLAGen.SortSass: a stable sort by variable name.
        ass.sort_by(|left, right| compare_java(&left.var, &right.var));
        let mut seen: Vec<&str> = Vec::new();
        for single in ass.iter() {
            let variable = single.var.as_str();
            if seen.contains(&variable) {
                continue;
            }
            seen.push(variable);
            let group: Vec<&SingleAssign> =
                ass.iter().filter(|other| other.var == variable).collect();
            if !self.vars.iter().any(|var| var == variable) {
                return Err(error_at(
                    &format!("Assignment to undeclared variable {variable}"),
                    group[0].pos,
                ));
            }
            // GenAssign also notes whether the assignment after the group lacks a subscript, but
            // its loop ends before reading that, so only the group's own assignments count.
            let has_assignment_with_no_subscript =
                group.iter().any(|other| other.sub.tokens.is_empty());
            if self.set_changed(&mut this_changed, variable) > 1
                || (group.len() > 1 && has_assignment_with_no_subscript)
            {
                return Err(error_at(&format!("Multiple assignment to {variable}"), pos));
            }
        }
        merge_changed(changed, &this_changed);
        Ok(())
    }

    fn gen_stmts(&self, stmts: &[StmtRef], changed: &mut [i64]) -> Result<(), PcalError> {
        stmts
            .iter()
            .try_for_each(|stmt| self.gen_stmt(stmt, changed))
    }

    fn gen_stmt(&self, stmt: &StmtRef, changed: &mut [i64]) -> Result<(), PcalError> {
        let kind = stmt.borrow().kind.name();
        if kind == "Assign" {
            return self.gen_assign(stmt, changed);
        }
        let borrowed = stmt.borrow();
        match &borrowed.kind {
            StmtKind::If { then, els, .. } => {
                let mut then_changed = changed.to_vec();
                let mut else_changed = changed.to_vec();
                self.gen_stmts(then, &mut then_changed)?;
                self.gen_stmts(els, &mut else_changed)?;
                merge_changed(changed, &then_changed);
                merge_changed(changed, &else_changed);
            }
            StmtKind::Either { ors } => {
                let mut all_changed = changed.to_vec();
                for or in ors {
                    let mut or_changed = changed.to_vec();
                    self.gen_stmts(or, &mut or_changed)?;
                    merge_changed(&mut all_changed, &or_changed);
                }
                merge_changed(changed, &all_changed);
            }
            StmtKind::With { body, .. } => self.gen_stmts(body, changed)?,
            StmtKind::When(_) | StmtKind::PrintS(_) | StmtKind::Assert(_) | StmtKind::Skip => {}
            other => return Err(bug(&format!("Unexpected AST type {}", other.name()))),
        }
        Ok(())
    }

    fn gen_body(&self, body: &[StmtRef]) -> Result<(), PcalError> {
        for stmt in body {
            let mut changed = vec![0; self.vars.len()];
            check_labeled(stmt)?;
            self.gen_stmts(&get_labeled_stmts(stmt), &mut changed)?;
        }
        Ok(())
    }
}

/// PCalTLAGenerator.removeNameConflicts followed by translate, for what they do to the AST and
/// the errors they report: the symbol table's renaming, PcalFixIDs, PcalTranslate.Explode and the
/// checks PcalTLAGen makes while generating the TLA+ translation, which SANY discards.
pub fn translate_algorithm(
    ast: &mut Algorithm,
    omit_pc: bool,
    has_default_initialization: bool,
    log: &mut Vec<String>,
) -> Result<(), PcalError> {
    let mut table = SymbolTable::create(ast)?;
    if table.disambiguate() {
        log.push("Warning: symbols were renamed.".to_owned());
    }
    Fixer {
        table: &mut table,
        log,
    }
    .fix(ast)?;
    let mut exploder = Exploder {
        table: &table,
        ast,
        omit_pc,
        procedure: None,
    };
    let mut prcd_bodies = Vec::new();
    for procedure in &ast.prcds {
        exploder.procedure = Some(procedure.name.clone());
        let error_label = table.use_this(LABEL, "Error", "");
        prcd_bodies.push(exploder.explode_body(&procedure.body, &error_label)?);
        exploder.procedure = None;
    }
    let bodies = match &ast.body {
        AlgorithmBody::Uniprocess(body) => vec![exploder.explode_body(body, "Done")?],
        AlgorithmBody::Multiprocess(procs) => procs
            .iter()
            .map(|process| exploder.explode_body(&process.body, "Done"))
            .collect::<Result<_, _>>()?,
    };
    let mut vars = if omit_pc {
        Vec::new()
    } else {
        vec!["pc".to_owned()]
    };
    vars.extend(ast.decls.iter().map(|decl| decl.var.clone()));
    if !ast.prcds.is_empty() {
        vars.push("stack".to_owned());
    }
    for procedure in &ast.prcds {
        vars.extend(procedure.params.iter().map(|param| param.var.clone()));
        vars.extend(procedure.decls.iter().map(|decl| decl.var.clone()));
    }
    if let AlgorithmBody::Multiprocess(procs) = &ast.body {
        for process in procs {
            vars.extend(process.decls.iter().map(|decl| decl.var.clone()));
        }
    }
    if vars.is_empty() {
        return Err(error("The algorithm has no variables."));
    }
    let generator = Generator { vars };
    for body in prcd_bodies.iter().chain(&bodies) {
        generator.gen_body(body)?;
    }
    if has_default_initialization {
        table.check_for_default_init_value()?;
    }
    Ok(())
}

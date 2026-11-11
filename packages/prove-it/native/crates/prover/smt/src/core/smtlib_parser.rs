//! Ported from Z3 (src/parsers/smt2/smt2parser.cpp), MIT license, through `smtlib-parser.ts`.
//! Parses the SMT-LIB subset that tlapm emits into Z3-style expressions.
//!
//! The s-expressions live in one arena and refer to each other by index, so that a deeply nested
//! input is neither read nor dropped by recursion. Where the TypeScript reads a missing element of a
//! list (`undefined`), the Rust takes `None`; where it then crashes with a `TypeError` (a missing
//! term: `(assert)`, `(! )`, a `let` or quantifier without a body), the Rust returns
//! `SmtError::Parse("expected a term")`.

use std::collections::{HashMap, HashSet};

use prove_num::{Int, Rational};

use crate::core::ast::{
    AstManager, Decl, Expr, FAMILY_ARITH, FAMILY_BASIC, KIND_QUANTIFIER, KIND_VAR, OP_ABS, OP_ADD,
    OP_AND, OP_DISTINCT, OP_DIV, OP_EQ, OP_FALSE, OP_GE, OP_GT, OP_IDIV, OP_IMPLIES, OP_IS_INT,
    OP_ITE, OP_LE, OP_LT, OP_MOD, OP_MUL, OP_NOT, OP_OR, OP_SUB, OP_TO_INT, OP_TO_REAL, OP_TRUE,
    OP_UMINUS, OP_UNINTERPRETED, OP_XOR, QuantifierData, SORT_BOOL, SORT_INT, SORT_REAL, SmtSymbol,
    Sort, is_arith_sort,
};
use crate::core::var_subst::replace_free_vars;
use crate::util::error::SmtError;

// An s-expression: an index into the arena that read_sexprs fills.
type SExprId = usize;

// A quoted symbol, |name|, names what the plain symbol name does, but is never a keyword, a numeral,
// a string or a parenthesis.
enum SExpr<'a> {
    Symbol(&'a str),
    Quoted(&'a str),
    List(Vec<SExprId>),
}

// A name in scope: a variable bound by a quantifier, or a let binding's term. depth is the number of
// binders above it.
#[derive(Clone, Copy)]
enum Binding {
    Var { depth: i32, sort: Sort },
    Let { depth: i32, expr: Expr },
}

/// What the script hands the solver as it is read: an assertion, or (reset), after which the
/// manager is a new one.
pub enum Command {
    Assert(Expr),
    Reset,
}

pub struct SmtProblem {
    pub assertions: Vec<Expr>,
    // Z3 prints no answer for a script without check-sat.
    pub has_check_sat: bool,
}

// An application that parse_term is parsing: its name, its list, where its arguments start on the
// result stack, and its next argument.
struct ApplicationFrame<'a> {
    name: &'a str,
    list: &'a [SExprId],
    start: usize,
    next: usize,
}

const BUILTIN_OPS: [(&str, i32); 16] = [
    ("and", OP_AND),
    ("or", OP_OR),
    ("not", OP_NOT),
    ("=>", OP_IMPLIES),
    ("xor", OP_XOR),
    ("ite", OP_ITE),
    ("distinct", OP_DISTINCT),
    ("+", OP_ADD),
    ("*", OP_MUL),
    ("/", OP_DIV),
    ("div", OP_IDIV),
    ("mod", OP_MOD),
    ("abs", OP_ABS),
    ("to_real", OP_TO_REAL),
    ("to_int", OP_TO_INT),
    ("is_int", OP_IS_INT),
];

// arith_decl_plugin's use_coercion: the operators that are Real when any argument is Real.
const COERCING_OPS: [i32; 8] = [
    OP_ADD, OP_SUB, OP_UMINUS, OP_MUL, OP_LE, OP_GE, OP_LT, OP_GT,
];

const CHAINABLE_OPS: [(&str, i32); 5] = [
    ("=", OP_EQ),
    ("<=", OP_LE),
    (">=", OP_GE),
    ("<", OP_LT),
    (">", OP_GT),
];

// The quantifiers, lets and annotations that may nest, which the parser enters by recursion where
// the TypeScript would exhaust its stack and give up. A decision runs on a 256 MB stack
// (design/prover.md 3.6), which this depth stays well within.
const MAX_NESTING: usize = 10_000;

fn get_op(ops: &[(&str, i32)], name: &str) -> Option<i32> {
    ops.iter()
        .find(|entry| entry.0 == name)
        .map(|entry| entry.1)
}

fn find_byte(bytes: &[u8], byte: u8, from: usize) -> Option<usize> {
    bytes
        .get(from..)
        .and_then(|rest| rest.iter().position(|current| *current == byte))
        .map(|offset| from + offset)
}

// The tokens, up to an error that ends them, if any.
fn tokenize(text: &str) -> (Vec<&str>, Option<SmtError>) {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut position = 0;
    while position < bytes.len() {
        let char = bytes[position];
        if char == b';' {
            position = find_byte(bytes, b'\n', position).map_or(bytes.len(), |end| end + 1);
        } else if char == b'(' || char == b')' {
            tokens.push(&text[position..position + 1]);
            position += 1;
        } else if char == b' ' || char == b'\n' || char == b'\t' || char == b'\r' {
            position += 1;
        } else if char == b'|' {
            let Some(end) = find_byte(bytes, b'|', position + 1) else {
                return (
                    tokens,
                    Some(SmtError::Parse("unterminated quoted symbol".into())),
                );
            };
            tokens.push(&text[position..end + 1]);
            position = end + 1;
        } else if char == b'"' {
            let mut end = position + 1;
            while end < bytes.len() && (bytes[end] != b'"' || bytes.get(end + 1) == Some(&b'"')) {
                end += if bytes[end] == b'"' { 2 } else { 1 };
            }
            tokens.push(&text[position..(end + 1).min(bytes.len())]);
            position = end + 1;
        } else {
            let mut end = position;
            while end < bytes.len() && !b" \n\t\r();|\"".contains(&bytes[end]) {
                end += 1;
            }
            tokens.push(&text[position..end]);
            position = end;
        }
    }
    (tokens, None)
}

// The arena of the s-expressions, the whole commands, and the error that ends them, if any: Z3 reads
// a command at a time, so what follows a check-sat or an exit is never read.
fn read_sexprs<'a>(tokens: &[&'a str]) -> (Vec<SExpr<'a>>, Vec<SExprId>, Option<SmtError>) {
    let mut nodes = Vec::new();
    let mut stack: Vec<Vec<SExprId>> = vec![Vec::new()];
    for token in tokens {
        if *token == "(" {
            stack.push(Vec::new());
        } else if *token == ")" {
            if stack.len() == 1 {
                let commands = stack.pop().unwrap_or_default();
                return (
                    nodes,
                    commands,
                    Some(SmtError::Parse("unbalanced parentheses".into())),
                );
            }
            let list = stack.pop().unwrap_or_default();
            let Some(top) = stack.last_mut() else {
                unreachable!("the commands stay below a list");
            };
            top.push(nodes.len());
            nodes.push(SExpr::List(list));
        } else if let Some(top) = stack.last_mut() {
            top.push(nodes.len());
            nodes.push(match token.strip_prefix('|') {
                Some(quoted) => SExpr::Quoted(&quoted[..quoted.len() - 1]),
                None => SExpr::Symbol(token),
            });
        }
    }
    let error = (stack.len() > 1).then(|| SmtError::Parse("unbalanced parentheses".into()));
    stack.truncate(1);
    let commands = stack.pop().unwrap_or_default();
    (nodes, commands, error)
}

fn is_digits(text: &str) -> bool {
    !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit())
}

fn parse_int(digits: &str) -> Result<Int, SmtError> {
    digits
        .parse()
        .map_err(|_| SmtError::Invariant(format!("{digits} is not a numeral")))
}

// JavaScript's Number of a string, as far as the weight of a quantifier needs it: NaN for what it
// does not read.
fn get_js_number(text: &str) -> f64 {
    let trimmed =
        text.trim_matches(|character: char| character.is_whitespace() || character == '\u{feff}');
    if trimmed.is_empty() {
        return 0.0;
    }
    for (prefix, radix) in [
        ("0x", 16),
        ("0X", 16),
        ("0o", 8),
        ("0O", 8),
        ("0b", 2),
        ("0B", 2),
    ] {
        if let Some(digits) = trimmed.strip_prefix(prefix) {
            return u128::from_str_radix(digits, radix)
                .ok()
                .filter(|_| !digits.starts_with('+'))
                .map_or(f64::NAN, |value| value as f64);
        }
    }
    let unsigned = trimmed.strip_prefix(['+', '-']).unwrap_or(trimmed);
    if unsigned == "Infinity" {
        return if trimmed.starts_with('-') {
            f64::NEG_INFINITY
        } else {
            f64::INFINITY
        };
    }
    // Rust also reads inf and nan, which JavaScript does not.
    if unsigned.starts_with(|character: char| character.is_ascii_alphabetic()) {
        return f64::NAN;
    }
    trimmed.parse().unwrap_or(f64::NAN)
}

// basic_decl_plugin::join: Int and Real join to Real. Other sorts join only with themselves.
fn get_join(m: &AstManager, args: &[Expr]) -> Option<Sort> {
    let arg_sorts: Vec<Sort> = args.iter().map(|arg| m.sorts[*arg as usize]).collect();
    if !arg_sorts.iter().all(|sort| is_arith_sort(*sort)) {
        return arg_sorts.first().copied();
    }
    Some(if arg_sorts.contains(&SORT_REAL) {
        SORT_REAL
    } else {
        SORT_INT
    })
}

// The sort of the arguments of a builtin, as Z3's decl plugins pick its declaration.
fn get_domain_sort(m: &AstManager, op: i32, args: &[Expr]) -> Option<Sort> {
    if op == OP_ITE {
        return get_join(m, args.get(1..).unwrap_or_default());
    }
    if op == OP_EQ || op == OP_DISTINCT {
        return get_join(m, args);
    }
    if COERCING_OPS.contains(&op) {
        return Some(if get_join(m, args) == Some(SORT_REAL) {
            SORT_REAL
        } else {
            SORT_INT
        });
    }
    if op == OP_ABS || op == OP_TO_REAL || op == OP_TO_INT {
        return args.first().map(|arg| m.sorts[*arg as usize]);
    }
    if op == OP_IDIV || op == OP_MOD {
        return Some(SORT_INT);
    }
    if op == OP_DIV || op == OP_IS_INT {
        return Some(SORT_REAL);
    }
    Some(SORT_BOOL)
}

fn get_range(op: i32, domain_sort: Sort) -> Sort {
    if op == OP_TO_REAL || op == OP_DIV {
        SORT_REAL
    } else if op == OP_TO_INT || op == OP_IDIV || op == OP_MOD {
        SORT_INT
    } else if op == OP_ITE
        || op == OP_ABS
        || op == OP_ADD
        || op == OP_SUB
        || op == OP_UMINUS
        || op == OP_MUL
    {
        domain_sort
    } else {
        SORT_BOOL
    }
}

// ast_manager::coerce_to: an Int argument of a Real position becomes to_real, and a Real argument
// of an Int position to_int.
fn coerce(m: &mut AstManager, arg: Expr, sort: Sort) -> Result<Expr, SmtError> {
    let arg_sort = m.sorts[arg as usize];
    if arg_sort == sort || !is_arith_sort(arg_sort) || !is_arith_sort(sort) {
        return Ok(arg);
    }
    if sort == SORT_REAL {
        m.mk_app(OP_TO_REAL, &[arg], SORT_REAL)
    } else {
        m.mk_app(OP_TO_INT, &[arg], SORT_INT)
    }
}

// Coerces the arguments of an application to the sorts of its declaration, as Z3 does with its
// default int_real_coercions, then checks their sorts and number, so the solver only sees
// well-sorted terms, and that quantifiers occur only under Boolean connectives.
fn mk_app(
    m: &mut AstManager,
    decl: Decl,
    input_args: &[Expr],
    domain_sort: Option<Sort>,
) -> Result<Expr, SmtError> {
    let func_decl = &m.func_decls[decl as usize];
    let op = func_decl.op;
    let is_uninterpreted = op == OP_UNINTERPRETED;
    let domain = func_decl.domain.clone();
    let range = func_decl.range;
    let is_builtin_arith = func_decl.family == FAMILY_ARITH;
    // None where the TypeScript's sort is undefined: abs, to_real and to_int without arguments.
    let builtin_sort = if is_uninterpreted {
        Some(-1)
    } else {
        domain_sort.or_else(|| get_domain_sort(m, op, input_args))
    };
    let get_expected = |index: usize| {
        if is_uninterpreted {
            domain.get(index).copied()
        } else if op == OP_ITE && index == 0 {
            Some(SORT_BOOL)
        } else {
            builtin_sort
        }
    };
    let mut args = Vec::with_capacity(input_args.len());
    for (index, arg) in input_args.iter().enumerate() {
        args.push(match get_expected(index) {
            None => *arg,
            Some(expected) => coerce(m, *arg, expected)?,
        });
    }
    let is_arity = |min: usize, max: usize| args.len() >= min && args.len() <= max;
    let is_arity_ok = if is_uninterpreted {
        args.len() == domain.len()
    } else if op == OP_AND || op == OP_OR {
        true
    } else if op == OP_ITE {
        is_arity(3, 3)
    } else if op == OP_EQ || op == OP_DISTINCT {
        is_arity(2, usize::MAX)
    } else if op == OP_NOT
        || op == OP_UMINUS
        || op == OP_ABS
        || op == OP_TO_REAL
        || op == OP_TO_INT
        || op == OP_IS_INT
    {
        is_arity(1, 1)
    } else if op == OP_IMPLIES
        || op == OP_XOR
        || op == OP_IDIV
        || op == OP_MOD
        || op == OP_DIV
        || op == OP_LE
        || op == OP_GE
        || op == OP_LT
        || op == OP_GT
    {
        is_arity(2, 2)
    } else {
        is_arity(1, usize::MAX)
    };
    let is_well_sorted = is_arity_ok
        && (!is_builtin_arith || builtin_sort.is_some_and(is_arith_sort))
        && args
            .iter()
            .enumerate()
            .all(|(index, arg)| Some(m.sorts[*arg as usize]) == get_expected(index));
    if !is_well_sorted {
        return Err(SmtError::Parse(format!(
            "ill-sorted application of {}",
            m.func_decls[decl as usize].name
        )));
    }
    // A builtin whose sort is None has no arguments, so its arity was refused above.
    let sort = if is_uninterpreted {
        range
    } else {
        get_range(op, builtin_sort.unwrap_or(-1))
    };
    m.mk_app(decl, &args, sort)
}

fn mk_chain(m: &mut AstManager, op: i32, args: &[Expr]) -> Result<Expr, SmtError> {
    let domain_sort = get_domain_sort(m, op, args);
    let mut pairs = Vec::new();
    let mut index = 0;
    while index + 1 < args.len() {
        pairs.push(mk_app(m, op, &[args[index], args[index + 1]], domain_sort)?);
        index += 1;
    }
    if pairs.len() == 1 {
        Ok(pairs[0])
    } else {
        mk_app(m, OP_AND, &pairs, None)
    }
}

fn expect_bool(m: &AstManager, expr: Expr) -> Result<Expr, SmtError> {
    if m.sorts[expr as usize] != SORT_BOOL {
        return Err(SmtError::Parse("expected a formula".into()));
    }
    Ok(expr)
}

// pattern_validator: a pattern has no Boolean operator other than equality, no quantifier, and
// every variable of its quantifier. The TypeScript recurses; the walk here keeps its own stack, and
// gives the same answer, since the variables it finds only count when every term is valid.
fn is_valid_pattern(m: &AstManager, pattern: Expr, num_decls: usize) -> bool {
    let mut found = HashSet::new();
    let mut todo: Vec<Expr> = m.get_args(pattern).into_iter().rev().collect();
    while let Some(expr) = todo.pop() {
        let kind = m.kinds[expr as usize];
        if kind == KIND_QUANTIFIER {
            return false;
        }
        if kind == KIND_VAR {
            let index = m.values[expr as usize];
            if (index as i64) < num_decls as i64 {
                found.insert(index);
            }
            continue;
        }
        let func_decl = &m.func_decls[m.decls[expr as usize] as usize];
        if func_decl.family == FAMILY_BASIC
            && func_decl.op != OP_EQ
            && func_decl.op != OP_TRUE
            && func_decl.op != OP_FALSE
        {
            return false;
        }
        todo.extend(m.get_arg_slice(expr).iter().rev());
    }
    found.len() == num_decls
}

// The weight of a quantifier, `Number(value)` in the TypeScript. A quantifier keeps an i32 weight,
// so one that Number does not make an i32 is unsupported.
fn get_weight(nodes: &[SExpr], value: Option<SExprId>) -> Result<i32, SmtError> {
    // A list's text is its elements' joined by commas, which Number reads only for a chain of lists
    // of one element.
    let mut current = value;
    let text = loop {
        match current.map(|id| &nodes[id]) {
            None => break None,
            Some(SExpr::Symbol(text)) => break Some(*text),
            Some(SExpr::Quoted(_)) => break None,
            Some(SExpr::List(list)) if list.is_empty() => break Some(""),
            Some(SExpr::List(list)) if list.len() == 1 => current = Some(list[0]),
            Some(SExpr::List(_)) => break None,
        }
    };
    let number = text.map_or(f64::NAN, get_js_number);
    if number.fract() == 0.0 && number >= f64::from(i32::MIN) && number <= f64::from(i32::MAX) {
        return Ok(number as i32);
    }
    Err(SmtError::Unsupported(format!(
        "the weight {} is not supported",
        text.unwrap_or("undefined")
    )))
}

struct SmtlibParser<'a> {
    nodes: &'a [SExpr<'a>],
    sorts: HashMap<&'a str, Sort>,
    funcs: HashMap<&'a str, Decl>,
    // The named terms, which a reference expands to as cmd_context expands a macro.
    named: HashMap<&'a str, Expr>,
    scopes: Vec<HashMap<&'a str, Binding>>,
    depth: i32,
    // The quantifiers, lets and annotations that parse_leaf is in.
    num_nested: usize,
}

impl<'a> SmtlibParser<'a> {
    fn get_list(&self, sexpr: Option<SExprId>) -> Option<&'a [SExprId]> {
        let nodes = self.nodes;
        match sexpr.map(|id| &nodes[id]) {
            Some(SExpr::List(list)) => Some(list),
            _ => None,
        }
    }

    fn get_symbol(&self, sexpr: Option<SExprId>) -> Option<&'a str> {
        let nodes = self.nodes;
        match sexpr.map(|id| &nodes[id]) {
            Some(SExpr::Symbol(text) | SExpr::Quoted(text)) => Some(text),
            _ => None,
        }
    }

    // A keyword, :name, which a quoted symbol never is.
    fn get_keyword(&self, sexpr: Option<SExprId>) -> Option<&'a str> {
        let nodes = self.nodes;
        match sexpr.map(|id| &nodes[id]) {
            Some(SExpr::Symbol(text)) if text.starts_with(':') => Some(text),
            _ => None,
        }
    }

    // check_identifier: a symbol, quoted or not, and not a keyword, a numeral, a string or a
    // bit-vector literal.
    fn get_identifier(&self, sexpr: Option<SExprId>) -> Option<&'a str> {
        let nodes = self.nodes;
        match sexpr.map(|id| &nodes[id]) {
            Some(SExpr::Quoted(text)) => Some(text),
            Some(SExpr::Symbol(text))
                if !text.starts_with([':', '"', '#'])
                    && !text.starts_with(|char: char| char.is_ascii_digit()) =>
            {
                Some(text)
            }
            _ => None,
        }
    }

    // consume_attributes: the keyword and value of each attribute of (! term attribute*).
    fn get_attributes(
        &self,
        list: &'a [SExprId],
    ) -> Result<Vec<(&'a str, Option<SExprId>)>, SmtError> {
        let mut attributes = Vec::new();
        for index in (2..list.len()).step_by(2) {
            let Some(keyword) = self.get_keyword(Some(list[index])) else {
                return Err(SmtError::Parse(
                    "invalid attributed expression, keyword expected".into(),
                ));
            };
            attributes.push((keyword, list.get(index + 1).copied()));
        }
        Ok(attributes)
    }

    fn expect_list(&self, sexpr: Option<SExprId>) -> Result<&'a [SExprId], SmtError> {
        self.get_list(sexpr)
            .ok_or_else(|| SmtError::Parse("expected a list".into()))
    }

    fn expect_symbol(&self, sexpr: Option<SExprId>) -> Result<&'a str, SmtError> {
        self.get_symbol(sexpr)
            .ok_or_else(|| SmtError::Parse("expected a symbol".into()))
    }

    fn parse_sort(&self, sexpr: Option<SExprId>) -> Result<Sort, SmtError> {
        let name = self.expect_symbol(sexpr)?;
        self.sorts
            .get(name)
            .copied()
            .ok_or_else(|| SmtError::Parse(format!("unknown sort {name}")))
    }

    fn lookup(&self, name: &str) -> Option<Binding> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
    }

    // push_pattern_frame with ignore_bad_patterns: (t1 ... tn) is a multi-pattern, (f a ...) a
    // pattern of one term, and a pattern that starts with a constant is dropped unparsed.
    fn parse_pattern(
        &mut self,
        m: &mut AstManager,
        sexpr: Option<SExprId>,
    ) -> Result<Option<Expr>, SmtError> {
        let Some(list) = self.get_list(sexpr).filter(|list| !list.is_empty()) else {
            return Ok(None);
        };
        let head = list[0];
        if self.get_list(Some(head)).is_some() {
            let mut terms = Vec::with_capacity(list.len());
            for item in list {
                terms.push(self.parse_term(m, Some(*item))?);
            }
            return m.mk_pattern(&terms).map(Some);
        }
        let decl = match self.get_symbol(Some(head)) {
            Some("true" | "false") => Some(-1),
            Some(name) if self.named.contains_key(name) => None,
            head => head.and_then(|name| self.funcs.get(name).copied()),
        };
        if decl == Some(-1)
            || decl.is_some_and(|decl| m.func_decls[decl as usize].domain.is_empty())
        {
            return Ok(None);
        }
        let term = self.parse_term(m, sexpr)?;
        m.mk_pattern(&[term]).map(Some)
    }

    fn parse_quantifier(
        &mut self,
        m: &mut AstManager,
        list: &'a [SExprId],
        is_forall: bool,
    ) -> Result<Expr, SmtError> {
        let declarations = self.expect_list(list.get(1).copied())?;
        let mut scope = HashMap::new();
        let mut names = Vec::with_capacity(declarations.len());
        for declaration in declarations {
            names.push(self.expect_symbol(self.expect_list(Some(*declaration))?.first().copied())?);
        }
        let mut var_sorts = Vec::with_capacity(declarations.len());
        for (index, declaration) in declarations.iter().enumerate() {
            let sort = self.parse_sort(self.expect_list(Some(*declaration))?.get(1).copied())?;
            scope.insert(
                names[index],
                Binding::Var {
                    depth: self.depth + index as i32,
                    sort,
                },
            );
            var_sorts.push(sort);
        }
        self.scopes.push(scope);
        self.depth += var_sorts.len() as i32;
        // parse_sorted_vars: the variables are created first, the first declared with the largest
        // index, and the parser's stack holds them until the quantifier is created.
        let mut bound_vars = Vec::with_capacity(var_sorts.len());
        for (index, sort) in var_sorts.iter().enumerate() {
            bound_vars.push(m.mk_var((var_sorts.len() - 1 - index) as i32, *sort));
        }
        for bound_var in &bound_vars {
            m.inc_ref(*bound_var);
        }
        let body_sexpr = list.get(2).copied();
        let annotation = self
            .get_list(body_sexpr)
            .filter(|body| self.get_symbol(body.first().copied()) == Some("!"));
        let body_term = match annotation {
            Some(annotation) => annotation.get(1).copied(),
            None => body_sexpr,
        };
        let body = self.parse_term(m, body_term)?;
        let body = expect_bool(m, body)?;
        let mut patterns = Vec::new();
        let mut weight = 1;
        let mut qid = String::new();
        if let Some(annotation) = annotation {
            for (keyword, value) in self.get_attributes(annotation)? {
                match keyword {
                    ":pattern" => {
                        if let Some(pattern) = self.parse_pattern(m, value)? {
                            m.inc_ref(pattern);
                            patterns.push(pattern);
                        }
                    }
                    ":weight" => weight = get_weight(self.nodes, value)?,
                    ":qid" => qid = self.expect_symbol(value)?.to_string(),
                    ":named" => self.name_term(m, value, body)?,
                    _ => {}
                }
            }
        }
        self.scopes.pop();
        self.depth -= var_sorts.len() as i32;
        // pop_quant_frame: the invalid patterns leave the parser's stack before the quantifier is
        // made, and the valid ones after.
        let mut num_kept = 0;
        for index in 0..patterns.len() {
            let pattern = patterns[index];
            if !is_valid_pattern(m, pattern, var_sorts.len()) {
                continue;
            }
            m.inc_ref(pattern);
            m.dec_ref(patterns[num_kept])?;
            patterns[num_kept] = pattern;
            num_kept += 1;
        }
        for removed in patterns.split_off(num_kept) {
            m.dec_ref(removed)?;
        }
        let quantifier = m.mk_quantifier(QuantifierData {
            is_forall,
            sorts: var_sorts,
            names: names
                .iter()
                .map(|name| SmtSymbol::Name((*name).into()))
                .collect(),
            body,
            patterns: patterns.clone(),
            weight,
            qid,
        })?;
        for pattern in patterns {
            m.dec_ref(pattern)?;
        }
        for bound_var in bound_vars {
            m.dec_ref(bound_var)?;
        }
        Ok(quantifier)
    }

    fn parse_let(&mut self, m: &mut AstManager, list: &'a [SExprId]) -> Result<Expr, SmtError> {
        let mut scope = HashMap::new();
        for binding in self.expect_list(list.get(1).copied())? {
            let pair = self.expect_list(Some(*binding))?;
            let expr = self.parse_term(m, pair.get(1).copied())?;
            scope.insert(
                self.expect_symbol(pair.first().copied())?,
                Binding::Let {
                    depth: self.depth,
                    expr,
                },
            );
        }
        self.scopes.push(scope);
        let body = self.parse_term(m, list.get(2).copied())?;
        self.scopes.pop();
        Ok(body)
    }

    fn parse_app(&self, m: &mut AstManager, name: &str, args: &[Expr]) -> Result<Expr, SmtError> {
        if let Some(chainable) = get_op(&CHAINABLE_OPS, name) {
            return mk_chain(m, chainable, args);
        }
        if name == "-" {
            return mk_app(
                m,
                if args.len() == 1 { OP_UMINUS } else { OP_SUB },
                args,
                None,
            );
        }
        // ast_manager::mk_app: / is left associative, so more arguments nest to the left.
        if name == "/" && args.len() > 2 {
            let mut dividend = args[0];
            for divisor in &args[1..] {
                dividend = mk_app(m, OP_DIV, &[dividend, *divisor], None)?;
            }
            return Ok(dividend);
        }
        if let Some(op) = get_op(&BUILTIN_OPS, name) {
            return mk_app(m, op, args, None);
        }
        // cmd_context::mk_app expands a macro first.
        if args.is_empty()
            && let Some(named) = self.named.get(name)
        {
            return Ok(*named);
        }
        let Some(decl) = self.funcs.get(name).copied() else {
            return Err(SmtError::Parse(format!("unknown function {name}")));
        };
        mk_app(m, decl, args, None)
    }

    // A term without nested applications to parse first: a symbol, a quantifier, a let or an
    // annotation.
    fn parse_leaf(&mut self, m: &mut AstManager, sexpr: Option<SExprId>) -> Result<Expr, SmtError> {
        let nodes = self.nodes;
        match sexpr.map(|id| &nodes[id]) {
            None => Err(SmtError::Parse("expected a term".into())),
            Some(SExpr::Symbol(text)) => self.parse_symbol(m, text, false),
            Some(SExpr::Quoted(text)) => self.parse_symbol(m, text, true),
            Some(SExpr::List(list)) => {
                if self.num_nested == MAX_NESTING {
                    return Err(SmtError::Unsupported(
                        "the term is nested too deeply".into(),
                    ));
                }
                self.num_nested += 1;
                let result = self.parse_binder(m, list);
                self.num_nested -= 1;
                result
            }
        }
    }

    fn parse_symbol(
        &mut self,
        m: &mut AstManager,
        text: &str,
        is_quoted: bool,
    ) -> Result<Expr, SmtError> {
        if !is_quoted && is_digits(text) {
            return Ok(m.mk_numeral(&parse_int(text)?));
        }
        if let Some((integer, fraction)) = text.split_once('.')
            && !is_quoted
            && is_digits(integer)
            && is_digits(fraction)
        {
            let value = Rational::of(
                parse_int(&format!("{integer}{fraction}"))?,
                Int::from(10u64).pow(fraction.len() as u32),
            );
            return Ok(m.mk_real_numeral(&value));
        }
        if text == "true" {
            return Ok(m.true_expr);
        }
        if text == "false" {
            return Ok(m.false_expr);
        }
        let depth = self.depth;
        match self.lookup(text) {
            Some(Binding::Var {
                depth: binding_depth,
                sort,
            }) => Ok(m.mk_var(depth - 1 - binding_depth, sort)),
            // Z3's var_shifter moves the free variables of a let binding up by the binders since.
            // Its cache holds the terms it makes, but this parser holds no references, so it
            // rebuilds the binding with replace_free_vars.
            Some(Binding::Let {
                depth: binding_depth,
                expr,
            }) => {
                if depth == binding_depth {
                    Ok(expr)
                } else {
                    replace_free_vars(m, expr, |m, variable, index, shift| {
                        let sort = m.sorts[variable as usize];
                        Ok(m.mk_var(index + shift + depth - binding_depth, sort))
                    })
                }
            }
            None => self.parse_app(m, text, &[]),
        }
    }

    // A quantifier, a let or an annotation.
    fn parse_binder(&mut self, m: &mut AstManager, list: &'a [SExprId]) -> Result<Expr, SmtError> {
        let head = self.get_symbol(list.first().copied());
        if head == Some("forall") || head == Some("exists") {
            return self.parse_quantifier(m, list, head == Some("forall"));
        }
        if head == Some("let") {
            return self.parse_let(m, list);
        }
        let named = self.parse_term(m, list.get(1).copied())?;
        for (keyword, value) in self.get_attributes(list)? {
            match keyword {
                ":named" => self.name_term(m, value, named)?,
                ":weight" | ":skolemid" | ":qid" | ":pattern" | ":no-pattern" => {
                    return Err(SmtError::Parse(
                        "invalid attribute, not in the scope of a quantifier".into(),
                    ));
                }
                _ => {}
            }
        }
        Ok(named)
    }

    // name_expr: cmd_context keeps a named expression as a macro.
    fn name_term(
        &mut self,
        m: &mut AstManager,
        name: Option<SExprId>,
        term: Expr,
    ) -> Result<(), SmtError> {
        if m.free_var_bounds[term as usize] > 0 {
            return Err(SmtError::Parse(
                "invalid named expression, expression contains free variables".into(),
            ));
        }
        let name = self
            .get_identifier(name)
            .ok_or_else(|| SmtError::Parse("invalid attribute value, symbol expected".into()))?;
        m.inc_ref(term);
        m.mk_macro(name, term);
        self.named.insert(name, term);
        Ok(())
    }

    fn enter(
        &mut self,
        m: &mut AstManager,
        current: Option<SExprId>,
        frames: &mut Vec<ApplicationFrame<'a>>,
        results: &mut Vec<Expr>,
    ) -> Result<(), SmtError> {
        let list = self.get_list(current);
        let head = list.and_then(|list| list.first().copied());
        match list {
            Some(list)
                if !matches!(
                    self.get_symbol(head),
                    Some("forall" | "exists" | "let" | "!")
                ) =>
            {
                frames.push(ApplicationFrame {
                    name: self.expect_symbol(head)?,
                    list,
                    start: results.len(),
                    next: 1,
                });
            }
            _ => results.push(self.parse_leaf(m, current)?),
        }
        Ok(())
    }

    // Applications keep their own stack, like Z3's parser, so deeply nested terms do not exhaust
    // the call stack.
    fn parse_term(&mut self, m: &mut AstManager, sexpr: Option<SExprId>) -> Result<Expr, SmtError> {
        let mut frames = Vec::new();
        let mut results = Vec::new();
        self.enter(m, sexpr, &mut frames, &mut results)?;
        while let Some(frame) = frames.last_mut() {
            if frame.next < frame.list.len() {
                let current = frame.list[frame.next];
                frame.next += 1;
                self.enter(m, Some(current), &mut frames, &mut results)?;
                continue;
            }
            let start = frame.start;
            let name = frame.name;
            frames.pop();
            let args = results.split_off(start);
            results.push(self.parse_app(m, name, &args)?);
        }
        results
            .first()
            .copied()
            .ok_or_else(|| SmtError::Invariant("a term parses to an expression".into()))
    }
}

// smt_logics::supported_logic of Z3 4.8.9: a logic Z3 sets, where it ignores any other. 5.3.3
// matches names by their parts instead.
const SUPPORTED_LOGICS: [&str; 61] = [
    "QF_UF",
    "UF",
    "QF_DT",
    "SMTFD",
    "ALL",
    "CSP",
    "QF_FD",
    "QF_LRA",
    "QF_LIA",
    "QF_RDL",
    "QF_IDL",
    "QF_AUFLIA",
    "QF_ALIA",
    "QF_AUFLIRA",
    "QF_AUFNIA",
    "QF_AUFNIRA",
    "QF_ANIA",
    "QF_LIRA",
    "QF_UFLIA",
    "QF_UFLRA",
    "QF_UFIDL",
    "QF_UFRDL",
    "QF_NIA",
    "QF_NRA",
    "QF_NIRA",
    "QF_UFNRA",
    "QF_UFNIA",
    "QF_UFNIRA",
    "QF_BVRE",
    "ALIA",
    "AUFLIA",
    "AUFLIRA",
    "AUFNIA",
    "AUFNIRA",
    "UFLIA",
    "UFLRA",
    "UFNRA",
    "UFNIRA",
    "NIA",
    "NRA",
    "UFNIA",
    "LIA",
    "LRA",
    "UFIDL",
    "QF_FP",
    "FP",
    "QF_FPBV",
    "QF_BVFP",
    "QF_S",
    "QF_SLIA",
    "HORN",
    "QF_FPLRA",
    "UFBV",
    "AUFBV",
    "ABV",
    "BV",
    "QF_BV",
    "QF_UFBV",
    "QF_ABV",
    "QF_AUFBV",
    "QF_AX",
];

fn is_supported_logic(name: &str) -> bool {
    SUPPORTED_LOGICS.contains(&name)
}

fn get_builtin_sorts<'a>() -> HashMap<&'a str, Sort> {
    HashMap::from([("Bool", SORT_BOOL), ("Int", SORT_INT), ("Real", SORT_REAL)])
}

/// Parses a script, and hands each assertion and reset to on_command as Z3's cmd_context does,
/// before it parses the next command. Expressions are created in the order of Z3's parser, and live
/// as long as there.
pub fn parse_smtlib(
    text: &str,
    m: &mut AstManager,
    mut on_command: impl FnMut(&mut AstManager, Command) -> Result<(), SmtError>,
) -> Result<SmtProblem, SmtError> {
    let (tokens, token_error) = tokenize(text);
    let (nodes, commands, read_error) = read_sexprs(&tokens);
    let mut parser = SmtlibParser {
        nodes: &nodes,
        sorts: get_builtin_sorts(),
        funcs: HashMap::new(),
        scopes: Vec::new(),
        depth: 0,
        num_nested: 0,
        named: HashMap::new(),
    };
    let mut assertions = Vec::new();
    let mut has_check_sat = false;
    let mut has_logic = false;
    // has_manager: Z3 4.8.9 makes its manager at the first declaration or assertion.
    let mut is_initialized = false;
    let mut is_exited = false;
    for command in commands {
        let list = parser.expect_list(Some(command))?;
        let name = parser.expect_symbol(list.first().copied())?;
        if matches!(
            name,
            "declare-sort" | "declare-fun" | "declare-const" | "assert"
        ) {
            is_initialized = true;
        }
        match name {
            "declare-sort" => {
                if let Some(arity) = list.get(2)
                    && parser.get_symbol(Some(*arity)) != Some("0")
                {
                    return Err(SmtError::Unsupported(
                        "parametric sorts are not supported".into(),
                    ));
                }
                let sort_name = parser.expect_symbol(list.get(1).copied())?;
                parser.sorts.insert(sort_name, m.mk_sort(sort_name));
            }
            "declare-fun" | "declare-const" => {
                let mut domain = Vec::new();
                if name == "declare-fun" {
                    for sort in parser.expect_list(list.get(2).copied())? {
                        domain.push(parser.parse_sort(Some(*sort))?);
                    }
                }
                let range = parser
                    .parse_sort(list.get(if name == "declare-fun" { 3 } else { 2 }).copied())?;
                // builtin_signature_collides and is_transcendental_shadow_decl each apply the builtin
                // of that name to fresh variables, which they then release.
                for _ in 0..2 {
                    let vars: Vec<Expr> = domain
                        .iter()
                        .enumerate()
                        .map(|(index, sort)| m.mk_var(index as i32, *sort))
                        .collect();
                    for domain_var in &vars {
                        m.inc_ref(*domain_var);
                    }
                    for domain_var in vars {
                        m.dec_ref(domain_var)?;
                    }
                }
                let func_name = parser.expect_symbol(list.get(1).copied())?;
                let decl = m.mk_func_decl(SmtSymbol::Name(func_name.into()), &domain, range, false);
                parser.funcs.insert(func_name, decl);
            }
            "assert" if list.len() > 2 => {
                return Err(SmtError::Parse(
                    "invalid assert command, ')' expected".into(),
                ));
            }
            "assert" => {
                // cmd_context::assert_expr keeps the assertion, and passes it to the solver.
                let assertion = parser.parse_term(m, list.get(1).copied())?;
                let assertion = expect_bool(m, assertion)?;
                m.inc_ref(assertion);
                assertions.push(assertion);
                on_command(m, Command::Assert(assertion))?;
            }
            "reset" => {
                if list.len() > 1 {
                    return Err(SmtError::Parse(
                        "invalid reset command, ')' expected".into(),
                    ));
                }
                // cmd_context::reset forgets the declarations, the named terms and the assertions,
                // and deletes the manager; the next command makes a new one, with its solver.
                parser.sorts = get_builtin_sorts();
                parser.funcs.clear();
                parser.named.clear();
                assertions.clear();
                has_logic = false;
                is_initialized = false;
                m.limit.restart();
                *m = AstManager::new(m.limit.clone());
                on_command(m, Command::Reset)?;
            }
            // cmd_context::set_logic. The solver is UFNIA's whatever the logic.
            "set-logic" => {
                if list.len() > 2 {
                    return Err(SmtError::Parse(
                        "invalid command, too many arguments".into(),
                    ));
                }
                let logic = parser.get_identifier(list.get(1).copied()).ok_or_else(|| {
                    SmtError::Parse("invalid command argument, symbol expected".into())
                })?;
                if has_logic {
                    return Err(SmtError::Parse("the logic has already been set".into()));
                }
                if is_initialized {
                    return Err(SmtError::Parse(
                        "logic must be set before initialization".into(),
                    ));
                }
                has_logic = is_supported_logic(logic);
            }
            // set_option_cmd's check_not_initialized, in Z3 4.8.9.
            "set-option"
                if is_initialized
                    && [
                        ":produce-proofs",
                        ":produce-unsat-cores",
                        ":produce-unsat-assumptions",
                        ":produce-assertions",
                        ":interactive-mode",
                        ":global-decls",
                        ":global-declarations",
                    ]
                    .contains(&parser.get_keyword(list.get(1).copied()).unwrap_or("")) =>
            {
                return Err(SmtError::Parse(
                    "option value cannot be modified after initialization".into(),
                ));
            }
            // Before the first check-sat there is no model, proof or core to get.
            "get-model"
            | "get-value"
            | "get-assignment"
            | "get-proof"
            | "get-unsat-core"
            | "get-unsat-assumptions"
            | "eval" => {
                return Err(SmtError::Parse(format!("{name} has nothing to get")));
            }
            // With arguments, check-sat is check-sat-assuming.
            "check-sat" if list.len() > 1 => {
                return Err(SmtError::Unsupported(
                    "check-sat with assumptions is not supported".into(),
                ));
            }
            "check-sat" => {
                has_check_sat = true;
                break;
            }
            "exit" if list.len() > 1 => {
                return Err(SmtError::Parse(
                    "invalid command, too many arguments".into(),
                ));
            }
            // Z3 reads no further.
            "exit" => {
                is_exited = true;
                break;
            }
            "push" | "pop" | "define-fun" | "define-sort" | "reset-assertions"
            | "check-sat-assuming" | "check-sat-using" => {
                return Err(SmtError::Unsupported(format!(
                    "the command {name} is not supported"
                )));
            }
            _ => {}
        }
    }
    if let Some(error) = token_error.or(read_error)
        && !has_check_sat
        && !is_exited
    {
        return Err(error);
    }
    Ok(SmtProblem {
        assertions,
        has_check_sat,
    })
}

#[cfg(test)]
mod tests {
    use prove_decide::Limits;

    use super::{MAX_NESTING, get_js_number, parse_smtlib};
    use crate::core::ast::AstManager;
    use crate::util::error::SmtError;
    use crate::util::rlimit::ResourceLimit;

    fn parse(text: &str) -> Result<usize, SmtError> {
        let limits = Limits::new(f64::INFINITY, None, None);
        let mut manager = AstManager::new(ResourceLimit::new(&limits));
        parse_smtlib(text, &mut manager, |_, _| Ok(())).map(|problem| problem.assertions.len())
    }

    fn get_nested_lets(count: usize) -> String {
        format!(
            "(assert {}(> x 0){})",
            "(let ((x 1)) ".repeat(count),
            ")".repeat(count)
        )
    }

    #[test]
    fn reads_numbers_as_javascript_does() {
        for (text, expected) in [
            ("", 0.0),
            ("12", 12.0),
            ("+5", 5.0),
            ("-0", 0.0),
            ("1e1", 10.0),
            ("1.5", 1.5),
            ("0x1F", 31.0),
            ("0b11", 3.0),
            ("Infinity", f64::INFINITY),
        ] {
            assert_eq!(get_js_number(text), expected, "{text}");
        }
        for text in ["inf", "nan", "0x", "-0x1", "1,2", "a1", "."] {
            assert!(get_js_number(text).is_nan(), "{text}");
        }
    }

    #[test]
    fn refuses_a_weight_that_is_not_an_i32() {
        for weight in ["1.5", "(1 2)", "4294967296"] {
            let text = format!("(assert (forall ((x Int)) (! (> x 0) :weight {weight})))");
            assert!(
                matches!(parse(&text), Err(SmtError::Unsupported(_))),
                "{weight}"
            );
        }
        assert_eq!(
            parse("(assert (forall ((x Int)) (! (> x 0) :weight ((7)))))"),
            Ok(1)
        );
    }

    #[test]
    fn parses_deep_applications_without_recursion() {
        let count = 100_000;
        let text = format!(
            "(assert {}true{})",
            "(not ".repeat(count),
            ")".repeat(count)
        );
        assert_eq!(parse(&text), Ok(1));
    }

    #[test]
    fn refuses_binders_nested_too_deeply() {
        // On a stack the size of a decision's.
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(|| {
                assert_eq!(parse(&get_nested_lets(MAX_NESTING)), Ok(1));
                assert_eq!(
                    parse(&get_nested_lets(MAX_NESTING + 1)),
                    Err(SmtError::Unsupported(
                        "the term is nested too deeply".into()
                    ))
                );
            })
            .and_then(|thread| thread.join().map_err(|_| std::io::Error::other("panicked")))
            .unwrap();
    }

    // The TypeScript crashes with a TypeError on these.
    #[test]
    fn refuses_a_missing_term() {
        for text in [
            "(assert)",
            "(assert (!))",
            "(assert (let ((x 1))))",
            "(assert (forall ((y Int))))",
        ] {
            assert_eq!(
                parse(text),
                Err(SmtError::Parse("expected a term".into())),
                "{text}"
            );
        }
    }
}

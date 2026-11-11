//! Ported from Z3 (src/ast/ast_lt.cpp, src/util/symbol.cpp), MIT license, through `ast-lt.ts`. A
//! total order on expressions that does not depend on their ids. The rewriter sorts a disjunction
//! only when its arguments are out of this order.
//!
//! The TypeScript's `compareAsts` recurses on the children of the two expressions. It returns the
//! first difference in a preorder walk of both, so here it walks them with a stack of its own, and
//! a deep term cannot exhaust the call stack.

use std::cmp::Ordering;

use prove_num::Rational;

use crate::core::ast::{
    AstManager, Expr, FAMILY_MODEL_VALUE, FAMILY_USER, KIND_APP, KIND_QUANTIFIER, KIND_VAR, OP_ITE,
    OP_NUM, OP_PATTERN, SORT_INT, SmtSymbol, Sort,
};
use crate::util::error::SmtError;

// A parameter of a declaration: Z3's PARAM_INT and the kinds in it, or PARAM_RATIONAL.
#[derive(Clone, Debug)]
enum Parameter {
    Int(i64),
    Rational(Rational),
}

// The name of a declaration: a symbol, or the name of a builtin.
#[derive(Clone, Debug)]
enum DeclName<'a> {
    Symbol(&'a SmtSymbol),
    Builtin(&'static str),
}

// The parts of a func_decl that lt compares: its name, parameters, domain and range.
struct DeclKey<'a> {
    name: DeclName<'a>,
    parameters: Vec<Parameter>,
    domain: Vec<Sort>,
    range: Sort,
}

// Z3's PARAM_INT, PARAM_AST and PARAM_RATIONAL kinds order the parameters of builtin declarations.
const PARAM_INT: i64 = 0;
const PARAM_RATIONAL: i64 = 3;

fn compare_values<T: Ord>(first: T, second: T) -> Ordering {
    first.cmp(&second)
}

fn compare_parameters(first: &Parameter, second: &Parameter) -> Ordering {
    match (first, second) {
        (Parameter::Rational(first), Parameter::Rational(second)) => first.compare(second),
        (Parameter::Int(first), Parameter::Int(second)) => compare_values(first, second),
        _ => Ordering::Equal,
    }
}

// JavaScript's < on strings: by UTF-16 code units.
fn compare_strings(first: &str, second: &str) -> Ordering {
    first.encode_utf16().cmp(second.encode_utf16())
}

// lt on symbols: numerical symbols come first, by number, and other names compare by their bytes.
fn compare_names(first: &DeclName, second: &DeclName) -> Ordering {
    let get_text = |name: &DeclName| -> Result<u64, String> {
        match name {
            DeclName::Symbol(SmtSymbol::Number(number)) => Ok(*number),
            DeclName::Symbol(SmtSymbol::Name(text)) => Err(text.clone()),
            DeclName::Builtin(text) => Err((*text).to_string()),
        }
    };
    match (get_text(first), get_text(second)) {
        (Ok(first), Ok(second)) => compare_values(first, second),
        (Ok(_), Err(_)) => Ordering::Less,
        (Err(_), Ok(_)) => Ordering::Greater,
        (Err(first), Err(second)) => compare_strings(&first, &second),
    }
}

fn compare_symbols(first: &SmtSymbol, second: &SmtSymbol) -> Ordering {
    compare_names(&DeclName::Symbol(first), &DeclName::Symbol(second))
}

fn get_decl_key(m: &AstManager, expr: Expr) -> Result<DeclKey<'_>, SmtError> {
    let decl = &m.func_decls[m.decls[expr as usize] as usize];
    let range = m.sorts[expr as usize];
    if decl.family == FAMILY_USER {
        return Ok(DeclKey {
            name: DeclName::Symbol(&decl.name),
            parameters: Vec::new(),
            domain: decl.domain.clone(),
            range,
        });
    }
    // A numeral's declaration has the parameters (value, is_int), and a model value's (index,
    // sort).
    if decl.op == OP_NUM {
        let is_int = range == SORT_INT;
        return Ok(DeclKey {
            name: DeclName::Builtin(if is_int { "Int" } else { "Real" }),
            parameters: vec![
                Parameter::Int(PARAM_RATIONAL),
                Parameter::Rational(m.get_rational_value(expr).clone()),
                Parameter::Int(PARAM_INT),
                Parameter::Int(if is_int { 1 } else { 0 }),
            ],
            domain: Vec::new(),
            range,
        });
    }
    if decl.family == FAMILY_MODEL_VALUE {
        return Ok(DeclKey {
            name: DeclName::Symbol(&decl.name),
            parameters: vec![
                Parameter::Int(PARAM_INT),
                Parameter::Int(i64::from(m.values[expr as usize])),
            ],
            domain: Vec::new(),
            range,
        });
    }
    let builtin = m.get_builtin_signature(decl.op, m.get_arg_slice(expr))?;
    Ok(DeclKey {
        name: DeclName::Builtin(builtin.name),
        parameters: Vec::new(),
        domain: builtin.domain,
        range,
    })
}

fn compare_sorts(m: &AstManager, first: Sort, second: Sort) -> Ordering {
    if first == second {
        return Ordering::Equal;
    }
    compare_strings(
        &m.sort_names[first as usize],
        &m.sort_names[second as usize],
    )
}

// Whether two applications of the same declaration have the same key: a user declaration's is its
// own, and a builtin's other than a numeral, model value or pattern follows from the sort of the
// argument that get_builtin_signature reads and the range.
fn is_same_decl_key(m: &AstManager, first: Expr, second: Expr) -> bool {
    let decl = &m.func_decls[m.decls[first as usize] as usize];
    if decl.family == FAMILY_USER {
        return true;
    }
    if decl.op == OP_NUM || decl.op == OP_PATTERN || decl.family == FAMILY_MODEL_VALUE {
        return false;
    }
    let index = if decl.op == OP_ITE { 1 } else { 0 };
    m.sorts[first as usize] == m.sorts[second as usize]
        && m.sorts[m.get_arg(first, index) as usize] == m.sorts[m.get_arg(second, index) as usize]
}

fn compare_decls(m: &AstManager, first: Expr, second: Expr) -> Result<Ordering, SmtError> {
    if m.decls[first as usize] == m.decls[second as usize] && is_same_decl_key(m, first, second) {
        return Ok(Ordering::Equal);
    }
    let first_key = get_decl_key(m, first)?;
    let second_key = get_decl_key(m, second)?;
    let by_name = compare_names(&first_key.name, &second_key.name);
    if by_name != Ordering::Equal {
        return Ok(by_name);
    }
    let by_arity = compare_values(first_key.domain.len(), second_key.domain.len());
    if by_arity != Ordering::Equal {
        return Ok(by_arity);
    }
    let by_parameter_count =
        compare_values(first_key.parameters.len(), second_key.parameters.len());
    if by_parameter_count != Ordering::Equal {
        return Ok(by_parameter_count);
    }
    for index in 0..first_key.parameters.len() {
        let by_parameter =
            compare_parameters(&first_key.parameters[index], &second_key.parameters[index]);
        if by_parameter != Ordering::Equal {
            return Ok(by_parameter);
        }
    }
    for index in 0..first_key.domain.len() {
        let by_domain = compare_sorts(m, first_key.domain[index], second_key.domain[index]);
        if by_domain != Ordering::Equal {
            return Ok(by_domain);
        }
    }
    Ok(compare_sorts(m, first_key.range, second_key.range))
}

// compareAsts on one pair: the order of their headers, and the pairs of children to compare next,
// in order, when the headers are equal.
fn compare_header(
    m: &AstManager,
    first: Expr,
    second: Expr,
    children: &mut Vec<(Expr, Expr)>,
) -> Result<Ordering, SmtError> {
    if first == second {
        return Ok(Ordering::Equal);
    }
    let kind = m.kinds[first as usize];
    let by_kind = compare_values(kind, m.kinds[second as usize]);
    if by_kind != Ordering::Equal {
        return Ok(by_kind);
    }
    if kind == KIND_VAR {
        let by_index = compare_values(m.values[first as usize], m.values[second as usize]);
        return Ok(by_index
            .then_with(|| compare_sorts(m, m.sorts[first as usize], m.sorts[second as usize])));
    }
    if kind == KIND_QUANTIFIER {
        let first_data = m.get_quantifier(first)?;
        let second_data = m.get_quantifier(second)?;
        let by_header = compare_values(
            if first_data.is_forall { 0 } else { 1 },
            if second_data.is_forall { 0 } else { 1 },
        )
        .then_with(|| compare_values(first_data.sorts.len(), second_data.sorts.len()))
        .then_with(|| compare_values(first_data.patterns.len(), second_data.patterns.len()))
        .then_with(|| compare_values(first_data.weight, second_data.weight));
        if by_header != Ordering::Equal {
            return Ok(by_header);
        }
        for index in 0..first_data.sorts.len() {
            let by_decl = compare_symbols(&first_data.names[index], &second_data.names[index])
                .then_with(|| compare_sorts(m, first_data.sorts[index], second_data.sorts[index]));
            if by_decl != Ordering::Equal {
                return Ok(by_decl);
            }
        }
        for index in 0..first_data.patterns.len() {
            children.push((first_data.patterns[index], second_data.patterns[index]));
        }
        children.push((first_data.body, second_data.body));
        return Ok(Ordering::Equal);
    }
    if kind != KIND_APP {
        return Ok(Ordering::Equal);
    }
    let by_header = compare_values(m.get_num_args(first), m.get_num_args(second))
        .then_with(|| compare_values(m.depths[first as usize], m.depths[second as usize]));
    let by_header = if by_header == Ordering::Equal {
        compare_decls(m, first, second)?
    } else {
        by_header
    };
    if by_header != Ordering::Equal {
        return Ok(by_header);
    }
    for index in 0..m.get_num_args(first) {
        children.push((m.get_arg(first, index), m.get_arg(second, index)));
    }
    Ok(Ordering::Equal)
}

fn compare_asts(m: &AstManager, first: Expr, second: Expr) -> Result<Ordering, SmtError> {
    // The pairs still to compare, the next one last.
    let mut stack = vec![(first, second)];
    let mut children = Vec::new();
    while let Some((first, second)) = stack.pop() {
        children.clear();
        let order = compare_header(m, first, second, &mut children)?;
        if order != Ordering::Equal {
            return Ok(order);
        }
        stack.extend(children.iter().rev());
    }
    Ok(Ordering::Equal)
}

/// lt: whether the first expression comes before the second.
pub fn is_ast_less(m: &AstManager, first: Expr, second: Expr) -> Result<bool, SmtError> {
    Ok(compare_asts(m, first, second)? == Ordering::Less)
}

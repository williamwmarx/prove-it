//! The check of unfolding a definition: a real definition from the input, or a pseudo-definition
//! that Zenon reads off a hypothesis.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::terms::{
    Binding, Checked, Checker, Env, Operators, RuleSpec, Term, TermKind, app, ensure, is_app, spec,
    variable,
};
use crate::expr::{Expr, Kind};
use crate::parse::Definition;

// Checks that `unfolded` is `folded` with occurrences of the defined symbol replaced by its body,
// going through applications and negations as Zenon does.
fn is_unfolding(
    checker: &mut Checker<'_>,
    definition: &Definition,
    folded: &Term,
    unfolded: &Term,
    is_formula_only: bool,
    is_in_term: bool,
) -> Checked<bool> {
    if checker.is_same(folded, unfolded)? {
        return Ok(true);
    }
    let is_defined = &**folded.symbol() == definition.symbol();
    let is_application = folded.kind() == TermKind::App && is_defined;
    let is_constant = folded.kind() == TermKind::Var && is_defined;
    if is_application || is_constant {
        if is_formula_only && is_in_term {
            return Ok(false);
        }
        let actuals = folded.args();
        let body = Term::from(definition.body());
        let params = definition.params();
        if params.is_empty() && is_application && body.kind() == TermKind::Var {
            return Ok(matches!(definition, Definition::Real { .. })
                && checker.is_same(unfolded, &app(body.symbol(), actuals))?);
        }
        if params.len() != actuals.len() {
            return Ok(false);
        }
        let mut env = Env::new();
        let mut operators = Operators::new();
        for (param, actual) in params.iter().zip(&actuals) {
            env.insert(
                param.symbol.clone(),
                Binding::Term {
                    formula: actual.clone(),
                    env: Rc::new(Env::new()),
                    operators: None,
                },
            );
            operators.insert(param.symbol.clone(), actual.clone());
        }
        return Ok(
            checker.get_key(&body, &Rc::new(env), 0, Some(&Rc::new(operators)))?
                == checker.get_top_key(unfolded)?,
        );
    }
    if folded.kind() != unfolded.kind() || folded.symbol() != unfolded.symbol() {
        return Ok(false);
    }
    if folded.kind() != TermKind::App && folded.kind() != TermKind::Not {
        return Ok(false);
    }
    if folded.arity() != unfolded.arity() {
        return Ok(false);
    }
    for index in 0..folded.arity() {
        if !is_unfolding(
            checker,
            definition,
            &folded.arg(index),
            &unfolded.arg(index),
            is_formula_only,
            is_in_term || folded.kind() == TermKind::App,
        )? {
            return Ok(false);
        }
    }
    Ok(true)
}

struct Quantified {
    bound: Vec<Rc<str>>,
    matrix: Expr,
}

fn get_bound(origin: &Expr) -> Quantified {
    let mut bound = Vec::new();
    let mut matrix = origin.clone();
    while matrix.kind == Kind::All {
        bound.push(matrix.args[0].symbol.clone());
        matrix = matrix.args[1].clone();
    }
    Quantified { bound, matrix }
}

// A pseudo-definition stands for its hypothesis, \A params : f(params) = body or <=> body.
fn is_defined_by(
    checker: &mut Checker<'_>,
    definition: &Definition,
    origin: &Expr,
) -> Checked<bool> {
    let quantified = get_bound(origin);
    let bound = &quantified.bound;
    let matrix = Term::from(&quantified.matrix);
    if !is_app(&matrix, "=", Some(2)) && matrix.kind() != TermKind::Equiv {
        return Ok(false);
    }
    let names: Vec<&Rc<str>> = definition
        .params()
        .iter()
        .map(|param| &param.symbol)
        .collect();
    if names.iter().collect::<HashSet<_>>().len() != names.len()
        || bound.iter().collect::<HashSet<_>>().len() != bound.len()
    {
        return Ok(false);
    }
    if names.len() != bound.len() || names.iter().any(|name| !bound.contains(*name)) {
        return Ok(false);
    }
    let params = definition.params();
    let mut heads = vec![app(
        definition.symbol(),
        params.iter().map(|param| variable(&param.symbol)).collect(),
    )];
    if params.is_empty() {
        heads.push(variable(definition.symbol()));
    }
    let sides = matrix.args();
    // The parameters are free in the head and the body, so compare them under the same names.
    let env = Rc::new(
        bound
            .iter()
            .zip(0..)
            .map(|(name, index)| (name.clone(), Binding::Depth(index)))
            .collect::<Env>(),
    );
    let depth = bound.len() as i64;
    let mut key_of = |formula: &Term| checker.get_key(formula, &env, depth, None);
    let head_keys = heads.iter().map(&mut key_of).collect::<Checked<Vec<_>>>()?;
    let body_key = key_of(&Term::from(definition.body()))?;
    Ok(
        (head_keys.contains(&key_of(&sides[0])?) && key_of(&sides[1])? == body_key)
            || (head_keys.contains(&key_of(&sides[1])?) && key_of(&sides[0])? == body_key),
    )
}

fn get_free_symbols(formula: &Expr, symbols: &mut Vec<Rc<str>>, seen: &mut HashSet<Rc<str>>) {
    if (formula.kind == Kind::Var || formula.kind == Kind::App)
        && seen.insert(formula.symbol.clone())
    {
        symbols.push(formula.symbol.clone());
    }
    for inner in &formula.args {
        get_free_symbols(inner, symbols, seen);
    }
}

fn visit(
    current: &Definition,
    by_symbol: &HashMap<&str, &Definition>,
    visiting: &mut HashSet<String>,
) -> bool {
    if !visiting.insert(current.symbol().to_string()) {
        return false;
    }
    let params: HashSet<&str> = current
        .params()
        .iter()
        .map(|param| &*param.symbol)
        .collect();
    let mut symbols = Vec::new();
    get_free_symbols(current.body(), &mut symbols, &mut HashSet::new());
    for symbol in &symbols {
        if let Some(next) = by_symbol.get(&**symbol)
            && !params.contains(&**symbol)
            && !visit(next, by_symbol, visiting)
        {
            return false;
        }
    }
    visiting.remove(current.symbol());
    true
}

// Real definitions are sound when each symbol has one and they don't refer to themselves.
fn is_well_founded(definition: &Definition, definitions: &[Rc<Definition>]) -> bool {
    let reals: Vec<&Definition> = definitions
        .iter()
        .map(|candidate| &**candidate)
        .filter(|candidate| matches!(candidate, Definition::Real { .. }))
        .collect();
    let by_symbol: HashMap<&str, &Definition> = reals
        .iter()
        .map(|candidate| (candidate.symbol(), *candidate))
        .collect();
    if reals
        .iter()
        .filter(|candidate| candidate.symbol() == definition.symbol())
        .count()
        != 1
    {
        return false;
    }
    visit(definition, &by_symbol, &mut HashSet::new())
}

/// The check of the rule that unfolds `definition`: `getDefinitionSpec`.
pub fn get_definition_spec(
    definition: &Rc<Definition>,
    args: &[Term],
    checker: &mut Checker<'_>,
) -> Checked<RuleSpec> {
    let context = checker.context;
    let definitions = context.definitions.as_slice();
    ensure(
        definitions
            .iter()
            .any(|candidate| Rc::ptr_eq(candidate, definition)),
    )?;
    // An equivalence only says the two sides have the same truth value, so it unfolds where a
    // formula is expected, not inside a term.
    let is_equivalence = match &**definition {
        Definition::Pseudo { origin, .. } => get_bound(origin).matrix.kind == Kind::Equiv,
        Definition::Real { .. } => false,
    };
    ensure(is_unfolding(
        checker,
        definition,
        &args[0],
        &args[1],
        is_equivalence,
        false,
    )?)?;
    match &**definition {
        Definition::Real { .. } => {
            ensure(is_well_founded(definition, definitions))?;
            spec(vec![args[0].clone()], vec![vec![args[1].clone()]])
        }
        Definition::Pseudo { origin, .. } => {
            ensure(is_defined_by(checker, definition, origin)?)?;
            spec(
                vec![args[0].clone(), Term::from(origin)],
                vec![vec![args[1].clone()]],
            )
        }
    }
}

//! Expr.Levels: the level of an expression (0 constant, 1 state, 2 action, 3 temporal, 4 undefined),
//! the weights of an operator's arguments, and the declared names the level depends on.
//! A port of `src/obligations/levels.ts`.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;

use crate::errors::{ObligationError, Result};
use crate::expression::{
    Bound, BoundDomain, Builtin, DefnCore, ExceptPoint, Expr, ExprCore, HypCore, IdentityCache,
    Level, Scope, ScopeRef, adjoin, adjoin_all, get_bound_fresh, get_bounded_fresh, get_fresh,
    get_local_defn, get_param_fresh, get_scope_at, hyp, is_builtin_apply, map_accumulate,
};

/// The TypeScript's `params` is a `Set` that is only unioned, filtered and tested for membership,
/// so no result depends on its order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LevelInfo {
    pub level: usize,
    pub weights: Vec<bool>,
    pub params: BTreeSet<String>,
}

fn get_info(level: usize, arity: usize) -> LevelInfo {
    LevelInfo {
        level,
        weights: vec![true; arity],
        params: BTreeSet::new(),
    }
}

/// `BUILTIN_LEVELS`: a builtin's level and arity.
fn get_builtin_level(builtin: Builtin) -> Option<(usize, usize)> {
    use Builtin::*;
    Some(match builtin {
        TRUE | FALSE => (0, 0),
        Implies | Equiv | Conj | Disj => (0, 2),
        Neg => (0, 1),
        Eq | Neq => (0, 2),
        STRING | BOOLEAN => (0, 0),
        SUBSET | UNION | DOMAIN => (0, 1),
        Subseteq | Mem | Notmem | Setminus | Cap | Cup => (0, 2),
        Actplus => (3, 2),
        BoxTrue | BoxFalse | Diamond => (3, 1),
        Prime | StrongPrime => (2, 1),
        ENABLED => (1, 1),
        UNCHANGED => (2, 1),
        Leadsto => (3, 2),
        Cdot => (2, 2),
        Nat | Int | Real | Infinity => (0, 0),
        Plus | Minus | Times | Ratio | Quotient | Remainder | Exp | Divides => (0, 2),
        Lteq | Lt | Gteq | Gt | Range => (0, 2),
        Uminus | Seq | Len => (0, 1),
        BSeq | Cat | Append => (0, 2),
        Head | Tail => (0, 1),
        SubSeq => (0, 3),
        SelectSeq | OneArg | Extend | Print => (0, 2),
        PrintT => (0, 1),
        Assert => (0, 2),
        JavaTime => (0, 0),
        TLCGet => (0, 1),
        TLCSet => (0, 2),
        Permutations => (0, 1),
        SortSeq => (0, 2),
        RandomElement => (0, 1),
        Any => (0, 0),
        ToString | Unprimable => (0, 1),
        Irregular => return None,
    })
}

/// `LEVEL_NUMBERS`.
pub fn level_number(level: Level) -> usize {
    match level {
        Level::Constant | Level::Unknown => 0,
        Level::State => 1,
        Level::Action => 2,
        Level::Temporal => 3,
    }
}

fn union<'a>(sets: impl IntoIterator<Item = &'a BTreeSet<String>>) -> BTreeSet<String> {
    sets.into_iter().flatten().cloned().collect()
}

fn combine_levels(infos: &[LevelInfo]) -> LevelInfo {
    LevelInfo {
        level: infos.iter().map(|info| info.level).fold(0, usize::max),
        weights: Vec::new(),
        params: union(infos.iter().map(|info| &info.params)),
    }
}

thread_local! {
    // The level of each hypothesis depends only on the scope before it.
    static HYP_LEVELS: RefCell<IdentityCache<Scope, LevelInfo>> =
        RefCell::new(IdentityCache::new());
}

fn compute_hyp_level(scope: &Rc<Scope>) -> Result<LevelInfo> {
    match &scope.hyp.core {
        HypCore::Flex { .. } => Ok(get_info(1, 0)),
        HypCore::Fresh {
            name, level, shape, ..
        } => Ok(LevelInfo {
            params: BTreeSet::from([name.clone()]),
            ..get_info(level_number(*level), *shape)
        }),
        HypCore::Defn { definition, .. } => match &definition.core {
            DefnCore::Operator { body, .. } | DefnCore::Bpragma { body, .. } => {
                get_level_info(&scope.rest, body)
            }
            _ => Err(ObligationError::assert_failure()),
        },
        HypCore::Fact { expression, .. } => get_level_info(&scope.rest, expression),
    }
}

fn get_hyp_level(scope: &Rc<Scope>) -> Result<LevelInfo> {
    if let Some(cached) = HYP_LEVELS.with(|cache| cache.borrow().get(scope)) {
        return Ok(cached);
    }
    let info = compute_hyp_level(scope)?;
    HYP_LEVELS.with(|cache| cache.borrow_mut().insert(scope, info.clone()));
    Ok(info)
}

fn get_bounds_level(scope: &ScopeRef, bounds: &[Bound], body: &Expr) -> Result<LevelInfo> {
    let domains = bounds
        .iter()
        .filter_map(|bound| match &bound.domain {
            BoundDomain::Domain(expression) => Some(get_level_info(scope, expression)),
            _ => None,
        })
        .collect::<Result<Vec<_>>>()?;
    let fresh = bounds.iter().map(get_bound_fresh).collect::<Vec<_>>();
    let mut infos = vec![get_level_info(&adjoin_all(scope, &fresh), body)?];
    infos.extend(domains);
    Ok(combine_levels(&infos))
}

fn apply_operator(operator: &LevelInfo, args: &[LevelInfo]) -> Result<LevelInfo> {
    if operator.weights.len() != args.len() {
        return Err(ObligationError::proof("Invalid number of arguments"));
    }
    let weighted = args
        .iter()
        .zip(&operator.weights)
        .filter(|(_arg, weight)| **weight)
        .map(|(arg, _weight)| arg)
        .collect::<Vec<_>>();
    Ok(LevelInfo {
        level: weighted
            .iter()
            .map(|arg| arg.level)
            .fold(operator.level, usize::max),
        weights: Vec::new(),
        params: union(
            std::iter::once(&operator.params).chain(weighted.iter().map(|arg| &arg.params)),
        ),
    })
}

fn recurse_all(scope: &ScopeRef, expressions: &[Expr]) -> Result<Vec<LevelInfo>> {
    expressions
        .iter()
        .map(|inner| get_level_info(scope, inner))
        .collect()
}

pub fn get_level_info(scope: &ScopeRef, expression: &Expr) -> Result<LevelInfo> {
    let recurse = |inner: &Expr| get_level_info(scope, inner);
    match &expression.core {
        ExprCore::Ix { index } => {
            let hyp_scope =
                get_scope_at(scope, index - 1).ok_or_else(ObligationError::assert_failure)?;
            get_hyp_level(&hyp_scope)
        }
        ExprCore::Internal { builtin } => {
            let entry = get_builtin_level(*builtin).ok_or_else(ObligationError::assert_failure)?;
            Ok(get_info(entry.0, entry.1))
        }
        ExprCore::Opaque { .. } | ExprCore::String { .. } | ExprCore::Num { .. } => {
            Ok(get_info(0, 0))
        }
        ExprCore::Lambda { params, body } => {
            let fresh = params.iter().map(get_param_fresh).collect::<Vec<_>>();
            let body = get_level_info(&adjoin_all(scope, &fresh), body)?;
            let names = params
                .iter()
                .map(|param| param.name.as_str())
                .collect::<Vec<_>>();
            Ok(LevelInfo {
                level: body.level,
                weights: params
                    .iter()
                    .map(|param| body.params.contains(&param.name))
                    .collect(),
                params: body
                    .params
                    .iter()
                    .filter(|name| !names.contains(&name.as_str()))
                    .cloned()
                    .collect(),
            })
        }
        ExprCore::Apply { operator, args } => {
            // The action frontend commutes a prime onto an operator, and tlapm keeps the level that
            // the application had.
            if let Some([inner]) = is_builtin_apply(operator, Builtin::Prime) {
                return recurse(&expression.with_core(ExprCore::Apply {
                    operator: inner.clone(),
                    args: args.clone(),
                }));
            }
            if let ExprCore::Opaque { .. } = operator.core {
                return apply_operator(&get_info(0, args.len()), &recurse_all(scope, args)?);
            }
            if let (ExprCore::Internal { builtin }, [arg]) = (&operator.core, args.as_slice()) {
                match builtin {
                    Builtin::Prime | Builtin::StrongPrime => {
                        if recurse(arg)?.level > 1 {
                            return Err(ObligationError::assert_failure());
                        }
                        return Ok(get_info(2, 1));
                    }
                    Builtin::ENABLED => {
                        let info = recurse(arg)?;
                        if info.level > 2 {
                            return Err(ObligationError::assert_failure());
                        }
                        return Ok(LevelInfo {
                            level: 1,
                            weights: Vec::new(),
                            params: info.params,
                        });
                    }
                    Builtin::UNCHANGED => {
                        let info = recurse(arg)?;
                        if info.level > 1 {
                            return Err(ObligationError::assert_failure());
                        }
                        return Ok(LevelInfo {
                            level: 2,
                            weights: Vec::new(),
                            params: info.params,
                        });
                    }
                    _ => {}
                }
            }
            if let ExprCore::Internal {
                builtin: Builtin::Cdot,
            } = operator.core
            {
                recurse_all(scope, args)?;
                return Ok(get_info(2, 0));
            }
            if let ExprCore::Internal {
                builtin: Builtin::Leadsto,
            } = operator.core
            {
                recurse_all(scope, args)?;
                return Ok(get_info(3, 2));
            }
            let operator = recurse(operator)?;
            apply_operator(&operator, &recurse_all(scope, args)?)
        }
        ExprCore::Sequent { sequent } => {
            let (inner, levels) =
                map_accumulate(scope.clone(), &sequent.context, |current, hyp| {
                    let next = adjoin(&current, hyp);
                    let level = match &next {
                        Some(next_scope) => get_hyp_level(next_scope)?.level,
                        // `adjoin` always gives a scope.
                        None => return Err(ObligationError::assert_failure()),
                    };
                    Ok((next, level))
                })?;
            let active = get_level_info(&inner, &sequent.active)?.level;
            Ok(get_info(
                levels.into_iter().fold(0, usize::max).max(active),
                0,
            ))
        }
        ExprCore::With {
            expression: inner, ..
        }
        | ExprCore::Dot {
            expression: inner, ..
        }
        | ExprCore::Parens {
            expression: inner, ..
        } => recurse(inner),
        ExprCore::Let { definitions, body } => {
            let defns = definitions
                .iter()
                .cloned()
                .map(get_local_defn)
                .collect::<Vec<_>>();
            get_level_info(&adjoin_all(scope, &defns), body)
        }
        ExprCore::If {
            condition,
            consequent,
            alternative,
        } => Ok(combine_levels(&[
            recurse(condition)?,
            recurse(consequent)?,
            recurse(alternative)?,
        ])),
        ExprCore::List { items, .. } => Ok(combine_levels(&recurse_all(scope, items)?)),
        ExprCore::Quant { bounds, body, .. } | ExprCore::Fcn { bounds, body } => {
            get_bounds_level(scope, bounds, body)
        }
        ExprCore::SetOf { element, bounds } => get_bounds_level(scope, bounds, element),
        ExprCore::Tquant { names, body, .. } => {
            let flexes = names
                .iter()
                .map(|name| hyp(HypCore::Flex { name: name.clone() }))
                .collect::<Vec<_>>();
            get_level_info(&adjoin_all(scope, &flexes), body)?;
            Ok(get_info(3, 0))
        }
        ExprCore::Choose { name, domain, body } => {
            get_binder_level(scope, name, domain.as_ref(), body)
        }
        ExprCore::SetSt { name, domain, body } => get_binder_level(scope, name, Some(domain), body),
        ExprCore::SetEnum { elements } | ExprCore::Tuple { elements } => {
            Ok(combine_levels(&recurse_all(scope, elements)?))
        }
        ExprCore::Product { factors } => Ok(combine_levels(&recurse_all(scope, factors)?)),
        ExprCore::FcnApp { function, args } => {
            let mut infos = vec![recurse(function)?];
            infos.extend(recurse_all(scope, args)?);
            Ok(combine_levels(&infos))
        }
        ExprCore::Arrow { domain, range } => {
            Ok(combine_levels(&[recurse(domain)?, recurse(range)?]))
        }
        ExprCore::Rect { fields } | ExprCore::Record { fields } => Ok(combine_levels(
            &fields
                .iter()
                .map(|field| recurse(&field.value))
                .collect::<Result<Vec<_>>>()?,
        )),
        ExprCore::Except { function, specs } => {
            let mut infos = vec![recurse(function)?];
            for spec in specs {
                for point in &spec.trail {
                    if let ExceptPoint::Apply(inner) = point {
                        infos.push(recurse(inner)?);
                    }
                }
                infos.push(recurse(&spec.value)?);
            }
            Ok(combine_levels(&infos))
        }
        ExprCore::Sub {
            action, subscript, ..
        } => Ok(LevelInfo {
            level: 2,
            ..combine_levels(&[recurse(action)?, recurse(subscript)?])
        }),
        ExprCore::Tsub {
            action, subscript, ..
        }
        | ExprCore::Fair {
            action, subscript, ..
        } => {
            recurse(action)?;
            recurse(subscript)?;
            Ok(get_info(3, 0))
        }
        ExprCore::Case { arms, other } => {
            let mut infos = Vec::new();
            for arm in arms {
                infos.push(recurse(&arm.condition)?);
                infos.push(recurse(&arm.body)?);
            }
            if let Some(other) = other {
                infos.push(recurse(other)?);
            }
            Ok(combine_levels(&infos))
        }
        ExprCore::Bang { .. } | ExprCore::At { .. } => Err(ObligationError::assert_failure()),
    }
}

/// The `Choose` and `SetSt` case.
fn get_binder_level(
    scope: &ScopeRef,
    name: &str,
    domain: Option<&Expr>,
    body: &Expr,
) -> Result<LevelInfo> {
    let domain_level = domain
        .map(|domain| get_level_info(scope, domain))
        .transpose()?;
    let bound = match domain {
        Some(domain) => get_bounded_fresh(name, domain.clone()),
        None => get_fresh(name, Level::Constant, 0),
    };
    let mut infos = vec![get_level_info(&adjoin(scope, &bound), body)?];
    infos.extend(domain_level);
    Ok(combine_levels(&infos))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::{
        Bound, CaseArm, Defn, ExceptSpec, Field, Hyp, Param, ParenForm, Quantifier, Sequent, Time,
        Visibility, WhereDefined, expr,
    };
    use crate::expression::{Bullet, Fairness, Modal};
    use crate::pragma::OldMethod;

    // The expected values come from running `levels.ts` under Bun on the same inputs.

    fn ix(index: isize) -> Expr {
        expr(ExprCore::Ix { index })
    }

    fn opaque(name: &str) -> Expr {
        expr(ExprCore::Opaque {
            name: name.to_owned(),
        })
    }

    fn internal(builtin: Builtin) -> Expr {
        expr(ExprCore::Internal { builtin })
    }

    fn apply(operator: Expr, args: Vec<Expr>) -> Expr {
        expr(ExprCore::Apply { operator, args })
    }

    fn apply_internal(builtin: Builtin, args: Vec<Expr>) -> Expr {
        apply(internal(builtin), args)
    }

    fn prime(inner: Expr) -> Expr {
        apply_internal(Builtin::Prime, vec![inner])
    }

    fn lambda(names: &[&str], body: Expr) -> Expr {
        expr(ExprCore::Lambda {
            params: names
                .iter()
                .map(|name| Param {
                    name: (*name).to_owned(),
                    shape: 0,
                    location: None,
                })
                .collect(),
            body,
        })
    }

    fn bang(inner: Expr) -> Expr {
        expr(ExprCore::Bang {
            expression: inner,
            selectors: Vec::new(),
        })
    }

    fn bound(name: &str, domain: BoundDomain) -> Bound {
        Bound {
            name: name.to_owned(),
            level: Level::Constant,
            domain,
        }
    }

    fn defn_hyp(core: DefnCore) -> Hyp {
        hyp(HypCore::Defn {
            definition: Defn {
                core,
                location: None,
            },
            where_defined: WhereDefined::User,
            visibility: Visibility::Visible,
            is_local: false,
            is_constness_unset: false,
        })
    }

    fn operator_hyp(name: &str, body: Expr) -> Hyp {
        defn_hyp(DefnCore::Operator {
            name: name.to_owned(),
            body,
        })
    }

    fn fact(expression: Expr) -> Hyp {
        hyp(HypCore::Fact {
            expression,
            visibility: Visibility::Visible,
            time: Time::Now,
            use_location: None,
        })
    }

    fn scope_of(hyps: &[Hyp]) -> ScopeRef {
        adjoin_all(&None, hyps)
    }

    /// #1 F (a constant operator of two arguments), #2 t, #3 x, #4 c.
    fn standard_scope() -> ScopeRef {
        scope_of(&[
            get_fresh("c", Level::Constant, 0),
            get_fresh("x", Level::State, 0),
            get_fresh("t", Level::Temporal, 0),
            get_fresh("F", Level::Constant, 2),
        ])
    }

    fn describe(scope: &ScopeRef, expression: &Expr) -> String {
        match get_level_info(scope, expression) {
            Ok(info) => format!(
                "{} [{}] {{{}}}",
                info.level,
                info.weights
                    .iter()
                    .map(bool::to_string)
                    .collect::<Vec<_>>()
                    .join(","),
                info.params.iter().cloned().collect::<Vec<_>>().join(",")
            ),
            Err(ObligationError::Proof {
                message, exception, ..
            }) => format!("error {message} | {exception}"),
            Err(other) => format!("unexpected {other:?}"),
        }
    }

    const BUG: &str = "error Oops, this seems to be a bug in TLAPM. | Assert_failure";
    const ARITY: &str =
        "error Invalid number of arguments | Failure(\"Invalid number of arguments\")";

    #[test]
    fn levels_of_leaves() {
        let empty = None;
        let scope = standard_scope();
        let cases = [
            (&empty, opaque("a"), "0 [] {}"),
            (
                &empty,
                expr(ExprCore::String {
                    value: "s".to_owned(),
                }),
                "0 [] {}",
            ),
            (
                &empty,
                expr(ExprCore::Num {
                    integer: "1".to_owned(),
                    fraction: String::new(),
                }),
                "0 [] {}",
            ),
            (&empty, internal(Builtin::Prime), "2 [true] {}"),
            (&empty, internal(Builtin::SubSeq), "0 [true,true,true] {}"),
            (&empty, internal(Builtin::Irregular), BUG),
            (&scope, ix(4), "0 [] {c}"),
            (&scope, ix(3), "1 [] {x}"),
            (&scope, ix(2), "3 [] {t}"),
            (&scope, ix(1), "0 [true,true] {F}"),
            (&scope, ix(0), "0 [true,true] {F}"),
            (&scope, ix(9), BUG),
            (&scope, expr(ExprCore::At { is_except: false }), BUG),
            (&scope, bang(ix(3)), BUG),
        ];
        for (scope, expression, expected) in cases {
            assert_eq!(describe(scope, &expression), expected);
        }
    }

    #[test]
    fn levels_of_applications() {
        let scope = standard_scope();
        let cases = [
            (apply(opaque("g"), vec![ix(3), ix(4)]), "1 [] {c,x}"),
            (prime(ix(3)), "2 [true] {}"),
            (prime(prime(ix(3))), BUG),
            (apply_internal(Builtin::StrongPrime, vec![ix(2)]), BUG),
            (
                apply_internal(
                    Builtin::ENABLED,
                    vec![apply_internal(Builtin::Eq, vec![prime(ix(3)), ix(3)])],
                ),
                "1 [] {x}",
            ),
            (apply_internal(Builtin::ENABLED, vec![ix(2)]), BUG),
            (apply_internal(Builtin::UNCHANGED, vec![ix(3)]), "2 [] {x}"),
            (apply_internal(Builtin::UNCHANGED, vec![prime(ix(3))]), BUG),
            (apply_internal(Builtin::Cdot, vec![ix(3), ix(2)]), "2 [] {}"),
            (
                apply_internal(Builtin::Leadsto, vec![ix(3), ix(4)]),
                "3 [true,true] {}",
            ),
            (
                apply_internal(Builtin::Conj, vec![ix(3), ix(4)]),
                "1 [] {c,x}",
            ),
            (apply_internal(Builtin::Conj, vec![ix(3)]), ARITY),
            (apply(ix(1), vec![ix(3), ix(4)]), "1 [] {F,c,x}"),
            (apply(ix(1), vec![ix(3)]), ARITY),
            (apply_internal(Builtin::Diamond, vec![ix(3)]), "3 [] {x}"),
            (
                lambda(
                    &["p", "q"],
                    apply_internal(Builtin::Plus, vec![ix(2), ix(5)]),
                ),
                "1 [true,false] {x}",
            ),
            (
                apply(
                    lambda(
                        &["p", "q"],
                        apply_internal(Builtin::Plus, vec![ix(2), ix(4)]),
                    ),
                    vec![ix(4), prime(ix(3))],
                ),
                "3 [] {c,t}",
            ),
            (apply(lambda(&["p"], ix(1)), Vec::new()), ARITY),
            (
                apply_internal(
                    Builtin::Conj,
                    vec![prime(prime(ix(3))), apply(ix(1), Vec::new())],
                ),
                BUG,
            ),
            (
                apply(apply(ix(1), Vec::new()), vec![prime(prime(ix(3)))]),
                ARITY,
            ),
        ];
        for (expression, expected) in cases {
            assert_eq!(describe(&scope, &expression), expected);
        }
        let primed_scope = scope_of(&[
            get_fresh("x", Level::State, 0),
            operator_hyp(
                "A",
                lambda(&["p"], apply_internal(Builtin::Plus, vec![ix(1), ix(2)])),
            ),
        ]);
        assert_eq!(
            describe(&primed_scope, &apply(prime(ix(1)), vec![ix(2)])),
            "1 [] {x}"
        );
    }

    #[test]
    fn levels_of_binders() {
        let scope = standard_scope();
        let tquant = |body: Expr| {
            expr(ExprCore::Tquant {
                quantifier: Quantifier::Exists,
                names: vec!["v".to_owned()],
                body,
            })
        };
        let cases = [
            (
                expr(ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![get_fresh("y", Level::Action, 0), fact(ix(1))],
                        active: ix(6),
                    },
                }),
                "2 [] {}",
            ),
            (
                expr(ExprCore::Sequent {
                    sequent: Sequent {
                        context: Vec::new(),
                        active: ix(4),
                    },
                }),
                "0 [] {}",
            ),
            (
                expr(ExprCore::Let {
                    definitions: vec![Defn {
                        core: DefnCore::Operator {
                            name: "D".to_owned(),
                            body: prime(ix(3)),
                        },
                        location: None,
                    }],
                    body: ix(1),
                }),
                "2 [true] {}",
            ),
            (
                expr(ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![
                        bound("b", BoundDomain::Domain(ix(4))),
                        bound("d", BoundDomain::Ditto),
                    ],
                    body: apply_internal(Builtin::Eq, vec![ix(1), ix(5)]),
                }),
                "1 [] {c,d,x}",
            ),
            (
                expr(ExprCore::Quant {
                    quantifier: Quantifier::Exists,
                    bounds: vec![bound("b", BoundDomain::Domain(ix(3)))],
                    body: ix(1),
                }),
                "1 [] {b,x}",
            ),
            (
                expr(ExprCore::Fcn {
                    bounds: vec![bound("b", BoundDomain::NoDomain)],
                    body: ix(1),
                }),
                "0 [] {b}",
            ),
            (
                expr(ExprCore::SetOf {
                    element: ix(3),
                    bounds: vec![bound("b", BoundDomain::Domain(ix(4)))],
                }),
                "3 [] {c,t}",
            ),
            (tquant(ix(1)), "3 [] {}"),
            (tquant(bang(ix(1))), BUG),
            (
                expr(ExprCore::Choose {
                    name: "k".to_owned(),
                    domain: None,
                    body: apply_internal(Builtin::Eq, vec![ix(1), ix(4)]),
                }),
                "1 [] {k,x}",
            ),
            (
                expr(ExprCore::Choose {
                    name: "k".to_owned(),
                    domain: Some(ix(4)),
                    body: apply_internal(Builtin::Eq, vec![ix(1), ix(4)]),
                }),
                "1 [] {c,k,x}",
            ),
            (
                expr(ExprCore::SetSt {
                    name: "k".to_owned(),
                    domain: ix(3),
                    body: apply_internal(Builtin::Mem, vec![ix(1), ix(5)]),
                }),
                "1 [] {c,k,x}",
            ),
        ];
        for (expression, expected) in cases {
            assert_eq!(describe(&scope, &expression), expected);
        }
    }

    #[test]
    fn levels_of_compound_expressions() {
        let scope = standard_scope();
        let field = |name: &str, value: Expr| Field {
            name: name.to_owned(),
            value,
        };
        let cases = [
            (
                expr(ExprCore::If {
                    condition: ix(4),
                    consequent: ix(3),
                    alternative: ix(4),
                }),
                "1 [] {c,x}",
            ),
            (
                expr(ExprCore::List {
                    bullet: Bullet::And,
                    items: vec![ix(4), ix(2)],
                }),
                "3 [] {c,t}",
            ),
            (
                expr(ExprCore::List {
                    bullet: Bullet::And,
                    items: Vec::new(),
                }),
                "0 [] {}",
            ),
            (
                expr(ExprCore::SetEnum {
                    elements: vec![ix(4), ix(3)],
                }),
                "1 [] {c,x}",
            ),
            (
                expr(ExprCore::Tuple {
                    elements: Vec::new(),
                }),
                "0 [] {}",
            ),
            (
                expr(ExprCore::Product {
                    factors: vec![ix(4), ix(4)],
                }),
                "0 [] {c}",
            ),
            (
                expr(ExprCore::FcnApp {
                    function: ix(4),
                    args: vec![ix(3)],
                }),
                "1 [] {c,x}",
            ),
            (
                expr(ExprCore::Arrow {
                    domain: ix(4),
                    range: ix(3),
                }),
                "1 [] {c,x}",
            ),
            (
                expr(ExprCore::Record {
                    fields: vec![field("a", ix(4)), field("b", ix(3))],
                }),
                "1 [] {c,x}",
            ),
            (
                expr(ExprCore::Rect {
                    fields: vec![field("a", ix(4))],
                }),
                "0 [] {c}",
            ),
            (
                expr(ExprCore::Except {
                    function: ix(4),
                    specs: vec![ExceptSpec {
                        trail: vec![ExceptPoint::Dot("a".to_owned()), ExceptPoint::Apply(ix(3))],
                        value: ix(4),
                    }],
                }),
                "1 [] {c,x}",
            ),
            (
                expr(ExprCore::Sub {
                    modal: Modal::Box,
                    action: ix(4),
                    subscript: ix(4),
                }),
                "2 [] {c}",
            ),
            (
                expr(ExprCore::Tsub {
                    modal: Modal::Dia,
                    action: ix(4),
                    subscript: ix(3),
                }),
                "3 [] {}",
            ),
            (
                expr(ExprCore::Fair {
                    fairness: Fairness::Weak,
                    subscript: ix(3),
                    action: ix(4),
                }),
                "3 [] {}",
            ),
            (
                expr(ExprCore::Case {
                    arms: vec![CaseArm {
                        condition: ix(4),
                        body: ix(4),
                    }],
                    other: Some(ix(3)),
                }),
                "1 [] {c,x}",
            ),
            (
                expr(ExprCore::Case {
                    arms: vec![CaseArm {
                        condition: ix(4),
                        body: ix(4),
                    }],
                    other: None,
                }),
                "0 [] {c}",
            ),
            (
                expr(ExprCore::With {
                    expression: ix(3),
                    method: OldMethod {
                        name: "zenon".to_owned(),
                        tactic: None,
                        timeout: None,
                    },
                }),
                "1 [] {x}",
            ),
            (
                expr(ExprCore::Dot {
                    expression: ix(2),
                    field: "f".to_owned(),
                }),
                "3 [] {t}",
            ),
            (
                expr(ExprCore::Parens {
                    expression: ix(3),
                    form: ParenForm::Syntax,
                }),
                "1 [] {x}",
            ),
        ];
        for (expression, expected) in cases {
            assert_eq!(describe(&scope, &expression), expected);
        }
    }

    #[test]
    fn levels_of_hypotheses() {
        let instance = scope_of(&[defn_hyp(DefnCore::Instance {
            name: "I".to_owned(),
            instance: crate::expression::InstanceDefinition {
                args: Vec::new(),
                module: "M".to_owned(),
                substitutions: Vec::new(),
                location: None,
            },
        })]);
        assert_eq!(describe(&instance, &ix(1)), BUG);
        let recursive = scope_of(&[defn_hyp(DefnCore::Recursive {
            name: "R".to_owned(),
            shape: 0,
        })]);
        assert_eq!(describe(&recursive, &ix(1)), BUG);
        let flex = scope_of(&[hyp(HypCore::Flex {
            name: "v".to_owned(),
        })]);
        assert_eq!(describe(&flex, &ix(1)), "1 [] {}");
        let facts = scope_of(&[get_fresh("x", Level::State, 0), fact(prime(ix(1)))]);
        assert_eq!(describe(&facts, &ix(1)), "2 [true] {}");
        // A second reading of the same scope comes from the cache and agrees.
        assert_eq!(describe(&facts, &ix(1)), "2 [true] {}");
    }

    #[test]
    fn level_numbers() {
        let numbers = [
            Level::Constant,
            Level::State,
            Level::Action,
            Level::Temporal,
            Level::Unknown,
        ]
        .map(level_number);
        assert_eq!(numbers, [0, 1, 2, 3, 0]);
    }
}

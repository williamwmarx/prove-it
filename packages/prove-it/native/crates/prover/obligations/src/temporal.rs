//! tlapm's expansions of temporal operators (Expr.Tla_norm), constant detection (Expr.Constness), and
//! the time of a fact (Expr.Temporal_props): a fact holds always when it is closed under [].
//! A port of `src/obligations/temporal.ts`.

use std::cell::RefCell;

use crate::errors::{ObligationError, Result};
use crate::expression::{
    BoundDomain, Builtin, Bullet, DefnCore, ExceptPoint, Expr, ExprCore, ExprNode, Fairness, Hyp,
    HypCore, IdentityCache, Level, Modal, ScopeRef, Time, adjoin, adjoin_all, apply_builtin, at,
    get_fresh, get_local_defn, get_scope_at, map_children,
};

/// `isApplied`: the arguments when the expression applies one of the builtins.
fn is_applied<'a>(expression: &'a ExprNode, builtins: &[Builtin]) -> Option<&'a [Expr]> {
    match &expression.core {
        ExprCore::Apply { operator, args } => match operator.core {
            ExprCore::Internal { builtin } if builtins.contains(&builtin) => Some(args),
            _ => None,
        },
        _ => None,
    }
}

fn apply_unchanged(expression: &Expr) -> Expr {
    apply_builtin(
        Builtin::UNCHANGED,
        vec![expression.clone()],
        &expression.props(),
    )
}

fn get_equality(expression: &Expr) -> Expr {
    let props = expression.props();
    apply_builtin(
        Builtin::Eq,
        vec![
            apply_builtin(Builtin::Prime, vec![expression.clone()], &props),
            expression.clone(),
        ],
        &props,
    )
}

/// E_tla_norm.rewrite_unch: UNCHANGED <<x, <<y>>>> as x' = x /\ y' = y.
pub fn rewrite_unchanged(expression: &Expr) -> Expr {
    fn flatten(inner: &Expr, items: &mut Vec<Expr>) {
        match &inner.core {
            ExprCore::Tuple { elements } => {
                for element in elements {
                    flatten(element, items);
                }
            }
            _ => items.push(inner.clone()),
        }
    }
    let mut items = Vec::new();
    flatten(expression, &mut items);
    match items.as_slice() {
        [] => at(
            ExprCore::Internal {
                builtin: Builtin::TRUE,
            },
            expression,
        ),
        [item] => get_equality(item),
        _ => at(
            ExprCore::List {
                bullet: Bullet::And,
                items: items.iter().map(get_equality).collect(),
            },
            expression,
        ),
    }
}

type Recurse<'a> = &'a dyn Fn(&Expr) -> Result<Expr>;

/// Each visitor rewrites the outermost match and leaves the rest of the tree as it is.
fn rewrite(
    expression: &Expr,
    matcher: &dyn Fn(&Expr, Recurse) -> Result<Option<Expr>>,
) -> Result<Expr> {
    let recurse = |inner: &Expr| rewrite(inner, matcher);
    match matcher(expression, &recurse)? {
        Some(rewritten) => Ok(rewritten),
        None => map_children(expression, &mut |inner| recurse(inner)),
    }
}

/// The TypeScript reads `args[0]` and `args[1]` of an application whatever its arity, and throws a
/// `TypeError` on a missing one; an application of the wrong arity is a bug in tlapm's terms.
fn get_arg(args: &[Expr], index: usize) -> Result<&Expr> {
    args.get(index).ok_or_else(ObligationError::assert_failure)
}

pub fn expand_leadsto(expression: &Expr) -> Result<Expr> {
    rewrite(expression, &|expression, recurse| {
        let Some(args) = is_applied(expression, &[Builtin::Leadsto]) else {
            return Ok(None);
        };
        let props = expression.props();
        let left = recurse(get_arg(args, 0)?)?;
        let right = recurse(get_arg(args, 1)?)?;
        Ok(Some(apply_builtin(
            Builtin::BoxTrue,
            vec![apply_builtin(
                Builtin::Implies,
                vec![left, apply_builtin(Builtin::Diamond, vec![right], &props)],
                &props,
            )],
            &props,
        )))
    })
}

pub fn expand_fairness(expression: &Expr) -> Result<Expr> {
    rewrite(expression, &|expression, _recurse| {
        let ExprCore::Fair {
            fairness,
            subscript,
            action,
        } = &expression.core
        else {
            return Ok(None);
        };
        let props = action.props();
        let enabled = apply_builtin(
            Builtin::ENABLED,
            vec![at(
                ExprCore::Sub {
                    modal: Modal::Dia,
                    action: action.clone(),
                    subscript: subscript.clone(),
                },
                action,
            )],
            &props,
        );
        let (outer, inner) = match fairness {
            Fairness::Weak => (Builtin::Diamond, Builtin::BoxTrue),
            Fairness::Strong => (Builtin::BoxTrue, Builtin::Diamond),
        };
        Ok(Some(apply_builtin(
            Builtin::Implies,
            vec![
                apply_builtin(
                    outer,
                    vec![apply_builtin(inner, vec![enabled], &props)],
                    &props,
                ),
                apply_builtin(
                    Builtin::BoxTrue,
                    vec![at(
                        ExprCore::Tsub {
                            modal: Modal::Dia,
                            action: action.clone(),
                            subscript: subscript.clone(),
                        },
                        action,
                    )],
                    &props,
                ),
            ],
            &props,
        )))
    })
}

pub fn expand_action(expression: &Expr) -> Result<Expr> {
    rewrite(expression, &|expression, recurse| {
        let (is_sub, modal, action, subscript) = match &expression.core {
            ExprCore::Sub {
                modal,
                action,
                subscript,
            } => (true, *modal, action, subscript),
            ExprCore::Tsub {
                modal,
                action,
                subscript,
            } => (false, *modal, action, subscript),
            _ => return Ok(None),
        };
        let props = expression.props();
        let action = recurse(action)?;
        let subscript = recurse(subscript)?;
        let step = match modal {
            Modal::Box => apply_builtin(
                Builtin::Disj,
                vec![action, apply_unchanged(&subscript)],
                &props,
            ),
            Modal::Dia => apply_builtin(
                Builtin::Conj,
                vec![
                    action,
                    apply_builtin(Builtin::Neg, vec![apply_unchanged(&subscript)], &props),
                ],
                &props,
            ),
        };
        if is_sub {
            return Ok(Some(step));
        }
        let outer = match modal {
            Modal::Box => Builtin::BoxTrue,
            Modal::Dia => Builtin::Diamond,
        };
        Ok(Some(apply_builtin(outer, vec![step], &props)))
    })
}

/// Only `get_time` uses this, so the locations `rewrite_unchanged` gives do not matter.
fn expand_unchanged(expression: &Expr) -> Result<Expr> {
    rewrite(expression, &|expression, _recurse| {
        let Some(args) = is_applied(expression, &[Builtin::UNCHANGED]) else {
            return Ok(None);
        };
        Ok(Some(rewrite_unchanged(get_arg(args, 0)?)))
    })
}

const TEMPORAL_BUILTINS: [Builtin; 10] = [
    Builtin::Prime,
    Builtin::StrongPrime,
    Builtin::Leadsto,
    Builtin::ENABLED,
    Builtin::UNCHANGED,
    Builtin::Cdot,
    Builtin::Actplus,
    Builtin::BoxTrue,
    Builtin::BoxFalse,
    Builtin::Diamond,
];

thread_local! {
    // Keyed by the body alone, as the TypeScript's is: the first scope a body is judged in decides
    // it for every later one, so the cache lives as long as the thread, as the TypeScript's module.
    static CONSTANT_BODIES: RefCell<IdentityCache<ExprNode, bool>> =
        RefCell::new(IdentityCache::new());
}

/// Forgets which bodies are constant.
pub(crate) fn reset_caches() {
    CONSTANT_BODIES.with(|cache| *cache.borrow_mut() = IdentityCache::new());
}

fn is_constant_hyp(scope: &ScopeRef, hyp: &Hyp) -> bool {
    match &hyp.core {
        HypCore::Fresh { level, .. } => *level == Level::Constant,
        HypCore::Defn { definition, .. } => match &definition.core {
            DefnCore::Operator { body, .. } => is_constant(scope, body),
            _ => false,
        },
        HypCore::Fact { expression, .. } => is_constant(scope, expression),
        HypCore::Flex { .. } => false,
    }
}

fn bind_constants<'a>(scope: &ScopeRef, names: impl Iterator<Item = &'a String>) -> ScopeRef {
    let fresh = names
        .map(|name| get_fresh(name, Level::Constant, 0))
        .collect::<Vec<_>>();
    adjoin_all(scope, &fresh)
}

pub fn is_constant(scope: &ScopeRef, expression: &Expr) -> bool {
    let recurse = |inner: &Expr| is_constant(scope, inner);
    match &expression.core {
        ExprCore::Ix { index } => {
            let Some(found) = get_scope_at(scope, index - 1) else {
                return false;
            };
            let body = match &found.hyp.core {
                HypCore::Fresh { level, .. } => return *level == Level::Constant,
                HypCore::Defn {
                    definition,
                    is_constness_unset: false,
                    ..
                } => match &definition.core {
                    DefnCore::Operator { body, .. } => body,
                    _ => return false,
                },
                _ => return false,
            };
            if let Some(cached) = CONSTANT_BODIES.with(|cache| cache.borrow().get(body)) {
                return cached;
            }
            let result = is_constant(&found.rest, body);
            CONSTANT_BODIES.with(|cache| cache.borrow_mut().insert(body, result));
            result
        }
        ExprCore::Opaque { .. }
        | ExprCore::String { .. }
        | ExprCore::Num { .. }
        | ExprCore::At { .. } => true,
        ExprCore::Internal { builtin } => !TEMPORAL_BUILTINS.contains(builtin),
        ExprCore::Tquant { .. }
        | ExprCore::Sub { .. }
        | ExprCore::Tsub { .. }
        | ExprCore::Fair { .. } => false,
        ExprCore::Lambda { params, body } => is_constant(
            &bind_constants(scope, params.iter().map(|param| &param.name)),
            body,
        ),
        ExprCore::Sequent { sequent } => {
            let mut inner = scope.clone();
            let mut is_good = true;
            for hyp in &sequent.context {
                let next = adjoin(&inner, hyp);
                is_good = is_good && is_constant_hyp(&inner, hyp);
                inner = next;
            }
            is_good && is_constant(&inner, &sequent.active)
        }
        ExprCore::Bang {
            expression: inner, ..
        }
        | ExprCore::With {
            expression: inner, ..
        }
        | ExprCore::Dot {
            expression: inner, ..
        }
        | ExprCore::Parens {
            expression: inner, ..
        } => recurse(inner),
        ExprCore::Apply { operator, args } => recurse(operator) && args.iter().all(recurse),
        ExprCore::Let { definitions, body } => {
            let mut inner = scope.clone();
            let mut is_good = true;
            for definition in definitions {
                let next = adjoin(&inner, &get_local_defn(definition.clone()));
                is_good = is_good
                    && match &definition.core {
                        DefnCore::Operator { body, .. } => is_constant(&inner, body),
                        _ => false,
                    };
                inner = next;
            }
            is_good && is_constant(&inner, body)
        }
        ExprCore::Quant { bounds, body, .. }
        | ExprCore::Fcn { bounds, body }
        | ExprCore::SetOf {
            bounds,
            element: body,
        } => {
            bounds.iter().all(|bound| match &bound.domain {
                BoundDomain::Domain(domain) => recurse(domain),
                _ => true,
            }) && is_constant(
                &bind_constants(scope, bounds.iter().map(|bound| &bound.name)),
                body,
            )
        }
        ExprCore::Choose { name, domain, body } => {
            domain.as_ref().is_none_or(recurse)
                && is_constant(&bind_constants(scope, std::iter::once(name)), body)
        }
        ExprCore::SetSt { name, domain, body } => {
            recurse(domain) && is_constant(&bind_constants(scope, std::iter::once(name)), body)
        }
        ExprCore::If {
            condition,
            consequent,
            alternative,
        } => recurse(condition) && recurse(consequent) && recurse(alternative),
        ExprCore::List { items, .. } => items.iter().all(recurse),
        ExprCore::Tuple { elements } | ExprCore::SetEnum { elements } => {
            elements.iter().all(recurse)
        }
        ExprCore::Product { factors } => factors.iter().all(recurse),
        ExprCore::FcnApp { function, args } => recurse(function) && args.iter().all(recurse),
        ExprCore::Rect { fields } | ExprCore::Record { fields } => {
            fields.iter().all(|field| recurse(&field.value))
        }
        ExprCore::Arrow { domain, range } => recurse(domain) && recurse(range),
        ExprCore::Except { function, specs } => {
            recurse(function)
                && specs.iter().all(|spec| {
                    spec.trail.iter().all(|point| match point {
                        ExceptPoint::Dot(_) => true,
                        ExceptPoint::Apply(inner) => recurse(inner),
                    }) && recurse(&spec.value)
                })
        }
        ExprCore::Case { arms, other } => {
            arms.iter()
                .all(|arm| recurse(&arm.condition) && recurse(&arm.body))
                && other.as_ref().is_none_or(recurse)
        }
    }
}

/// Temporal_props.box_closure: whether the formula is equivalent to [] of itself, judged by its
/// shape. Under a negation or on the left of =>, <> takes the place of [].
fn is_closed(scope: &ScopeRef, expression: &Expr, is_box: bool) -> bool {
    if is_constant(scope, expression) {
        return true;
    }
    let args = match &expression.core {
        ExprCore::Internal { builtin } => {
            return [
                Builtin::Eq,
                Builtin::Neq,
                Builtin::UNCHANGED,
                Builtin::TRUE,
                Builtin::FALSE,
            ]
            .contains(builtin);
        }
        ExprCore::List { items, .. } => {
            return items.iter().all(|item| is_closed(scope, item, is_box));
        }
        ExprCore::Sequent { sequent } => {
            return is_closed(
                &adjoin_all(scope, &sequent.context),
                &sequent.active,
                is_box,
            );
        }
        ExprCore::Apply { args, .. } => args,
        _ => return false,
    };
    let is_applied_to = |builtins: &[Builtin]| is_applied(expression, builtins).is_some();
    if is_applied_to(&[Builtin::BoxTrue, Builtin::BoxFalse]) && is_box {
        return true;
    }
    if is_applied_to(&[Builtin::Diamond]) && !is_box {
        return true;
    }
    match args.as_slice() {
        [arg]
            if is_applied_to(&[
                Builtin::BoxTrue,
                Builtin::BoxFalse,
                Builtin::Diamond,
                Builtin::Prime,
            ]) =>
        {
            return is_closed(scope, arg, is_box);
        }
        [arg] if is_applied_to(&[Builtin::Neg]) => return is_closed(scope, arg, !is_box),
        [left, right] if is_applied_to(&[Builtin::Conj, Builtin::Disj]) => {
            return is_closed(scope, left, is_box) && is_closed(scope, right, is_box);
        }
        [left, right] if is_applied_to(&[Builtin::Implies]) => {
            return is_closed(scope, left, !is_box) && is_closed(scope, right, is_box);
        }
        [left, right] if is_applied_to(&[Builtin::Equiv]) => {
            return [true, false].iter().all(|is_flipped| {
                is_closed(scope, left, is_box != *is_flipped)
                    && is_closed(scope, right, is_box == *is_flipped)
            });
        }
        _ => {}
    }
    let ExprCore::Apply { operator, .. } = &expression.core else {
        return false;
    };
    is_closed(scope, operator, is_box) && args.iter().all(|arg| is_closed(scope, arg, is_box))
}

pub fn get_time(scope: &ScopeRef, expression: &Expr) -> Result<Time> {
    let expanded = expand_leadsto(&expand_fairness(&expand_action(&expand_unchanged(
        expression,
    )?)?)?)?;
    Ok(if is_closed(scope, &expanded, true) {
        Time::Always
    } else {
        Time::Now
    })
}

/// Temporal_props.check_time_change: a proof stays in the always scope while no fact it assumes
/// holds only now.
pub fn get_scope_time(context: &[Hyp], time: Time) -> Time {
    if time == Time::Always
        && context.iter().any(|hyp| {
            matches!(
                hyp.core,
                HypCore::Fact {
                    time: Time::Now,
                    ..
                }
            )
        })
    {
        Time::Now
    } else {
        time
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;
    use crate::expression::{
        Bound, CaseArm, Defn, ExceptSpec, Field, Locus, Param, Quantifier, Sequent, Visibility,
        WhereDefined, expr, hyp,
    };

    // The expected values come from running `temporal.ts` under Bun on the same inputs.

    fn located(expression: Expr, line: u32) -> Expr {
        Rc::new(ExprNode {
            core: expression.core.clone(),
            location: Some(Locus {
                file: "f".into(),
                start_line: line,
                start_column: 1,
                end_line: line,
                end_column: 2,
            }),
            is_atomic: false,
        })
    }

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

    fn tuple(elements: Vec<Expr>) -> Expr {
        expr(ExprCore::Tuple { elements })
    }

    fn sub(modal: Modal, action: Expr, subscript: Expr) -> Expr {
        expr(ExprCore::Sub {
            modal,
            action,
            subscript,
        })
    }

    fn tsub(modal: Modal, action: Expr, subscript: Expr) -> Expr {
        expr(ExprCore::Tsub {
            modal,
            action,
            subscript,
        })
    }

    fn fair(fairness: Fairness, subscript: Expr, action: Expr) -> Expr {
        expr(ExprCore::Fair {
            fairness,
            subscript,
            action,
        })
    }

    fn if_then(condition: Expr, consequent: Expr, alternative: Expr) -> Expr {
        expr(ExprCore::If {
            condition,
            consequent,
            alternative,
        })
    }

    fn bound(name: &str, level: Level, domain: BoundDomain) -> Bound {
        Bound {
            name: name.to_owned(),
            level,
            domain,
        }
    }

    fn operator_defn(name: &str, body: Expr) -> Defn {
        Defn {
            core: DefnCore::Operator {
                name: name.to_owned(),
                body,
            },
            location: None,
        }
    }

    fn defn_hyp(definition: Defn, is_constness_unset: bool) -> Hyp {
        hyp(HypCore::Defn {
            definition,
            where_defined: WhereDefined::User,
            visibility: Visibility::Visible,
            is_local: false,
            is_constness_unset,
        })
    }

    fn fact(expression: Expr, time: Time) -> Hyp {
        hyp(HypCore::Fact {
            expression,
            visibility: Visibility::Visible,
            time,
            use_location: None,
        })
    }

    fn sequent(context: Vec<Hyp>, active: Expr) -> Expr {
        expr(ExprCore::Sequent {
            sequent: Sequent { context, active },
        })
    }

    fn scope_of(hyps: &[Hyp]) -> ScopeRef {
        adjoin_all(&None, hyps)
    }

    /// #1 F, #2 t, #3 x, #4 c.
    fn standard_scope() -> ScopeRef {
        scope_of(&[
            get_fresh("c", Level::Constant, 0),
            get_fresh("x", Level::State, 0),
            get_fresh("t", Level::Temporal, 0),
            get_fresh("F", Level::Constant, 2),
        ])
    }

    /// The shape of an expression, with `@line` after each located node.
    fn show(expression: &Expr) -> String {
        let shown = match &expression.core {
            ExprCore::Ix { index } => format!("#{index}"),
            ExprCore::Opaque { name } => name.clone(),
            ExprCore::Internal { builtin } => builtin.name().to_owned(),
            ExprCore::Apply { operator, args } => format!(
                "({})",
                std::iter::once(operator)
                    .chain(args)
                    .map(show)
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            ExprCore::List { bullet, items } => format!(
                "({bullet:?} {})",
                items.iter().map(show).collect::<Vec<_>>().join(" ")
            ),
            ExprCore::Tuple { elements } => format!(
                "<<{}>>",
                elements.iter().map(show).collect::<Vec<_>>().join(" ")
            ),
            ExprCore::Sub {
                modal,
                action,
                subscript,
            } => format!("(Sub {modal:?} {} {})", show(action), show(subscript)),
            ExprCore::Tsub {
                modal,
                action,
                subscript,
            } => format!("(Tsub {modal:?} {} {})", show(action), show(subscript)),
            ExprCore::Fair {
                fairness,
                subscript,
                action,
            } => format!("(Fair {fairness:?} {} {})", show(subscript), show(action)),
            ExprCore::If {
                condition,
                consequent,
                alternative,
            } => format!(
                "(If {} {} {})",
                show(condition),
                show(consequent),
                show(alternative)
            ),
            other => format!("{other:?}"),
        };
        match &expression.location {
            Some(location) => format!("{shown}@{}", location.start_line),
            None => shown,
        }
    }

    fn show_result(result: Result<Expr>) -> String {
        result.map_or_else(
            |error| format!("error {}", error.message()),
            |expression| show(&expression),
        )
    }

    #[test]
    fn rewrites_unchanged() {
        let x = located(opaque("x"), 1);
        let y = located(opaque("y"), 2);
        let z = located(opaque("z"), 3);
        let cases = [
            (
                located(tuple(vec![x.clone(), located(tuple(vec![y, z]), 5)]), 4),
                "(And (Eq@1 (Prime@1 x@1)@1 x@1)@1 (Eq@2 (Prime@2 y@2)@2 y@2)@2 (Eq@3 (Prime@3 z@3)@3 z@3)@3)@4",
            ),
            (
                located(tuple(vec![x.clone()]), 4),
                "(Eq@1 (Prime@1 x@1)@1 x@1)@1",
            ),
            (
                located(tuple(vec![located(tuple(Vec::new()), 6)]), 4),
                "TRUE@4",
            ),
            (x, "(Eq@1 (Prime@1 x@1)@1 x@1)@1"),
        ];
        for (expression, expected) in cases {
            assert_eq!(show(&rewrite_unchanged(&expression)), expected);
        }
    }

    #[test]
    fn expands_temporal_operators() {
        let x = located(opaque("x"), 1);
        let y = located(opaque("y"), 2);
        let z = located(opaque("z"), 3);
        let leadsto = located(
            apply_internal(
                Builtin::Conj,
                vec![
                    located(
                        apply_internal(
                            Builtin::Leadsto,
                            vec![
                                x.clone(),
                                located(
                                    apply_internal(Builtin::Leadsto, vec![y.clone(), z.clone()]),
                                    8,
                                ),
                            ],
                        ),
                        7,
                    ),
                    z.clone(),
                ],
            ),
            9,
        );
        assert_eq!(
            show_result(expand_leadsto(&leadsto)),
            "(Conj (BoxTrue@7 (Implies@7 x@1 (Diamond@7 (BoxTrue@8 (Implies@8 y@2 (Diamond@8 z@3)@8)@8)@8)@7)@7)@7 z@3)@9"
        );
        assert_eq!(
            show_result(expand_leadsto(&apply_internal(
                Builtin::Conj,
                vec![x.clone(), y.clone()]
            ))),
            "(Conj x@1 y@2)"
        );
        assert_eq!(
            show_result(expand_leadsto(&apply_internal(
                Builtin::Leadsto,
                vec![x.clone()]
            ))),
            "error Oops, this seems to be a bug in TLAPM."
        );

        let cases = [
            (
                expand_fairness(&located(fair(Fairness::Weak, y.clone(), x.clone()), 7)),
                "(Implies@1 (Diamond@1 (BoxTrue@1 (ENABLED@1 (Sub Dia x@1 y@2)@1)@1)@1)@1 (BoxTrue@1 (Tsub Dia x@1 y@2)@1)@1)@1",
            ),
            (
                expand_fairness(&apply_internal(
                    Builtin::Neg,
                    vec![fair(
                        Fairness::Strong,
                        y.clone(),
                        located(apply_internal(Builtin::Prime, vec![x.clone()]), 8),
                    )],
                )),
                "(Neg (Implies@8 (BoxTrue@8 (Diamond@8 (ENABLED@8 (Sub Dia (Prime x@1)@8 y@2)@8)@8)@8)@8 (BoxTrue@8 (Tsub Dia (Prime x@1)@8 y@2)@8)@8)@8)",
            ),
            (
                expand_fairness(&fair(
                    Fairness::Weak,
                    y.clone(),
                    fair(Fairness::Weak, y.clone(), x.clone()),
                )),
                "(Implies (Diamond (BoxTrue (ENABLED (Sub Dia (Fair Weak y@2 x@1) y@2)))) (BoxTrue (Tsub Dia (Fair Weak y@2 x@1) y@2)))",
            ),
            (
                expand_action(&located(sub(Modal::Box, x.clone(), y.clone()), 7)),
                "(Disj@7 x@1 (UNCHANGED@2 y@2)@2)@7",
            ),
            (
                expand_action(&located(sub(Modal::Dia, x.clone(), y.clone()), 7)),
                "(Conj@7 x@1 (Neg@7 (UNCHANGED@2 y@2)@2)@7)@7",
            ),
            (
                expand_action(&located(
                    tsub(Modal::Box, sub(Modal::Dia, x.clone(), z.clone()), y.clone()),
                    7,
                )),
                "(BoxTrue@7 (Disj@7 (Conj x@1 (Neg (UNCHANGED@3 z@3)@3)) (UNCHANGED@2 y@2)@2)@7)@7",
            ),
            (
                expand_action(&tsub(
                    Modal::Dia,
                    x.clone(),
                    located(tuple(vec![y.clone(), z.clone()]), 6),
                )),
                "(Diamond (Conj x@1 (Neg (UNCHANGED@6 <<y@2 z@3>>@6)@6)))",
            ),
            (
                expand_action(&if_then(
                    x.clone(),
                    sub(Modal::Box, x.clone(), y.clone()),
                    z.clone(),
                )),
                "(If x@1 (Disj x@1 (UNCHANGED@2 y@2)@2) z@3)",
            ),
        ];
        for (result, expected) in cases {
            assert_eq!(show_result(result), expected);
        }
    }

    #[test]
    fn judges_constants() {
        let scope = standard_scope();
        let lambda = |body: Expr| {
            expr(ExprCore::Lambda {
                params: vec![Param {
                    name: "p".to_owned(),
                    shape: 0,
                    location: None,
                }],
                body,
            })
        };
        let let_in = |definition: Defn, body: Expr| {
            expr(ExprCore::Let {
                definitions: vec![definition],
                body,
            })
        };
        let cases = [
            (ix(4), true),
            (ix(3), false),
            (ix(9), false),
            (ix(0), true),
            (opaque("a"), true),
            (expr(ExprCore::At { is_except: true }), true),
            (internal(Builtin::Prime), false),
            (internal(Builtin::Plus), true),
            (apply_internal(Builtin::Plus, vec![ix(4), ix(4)]), true),
            (apply_internal(Builtin::Plus, vec![ix(4), ix(3)]), false),
            (
                expr(ExprCore::Tquant {
                    quantifier: Quantifier::Exists,
                    names: vec!["v".to_owned()],
                    body: opaque("a"),
                }),
                false,
            ),
            (sub(Modal::Box, opaque("a"), opaque("b")), false),
            (lambda(ix(1)), true),
            (lambda(ix(4)), false),
            (
                sequent(
                    vec![get_fresh("k", Level::Constant, 0), fact(ix(1), Time::Now)],
                    ix(2),
                ),
                true,
            ),
            (
                sequent(
                    vec![hyp(HypCore::Flex {
                        name: "v".to_owned(),
                    })],
                    opaque("a"),
                ),
                false,
            ),
            (
                sequent(vec![defn_hyp(operator_defn("D", ix(4)), false)], ix(1)),
                true,
            ),
            (
                expr(ExprCore::Bang {
                    expression: ix(3),
                    selectors: Vec::new(),
                }),
                false,
            ),
            (let_in(operator_defn("D", ix(4)), ix(1)), true),
            (let_in(operator_defn("D", ix(4)), ix(5)), true),
            (
                let_in(
                    Defn {
                        core: DefnCore::Recursive {
                            name: "D".to_owned(),
                            shape: 0,
                        },
                        location: None,
                    },
                    opaque("a"),
                ),
                false,
            ),
            (
                expr(ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![bound("b", Level::State, BoundDomain::Domain(ix(4)))],
                    body: ix(1),
                }),
                true,
            ),
            (
                expr(ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![bound("b", Level::Constant, BoundDomain::Domain(ix(3)))],
                    body: ix(1),
                }),
                false,
            ),
            (
                expr(ExprCore::SetOf {
                    element: ix(2),
                    bounds: vec![
                        bound("b", Level::Constant, BoundDomain::Ditto),
                        bound("e", Level::Constant, BoundDomain::NoDomain),
                    ],
                }),
                true,
            ),
            (
                expr(ExprCore::Choose {
                    name: "k".to_owned(),
                    domain: None,
                    body: ix(1),
                }),
                true,
            ),
            (
                expr(ExprCore::SetSt {
                    name: "k".to_owned(),
                    domain: ix(3),
                    body: ix(1),
                }),
                false,
            ),
            (if_then(ix(4), ix(4), ix(3)), false),
            (tuple(vec![ix(4)]), true),
            (
                expr(ExprCore::Except {
                    function: ix(4),
                    specs: vec![ExceptSpec {
                        trail: vec![ExceptPoint::Dot("a".to_owned()), ExceptPoint::Apply(ix(4))],
                        value: ix(3),
                    }],
                }),
                false,
            ),
            (
                expr(ExprCore::Case {
                    arms: vec![CaseArm {
                        condition: ix(4),
                        body: ix(4),
                    }],
                    other: Some(ix(4)),
                }),
                true,
            ),
            (
                expr(ExprCore::Record {
                    fields: vec![Field {
                        name: "a".to_owned(),
                        value: ix(3),
                    }],
                }),
                false,
            ),
            (
                expr(ExprCore::Arrow {
                    domain: ix(4),
                    range: ix(4),
                }),
                true,
            ),
            (
                expr(ExprCore::FcnApp {
                    function: ix(4),
                    args: vec![ix(3)],
                }),
                false,
            ),
        ];
        for (expression, expected) in cases {
            assert_eq!(is_constant(&scope, &expression), expected, "{expression:?}");
        }
    }

    #[test]
    fn caches_constant_bodies_by_identity() {
        // The first scope a shared body is judged in decides it, as in the TypeScript.
        let shared = ix(1);
        let constant_scope = scope_of(&[
            get_fresh("c", Level::Constant, 0),
            defn_hyp(operator_defn("A", shared.clone()), false),
        ]);
        let state_scope = scope_of(&[
            get_fresh("v", Level::State, 0),
            defn_hyp(operator_defn("B", shared), false),
        ]);
        assert!(is_constant(&constant_scope, &ix(1)));
        assert!(is_constant(&state_scope, &ix(1)));
        let other_scope = scope_of(&[
            get_fresh("v", Level::State, 0),
            defn_hyp(operator_defn("B", ix(1)), false),
        ]);
        assert!(!is_constant(&other_scope, &ix(1)));
        let unset_scope = scope_of(&[
            get_fresh("c", Level::Constant, 0),
            defn_hyp(operator_defn("U", ix(1)), true),
        ]);
        assert!(!is_constant(&unset_scope, &ix(1)));
    }

    #[test]
    fn judges_constant_bodies_anew_after_a_reset() {
        let shared = ix(1);
        let constant_scope = scope_of(&[
            get_fresh("c", Level::Constant, 0),
            defn_hyp(operator_defn("A", shared.clone()), false),
        ]);
        let state_scope = scope_of(&[
            get_fresh("v", Level::State, 0),
            defn_hyp(operator_defn("B", shared), false),
        ]);
        assert!(is_constant(&constant_scope, &ix(1)));
        assert!(is_constant(&state_scope, &ix(1)));
        crate::reset_caches();
        assert!(!is_constant(&state_scope, &ix(1)));
        assert!(!is_constant(&constant_scope, &ix(1)));
    }

    #[test]
    fn gets_times() {
        let scope = standard_scope();
        let box_x = || apply_internal(Builtin::BoxTrue, vec![ix(3)]);
        let diamond_x = || apply_internal(Builtin::Diamond, vec![ix(3)]);
        let cases = [
            (ix(4), Time::Always),
            (ix(3), Time::Now),
            (box_x(), Time::Always),
            (diamond_x(), Time::Now),
            (
                apply_internal(Builtin::Neg, vec![diamond_x()]),
                Time::Always,
            ),
            (apply_internal(Builtin::Neg, vec![box_x()]), Time::Now),
            (
                apply_internal(Builtin::Implies, vec![diamond_x(), box_x()]),
                Time::Always,
            ),
            (
                apply_internal(Builtin::Implies, vec![box_x(), box_x()]),
                Time::Now,
            ),
            (
                apply_internal(Builtin::Equiv, vec![box_x(), box_x()]),
                Time::Now,
            ),
            (
                apply_internal(Builtin::Conj, vec![box_x(), ix(4)]),
                Time::Always,
            ),
            (
                apply_internal(Builtin::Leadsto, vec![ix(3), ix(3)]),
                Time::Always,
            ),
            (fair(Fairness::Weak, ix(3), ix(3)), Time::Always),
            (tsub(Modal::Box, ix(3), ix(3)), Time::Always),
            (tsub(Modal::Dia, ix(3), ix(3)), Time::Now),
            (apply_internal(Builtin::UNCHANGED, vec![ix(3)]), Time::Now),
            (
                expr(ExprCore::List {
                    bullet: Bullet::And,
                    items: vec![box_x(), ix(4)],
                }),
                Time::Always,
            ),
            (
                sequent(
                    vec![get_fresh("k", Level::State, 0)],
                    apply_internal(Builtin::BoxTrue, vec![ix(1)]),
                ),
                Time::Always,
            ),
            (internal(Builtin::Eq), Time::Always),
            (internal(Builtin::Conj), Time::Always),
            (apply(opaque("P"), vec![box_x()]), Time::Always),
            (if_then(ix(3), ix(4), ix(4)), Time::Now),
        ];
        for (expression, expected) in cases {
            assert_eq!(
                get_time(&scope, &expression),
                Ok(expected),
                "{expression:?}"
            );
        }
    }

    #[test]
    fn gets_scope_times() {
        let always = fact(opaque("a"), Time::Always);
        let now = fact(opaque("a"), Time::Now);
        assert_eq!(
            get_scope_time(&[always, get_fresh("k", Level::Constant, 0)], Time::Always),
            Time::Always
        );
        assert_eq!(
            get_scope_time(std::slice::from_ref(&now), Time::Always),
            Time::Now
        );
        assert_eq!(get_scope_time(&[now], Time::Now), Time::Now);
        assert_eq!(get_scope_time(&[], Time::Always), Time::Always);
    }
}

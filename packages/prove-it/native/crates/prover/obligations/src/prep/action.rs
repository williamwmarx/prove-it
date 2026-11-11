//! A port of tlapm's action frontend (Action.process_obligation), which makes an obligation first
//! order for the backends: [A]_v, <<A>>_v and UNCHANGED become primes (Expr.Tla_norm), primes move
//! down to the variables (Symbol_commute), and what remains modal becomes opaque (Coalesce).
//! A port of `src/prover/prep/action.ts`.
//!
//! The TypeScript's module-level `createContextMap`s live in thread-locals here, so they share each
//! mapped prefix of a context across obligations as the TypeScript's do.

use std::cell::RefCell;
use std::thread::LocalKey;

use crate::errors::{ObligationError, Result};
use crate::expression::{
    Bound, BoundDomain, Builtin, ContextMap, Defn, DefnCore, Expr, ExprCore, Hyp, HypCore, HypNode,
    Hyps, IdentityCache, Level, Modal, Param, Quantifier, ScopeRef, Sequent, adjoin, adjoin_all,
    apply_builtin, at, expr, get_bound_fresh, get_bounded_fresh, get_fresh, get_local_defn,
    get_param_fresh, get_scope_at, get_scope_hyps, hyp, map_accumulate, map_hyp, map_scoped,
    to_index,
};
use crate::format::render_doc;
use crate::levels::get_level_info;
use crate::prep::md5::get_md5;
use crate::printer::print_expression;
use crate::temporal::rewrite_unchanged;

type Rewrite = fn(&ScopeRef, &Expr) -> Result<Expr>;

fn get_hyp(scope: &ScopeRef, index: isize) -> Result<Hyp> {
    get_scope_at(scope, index - 1)
        .map(|found| found.hyp.clone())
        .ok_or_else(ObligationError::assert_failure)
}

fn get_level(scope: &ScopeRef, expression: &Expr) -> Result<usize> {
    Ok(get_level_info(scope, expression)?.level)
}

/// The arguments when the expression applies one of the builtins.
fn is_builtin<'a>(expression: &'a Expr, builtins: &[Builtin]) -> Option<&'a [Expr]> {
    match &expression.core {
        ExprCore::Apply { operator, args } => match operator.core {
            ExprCore::Internal { builtin } if builtins.contains(&builtin) => Some(args),
            _ => None,
        },
        _ => None,
    }
}

/// `mapScoped` with the scope as its state.
fn map_in_scope(scope: &ScopeRef, expression: &Expr, rewrite: Rewrite, hyps: Hyps) -> Result<Expr> {
    map_scoped(
        scope,
        expression,
        &mut |inner_scope, inner| rewrite(inner_scope, inner),
        &mut adjoin,
        hyps,
    )
}

type Step<State> = fn(&State, &Hyp, &Hyp) -> Result<(State, Option<Hyp>)>;

type SharedContextMap<State> = RefCell<ContextMap<State, Step<State>>>;

// A step of a sequent map: the hypothesis maps in the scope before it, hidden ones too if hyps is
// "all".
fn map_context_hyp(
    map: Rewrite,
    hyps: Hyps,
    scope: &ScopeRef,
    hyp: &Hyp,
) -> Result<(ScopeRef, Option<Hyp>)> {
    let mapped = map_hyp(hyp, &mut |inner| map(scope, inner), hyps)?;
    Ok((adjoin(scope, &mapped), Some(mapped)))
}

// Visit.map over a sequent: each hypothesis maps in the scope before it. The context maps by the
// obligation's own hypotheses, from which it derives.
fn map_sequent(
    context_map: &'static LocalKey<SharedContextMap<ScopeRef>>,
    map: Rewrite,
    keys: &[Hyp],
    sequent: &Sequent,
) -> Result<Sequent> {
    let mapped =
        context_map.with(|shared| shared.borrow_mut().map(keys, Some(&sequent.context)))?;
    Ok(Sequent {
        context: mapped.context,
        active: map(&mapped.state, &sequent.active)?,
    })
}

// Expr.Tla_norm.expand_action, then expand_unchanged.
fn expand_action(scope: &ScopeRef, expression: &Expr) -> Result<Expr> {
    let (ExprCore::Sub {
        modal,
        action,
        subscript,
    }
    | ExprCore::Tsub {
        modal,
        action,
        subscript,
    }) = &expression.core
    else {
        return map_in_scope(scope, expression, expand_action, Hyps::All);
    };
    let props = expression.props();
    let action = expand_action(scope, action)?;
    let subscript = expand_action(scope, subscript)?;
    let unchanged = apply_builtin(Builtin::UNCHANGED, vec![subscript], &props);
    let step = if *modal == Modal::Box {
        apply_builtin(Builtin::Disj, vec![action, unchanged], &props)
    } else {
        apply_builtin(
            Builtin::Conj,
            vec![action, apply_builtin(Builtin::Neg, vec![unchanged], &props)],
            &props,
        )
    };
    if matches!(expression.core, ExprCore::Sub { .. }) {
        return Ok(step);
    }
    let builtin = if *modal == Modal::Box {
        Builtin::BoxTrue
    } else {
        Builtin::Diamond
    };
    Ok(apply_builtin(builtin, vec![step], &props))
}

fn expand_unchanged(scope: &ScopeRef, expression: &Expr) -> Result<Expr> {
    match is_builtin(expression, &[Builtin::UNCHANGED]) {
        Some([arg]) => Ok(rewrite_unchanged(arg)),
        _ => map_in_scope(scope, expression, expand_unchanged, Hyps::All),
    }
}

fn apply_modal(builtin: Builtin, expression: &Expr) -> Expr {
    apply_builtin(builtin, vec![expression.clone()], &expression.props())
}

// prime_commuter: a prime distributes down to the declarations that are not constant.
fn commute_prime(scope: &ScopeRef, expression: &Expr) -> Result<Expr> {
    if let ExprCore::Ix { index } = expression.core {
        let hyp = get_hyp(scope, index)?;
        match &hyp.core {
            HypCore::Fresh {
                level: Level::Constant,
                ..
            } => return Ok(expression.clone()),
            HypCore::Defn {
                definition:
                    Defn {
                        core: DefnCore::Operator { body, .. },
                        ..
                    },
                ..
            } if get_level(&get_scope_at(scope, index), body)? == 0 => {
                return Ok(expression.clone());
            }
            _ => {}
        }
        return Ok(apply_modal(Builtin::Prime, expression));
    }
    if is_builtin(expression, &[Builtin::ENABLED]).is_some()
        || matches!(
            expression.core,
            ExprCore::Opaque { .. } | ExprCore::Sequent { .. } | ExprCore::Let { .. }
        )
    {
        return Ok(apply_modal(Builtin::Prime, expression));
    }
    if is_builtin(
        expression,
        &[
            Builtin::UNCHANGED,
            Builtin::Cdot,
            Builtin::Leadsto,
            Builtin::Actplus,
            Builtin::BoxTrue,
            Builtin::BoxFalse,
            Builtin::Diamond,
        ],
    )
    .is_some()
        || matches!(
            expression.core,
            ExprCore::Tquant { .. }
                | ExprCore::Sub { .. }
                | ExprCore::Tsub { .. }
                | ExprCore::Fair { .. }
        )
    {
        return Err(ObligationError::assert_failure());
    }
    map_in_scope(scope, expression, commute_prime, Hyps::Visible)
}

// box_commuter and dia_commuter: [] distributes over /\ and \A, and <> over \/ and \E, and both
// vanish on a constant.
fn commute_modal(builtin: Builtin, scope: &ScopeRef, expression: &Expr) -> Result<Expr> {
    let (connective, quantifier) = if builtin == Builtin::BoxTrue {
        (Builtin::Conj, Quantifier::Forall)
    } else {
        (Builtin::Disj, Quantifier::Exists)
    };
    if get_level(scope, expression)? == 0 {
        return Ok(expression.clone());
    }
    let is_distributed = is_builtin(expression, &[connective]).is_some()
        || matches!(
            &expression.core,
            ExprCore::Quant { quantifier: bound, .. } | ExprCore::Tquant { quantifier: bound, .. }
                if *bound == quantifier
        );
    if !is_distributed {
        return Ok(apply_modal(builtin, expression));
    }
    if builtin == Builtin::BoxTrue {
        map_in_scope(scope, expression, commute_box, Hyps::Visible)
    } else {
        map_in_scope(scope, expression, commute_diamond, Hyps::Visible)
    }
}

fn commute_box(scope: &ScopeRef, expression: &Expr) -> Result<Expr> {
    commute_modal(Builtin::BoxTrue, scope, expression)
}

fn commute_diamond(scope: &ScopeRef, expression: &Expr) -> Result<Expr> {
    commute_modal(Builtin::Diamond, scope, expression)
}

/// `COMMUTERS`.
fn get_commuter(builtin: Builtin) -> Option<Rewrite> {
    match builtin {
        Builtin::Prime => Some(commute_prime),
        Builtin::BoxTrue => Some(commute_box),
        Builtin::Diamond => Some(commute_diamond),
        _ => None,
    }
}

// symbol_commute: each prime, [] and <> commutes down its operand.
fn commute_symbols(scope: &ScopeRef, expression: &Expr) -> Result<Expr> {
    if let ExprCore::Apply { operator, args } = &expression.core
        && let ExprCore::Internal { builtin } = operator.core
        && let Some(commuter) = get_commuter(builtin)
    {
        let [arg] = args.as_slice() else {
            return Err(ObligationError::assert_failure());
        };
        return commuter(scope, arg);
    }
    map_in_scope(scope, expression, commute_symbols, Hyps::All)
}

/// `LEVEL_PREFIXES`: the prefix rename_with_loc gives a declaration of each level.
pub fn level_prefix(level: Level) -> &'static str {
    match level {
        Level::Constant => "CONSTANT",
        Level::State => "STATE",
        Level::Action => "ACTION",
        Level::Temporal => "TEMPORAL",
        Level::Unknown => "Unknown",
    }
}

/// The prefix rename_with_loc gives a definition by the number of its body's level.
pub const LEVEL_NUMBER_PREFIXES: [&str; 4] = ["CONSTANT", "STATE", "ACTION", "TEMPORAL"];

fn get_renamed(kind: &str, name: &str) -> String {
    format!("{kind}_{name}_")
}

#[derive(Clone)]
struct RenameState {
    scope: ScopeRef,
    original: ScopeRef,
}

// rename_with_loc: each declaration's name tells its level, as in CONSTANT_x_ or VARIABLE_x_. A
// definition's level is the one its body had before the commuters ran, unless given.
fn rename_defn(scope: &ScopeRef, definition: &Defn, level: Option<usize>) -> Result<Defn> {
    let core = match &definition.core {
        DefnCore::Operator { name, body } => {
            let body = rename(scope, body)?;
            let level = match level {
                Some(level) => level,
                None => get_level(scope, &body)?,
            };
            let kind = LEVEL_NUMBER_PREFIXES
                .get(level)
                .ok_or_else(ObligationError::assert_failure)?;
            DefnCore::Operator {
                name: get_renamed(kind, name),
                body,
            }
        }
        DefnCore::Bpragma {
            name,
            body,
            methods,
        } => DefnCore::Bpragma {
            name: name.clone(),
            body: rename(scope, body)?,
            methods: methods.clone(),
        },
        _ => return Ok(definition.clone()),
    };
    Ok(Defn {
        core,
        location: definition.location.clone(),
    })
}

fn rename_hyp(scope: &ScopeRef, hyp: &Hyp, level: Option<usize>) -> Result<Hyp> {
    let core = match &hyp.core {
        HypCore::Fresh {
            name,
            shape,
            level: fresh_level,
            domain,
            domain_visibility,
        } => HypCore::Fresh {
            name: get_renamed(level_prefix(*fresh_level), name),
            shape: *shape,
            level: *fresh_level,
            domain: domain
                .as_ref()
                .map(|domain| rename(scope, domain))
                .transpose()?,
            domain_visibility: *domain_visibility,
        },
        HypCore::Flex { name } => HypCore::Flex {
            name: get_renamed("VARIABLE", name),
        },
        HypCore::Defn {
            definition,
            where_defined,
            visibility,
            is_local,
            is_constness_unset,
        } => HypCore::Defn {
            definition: rename_defn(scope, definition, level)?,
            where_defined: *where_defined,
            visibility: *visibility,
            is_local: *is_local,
            is_constness_unset: *is_constness_unset,
        },
        HypCore::Fact {
            expression,
            visibility,
            time,
            use_location,
        } => HypCore::Fact {
            expression: rename(scope, expression)?,
            visibility: *visibility,
            time: *time,
            use_location: use_location.clone(),
        },
    };
    Ok(hyp.with_core(core))
}

// tlapm reads levels from properties that Expr.Levels computes before the frontend rewrites
// anything, and each node it builds takes the properties of a node it replaces: UNCHANGED's
// equalities those of the tuple or its only element, and a commuted prime, [] or <> those of its
// operand. A definition's name tells the level its body's top node ends up with.
fn get_original_level(scope: &ScopeRef, hyp: &Hyp) -> Result<Option<usize>> {
    let HypCore::Defn {
        definition:
            Defn {
                core: DefnCore::Operator { body, .. },
                ..
            },
        ..
    } = &hyp.core
    else {
        return Ok(None);
    };
    let get_node_level = |expression: &Expr| {
        let Some(args) = is_builtin(expression, &[Builtin::UNCHANGED]) else {
            return get_level(scope, expression);
        };
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
        // The TypeScript reads args[0] whatever the arity, and throws a TypeError without one.
        let tuple = args.first().ok_or_else(ObligationError::assert_failure)?;
        let mut items = Vec::new();
        flatten(tuple, &mut items);
        match items.as_slice() {
            [item] => get_level(scope, item),
            _ => get_level(scope, tuple),
        }
    };
    let commuted = match is_builtin(body, &[Builtin::Prime, Builtin::BoxTrue, Builtin::Diamond]) {
        Some([operand]) => operand,
        _ => body,
    };
    get_node_level(commuted).map(Some)
}

// renameSequent on the obligation, with the levels of its definitions from before commuting.
fn rename_context(
    current: &RenameState,
    hyp: &Hyp,
    original: &Hyp,
) -> Result<(RenameState, Option<Hyp>)> {
    let renamed = rename_hyp(
        &current.scope,
        hyp,
        get_original_level(&current.original, original)?,
    )?;
    let next = RenameState {
        scope: adjoin(&current.scope, &renamed),
        original: adjoin(&current.original, original),
    };
    Ok((next, Some(renamed)))
}

fn rename_obligation(commuted: &Sequent, original: &Sequent) -> Result<Sequent> {
    let renamed = RENAME_CONTEXT.with(|shared| {
        shared
            .borrow_mut()
            .map(&original.context, Some(&commuted.context))
    })?;
    Ok(Sequent {
        context: renamed.context,
        active: rename(&renamed.state.scope, &commuted.active)?,
    })
}

fn rename_sequent(scope: &ScopeRef, sequent: &Sequent) -> Result<Sequent> {
    let (inner, context) = map_accumulate(scope.clone(), &sequent.context, |current, hyp| {
        let renamed = rename_hyp(&current, hyp, None)?;
        Ok((adjoin(&current, &renamed), renamed))
    })?;
    Ok(Sequent {
        context,
        active: rename(&inner, &sequent.active)?,
    })
}

fn rename(scope: &ScopeRef, expression: &Expr) -> Result<Expr> {
    let core = match &expression.core {
        ExprCore::Lambda { params, body } => {
            let params: Vec<_> = params
                .iter()
                .map(|param| Param {
                    name: get_renamed("Unknown", &param.name),
                    ..param.clone()
                })
                .collect();
            let fresh: Vec<_> = params.iter().map(get_param_fresh).collect();
            let inner = adjoin_all(scope, &fresh);
            ExprCore::Lambda {
                body: rename(&inner, body)?,
                params,
            }
        }
        ExprCore::Tquant {
            quantifier,
            names,
            body,
        } => {
            let flex: Vec<_> = names
                .iter()
                .map(|name| {
                    hyp(HypCore::Flex {
                        name: get_renamed("VARIABLE", name),
                    })
                })
                .collect();
            let inner = adjoin_all(scope, &flex);
            ExprCore::Tquant {
                quantifier: *quantifier,
                names: names.clone(),
                body: rename(&inner, body)?,
            }
        }
        ExprCore::Choose { name, domain, body } => {
            let domain = domain
                .as_ref()
                .map(|domain| rename(scope, domain))
                .transpose()?;
            let name = get_renamed("CONSTANT", name);
            let bound = match &domain {
                Some(domain) => get_bounded_fresh(&name, domain.clone()),
                None => get_fresh(&name, Level::Constant, 0),
            };
            ExprCore::Choose {
                body: rename(&adjoin(scope, &bound), body)?,
                name,
                domain,
            }
        }
        ExprCore::SetSt { name, domain, body } => {
            let domain = rename(scope, domain)?;
            let name = get_renamed("CONSTANT", name);
            let body = rename(
                &adjoin(scope, &get_bounded_fresh(&name, domain.clone())),
                body,
            )?;
            ExprCore::SetSt { name, domain, body }
        }
        ExprCore::Quant { bounds, .. }
        | ExprCore::Fcn { bounds, .. }
        | ExprCore::SetOf { bounds, .. } => {
            let bounds = bounds
                .iter()
                .map(|bound| {
                    Ok(Bound {
                        name: get_renamed(level_prefix(bound.level), &bound.name),
                        level: bound.level,
                        domain: match &bound.domain {
                            BoundDomain::Domain(domain) => {
                                BoundDomain::Domain(rename(scope, domain)?)
                            }
                            other => other.clone(),
                        },
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            let fresh: Vec<_> = bounds.iter().map(get_bound_fresh).collect();
            let inner = adjoin_all(scope, &fresh);
            match &expression.core {
                ExprCore::SetOf { element, .. } => ExprCore::SetOf {
                    element: rename(&inner, element)?,
                    bounds,
                },
                ExprCore::Quant {
                    quantifier, body, ..
                } => ExprCore::Quant {
                    quantifier: *quantifier,
                    body: rename(&inner, body)?,
                    bounds,
                },
                ExprCore::Fcn { body, .. } => ExprCore::Fcn {
                    body: rename(&inner, body)?,
                    bounds,
                },
                _ => return Err(ObligationError::assert_failure()),
            }
        }
        ExprCore::Let { definitions, body } => {
            let (inner, definitions) =
                map_accumulate(scope.clone(), definitions, |current, definition| {
                    let renamed = rename_defn(&current, definition, None)?;
                    Ok((adjoin(&current, &get_local_defn(renamed.clone())), renamed))
                })?;
            ExprCore::Let {
                definitions,
                body: rename(&inner, body)?,
            }
        }
        ExprCore::Sequent { sequent } => ExprCore::Sequent {
            sequent: rename_sequent(scope, sequent)?,
        },
        _ => return map_in_scope(scope, expression, rename, Hyps::All),
    };
    Ok(expression.with_core(core))
}

thread_local! {
    // E_substitutive.make_array's results, keyed by the hypothesis that holds the definition, as
    // the TypeScript keys them by the definition: one is never shared between hypotheses there.
    static SUBSTITUTIVE_ARGS: RefCell<IdentityCache<HypNode, Vec<bool>>> =
        RefCell::new(IdentityCache::new());
}

// E_substitutive.make_array: for each parameter of an operator, counting from the last, whether
// the body uses it only outside primes and the other modal operators.
fn get_substitutive_args(scope: &ScopeRef, hyp: &Hyp) -> Result<Vec<bool>> {
    if let Some(cached) = SUBSTITUTIVE_ARGS.with(|cache| cache.borrow().get(hyp)) {
        return Ok(cached);
    }
    let HypCore::Defn {
        definition:
            Defn {
                core: DefnCore::Operator { body, .. },
                ..
            },
        ..
    } = &hyp.core
    else {
        return Ok(Vec::new());
    };
    let ExprCore::Lambda {
        params,
        body: lambda_body,
    } = &body.core
    else {
        return Ok(Vec::new());
    };
    let fresh: Vec<_> = params.iter().map(get_param_fresh).collect();
    let inner = adjoin_all(scope, &fresh);
    let result = (1..=params.len())
        .map(|index| is_substitutive(&inner, lambda_body, to_index(index), true))
        .collect::<Result<Vec<_>>>()?;
    SUBSTITUTIVE_ARGS.with(|cache| cache.borrow_mut().insert(hyp, result.clone()));
    Ok(result)
}

const UNARY_MODALS: [Builtin; 7] = [
    Builtin::Prime,
    Builtin::StrongPrime,
    Builtin::BoxTrue,
    Builtin::BoxFalse,
    Builtin::Diamond,
    Builtin::ENABLED,
    Builtin::UNCHANGED,
];

const BINARY_MODALS: [Builtin; 3] = [Builtin::Leadsto, Builtin::Actplus, Builtin::Cdot];

// compute_substitutivity_array: whether the parameter at index occurs only where scope holds.
fn is_substitutive(
    scope: &ScopeRef,
    expression: &Expr,
    index: isize,
    is_in_scope: bool,
) -> Result<bool> {
    if let ExprCore::Ix { index: found } = expression.core {
        return Ok(is_in_scope || found != index);
    }
    if let ExprCore::Apply { operator, args } = &expression.core
        && let ExprCore::Internal { builtin } = operator.core
        && ((UNARY_MODALS.contains(&builtin) && args.len() == 1)
            || (BINARY_MODALS.contains(&builtin) && args.len() == 2))
    {
        return every(args, |arg| is_substitutive(scope, arg, index, false));
    }
    if let ExprCore::Sub {
        action, subscript, ..
    } = &expression.core
    {
        return every(&[action.clone(), subscript.clone()], |inner| {
            is_substitutive(scope, inner, index, false)
        });
    }
    if let ExprCore::Apply { operator, args } = &expression.core
        && let ExprCore::Ix {
            index: operator_index,
        } = operator.core
        && let Some(hyp_scope) = get_scope_at(scope, operator_index - 1)
        && let HypCore::Defn {
            definition:
                Defn {
                    core: DefnCore::Operator { .. },
                    ..
                },
            ..
        } = &hyp_scope.hyp.core
    {
        let substitutive = get_substitutive_args(&hyp_scope.rest, &hyp_scope.hyp)?;
        for (position, arg) in args.iter().enumerate() {
            let is_arg_in_scope = *substitutive
                .get(position)
                .ok_or_else(ObligationError::assert_failure)?;
            if !is_substitutive(scope, arg, index, is_arg_in_scope)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    let mut is_found = true;
    map_scoped(
        &(scope.clone(), index),
        expression,
        &mut |state, inner| {
            if is_found {
                is_found = is_substitutive(&state.0, inner, state.1, is_in_scope)?;
            }
            Ok(inner.clone())
        },
        &mut |state, hyp| (adjoin(&state.0, hyp), state.1 + 1),
        Hyps::All,
    )?;
    Ok(is_found)
}

/// `Array.prototype.every`, which stops at the first false.
fn every(items: &[Expr], mut test: impl FnMut(&Expr) -> Result<bool>) -> Result<bool> {
    for item in items {
        if !test(item)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Coalesce.crypthash: h and the first five hexadecimal digits of the MD5 of the expression as
/// tlapm prints it.
pub fn get_hash_name(hyps: &[Hyp], expression: &Expr) -> Result<String> {
    let printed = render_doc(&print_expression(hyps, expression)?, 68)?;
    Ok(format!("h{}", &get_md5(&printed)[..5]))
}

fn coalesce(scope: &ScopeRef, expression: &Expr) -> Result<Expr> {
    Ok(at(
        ExprCore::Opaque {
            name: get_hash_name(&get_scope_hyps(scope), expression)?,
        },
        expression,
    ))
}

/// `substitutive[args.length - position - 1]`, which is undefined, so false, past its end.
fn is_substitutive_at(substitutive: &[bool], count: usize, position: usize) -> bool {
    substitutive
        .get(count - position - 1)
        .copied()
        .unwrap_or(false)
}

// coalesce_operator: an operator applied to arguments that are not all substitutive is opaque,
// hiding the arguments that are constant or substitutive.
fn coalesce_operator(
    scope: &ScopeRef,
    name: &str,
    substitutive: &[bool],
    from: &Expr,
    args: &[Expr],
) -> Result<Expr> {
    let starred = args
        .iter()
        .enumerate()
        .map(|(position, arg)| {
            let is_hidden = get_level(scope, arg)? == 0
                || is_substitutive_at(substitutive, args.len(), position);
            Ok(if is_hidden {
                at(
                    ExprCore::Opaque {
                        name: "*".to_owned(),
                    },
                    arg,
                )
            } else {
                arg.clone()
            })
        })
        .collect::<Result<Vec<_>>>()?;
    coalesce(
        scope,
        &at(
            ExprCore::Apply {
                operator: expr(ExprCore::Opaque {
                    name: name.to_owned(),
                }),
                args: starred,
            },
            from,
        ),
    )
}

const MODAL_BUILTINS: [Builtin; 9] = [
    Builtin::Prime,
    Builtin::StrongPrime,
    Builtin::BoxTrue,
    Builtin::BoxFalse,
    Builtin::Diamond,
    Builtin::Leadsto,
    Builtin::ENABLED,
    Builtin::Cdot,
    Builtin::UNCHANGED,
];

fn coalesce_args(scope: &ScopeRef, args: &[Expr]) -> Result<Vec<Expr>> {
    args.iter()
        .map(|inner| coalesce_modal(scope, inner))
        .collect()
}

// coalesce_modal_visitor: a primed declaration becomes the opaque name#prime, and every other
// modal expression an opaque name. tlapm means to apply that name to the expression's free
// variables, but compute_vars collects them into an instance variable and returns its own empty
// set, so the name always stands alone.
fn coalesce_modal(scope: &ScopeRef, expression: &Expr) -> Result<Expr> {
    let ExprCore::Apply { operator, args } = &expression.core else {
        return map_in_scope(scope, expression, coalesce_modal, Hyps::Visible);
    };
    if let Some([arg]) = is_builtin(expression, &[Builtin::Prime, Builtin::StrongPrime])
        && let ExprCore::Ix { index } = arg.core
    {
        let hyp = get_hyp(scope, index)?;
        if let HypCore::Fresh { name, .. } | HypCore::Flex { name } = &hyp.core {
            return Ok(at(
                ExprCore::Opaque {
                    name: format!("{name}#prime"),
                },
                expression,
            ));
        }
    }
    if is_builtin(expression, &MODAL_BUILTINS).is_some() {
        return coalesce(scope, expression);
    }
    let ExprCore::Ix {
        index: operator_index,
    } = operator.core
    else {
        return map_in_scope(scope, expression, coalesce_modal, Hyps::Visible);
    };
    let hyp_scope =
        get_scope_at(scope, operator_index - 1).ok_or_else(ObligationError::assert_failure)?;
    match &hyp_scope.hyp.core {
        HypCore::Defn {
            definition:
                Defn {
                    core: DefnCore::Operator { name, .. },
                    ..
                },
            ..
        } => {
            let substitutive = get_substitutive_args(&hyp_scope.rest, &hyp_scope.hyp)?;
            let mut is_kept = true;
            for (position, inner) in args.iter().enumerate() {
                if !(get_level(scope, inner)? == 0
                    || is_substitutive_at(&substitutive, args.len(), position))
                {
                    is_kept = false;
                    break;
                }
            }
            if is_kept {
                return map_in_scope(scope, expression, coalesce_modal, Hyps::Visible);
            }
            let opaque = coalesce_operator(scope, name, &substitutive, operator, args)?;
            Ok(at(
                ExprCore::Apply {
                    operator: opaque,
                    args: coalesce_args(scope, args)?,
                },
                expression,
            ))
        }
        HypCore::Flex { .. } => map_in_scope(scope, expression, coalesce_modal, Hyps::Visible),
        HypCore::Fresh {
            level: Level::Constant,
            ..
        } => Ok(at(
            ExprCore::Apply {
                operator: operator.clone(),
                args: coalesce_args(scope, args)?,
            },
            expression,
        )),
        HypCore::Fresh { name, .. } => {
            let not_substitutive = vec![false; args.len()];
            coalesce_operator(scope, name, &not_substitutive, operator, args)
        }
        _ => Err(ObligationError::assert_failure()),
    }
}

thread_local! {
    static EXPAND_ACTION_SEQUENT: SharedContextMap<ScopeRef> =
        RefCell::new(ContextMap::new(None, |scope, hyp, _| {
            map_context_hyp(expand_action, Hyps::All, scope, hyp)
        }));

    static EXPAND_UNCHANGED_SEQUENT: SharedContextMap<ScopeRef> =
        RefCell::new(ContextMap::new(None, |scope, hyp, _| {
            map_context_hyp(expand_unchanged, Hyps::All, scope, hyp)
        }));

    static COMMUTE_SEQUENT: SharedContextMap<ScopeRef> =
        RefCell::new(ContextMap::new(None, |scope, hyp, _| {
            map_context_hyp(commute_symbols, Hyps::All, scope, hyp)
        }));

    static COALESCE_SEQUENT: SharedContextMap<ScopeRef> =
        RefCell::new(ContextMap::new(None, |scope, hyp, _| {
            map_context_hyp(coalesce_modal, Hyps::Visible, scope, hyp)
        }));

    static RENAME_CONTEXT: SharedContextMap<RenameState> = RefCell::new(ContextMap::new(
        RenameState {
            scope: None,
            original: None,
        },
        rename_context,
    ));
}

/// Forgets the mapped contexts and the operators' substitutive arguments.
pub(crate) fn reset_caches() {
    for context_map in [
        &EXPAND_ACTION_SEQUENT,
        &EXPAND_UNCHANGED_SEQUENT,
        &COMMUTE_SEQUENT,
        &COALESCE_SEQUENT,
    ] {
        context_map.with(|shared| shared.borrow_mut().clear());
    }
    RENAME_CONTEXT.with(|shared| shared.borrow_mut().clear());
    SUBSTITUTIVE_ARGS.with(|cache| *cache.borrow_mut() = IdentityCache::new());
}

/// process_eob, on an obligation's sequent.
pub fn process_obligation(sequent: &Sequent) -> Result<Sequent> {
    let keys = &sequent.context;
    let expanded = map_sequent(
        &EXPAND_UNCHANGED_SEQUENT,
        expand_unchanged,
        keys,
        &map_sequent(&EXPAND_ACTION_SEQUENT, expand_action, keys, sequent)?,
    )?;
    let commuted = map_sequent(&COMMUTE_SEQUENT, commute_symbols, keys, &expanded)?;
    map_sequent(
        &COALESCE_SEQUENT,
        coalesce_modal,
        keys,
        &rename_obligation(&commuted, sequent)?,
    )
}

#[cfg(test)]
pub(crate) mod tests {

    // The expected values come from running `action.ts` and `encode.ts` under Bun on the same
    // sequents, serialized as JSON.

    use std::rc::Rc;

    use super::{LEVEL_NUMBER_PREFIXES, get_hash_name, level_prefix, process_obligation};
    use crate::errors::{ObligationError, Result};
    use crate::expression::{
        Bound, BoundDomain, Builtin, Bullet, CaseArm, Defn, DefnCore, ExceptPoint, ExceptSpec,
        Expr, ExprCore, ExprNode, Fairness, Field, Hyp, HypCore, HypNode, InstanceDefinition,
        Level, Locus, Modal, Param, ParenForm, Quantifier, Selector, Sequent, Substitution, Time,
        Visibility, WhereDefined, XlabelIndex,
    };
    use crate::pragma::{OldMethod, PragmaSetting, PragmaValue};

    /// The JSON the TypeScript serializes its inputs and results to.
    #[derive(Clone, Debug)]
    pub(crate) enum Json {
        Null,
        Bool(bool),
        Number(f64),
        Text(String),
        Array(Vec<Json>),
        Object(Vec<(String, Json)>),
    }

    struct JsonReader<'text> {
        characters: std::iter::Peekable<std::str::Chars<'text>>,
    }

    impl JsonReader<'_> {
        fn skip_space(&mut self) {
            while self
                .characters
                .peek()
                .is_some_and(char::is_ascii_whitespace)
            {
                self.characters.next();
            }
        }

        fn read_string(&mut self) -> String {
            self.skip_space();
            assert_eq!(self.characters.next(), Some('"'));
            let mut value = String::new();
            let mut pending_high = None;
            loop {
                let character = self.characters.next().expect("unterminated string");
                if character == '"' {
                    return value;
                }
                if character != '\\' {
                    value.push(character);
                    continue;
                }
                let escaped = self.characters.next().expect("escape");
                let unescaped = match escaped {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    'b' => '\u{8}',
                    'f' => '\u{c}',
                    'u' => {
                        let digits: String =
                            (0..4).filter_map(|_| self.characters.next()).collect();
                        let code = u32::from_str_radix(&digits, 16).expect("hex");
                        if (0xd800..0xdc00).contains(&code) {
                            pending_high = Some(code);
                            continue;
                        }
                        let code = pending_high.take().map_or(code, |high| {
                            0x10000 + ((high - 0xd800) << 10) + (code - 0xdc00)
                        });
                        char::from_u32(code).expect("scalar")
                    }
                    other => other,
                };
                value.push(unescaped);
            }
        }

        fn read(&mut self) -> Json {
            self.skip_space();
            match self.characters.peek().copied() {
                Some('"') => Json::Text(self.read_string()),
                Some('[') => {
                    self.characters.next();
                    let mut items = Vec::new();
                    self.skip_space();
                    if self.characters.peek() == Some(&']') {
                        self.characters.next();
                        return Json::Array(items);
                    }
                    loop {
                        items.push(self.read());
                        self.skip_space();
                        if self.characters.next() == Some(']') {
                            return Json::Array(items);
                        }
                    }
                }
                Some('{') => {
                    self.characters.next();
                    let mut entries = Vec::new();
                    self.skip_space();
                    if self.characters.peek() == Some(&'}') {
                        self.characters.next();
                        return Json::Object(entries);
                    }
                    loop {
                        let key = self.read_string();
                        self.skip_space();
                        assert_eq!(self.characters.next(), Some(':'));
                        entries.push((key, self.read()));
                        self.skip_space();
                        if self.characters.next() == Some('}') {
                            return Json::Object(entries);
                        }
                    }
                }
                _ => {
                    let mut word = String::new();
                    while let Some(&character) = self.characters.peek() {
                        if !(character.is_ascii_alphanumeric() || "+-.".contains(character)) {
                            break;
                        }
                        word.push(character);
                        self.characters.next();
                    }
                    match word.as_str() {
                        "null" => Json::Null,
                        "true" => Json::Bool(true),
                        "false" => Json::Bool(false),
                        _ => Json::Number(word.parse().expect("number")),
                    }
                }
            }
        }
    }

    pub(crate) fn parse_json(text: &str) -> Json {
        JsonReader {
            characters: text.chars().peekable(),
        }
        .read()
    }

    impl Json {
        pub(crate) fn get(&self, key: &str) -> Option<&Self> {
            match self {
                Self::Object(entries) => entries
                    .iter()
                    .find(|entry| entry.0 == key)
                    .map(|entry| &entry.1)
                    .filter(|value| !matches!(value, Self::Null)),
                _ => None,
            }
        }

        pub(crate) fn field(&self, key: &str) -> &Self {
            self.get(key)
                .unwrap_or_else(|| panic!("missing {key} in {self:?}"))
        }

        pub(crate) fn text(&self, key: &str) -> String {
            match self.field(key) {
                Self::Text(value) => value.clone(),
                other => panic!("not a string: {other:?}"),
            }
        }

        fn float(&self, key: &str) -> f64 {
            match self.field(key) {
                Self::Number(value) => *value,
                other => panic!("not a number: {other:?}"),
            }
        }

        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        pub(crate) fn number(&self, key: &str) -> usize {
            self.float(key) as usize
        }

        #[allow(clippy::cast_possible_truncation)]
        fn signed(&self, key: &str) -> isize {
            self.float(key) as isize
        }

        fn flag(&self, key: &str) -> bool {
            matches!(self.get(key), Some(Self::Bool(true)))
        }

        pub(crate) fn items(&self, key: &str) -> &[Self] {
            match self.field(key) {
                Self::Array(items) => items,
                other => panic!("not an array: {other:?}"),
            }
        }

        fn texts(&self, key: &str) -> Vec<String> {
            self.items(key)
                .iter()
                .map(|item| match item {
                    Self::Text(value) => value.clone(),
                    other => panic!("not a string: {other:?}"),
                })
                .collect()
        }
    }

    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    fn to_locus(item: Option<&Json>) -> Option<Locus> {
        let item = item?;
        Some(Locus {
            file: item.text("file").into(),
            start_line: item.float("startLine") as u32,
            start_column: item.float("startColumn") as u32,
            end_line: item.float("endLine") as u32,
            end_column: item.float("endColumn") as u32,
        })
    }

    fn to_exprs(items: &[Json]) -> Vec<Expr> {
        items.iter().map(to_expr).collect()
    }

    const BUILTINS: &[Builtin] = &[
        Builtin::TRUE,
        Builtin::FALSE,
        Builtin::Implies,
        Builtin::Equiv,
        Builtin::Conj,
        Builtin::Disj,
        Builtin::Neg,
        Builtin::Eq,
        Builtin::Neq,
        Builtin::STRING,
        Builtin::BOOLEAN,
        Builtin::SUBSET,
        Builtin::UNION,
        Builtin::DOMAIN,
        Builtin::Subseteq,
        Builtin::Mem,
        Builtin::Notmem,
        Builtin::Setminus,
        Builtin::Cap,
        Builtin::Cup,
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
        Builtin::Nat,
        Builtin::Int,
        Builtin::Real,
        Builtin::Plus,
        Builtin::Minus,
        Builtin::Uminus,
        Builtin::Times,
        Builtin::Ratio,
        Builtin::Quotient,
        Builtin::Remainder,
        Builtin::Exp,
        Builtin::Infinity,
        Builtin::Lteq,
        Builtin::Lt,
        Builtin::Gteq,
        Builtin::Gt,
        Builtin::Divides,
        Builtin::Range,
        Builtin::Seq,
        Builtin::Len,
        Builtin::BSeq,
        Builtin::Cat,
        Builtin::Append,
        Builtin::Head,
        Builtin::Tail,
        Builtin::SubSeq,
        Builtin::SelectSeq,
        Builtin::OneArg,
        Builtin::Extend,
        Builtin::Print,
        Builtin::PrintT,
        Builtin::Assert,
        Builtin::JavaTime,
        Builtin::TLCGet,
        Builtin::TLCSet,
        Builtin::Permutations,
        Builtin::SortSeq,
        Builtin::RandomElement,
        Builtin::Any,
        Builtin::ToString,
        Builtin::Unprimable,
        Builtin::Irregular,
    ];

    fn to_builtin(name: &str) -> Builtin {
        BUILTINS
            .iter()
            .copied()
            .find(|builtin| builtin.name() == name)
            .unwrap_or_else(|| panic!("unknown builtin {name}"))
    }

    fn to_level(name: &str) -> Level {
        match name {
            "Constant" => Level::Constant,
            "State" => Level::State,
            "Action" => Level::Action,
            "Temporal" => Level::Temporal,
            "Unknown" => Level::Unknown,
            other => panic!("unknown level {other}"),
        }
    }

    fn to_visibility(name: &str) -> Visibility {
        match name {
            "Hidden" => Visibility::Hidden,
            "Visible" => Visibility::Visible,
            other => panic!("unknown visibility {other}"),
        }
    }

    fn to_time(name: &str) -> Time {
        match name {
            "Always" => Time::Always,
            "Now" => Time::Now,
            other => panic!("unknown time {other}"),
        }
    }

    fn to_params(items: &[Json]) -> Vec<Param> {
        items
            .iter()
            .map(|item| Param {
                name: item.text("name"),
                shape: item.number("shape"),
                location: to_locus(item.get("location")),
            })
            .collect()
    }

    fn to_bounds(items: &[Json]) -> Vec<Bound> {
        items
            .iter()
            .map(|item| {
                let domain = item.field("domain");
                Bound {
                    name: item.text("name"),
                    level: to_level(&item.text("level")),
                    domain: match domain.text("kind").as_str() {
                        "NoDomain" => BoundDomain::NoDomain,
                        "Ditto" => BoundDomain::Ditto,
                        _ => BoundDomain::Domain(to_expr(domain.field("expression"))),
                    },
                }
            })
            .collect()
    }

    fn to_selector(item: &Json) -> Selector {
        match item.text("kind").as_str() {
            "Down" => Selector::Down,
            "Number" => Selector::Number(item.number("value")),
            "Left" => Selector::Left,
            "Right" => Selector::Right,
            "At" => Selector::At,
            "Instance" => Selector::Instance(to_exprs(item.items("args"))),
            _ => Selector::Label {
                label: item.text("label"),
                args: to_exprs(item.items("args")),
            },
        }
    }

    fn to_pragma_setting(item: &Json) -> PragmaSetting {
        let value = item.field("value");
        PragmaSetting {
            hint: item.text("hint"),
            value: match value.text("kind").as_str() {
                "Default" => PragmaValue::Default,
                "String" => PragmaValue::String(value.text("value")),
                _ => PragmaValue::Float(value.float("value")),
            },
        }
    }

    fn to_defn(item: &Json) -> Defn {
        let name = item.text("name");
        let core = match item.text("kind").as_str() {
            "Recursive" => DefnCore::Recursive {
                name,
                shape: item.number("shape"),
            },
            "Operator" => DefnCore::Operator {
                name,
                body: to_expr(item.field("body")),
            },
            "Bpragma" => DefnCore::Bpragma {
                name,
                body: to_expr(item.field("body")),
                methods: item
                    .items("methods")
                    .iter()
                    .map(|group| match group {
                        Json::Array(settings) => settings.iter().map(to_pragma_setting).collect(),
                        other => panic!("not an array: {other:?}"),
                    })
                    .collect(),
            },
            _ => {
                let instance = item.field("instance");
                DefnCore::Instance {
                    name,
                    instance: InstanceDefinition {
                        args: instance.texts("args"),
                        module: instance.text("module"),
                        substitutions: instance
                            .items("substitutions")
                            .iter()
                            .map(|entry| Substitution {
                                name: entry.text("name"),
                                expression: to_expr(entry.field("expression")),
                            })
                            .collect(),
                        location: to_locus(instance.get("location")),
                    },
                }
            }
        };
        Defn {
            core,
            location: to_locus(item.get("location")),
        }
    }

    pub(crate) fn to_hyp(item: &Json) -> Hyp {
        let core = match item.text("kind").as_str() {
            "Fresh" => HypCore::Fresh {
                name: item.text("name"),
                shape: item.number("shape"),
                level: to_level(&item.text("level")),
                domain: item.get("domain").map(to_expr),
                domain_visibility: to_visibility(&item.text("domainVisibility")),
            },
            "Flex" => HypCore::Flex {
                name: item.text("name"),
            },
            "Defn" => HypCore::Defn {
                definition: to_defn(item.field("definition")),
                where_defined: match item.field("whereDefined") {
                    Json::Text(name) if name == "User" => WhereDefined::User,
                    Json::Text(name) if name == "Builtin" => WhereDefined::Builtin,
                    proof => WhereDefined::Proof(to_time(&proof.text("time"))),
                },
                visibility: to_visibility(&item.text("visibility")),
                is_local: item.flag("isLocal"),
                is_constness_unset: item.flag("isConstnessUnset"),
            },
            _ => HypCore::Fact {
                expression: to_expr(item.field("expression")),
                visibility: to_visibility(&item.text("visibility")),
                time: to_time(&item.text("time")),
                use_location: to_locus(item.get("useLocation")),
            },
        };
        Rc::new(HypNode {
            core,
            location: to_locus(item.get("location")),
        })
    }

    pub(crate) fn to_sequent(item: &Json) -> Sequent {
        Sequent {
            context: item.items("context").iter().map(to_hyp).collect(),
            active: to_expr(item.field("active")),
        }
    }

    fn to_modal(item: &Json) -> Modal {
        if item.text("modal") == "Box" {
            Modal::Box
        } else {
            Modal::Dia
        }
    }

    fn to_quantifier(item: &Json) -> Quantifier {
        if item.text("quantifier") == "Forall" {
            Quantifier::Forall
        } else {
            Quantifier::Exists
        }
    }

    fn to_fields(item: &Json) -> Vec<Field> {
        item.items("fields")
            .iter()
            .map(|field| Field {
                name: field.text("name"),
                value: to_expr(field.field("value")),
            })
            .collect()
    }

    fn to_paren_form(form: &Json) -> ParenForm {
        match form.text("kind").as_str() {
            "Syntax" => ParenForm::Syntax,
            "Nlabel" => ParenForm::Nlabel {
                label: form.text("label"),
                names: form.texts("names"),
            },
            _ => ParenForm::Xlabel {
                label: form.text("label"),
                indices: form
                    .items("indices")
                    .iter()
                    .map(|entry| XlabelIndex {
                        name: entry.text("name"),
                        index: entry.number("index"),
                    })
                    .collect(),
            },
        }
    }

    fn to_except_spec(spec: &Json) -> ExceptSpec {
        ExceptSpec {
            trail: spec
                .items("trail")
                .iter()
                .map(|point| {
                    if point.text("kind") == "Dot" {
                        ExceptPoint::Dot(point.text("field"))
                    } else {
                        ExceptPoint::Apply(to_expr(point.field("expression")))
                    }
                })
                .collect(),
            value: to_expr(spec.field("value")),
        }
    }

    #[allow(clippy::too_many_lines)]
    pub(crate) fn to_expr(item: &Json) -> Expr {
        let child = |key: &str| to_expr(item.field(key));
        let core = match item.text("kind").as_str() {
            "Ix" => ExprCore::Ix {
                index: item.signed("index"),
            },
            "Opaque" => ExprCore::Opaque {
                name: item.text("name"),
            },
            "Internal" => ExprCore::Internal {
                builtin: to_builtin(&item.text("builtin")),
            },
            "Lambda" => ExprCore::Lambda {
                params: to_params(item.items("params")),
                body: child("body"),
            },
            "Sequent" => ExprCore::Sequent {
                sequent: to_sequent(item.field("sequent")),
            },
            "Bang" => ExprCore::Bang {
                expression: child("expression"),
                selectors: item.items("selectors").iter().map(to_selector).collect(),
            },
            "Apply" => ExprCore::Apply {
                operator: child("operator"),
                args: to_exprs(item.items("args")),
            },
            "With" => {
                let method = item.field("method");
                ExprCore::With {
                    expression: child("expression"),
                    method: OldMethod {
                        name: method.text("name"),
                        tactic: method.get("tactic").map(|_| method.text("tactic")),
                        timeout: method.get("timeout").map(|_| method.float("timeout")),
                    },
                }
            }
            "If" => ExprCore::If {
                condition: child("condition"),
                consequent: child("consequent"),
                alternative: child("alternative"),
            },
            "List" => ExprCore::List {
                bullet: match item.text("bullet").as_str() {
                    "And" => Bullet::And,
                    "Or" => Bullet::Or,
                    _ => Bullet::Refs,
                },
                items: to_exprs(item.items("items")),
            },
            "Let" => ExprCore::Let {
                definitions: item.items("definitions").iter().map(to_defn).collect(),
                body: child("body"),
            },
            "Quant" => ExprCore::Quant {
                quantifier: to_quantifier(item),
                bounds: to_bounds(item.items("bounds")),
                body: child("body"),
            },
            "Tquant" => ExprCore::Tquant {
                quantifier: to_quantifier(item),
                names: item.texts("names"),
                body: child("body"),
            },
            "Choose" => ExprCore::Choose {
                name: item.text("name"),
                domain: item.get("domain").map(to_expr),
                body: child("body"),
            },
            "SetSt" => ExprCore::SetSt {
                name: item.text("name"),
                domain: child("domain"),
                body: child("body"),
            },
            "SetOf" => ExprCore::SetOf {
                element: child("element"),
                bounds: to_bounds(item.items("bounds")),
            },
            "SetEnum" => ExprCore::SetEnum {
                elements: to_exprs(item.items("elements")),
            },
            "Product" => ExprCore::Product {
                factors: to_exprs(item.items("factors")),
            },
            "Tuple" => ExprCore::Tuple {
                elements: to_exprs(item.items("elements")),
            },
            "Fcn" => ExprCore::Fcn {
                bounds: to_bounds(item.items("bounds")),
                body: child("body"),
            },
            "FcnApp" => ExprCore::FcnApp {
                function: child("function"),
                args: to_exprs(item.items("args")),
            },
            "Arrow" => ExprCore::Arrow {
                domain: child("domain"),
                range: child("range"),
            },
            "Rect" => ExprCore::Rect {
                fields: to_fields(item),
            },
            "Record" => ExprCore::Record {
                fields: to_fields(item),
            },
            "Except" => ExprCore::Except {
                function: child("function"),
                specs: item.items("specs").iter().map(to_except_spec).collect(),
            },
            "Dot" => ExprCore::Dot {
                expression: child("expression"),
                field: item.text("field"),
            },
            "Sub" => ExprCore::Sub {
                modal: to_modal(item),
                action: child("action"),
                subscript: child("subscript"),
            },
            "Tsub" => ExprCore::Tsub {
                modal: to_modal(item),
                action: child("action"),
                subscript: child("subscript"),
            },
            "Fair" => ExprCore::Fair {
                fairness: if item.text("fairness") == "Weak" {
                    Fairness::Weak
                } else {
                    Fairness::Strong
                },
                subscript: child("subscript"),
                action: child("action"),
            },
            "Case" => ExprCore::Case {
                arms: item
                    .items("arms")
                    .iter()
                    .map(|arm| CaseArm {
                        condition: to_expr(arm.field("condition")),
                        body: to_expr(arm.field("body")),
                    })
                    .collect(),
                other: item.get("other").map(to_expr),
            },
            "String" => ExprCore::String {
                value: item.text("value"),
            },
            "Num" => ExprCore::Num {
                integer: item.text("integer"),
                fraction: item.text("fraction"),
            },
            "At" => ExprCore::At {
                is_except: item.flag("isExcept"),
            },
            "Parens" => ExprCore::Parens {
                expression: child("expression"),
                form: to_paren_form(item.field("form")),
            },
            other => panic!("unknown kind {other}"),
        };
        Rc::new(ExprNode {
            core,
            location: to_locus(item.get("location")),
            is_atomic: item.flag("isAtomic"),
        })
    }

    /// `${name}: ${message}`, and a proof error's exception in brackets, as the TypeScript's errors
    /// were described.
    pub(crate) fn describe(error: &ObligationError) -> String {
        match error {
            ObligationError::Proof { exception, .. } => {
                format!("{}: {} [{exception}]", error.name(), error.message())
            }
            _ => format!("{}: {}", error.name(), error.message()),
        }
    }

    /// A module of cases: its hypotheses, shared by identity as the TypeScript's were, and each
    /// case's input sequent and expected results, as `{"output": ...}` or `{"error": ...}`.
    pub(crate) struct Fixture {
        pub(crate) hyps: Vec<Hyp>,
        pub(crate) cases: Vec<Json>,
    }

    pub(crate) fn read_fixture(text: &str) -> Fixture {
        let module = parse_json(text);
        Fixture {
            hyps: module.items("hyps").iter().map(to_hyp).collect(),
            cases: module.items("cases").to_vec(),
        }
    }

    impl Fixture {
        pub(crate) fn context(&self, item: &Json) -> Vec<Hyp> {
            item.items("context")
                .iter()
                .map(|id| match id {
                    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                    Json::Number(value) => self.hyps[*value as usize].clone(),
                    other => panic!("not an id: {other:?}"),
                })
                .collect()
        }

        pub(crate) fn input(&self, case: &Json) -> Sequent {
            let input = case.field("input");
            Sequent {
                context: self.context(input),
                active: to_expr(input.field("active")),
            }
        }
    }

    /// Whether a text result is the one expected, reporting a difference.
    pub(crate) fn is_expected_text(actual: Result<String>, expected: &Json) -> bool {
        let actual = actual.map_err(|error| describe(&error));
        let expected = match expected.get("error") {
            Some(_) => Err(expected.text("error")),
            None => Ok(expected.text("output")),
        };
        if actual != expected {
            eprintln!("expected {expected:?}\nactual   {actual:?}");
        }
        actual == expected
    }

    pub(crate) const FIXTURES: [&str; 3] = [FIXTURE, TAME, RANDOM];

    /// The obligations of small modules with actions and temporal operators, without locations.
    const FIXTURE: &str = r##"{"id":"fixture","hyps":[
{"kind":"Flex","name":"x"},
{"kind":"Flex","name":"y"},
{"kind":"Fresh","name":"N","shape":0,"level":"Constant","domainVisibility":"Visible"},
{"kind":"Defn","definition":{"kind":"Operator","name":"vars","body":{"kind":"Tuple","elements":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Init","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inc","body":{"kind":"Lambda","params":[{"name":"v","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Next","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":5}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inv","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Step","body":{"kind":"Lambda","params":[{"name":"A","shape":0},{"name":"B","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Both","body":{"kind":"Lambda","params":[{"name":"P","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":6},{"kind":"Ix","index":3}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":4},{"kind":"Sub","modal":"Box","action":{"kind":"Ix","index":5},"subscript":{"kind":"Ix","index":8}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":8},{"kind":"Ix","index":5}]},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":6},{"kind":"Sub","modal":"Box","action":{"kind":"Ix","index":7},"subscript":{"kind":"Ix","index":10}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":6}]}]},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},
{"kind":"Flex","name":"VARIABLE_x_"},
{"kind":"Flex","name":"VARIABLE_y_"},
{"kind":"Fresh","name":"CONSTANT_N_","shape":0,"level":"Constant","domainVisibility":"Visible"},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_vars_","body":{"kind":"Tuple","elements":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Init_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Inc_","body":{"kind":"Lambda","params":[{"name":"Unknown_v_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Next_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Ix","index":5}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Inv_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Step_","body":{"kind":"Lambda","params":[{"name":"Unknown_A_","shape":0},{"name":"Unknown_B_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Both_","body":{"kind":"Lambda","params":[{"name":"Unknown_P_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":6},{"kind":"Ix","index":3}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":4},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":5},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":8}]},{"kind":"Ix","index":8}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":8},{"kind":"Ix","index":5}]},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":6},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":7},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"h6fbaa"},{"kind":"Ix","index":10}]}]}]},{"kind":"Opaque","name":"hdb2fe"}]},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"vars","body":{"kind":"Tuple","elements":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Init","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inc","body":{"kind":"Lambda","params":[{"name":"v","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Next","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":5}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inv","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Step","body":{"kind":"Lambda","params":[{"name":"A","shape":0},{"name":"B","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Both","body":{"kind":"Lambda","params":[{"name":"P","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":6},{"kind":"Ix","index":3}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":4},{"kind":"Sub","modal":"Box","action":{"kind":"Ix","index":5},"subscript":{"kind":"Ix","index":8}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_vars_","body":{"kind":"Tuple","elements":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Init_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Inc_","body":{"kind":"Lambda","params":[{"name":"Unknown_v_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Next_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Ix","index":5}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Inv_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Step_","body":{"kind":"Lambda","params":[{"name":"Unknown_A_","shape":0},{"name":"Unknown_B_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Both_","body":{"kind":"Lambda","params":[{"name":"Unknown_P_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":6},{"kind":"Ix","index":3}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":4},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":5},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":8}]},{"kind":"Ix","index":8}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":8},{"kind":"Ix","index":5}]},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":8},{"kind":"Ix","index":5}]},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":6},{"kind":"Sub","modal":"Box","action":{"kind":"Ix","index":7},"subscript":{"kind":"Ix","index":10}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":6}]}]},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":6},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":7},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"h6fbaa"},{"kind":"Ix","index":10}]}]}]},{"kind":"Opaque","name":"hdb2fe"}]},"visibility":"Visible","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inc","body":{"kind":"Lambda","params":[{"name":"v","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Next","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":5}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":4}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Spec","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":6},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":5},{"kind":"Num","integer":"0","fraction":""}]}]},{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":1},"subscript":{"kind":"Ix","index":3}}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":3},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Step","body":{"kind":"Lambda","params":[{"name":"A","shape":0},{"name":"B","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Both","body":{"kind":"Lambda","params":[{"name":"P","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"List","bullet":"Refs","items":[]},"visibility":"Hidden","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Inc_","body":{"kind":"Lambda","params":[{"name":"Unknown_v_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Next_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":5}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Ix","index":4}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Spec_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":6},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":5},{"kind":"Num","integer":"0","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Ix","index":3}]}]}]}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":3},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Step_","body":{"kind":"Lambda","params":[{"name":"Unknown_A_","shape":0},{"name":"Unknown_B_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Both_","body":{"kind":"Lambda","params":[{"name":"Unknown_P_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"List","bullet":"Refs","items":[]},"visibility":"Hidden","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"Init","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Spec","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Tsub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":4},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":3}]}]},"subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":4},{"kind":"Ix","index":3}]}}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":4},{"kind":"Ix","index":3}]},"action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":4},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":3}]}]}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Step","body":{"kind":"Lambda","params":[{"name":"A","shape":0},{"name":"B","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Both","body":{"kind":"Lambda","params":[{"name":"P","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":4},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"List","bullet":"Refs","items":[]},"visibility":"Hidden","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Init_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Spec_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":4},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Ix","index":3}]}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Ix","index":4}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Ix","index":3}]}]}]}]}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":4},{"kind":"Ix","index":3}]},"action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":4},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Ix","index":3}]}]}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Step_","body":{"kind":"Lambda","params":[{"name":"Unknown_A_","shape":0},{"name":"Unknown_B_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Both_","body":{"kind":"Lambda","params":[{"name":"Unknown_P_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":4},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"List","bullet":"Refs","items":[]},"visibility":"Hidden","time":"Always"},
{"kind":"Flex","name":"x"},
{"kind":"Flex","name":"y"},
{"kind":"Fresh","name":"N","shape":0,"level":"Constant","domainVisibility":"Visible"},
{"kind":"Defn","definition":{"kind":"Operator","name":"vars","body":{"kind":"Tuple","elements":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Init","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inc","body":{"kind":"Lambda","params":[{"name":"v","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Next","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":5}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Spec","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":3},{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":1},"subscript":{"kind":"Ix","index":4}}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":4},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inv","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":8},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Step","body":{"kind":"Lambda","params":[{"name":"A","shape":0},{"name":"B","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Both","body":{"kind":"Lambda","params":[{"name":"P","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":4},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Leadsto"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":11},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":11},{"kind":"Num","integer":"1","fraction":""}]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":5},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Leadsto"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":12},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":12},{"kind":"Num","integer":"2","fraction":""}]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":6},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Leadsto"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":13},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":13},{"kind":"Num","integer":"1","fraction":""}]}]}]},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":7},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Leadsto"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"2","fraction":""}]}]}]},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},
{"kind":"Flex","name":"VARIABLE_x_"},
{"kind":"Flex","name":"VARIABLE_y_"},
{"kind":"Fresh","name":"CONSTANT_N_","shape":0,"level":"Constant","domainVisibility":"Visible"},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_vars_","body":{"kind":"Tuple","elements":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Init_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Inc_","body":{"kind":"Lambda","params":[{"name":"Unknown_v_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Next_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Ix","index":5}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Spec_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":3},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Ix","index":4}]}]}]}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":4},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Inv_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":8},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Step_","body":{"kind":"Lambda","params":[{"name":"Unknown_A_","shape":0},{"name":"Unknown_B_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Both_","body":{"kind":"Lambda","params":[{"name":"Unknown_P_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":4},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Leadsto"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":11},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":11},{"kind":"Num","integer":"1","fraction":""}]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":5},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Leadsto"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":12},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":12},{"kind":"Num","integer":"2","fraction":""}]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":6},{"kind":"Opaque","name":"h40870"}]},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":7},{"kind":"Opaque","name":"h81f4c"}]},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},
{"kind":"Flex","name":"x"},
{"kind":"Flex","name":"y"},
{"kind":"Fresh","name":"N","shape":0,"level":"Constant","domainVisibility":"Visible"},
{"kind":"Defn","definition":{"kind":"Operator","name":"vars","body":{"kind":"Tuple","elements":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Init","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inc","body":{"kind":"Lambda","params":[{"name":"v","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Spec","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Tsub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":5}]}]},"subscript":{"kind":"Ix","index":3}}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":3},"action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":5}]}]}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inv","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fresh","name":"n","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Nat"},"domainVisibility":"Visible"},
{"kind":"Flex","name":"z"},
{"kind":"Fact","expression":{"kind":"Tsub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"Ix","index":10}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":9}]}]},"subscript":{"kind":"Ix","index":7}},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Sub","modal":"Dia","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":6},"args":[{"kind":"Ix","index":11}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":10}]}]},"subscript":{"kind":"Ix","index":8}}]},"visibility":"Visible","time":"Now"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},
{"kind":"Flex","name":"VARIABLE_x_"},
{"kind":"Flex","name":"VARIABLE_y_"},
{"kind":"Fresh","name":"CONSTANT_N_","shape":0,"level":"Constant","domainVisibility":"Visible"},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_vars_","body":{"kind":"Tuple","elements":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Init_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Inc_","body":{"kind":"Lambda","params":[{"name":"Unknown_v_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Spec_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Ix","index":5}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Ix","index":3}]}]}]}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":3},"action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Ix","index":5}]}]}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Inv_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fresh","name":"CONSTANT_n_","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Nat"},"domainVisibility":"Visible"},
{"kind":"Flex","name":"VARIABLE_z_"},
{"kind":"Fact","expression":{"kind":"Opaque","name":"h0a577"},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Opaque","name":"h55ed7"},"visibility":"Visible","time":"Now"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"Next","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":5},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":4}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Spec","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":1},"subscript":{"kind":"Ix","index":3}}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":3},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inv","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Step","body":{"kind":"Lambda","params":[{"name":"A","shape":0},{"name":"B","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Both","body":{"kind":"Lambda","params":[{"name":"P","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"n","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Nat"},"domainVisibility":"Visible"},{"kind":"Flex","name":"z"},{"kind":"Fact","expression":{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":7},"subscript":{"kind":"Ix","index":9}},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Sub","modal":"Dia","action":{"kind":"Ix","index":8},"subscript":{"kind":"Ix","index":10}}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":14}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":6},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Ix","index":13}]},{"kind":"Ix","index":9}]}]},{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":14},{"kind":"Ix","index":12}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Next_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":5},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Ix","index":4}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Spec_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Ix","index":3}]}]}]}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":3},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Inv_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Step_","body":{"kind":"Lambda","params":[{"name":"Unknown_A_","shape":0},{"name":"Unknown_B_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Both_","body":{"kind":"Lambda","params":[{"name":"Unknown_P_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"CONSTANT_n_","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Nat"},"domainVisibility":"Visible"},{"kind":"Flex","name":"VARIABLE_z_"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":7},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":9}]},{"kind":"Ix","index":9}]}]}]},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":8},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":10}]},{"kind":"Ix","index":10}]}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":14}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":6},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Ix","index":13}]},{"kind":"Ix","index":9}]}]},{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":14},{"kind":"Ix","index":12}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"vars","body":{"kind":"Tuple","elements":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Init","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Next","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":5},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":4}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Spec","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":1},"subscript":{"kind":"Ix","index":3}}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":3},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inv","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Step","body":{"kind":"Lambda","params":[{"name":"A","shape":0},{"name":"B","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Both","body":{"kind":"Lambda","params":[{"name":"P","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"n","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Nat"},"domainVisibility":"Visible"},{"kind":"Flex","name":"z"},{"kind":"Fact","expression":{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":7},"subscript":{"kind":"Ix","index":9}},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Sub","modal":"Dia","action":{"kind":"Ix","index":8},"subscript":{"kind":"Ix","index":10}}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":14}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":6},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Ix","index":13}]},{"kind":"Ix","index":9}]}]},{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":14},{"kind":"Ix","index":12}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"k","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"Nat"}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":12},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":12},{"kind":"Ix","index":1}]}]}]}]}},"visibility":"Hidden","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_vars_","body":{"kind":"Tuple","elements":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Init_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Next_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":5},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Ix","index":4}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Spec_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Ix","index":3}]}]}]}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":3},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Inv_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Step_","body":{"kind":"Lambda","params":[{"name":"Unknown_A_","shape":0},{"name":"Unknown_B_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Both_","body":{"kind":"Lambda","params":[{"name":"Unknown_P_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"CONSTANT_n_","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Nat"},"domainVisibility":"Visible"},{"kind":"Flex","name":"VARIABLE_z_"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":7},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":9}]},{"kind":"Ix","index":9}]}]}]},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":8},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":10}]},{"kind":"Ix","index":10}]}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":14}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":6},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Ix","index":13}]},{"kind":"Ix","index":9}]}]},{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":14},{"kind":"Ix","index":12}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_k_","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"Nat"}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":12},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":12},{"kind":"Ix","index":1}]}]}]}]}},"visibility":"Hidden","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inc","body":{"kind":"Lambda","params":[{"name":"v","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Next","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":5}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Spec","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":3},{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":1},"subscript":{"kind":"Ix","index":4}}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":4},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inv","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":8},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Step","body":{"kind":"Lambda","params":[{"name":"A","shape":0},{"name":"B","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Both","body":{"kind":"Lambda","params":[{"name":"P","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"n","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Nat"},"domainVisibility":"Visible"},{"kind":"Flex","name":"z"},{"kind":"Fact","expression":{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":7},"subscript":{"kind":"Ix","index":10}},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Sub","modal":"Dia","action":{"kind":"Ix","index":8},"subscript":{"kind":"Ix","index":11}}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":15}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":15},{"kind":"Num","integer":"1","fraction":""}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":6},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":15},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Ix","index":14}]},{"kind":"Ix","index":9}]}]},{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":15},{"kind":"Ix","index":13}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"k","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"Nat"}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":13},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":13},{"kind":"Ix","index":1}]}]}]}]}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":13}]},{"kind":"Ix","index":13}]},{"kind":"Sub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Ix","index":8},"args":[{"kind":"Ix","index":12}]},"subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":12}]}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Tuple","elements":[{"kind":"Ix","index":13},{"kind":"Tuple","elements":[{"kind":"Ix","index":12}]}]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Inc_","body":{"kind":"Lambda","params":[{"name":"Unknown_v_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Next_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Ix","index":5}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Spec_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":3},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Ix","index":4}]}]}]}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":4},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Inv_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":8},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Step_","body":{"kind":"Lambda","params":[{"name":"Unknown_A_","shape":0},{"name":"Unknown_B_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Both_","body":{"kind":"Lambda","params":[{"name":"Unknown_P_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"CONSTANT_n_","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Nat"},"domainVisibility":"Visible"},{"kind":"Flex","name":"VARIABLE_z_"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":7},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":10}]},{"kind":"Ix","index":10}]}]}]},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":8},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":11}]},{"kind":"Ix","index":11}]}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":15}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":15},{"kind":"Num","integer":"1","fraction":""}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":6},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":15},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Ix","index":14}]},{"kind":"Ix","index":9}]}]},{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":15},{"kind":"Ix","index":13}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_k_","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"Nat"}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":13},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":13},{"kind":"Ix","index":1}]}]}]}]}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":13}]},{"kind":"Ix","index":13}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":8},"args":[{"kind":"Ix","index":12}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]}]}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":13}]},{"kind":"Ix","index":13}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"Init","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inc","body":{"kind":"Lambda","params":[{"name":"v","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Next","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":5}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":4}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Spec","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":3},{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":1},"subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":6},{"kind":"Ix","index":5}]}}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":6},{"kind":"Ix","index":5}]},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inv","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Step","body":{"kind":"Lambda","params":[{"name":"A","shape":0},{"name":"B","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Both","body":{"kind":"Lambda","params":[{"name":"P","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"n","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Nat"},"domainVisibility":"Visible"},{"kind":"Flex","name":"z"},{"kind":"Fact","expression":{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":7},"subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":12},{"kind":"Ix","index":11}]}},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Sub","modal":"Dia","action":{"kind":"Ix","index":8},"subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":13},{"kind":"Ix","index":12}]}}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":14}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":6},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Ix","index":13}]},{"kind":"Ix","index":9}]}]},{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":14},{"kind":"Ix","index":12}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"k","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"Nat"}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":12},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":12},{"kind":"Ix","index":1}]}]}]}]}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]},{"kind":"Sub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Ix","index":8},"args":[{"kind":"Ix","index":11}]},"subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":11}]}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Tuple","elements":[{"kind":"Ix","index":12},{"kind":"Tuple","elements":[{"kind":"Ix","index":11}]}]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Choose","name":"c","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Ix","index":14}]}},{"kind":"Ix","index":13}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetSt","name":"e","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":14}]}]}},{"kind":"SetEnum","elements":[]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Init_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Inc_","body":{"kind":"Lambda","params":[{"name":"Unknown_v_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Next_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":5}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Ix","index":4}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Spec_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":3},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":1},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":6}]},{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Ix","index":5}]}]}]}]}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":6},{"kind":"Ix","index":5}]},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Inv_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Step_","body":{"kind":"Lambda","params":[{"name":"Unknown_A_","shape":0},{"name":"Unknown_B_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Both_","body":{"kind":"Lambda","params":[{"name":"Unknown_P_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"CONSTANT_n_","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Nat"},"domainVisibility":"Visible"},{"kind":"Flex","name":"VARIABLE_z_"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":7},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":11}]},{"kind":"Ix","index":11}]}]}]}]},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":8},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":13}]},{"kind":"Ix","index":13}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]}]}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":14}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":6},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Ix","index":13}]},{"kind":"Ix","index":9}]}]},{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":14},{"kind":"Ix","index":12}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_k_","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"Nat"}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":12},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":12},{"kind":"Ix","index":1}]}]}]}]}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":8},"args":[{"kind":"Ix","index":11}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":11}]},{"kind":"Ix","index":11}]}]}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":11}]},{"kind":"Ix","index":11}]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Choose","name":"CONSTANT_c_","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":14}]}},{"kind":"Ix","index":13}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetSt","name":"CONSTANT_e_","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":14}]}]}},{"kind":"SetEnum","elements":[]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"Init","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inc","body":{"kind":"Lambda","params":[{"name":"v","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Next","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":5}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":4}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Spec","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":3},{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":1},"subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":6},{"kind":"Ix","index":5}]}}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":6},{"kind":"Ix","index":5}]},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inv","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Step","body":{"kind":"Lambda","params":[{"name":"A","shape":0},{"name":"B","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Both","body":{"kind":"Lambda","params":[{"name":"P","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"n","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Nat"},"domainVisibility":"Visible"},{"kind":"Flex","name":"z"},{"kind":"Fact","expression":{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":7},"subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":12},{"kind":"Ix","index":11}]}},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Sub","modal":"Dia","action":{"kind":"Ix","index":8},"subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":13},{"kind":"Ix","index":12}]}}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":14}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":6},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Ix","index":13}]},{"kind":"Ix","index":9}]}]},{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":14},{"kind":"Ix","index":12}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"k","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"Nat"}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":12},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":12},{"kind":"Ix","index":1}]}]}]}]}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]},{"kind":"Sub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Ix","index":8},"args":[{"kind":"Ix","index":11}]},"subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":11}]}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Tuple","elements":[{"kind":"Ix","index":12},{"kind":"Tuple","elements":[{"kind":"Ix","index":11}]}]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Choose","name":"c","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Ix","index":14}]}},{"kind":"Ix","index":13}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetSt","name":"e","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":14}]}]}},{"kind":"SetEnum","elements":[]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Init_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"0","fraction":""}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Inc_","body":{"kind":"Lambda","params":[{"name":"Unknown_v_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Next_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":5}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Ix","index":4}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Spec_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":3},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":1},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":6}]},{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Ix","index":5}]}]}]}]}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":6},{"kind":"Ix","index":5}]},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Inv_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":7},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Step_","body":{"kind":"Lambda","params":[{"name":"Unknown_A_","shape":0},{"name":"Unknown_B_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Both_","body":{"kind":"Lambda","params":[{"name":"Unknown_P_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"CONSTANT_n_","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Nat"},"domainVisibility":"Visible"},{"kind":"Flex","name":"VARIABLE_z_"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":7},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":11}]},{"kind":"Ix","index":11}]}]}]}]},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":8},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":13}]},{"kind":"Ix","index":13}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]}]}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":14}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":6},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Ix","index":13}]},{"kind":"Ix","index":9}]}]},{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":14},{"kind":"Ix","index":12}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_k_","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"Nat"}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":12},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":12},{"kind":"Ix","index":1}]}]}]}]}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":8},"args":[{"kind":"Ix","index":11}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":11}]},{"kind":"Ix","index":11}]}]}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":11}]},{"kind":"Ix","index":11}]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Choose","name":"CONSTANT_c_","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":14}]}},{"kind":"Ix","index":13}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetSt","name":"CONSTANT_e_","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":14}]}]}},{"kind":"SetEnum","elements":[]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"Next","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":5}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Spec","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":3},{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":1},"subscript":{"kind":"Ix","index":4}}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":4},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Inv","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":8},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Step","body":{"kind":"Lambda","params":[{"name":"A","shape":0},{"name":"B","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"Both","body":{"kind":"Lambda","params":[{"name":"P","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"n","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Nat"},"domainVisibility":"Visible"},{"kind":"Flex","name":"z"},{"kind":"Fact","expression":{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":7},"subscript":{"kind":"Ix","index":10}},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Sub","modal":"Dia","action":{"kind":"Ix","index":8},"subscript":{"kind":"Ix","index":11}}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":15}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":15},{"kind":"Num","integer":"1","fraction":""}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":6},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":15},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Ix","index":14}]},{"kind":"Ix","index":9}]}]},{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":15},{"kind":"Ix","index":13}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"k","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"Nat"}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":13},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":13},{"kind":"Ix","index":1}]}]}]}]}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":13}]},{"kind":"Ix","index":13}]},{"kind":"Sub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Ix","index":8},"args":[{"kind":"Ix","index":12}]},"subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":12}]}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Tuple","elements":[{"kind":"Ix","index":13},{"kind":"Tuple","elements":[{"kind":"Ix","index":12}]}]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Choose","name":"c","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Ix","index":15}]}},{"kind":"Ix","index":14}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetSt","name":"e","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":15}]}]}},{"kind":"SetEnum","elements":[]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Tquant","quantifier":"Exists","names":["t"],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":16}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":16}]},{"kind":"Ix","index":15}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":13}]}]}]}},"visibility":"Hidden","time":"Always"},
{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},
{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domain":{"kind":"Ix","index":1},"domainVisibility":"Visible"},
{"kind":"Fresh","name":"T","shape":0,"level":"Constant","domain":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Ix","index":2}]},"domainVisibility":"Visible"},
{"kind":"Fresh","name":"p","shape":0,"level":"State","domainVisibility":"Visible"},
{"kind":"Fresh","name":"a","shape":0,"level":"Action","domainVisibility":"Visible"},
{"kind":"Fresh","name":"f","shape":0,"level":"Temporal","domainVisibility":"Visible"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Next_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":6}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Ix","index":5}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Spec_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":3},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Ix","index":4}]}]}]}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":4},"action":{"kind":"Ix","index":1}}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_Inv_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":8},{"kind":"Internal","builtin":"Nat"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_Step_","body":{"kind":"Lambda","params":[{"name":"Unknown_A_","shape":0},{"name":"Unknown_B_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"TEMPORAL_Both_","body":{"kind":"Lambda","params":[{"name":"Unknown_P_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"CONSTANT_n_","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Nat"},"domainVisibility":"Visible"},{"kind":"Flex","name":"VARIABLE_z_"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":7},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":10}]},{"kind":"Ix","index":10}]}]}]},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":8},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":11}]},{"kind":"Ix","index":11}]}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":15}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":15},{"kind":"Num","integer":"1","fraction":""}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":6},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":15},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Ix","index":14}]},{"kind":"Ix","index":9}]}]},{"kind":"Apply","operator":{"kind":"Ix","index":5},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":15},{"kind":"Ix","index":13}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_k_","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"Nat"}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":13},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":13},{"kind":"Ix","index":1}]}]}]}]}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":13}]},{"kind":"Ix","index":13}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":8},"args":[{"kind":"Ix","index":12}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]}]}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":13}]},{"kind":"Ix","index":13}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Choose","name":"CONSTANT_c_","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":15}]}},{"kind":"Ix","index":14}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetSt","name":"CONSTANT_e_","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":15}]}]}},{"kind":"SetEnum","elements":[]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Tquant","quantifier":"Exists","names":["t"],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":16}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":16}]},{"kind":"Ix","index":15}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":13}]},{"kind":"Ix","index":13}]}]}]}},"visibility":"Hidden","time":"Always"},
{"kind":"Fresh","name":"CONSTANT_S_","shape":0,"level":"Constant","domainVisibility":"Visible"},
{"kind":"Fresh","name":"CONSTANT_s_","shape":0,"level":"Constant","domain":{"kind":"Ix","index":1},"domainVisibility":"Visible"},
{"kind":"Fresh","name":"CONSTANT_T_","shape":0,"level":"Constant","domain":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Ix","index":2}]},"domainVisibility":"Visible"},
{"kind":"Fresh","name":"STATE_p_","shape":0,"level":"State","domainVisibility":"Visible"},
{"kind":"Fresh","name":"ACTION_a_","shape":0,"level":"Action","domainVisibility":"Visible"},
{"kind":"Fresh","name":"TEMPORAL_f_","shape":0,"level":"Temporal","domainVisibility":"Visible"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Choose","name":"c","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Ix","index":15}]}},{"kind":"Ix","index":14}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetSt","name":"e","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":15}]}]}},{"kind":"SetEnum","elements":[]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Tquant","quantifier":"Exists","names":["t"],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":16}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":16}]},{"kind":"Ix","index":15}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":13}]}]}]}},"visibility":"Hidden","time":"Always"},
{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domain":{"kind":"Ix","index":1},"domainVisibility":"Visible"},
{"kind":"Fresh","name":"T","shape":0,"level":"Constant","domain":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Ix","index":2}]},"domainVisibility":"Visible"},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Choose","name":"CONSTANT_c_","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":15}]}},{"kind":"Ix","index":14}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetSt","name":"CONSTANT_e_","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":15}]}]}},{"kind":"SetEnum","elements":[]}]}]},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Tquant","quantifier":"Exists","names":["t"],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":16}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":16}]},{"kind":"Ix","index":15}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":13}]},{"kind":"Ix","index":13}]}]}]}},"visibility":"Hidden","time":"Always"},
{"kind":"Fresh","name":"CONSTANT_S_","shape":0,"level":"Constant","domainVisibility":"Visible"},
{"kind":"Fresh","name":"CONSTANT_s_","shape":0,"level":"Constant","domain":{"kind":"Ix","index":1},"domainVisibility":"Visible"},
{"kind":"Fresh","name":"CONSTANT_T_","shape":0,"level":"Constant","domain":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Ix","index":2}]},"domainVisibility":"Visible"},
{"kind":"Fresh","name":"STATE_p_","shape":0,"level":"State","domainVisibility":"Visible"},
{"kind":"Fresh","name":"ACTION_a_","shape":0,"level":"Action","domainVisibility":"Visible"},
{"kind":"Fresh","name":"TEMPORAL_f_","shape":0,"level":"Temporal","domainVisibility":"Visible"},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domain":{"kind":"Ix","index":1},"domainVisibility":"Visible"},{"kind":"Fresh","name":"T","shape":0,"level":"Constant","domain":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Ix","index":2}]},"domainVisibility":"Visible"},{"kind":"Fresh","name":"p","shape":0,"level":"State","domainVisibility":"Visible"},{"kind":"Fresh","name":"a","shape":0,"level":"Action","domainVisibility":"Visible"},{"kind":"Fresh","name":"f","shape":0,"level":"Temporal","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":3}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"CONSTANT_S_","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"CONSTANT_s_","shape":0,"level":"Constant","domain":{"kind":"Ix","index":1},"domainVisibility":"Visible"},{"kind":"Fresh","name":"CONSTANT_T_","shape":0,"level":"Constant","domain":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Ix","index":2}]},"domainVisibility":"Visible"},{"kind":"Fresh","name":"STATE_p_","shape":0,"level":"State","domainVisibility":"Visible"},{"kind":"Fresh","name":"ACTION_a_","shape":0,"level":"Action","domainVisibility":"Visible"},{"kind":"Fresh","name":"TEMPORAL_f_","shape":0,"level":"Temporal","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":3}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domain":{"kind":"Ix","index":1},"domainVisibility":"Visible"},{"kind":"Fresh","name":"T","shape":0,"level":"Constant","domain":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Ix","index":2}]},"domainVisibility":"Visible"},{"kind":"Fresh","name":"p","shape":0,"level":"State","domainVisibility":"Visible"},{"kind":"Fresh","name":"a","shape":0,"level":"Action","domainVisibility":"Visible"},{"kind":"Fresh","name":"f","shape":0,"level":"Temporal","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":3}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]}]}]}}},"visibility":"Hidden","time":"Always"},
{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"CONSTANT_S_","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"CONSTANT_s_","shape":0,"level":"Constant","domain":{"kind":"Ix","index":1},"domainVisibility":"Visible"},{"kind":"Fresh","name":"CONSTANT_T_","shape":0,"level":"Constant","domain":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Ix","index":2}]},"domainVisibility":"Visible"},{"kind":"Fresh","name":"STATE_p_","shape":0,"level":"State","domainVisibility":"Visible"},{"kind":"Fresh","name":"ACTION_a_","shape":0,"level":"Action","domainVisibility":"Visible"},{"kind":"Fresh","name":"TEMPORAL_f_","shape":0,"level":"Temporal","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":3}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]}]}]}}},"visibility":"Hidden","time":"Always"}
],"cases":[
{"input":{"context":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":11},{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":9},"subscript":{"kind":"Ix","index":12}}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":12},"action":{"kind":"Ix","index":9}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":8}]}]}},"process":{"context":[15,16,17,18,19,20,21,22,23,24,25,26,27,28,29],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":11},{"kind":"Opaque","name":"hc7a9d"}]},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":12},"action":{"kind":"Ix","index":9}}]},{"kind":"Opaque","name":"h65a93"}]}},"ptl":{"output":"not (((always (h8828a -> h2f89a)) & (always ((h2f89a & (hfc35e | h18388)) -> (next h2f89a))) & (always (cc | ~ cc)) -> (((h8828a & (always (hfc35e | h18388))) & ((sometime (always hc5714)) -> (always (sometime (hfc35e & (~ h18388)))))) -> (always h2f89a))))"},"hash":{"output":"hed6db"}},
{"input":{"context":[0,1,2,30,31,32,33,34,35,36,37,38],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":8},{"kind":"Ix","index":5}]}},"process":{"context":[15,16,17,39,40,41,42,43,44,45,46,47],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":8},{"kind":"Ix","index":5}]}},"ptl":{"output":"not ((h8828a -> h2f89a))"},"hash":{"output":"h86250"}},
{"input":{"context":[0,1,2,30,31,32,33,34,35,36,37,38,48],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":6},{"kind":"Sub","modal":"Box","action":{"kind":"Ix","index":7},"subscript":{"kind":"Ix","index":10}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":6}]}]}},"process":{"context":[15,16,17,39,40,41,42,43,44,45,46,47,49],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":6},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":7},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"h6fbaa"},{"kind":"Ix","index":10}]}]}]},{"kind":"Opaque","name":"hdb2fe"}]}},"ptl":{"output":"not (((always (h8828a -> h2f89a)) -> ((h2f89a & (hfc35e | h18388)) -> (next h2f89a))))"},"hash":{"output":"h0ebd6"}},
{"input":{"context":[0,1,2,30,31,32,33,34,35,36,37,38,48,50],"active":{"kind":"Internal","builtin":"TRUE"}},"process":{"context":[15,16,17,39,40,41,42,43,44,45,46,47,49,51],"active":{"kind":"Internal","builtin":"TRUE"}},"ptl":{"output":"not (((always (h8828a -> h2f89a)) & (always ((h2f89a & (hfc35e | h18388)) -> (next h2f89a))) -> (cc | ~ cc)))"},"hash":{"output":"hc0d83"}},
{"input":{"context":[0,1,2,30,52,53,54,55,56,57,58],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":11},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":10},{"kind":"Num","integer":"0","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":11},{"kind":"Internal","builtin":"Nat"}]}]}},"process":{"context":[15,16,17,39,59,60,61,62,63,64,65],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":11},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":10},{"kind":"Num","integer":"0","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":11},{"kind":"Internal","builtin":"Nat"}]}]}},"ptl":{"output":"not (((h4ca64 & h47f9b) -> h276c9))"},"hash":{"output":"h5384d"}},
{"input":{"context":[0,1,2,66,67,68,69,70,71,72],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":10},{"kind":"Internal","builtin":"Nat"}]},{"kind":"Sub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":10}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":10},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":9}]}]},"subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":10},{"kind":"Ix","index":9}]}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":10},{"kind":"Internal","builtin":"Nat"}]}]}]}},"process":{"context":[15,16,17,73,74,75,76,77,78,79],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":10},{"kind":"Internal","builtin":"Nat"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"VARIABLE_x_#prime"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":10},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"VARIABLE_y_#prime"},{"kind":"Ix","index":9}]}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"VARIABLE_x_#prime"},{"kind":"Ix","index":10}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"VARIABLE_y_#prime"},{"kind":"Ix","index":9}]}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Opaque","name":"VARIABLE_x_#prime"},{"kind":"Internal","builtin":"Nat"}]}]}},"ptl":{"output":"not (((h276c9 & ((hb2120 & he47d0) | hcdc48)) -> (next h276c9)))"},"hash":{"output":"h7b806"}},
{"input":{"context":[80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":9},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Leadsto"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":16},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":16},{"kind":"Num","integer":"2","fraction":""}]}]}]}},"process":{"context":[96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":9},{"kind":"Opaque","name":"hb5824"}]}},"ptl":{"output":"not (((always (h94a4d -> (always (h4ca64 -> (sometime h7fe4a))))) & (always (h94a4d -> (always (h7fe4a -> (sometime hda924))))) & (always (cc | ~ cc)) -> (h94a4d -> (always (h4ca64 -> (sometime hda924))))))"},"hash":{"output":"h5c1fe"}},
{"input":{"context":[80,81,82,83,84,85,86,87,88,89,90,91,92],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":6},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Leadsto"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":13},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":13},{"kind":"Num","integer":"1","fraction":""}]}]}]}},"process":{"context":[96,97,98,99,100,101,102,103,104,105,106,107,108],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":6},{"kind":"Opaque","name":"h40870"}]}},"ptl":{"output":"not ((h94a4d -> (always (h4ca64 -> (sometime h7fe4a)))))"},"hash":{"output":"h159fd"}},
{"input":{"context":[80,81,82,83,84,85,86,87,88,89,90,91,92,93],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":7},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Leadsto"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":14},{"kind":"Num","integer":"2","fraction":""}]}]}]}},"process":{"context":[96,97,98,99,100,101,102,103,104,105,106,107,108,109],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":7},{"kind":"Opaque","name":"h81f4c"}]}},"ptl":{"output":"not (((always (h94a4d -> (always (h4ca64 -> (sometime h7fe4a))))) -> (h94a4d -> (always (h7fe4a -> (sometime hda924))))))"},"hash":{"output":"h7a8c8"}},
{"input":{"context":[80,81,82,83,84,85,86,87,88,89,90,91,92,93,94],"active":{"kind":"Internal","builtin":"TRUE"}},"process":{"context":[96,97,98,99,100,101,102,103,104,105,106,107,108,109,110],"active":{"kind":"Internal","builtin":"TRUE"}},"ptl":{"output":"not (((always (h94a4d -> (always (h4ca64 -> (sometime h7fe4a))))) & (always (h94a4d -> (always (h7fe4a -> (sometime hda924))))) -> (cc | ~ cc)))"},"hash":{"output":"hc0d83"}},
{"input":{"context":[112,113,114,115,116,117,118,119,120,121,122,123,124],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":13}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":13},{"kind":"Num","integer":"1","fraction":""}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":13},{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":8},"args":[{"kind":"Ix","index":13}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":12}]}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":13},{"kind":"Ix","index":11}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":13},{"kind":"Ix","index":11}]}]}]}]}},"process":{"context":[125,126,127,128,129,130,131,132,133,134,135,136,137],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Opaque","name":"h7edcc"},{"kind":"Opaque","name":"h5b9d6"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Opaque","name":"h4e514"},{"kind":"Opaque","name":"h16934"}]}]}},"ptl":{"output":"not (((always h2d8ad) & (always (always ((hc171d & he47d0) | h18388))) & h628fb & (always (cc | ~ cc)) -> (((sometime hb2120) & h5b035) & ((always h7b860) & (sometime h7b860)))))"},"hash":{"output":"h421b8"}},
{"input":{"context":[112,113,114,115,116,117,118,119,120,121,122,123],"active":{"kind":"Internal","builtin":"TRUE"}},"process":{"context":[125,126,127,128,129,130,131,132,133,134,135,136],"active":{"kind":"Internal","builtin":"TRUE"}},"ptl":{"output":"not (((always h2d8ad) & (always (always ((hc171d & he47d0) | h18388))) & h628fb -> (cc | ~ cc)))"},"hash":{"output":"hc0d83"}},
{"input":{"context":[112,113,114,115,116,138,139,140,141,142,143],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"k","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"Nat"}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":12},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":12},{"kind":"Ix","index":1}]}]}]}]}}},"process":{"context":[125,126,127,128,129,144,145,146,147,148,149],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_k_","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Internal","builtin":"Nat"}}}],"body":{"kind":"Opaque","name":"ha41e1"}}},"ptl":{"output":"not (h15048)"},"hash":{"output":"h6aa49"}},
{"input":{"context":[112,113,114,150,151,152,153,154,155,156,157,158],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":12}]},{"kind":"Ix","index":12}]},{"kind":"Sub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":11}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":11},{"kind":"Num","integer":"1","fraction":""}]}]},"subscript":{"kind":"Tuple","elements":[{"kind":"Ix","index":11}]}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Tuple","elements":[{"kind":"Ix","index":12},{"kind":"Tuple","elements":[{"kind":"Ix","index":11}]}]}]}]}},"process":{"context":[125,126,127,159,160,161,162,163,164,165,166,167],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"VARIABLE_x_#prime"},{"kind":"Ix","index":12}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"VARIABLE_y_#prime"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":11},{"kind":"Num","integer":"1","fraction":""}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"VARIABLE_y_#prime"},{"kind":"Ix","index":11}]}]}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"VARIABLE_x_#prime"},{"kind":"Ix","index":12}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"VARIABLE_y_#prime"},{"kind":"Ix","index":11}]}]}]}},"ptl":{"output":"not (((h8e953 & (ha0d74 | h3ad28)) -> h5c2cb))"},"hash":{"output":"h874a2"}},
{"input":{"context":[112,113,114,150,151,168,169,170,171,172,173,174,175,176,177],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Choose","name":"c","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Ix","index":16}]}},{"kind":"Ix","index":15}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetSt","name":"e","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":16}]}]}},{"kind":"SetEnum","elements":[]}]}]}},"process":{"context":[125,126,127,159,160,178,179,180,181,182,183,184,185,186,187],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Choose","name":"CONSTANT_c_","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":16}]}},{"kind":"Ix","index":15}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetSt","name":"CONSTANT_e_","domain":{"kind":"Internal","builtin":"Nat"},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Opaque","name":"VARIABLE_x_#prime"}]}},{"kind":"SetEnum","elements":[]}]}]}},"ptl":{"output":"not (((always (cc | ~ cc)) -> (ha0322 & heade3)))"},"hash":{"output":"ha4e76"}},
{"input":{"context":[112,113,114,150,151,168,169,170,171,172,173,174,175,176],"active":{"kind":"Internal","builtin":"TRUE"}},"process":{"context":[125,126,127,159,160,178,179,180,181,182,183,184,185,186],"active":{"kind":"Internal","builtin":"TRUE"}},"ptl":{"output":"not ((cc | ~ cc))"},"hash":{"output":"hc0d83"}},
{"input":{"context":[112,113,114,188,189,190,191,192,193,194,195,196,197,198,199],"active":{"kind":"Tquant","quantifier":"Exists","names":["t"],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":16}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":16}]},{"kind":"Ix","index":15}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Tuple","elements":[{"kind":"Ix","index":16},{"kind":"Ix","index":15}]}]}]}]}}},"process":{"context":[125,126,127,200,201,202,203,204,205,206,207,208,209,210,211],"active":{"kind":"Tquant","quantifier":"Exists","names":["t"],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Opaque","name":"hfca63"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"VARIABLE_x_#prime"},{"kind":"Ix","index":15}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"VARIABLE_x_#prime"},{"kind":"Ix","index":16}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"VARIABLE_y_#prime"},{"kind":"Ix","index":15}]}]}]}]}}},"ptl":{"output":"not (((always (cc | ~ cc)) -> h1fd45))"},"hash":{"output":"h11334"}},
{"input":{"context":[112,113,114,212,213,214,215,216,217,218,219,220,221,222],"active":{"kind":"Internal","builtin":"TRUE"}},"process":{"context":[125,126,127,223,224,225,226,227,228,229,230,231,232,233],"active":{"kind":"Internal","builtin":"TRUE"}},"ptl":{"output":"not ((cc | ~ cc))"},"hash":{"output":"hc0d83"}},
{"input":{"context":[112,113,114,115,116,117,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":3}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Diamond"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Ix","index":4}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BoxTrue"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":3},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]}]}]}]}},"process":{"context":[125,126,127,128,129,130,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":3}]},{"kind":"Opaque","name":"h9f4b3"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Opaque","name":"h6920a"},{"kind":"Opaque","name":"hdc84b"}]}]}},"ptl":{"output":"not (((always hd2a9d) & h0d694 & (always (cc | ~ cc)) -> (((h49bfb & h5edcc) & (always ha85fb)) -> ((sometime (always h49bfb)) | (always (h5edcc -> (next h49bfb)))))))"},"hash":{"output":"h89f0e"}},
{"input":{"context":[112,113,114,150,151,168,169,170,171,172,173,174,175,176,268,269,244,270,271,247,248,249],"active":{"kind":"Internal","builtin":"TRUE"}},"process":{"context":[125,126,127,159,160,178,179,180,181,182,183,184,185,186,272,273,274,275,276,277,278,279],"active":{"kind":"Internal","builtin":"TRUE"}},"ptl":{"output":"not (((always hd2a9d) & h0d694 -> (cc | ~ cc)))"},"hash":{"output":"hc0d83"}},
{"input":{"context":[112,113,114,115,116,117,234,235,236,237,238,239,240,241,242,243,280,281],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Sub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":18}]},{"kind":"Num","integer":"0","fraction":""}]},"subscript":{"kind":"Ix","index":18}},{"kind":"Fair","fairness":"Strong","subscript":{"kind":"Ix","index":17},"action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":17}]},{"kind":"Ix","index":17}]}}]}},"process":{"context":[125,126,127,128,129,130,251,252,253,254,255,256,257,258,259,260,282,283],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Opaque","name":"VARIABLE_x_#prime"},{"kind":"Num","integer":"0","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"VARIABLE_x_#prime"},{"kind":"Ix","index":18}]}]},{"kind":"Fair","fairness":"Strong","subscript":{"kind":"Ix","index":17},"action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neq"},"args":[{"kind":"Opaque","name":"VARIABLE_y_#prime"},{"kind":"Ix","index":17}]}}]}},"ptl":{"output":"not (((always (cc | ~ cc)) -> ((h35c28 | h0d12a) -> ((always (sometime h5bea8)) -> (always (sometime (he3431 & (~ he47d0))))))))"},"hash":{"output":"hcd4ef"}},
{"input":{"context":[112,113,114,150,151,168,169,170,171,172,173,174,175,176,268,269,284],"active":{"kind":"Internal","builtin":"TRUE"}},"process":{"context":[125,126,127,159,160,178,179,180,181,182,183,184,185,186,272,273,285],"active":{"kind":"Internal","builtin":"TRUE"}},"ptl":{"output":"not ((cc | ~ cc))"},"hash":{"output":"hc0d83"}}
]}"##;

    /// Random sequents whose operators take as many arguments as they are defined with.
    const TAME: &str = r##"{"id":"random-53","hyps":[
{"kind":"Fresh","name":"y","shape":0,"level":"Temporal","domainVisibility":"Visible"},
{"kind":"Defn","definition":{"kind":"Operator","name":"y","body":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"f","level":"Action","domain":{"kind":"NoDomain"}}],"body":{"kind":"Fcn","bounds":[{"name":"i","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Defn","definition":{"kind":"Recursive","name":"f","shape":0},"whereDefined":{"kind":"Proof","time":"Now"},"visibility":"Visible","isLocal":true}],"active":{"kind":"Internal","builtin":"Nat","location":{"file":"R.tla","startLine":11912,"startColumn":1,"endLine":11912,"endColumn":9}}},"location":{"file":"R.tla","startLine":11910,"startColumn":1,"endLine":11910,"endColumn":9}}}}],"body":{"kind":"If","condition":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Ix","index":2,"location":{"file":"R.tla","startLine":11915,"startColumn":1,"endLine":11915,"endColumn":9}},{"kind":"Ix","index":3}],"location":{"file":"R.tla","startLine":11914,"startColumn":1,"endLine":11914,"endColumn":9}},"consequent":{"kind":"SetOf","bounds":[{"name":"e","level":"Temporal","domain":{"kind":"Domain","expression":{"kind":"Ix","index":3}}}],"element":{"kind":"Fcn","bounds":[{"name":"i","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":2}}}],"body":{"kind":"Ix","index":2}}},"alternative":{"kind":"Ix","index":3,"location":{"file":"R.tla","startLine":11922,"startColumn":1,"endLine":11922,"endColumn":9}}}},"location":{"file":"R.tla","startLine":11908,"startColumn":1,"endLine":11908,"endColumn":9}}},"whereDefined":"User","visibility":"Visible","isLocal":false,"location":{"file":"R.tla","startLine":11907,"startColumn":1,"endLine":11907,"endColumn":9}},
{"kind":"Defn","definition":{"kind":"Operator","name":"q","body":{"kind":"Sequent","sequent":{"context":[{"kind":"Fact","expression":{"kind":"Fcn","bounds":[{"name":"i","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Fair","fairness":"Strong","subscript":{"kind":"Tuple","elements":[{"kind":"Internal","builtin":"TRUE"}],"location":{"file":"R.tla","startLine":11928,"startColumn":1,"endLine":11928,"endColumn":9}},"action":{"kind":"Ix","index":1,"location":{"file":"R.tla","startLine":11931,"startColumn":1,"endLine":11931,"endColumn":9}}}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Lt","location":{"file":"R.tla","startLine":11932,"startColumn":1,"endLine":11932,"endColumn":9}},"args":[{"kind":"SetSt","name":"y","domain":{"kind":"Opaque","name":"q","isAtomic":true},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"SetSt","name":"vars","domain":{"kind":"Internal","builtin":"Nat","location":{"file":"R.tla","startLine":11937,"startColumn":1,"endLine":11937,"endColumn":9}},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":4},{"kind":"Tquant","quantifier":"Exists","names":["v"],"body":{"kind":"Opaque","name":"z"}}]}},{"kind":"Lambda","params":[{"name":"a","shape":0}],"body":{"kind":"Ix","index":4}}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj","location":{"file":"R.tla","startLine":11944,"startColumn":1,"endLine":11944,"endColumn":9}},"args":[{"kind":"Internal","builtin":"Nat"},{"kind":"Ix","index":2}]}]}},"visibility":"Visible","time":"Now","location":{"file":"R.tla","startLine":11925,"startColumn":1,"endLine":11925,"endColumn":9}}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Choose","name":"Next","body":{"kind":"Ix","index":2,"location":{"file":"R.tla","startLine":11949,"startColumn":1,"endLine":11949,"endColumn":9}}}],"isAtomic":true}},"location":{"file":"R.tla","startLine":11924,"startColumn":1,"endLine":11924,"endColumn":9}}},"whereDefined":{"kind":"Proof","time":"Now"},"visibility":"Visible","isLocal":false},
{"kind":"Defn","definition":{"kind":"Operator","name":"S","body":{"kind":"Lambda","params":[{"name":"p0","shape":0},{"name":"p1","shape":0}],"body":{"kind":"List","bullet":"And","items":[]}}},"whereDefined":{"kind":"Proof","time":"Now"},"visibility":"Visible","isLocal":false},
{"kind":"Fresh","name":"vars","shape":0,"level":"Unknown","domainVisibility":"Visible","location":{"file":"R.tla","startLine":11994,"startColumn":1,"endLine":11994,"endColumn":9}},
{"kind":"Defn","definition":{"kind":"Operator","name":"S","body":{"kind":"Tquant","quantifier":"Forall","names":["v"],"body":{"kind":"Ix","index":6,"location":{"file":"R.tla","startLine":11997,"startColumn":1,"endLine":11997,"endColumn":9}}}},"whereDefined":"User","visibility":"Visible","isLocal":true},
{"kind":"Fresh","name":"TEMPORAL_y_","shape":0,"level":"Temporal","domainVisibility":"Visible"},
{"kind":"Flex","name":"S","location":{"file":"R.tla","startLine":12046,"startColumn":1,"endLine":12046,"endColumn":9}},
{"kind":"Fresh","name":"q","shape":0,"level":"Temporal","domainVisibility":"Visible"}
],"cases":[
{"input":{"context":[0,1,2,3,4,5],"active":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"vars","shape":0,"level":"Action","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Tsub","modal":"Dia","action":{"kind":"Ix","index":5,"location":{"file":"R.tla","startLine":12003,"startColumn":1,"endLine":12003,"endColumn":9}},"subscript":{"kind":"Tuple","elements":[]}}]}},"location":{"file":"R.tla","startLine":11998,"startColumn":1,"endLine":11998,"endColumn":9}}},"process":{"error":"TlaProofError: Oops, this seems to be a bug in TLAPM. [Assert_failure]"},"ptl":{"error":"TlaProofError: Oops, this seems to be a bug in TLAPM. [Assert_failure]"},"hash":{"output":"hb853a"}},
{"input":{"context":[0],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Tsub","modal":"Dia","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"DOMAIN"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem","location":{"file":"R.tla","startLine":12007,"startColumn":1,"endLine":12007,"endColumn":9}},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"FALSE"}]}],"location":{"file":"R.tla","startLine":12006,"startColumn":1,"endLine":12006,"endColumn":9}},"subscript":{"kind":"If","condition":{"kind":"Ix","index":1},"consequent":{"kind":"Tuple","elements":[{"kind":"Ix","index":1,"location":{"file":"R.tla","startLine":12014,"startColumn":1,"endLine":12014,"endColumn":9}},{"kind":"Ix","index":1}]},"alternative":{"kind":"SetSt","name":"S","domain":{"kind":"Ix","index":1,"location":{"file":"R.tla","startLine":12017,"startColumn":1,"endLine":12017,"endColumn":9}},"body":{"kind":"SetOf","bounds":[{"name":"e","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"List","bullet":"Or","items":[{"kind":"Ix","index":1,"location":{"file":"R.tla","startLine":12020,"startColumn":1,"endLine":12020,"endColumn":9}},{"kind":"Ix","index":1},{"kind":"Ix","index":2,"location":{"file":"R.tla","startLine":12022,"startColumn":1,"endLine":12022,"endColumn":9}}]}}}],"element":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj","location":{"file":"R.tla","startLine":12024,"startColumn":1,"endLine":12024,"endColumn":9}},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":1}],"location":{"file":"R.tla","startLine":12024,"startColumn":1,"endLine":12024,"endColumn":9},"isAtomic":true}},"isAtomic":true}},"location":{"file":"R.tla","startLine":12005,"startColumn":1,"endLine":12005,"endColumn":9}}],"location":{"file":"R.tla","startLine":12004,"startColumn":1,"endLine":12004,"endColumn":9}}},"process":{"error":"TlaProofError: Oops, this seems to be a bug in TLAPM. [Assert_failure]"},"ptl":{"output":"not (h8d6f6)"},"hash":{"output":"h9cba2"}},
{"input":{"context":[0],"active":{"kind":"SetOf","bounds":[{"name":"e","level":"State","domain":{"kind":"Domain","expression":{"kind":"Tuple","elements":[{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"S","level":"State","domain":{"kind":"Domain","expression":{"kind":"Choose","name":"p","body":{"kind":"Ix","index":1}}}},{"name":"y","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}}],"body":{"kind":"Ix","index":2}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":1}]}]}}}],"element":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"x","level":"Temporal","domain":{"kind":"NoDomain"}},{"name":"z","level":"Temporal","domain":{"kind":"NoDomain"}}],"body":{"kind":"Ix","index":4,"location":{"file":"R.tla","startLine":12038,"startColumn":1,"endLine":12038,"endColumn":9}}}}},"process":{"context":[6],"active":{"kind":"SetOf","bounds":[{"name":"STATE_e_","level":"State","domain":{"kind":"Domain","expression":{"kind":"Tuple","elements":[{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"STATE_S_","level":"State","domain":{"kind":"Domain","expression":{"kind":"Choose","name":"CONSTANT_p_","body":{"kind":"Ix","index":1}}}},{"name":"CONSTANT_y_","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}}],"body":{"kind":"Ix","index":2}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"TEMPORAL_y_#prime"},{"kind":"Ix","index":1}]}]}}}],"element":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"TEMPORAL_x_","level":"Temporal","domain":{"kind":"NoDomain"}},{"name":"TEMPORAL_z_","level":"Temporal","domain":{"kind":"NoDomain"}}],"body":{"kind":"Ix","index":4,"location":{"file":"R.tla","startLine":12038,"startColumn":1,"endLine":12038,"endColumn":9}}}}},"ptl":{"output":"not (he3b83)"},"hash":{"output":"hc14a9"}},
{"input":{"context":[],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"FcnApp","function":{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Internal","builtin":"Nat","location":{"file":"R.tla","startLine":12043,"startColumn":1,"endLine":12043,"endColumn":9}},"action":{"kind":"Internal","builtin":"Nat"}},"args":[{"kind":"Internal","builtin":"TRUE"}]}]}},"process":{"context":[],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"FcnApp","function":{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Internal","builtin":"Nat","location":{"file":"R.tla","startLine":12043,"startColumn":1,"endLine":12043,"endColumn":9}},"action":{"kind":"Internal","builtin":"Nat"}},"args":[{"kind":"Internal","builtin":"TRUE"}]}]}},"ptl":{"output":"not ((~ h51f3d))"},"hash":{"output":"hb8c33"}},
{"input":{"context":[0,1,2,3,7,8],"active":{"kind":"Tquant","quantifier":"Exists","names":["v"],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"StrongPrime"},"args":[{"kind":"Lambda","params":[{"name":"a","shape":0}],"body":{"kind":"Ix","index":6}}]}}},"process":{"error":"TlaProofError: Oops, this seems to be a bug in TLAPM. [Assert_failure]"},"ptl":{"error":"TlaProofError: Oops, this seems to be a bug in TLAPM. [Assert_failure]"},"hash":{"output":"h1f33f"}}
]}"##;

    /// Random sequents with indices and arities that are often wrong.
    const RANDOM: &str = r##"{"id":"random-95","hyps":[
{"kind":"Fresh","name":"vars","shape":0,"level":"Constant","domainVisibility":"Visible"},
{"kind":"Fresh","name":"y","shape":0,"level":"Constant","domainVisibility":"Visible"},
{"kind":"Defn","definition":{"kind":"Operator","name":"f","body":{"kind":"Lambda","params":[{"name":"a","shape":0}],"body":{"kind":"SetSt","name":"vars","domain":{"kind":"Sub","modal":"Box","action":{"kind":"Ix","index":3,"location":{"file":"R.tla","startLine":36125,"startColumn":1,"endLine":36125,"endColumn":9}},"subscript":{"kind":"Tuple","elements":[]}},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Lt","location":{"file":"R.tla","startLine":36126,"startColumn":1,"endLine":36126,"endColumn":9}},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}],"location":{"file":"R.tla","startLine":36127,"startColumn":1,"endLine":36127,"endColumn":9}},{"kind":"Apply","operator":{"kind":"Ix","index":3},"args":[{"kind":"Num","integer":"3","fraction":"","location":{"file":"R.tla","startLine":36131,"startColumn":1,"endLine":36131,"endColumn":9}},{"kind":"String","value":"é","location":{"file":"R.tla","startLine":36132,"startColumn":1,"endLine":36132,"endColumn":9}}],"location":{"file":"R.tla","startLine":36130,"startColumn":1,"endLine":36130,"endColumn":9}}],"location":{"file":"R.tla","startLine":36126,"startColumn":1,"endLine":36126,"endColumn":9}}}}},"whereDefined":"Builtin","visibility":"Visible","isLocal":false},
{"kind":"Defn","definition":{"kind":"Recursive","name":"S","shape":0},"whereDefined":"User","visibility":"Visible","isLocal":false},
{"kind":"Fact","expression":{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":2},"action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj","location":{"file":"R.tla","startLine":36138,"startColumn":1,"endLine":36138,"endColumn":9}},"args":[{"kind":"Internal","builtin":"TRUE","location":{"file":"R.tla","startLine":36139,"startColumn":1,"endLine":36139,"endColumn":9}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"Nat"}]}],"location":{"file":"R.tla","startLine":36138,"startColumn":1,"endLine":36138,"endColumn":9}},"location":{"file":"R.tla","startLine":36135,"startColumn":1,"endLine":36135,"endColumn":9}},"visibility":"Hidden","time":"Now"},
{"kind":"Fresh","name":"CONSTANT_vars_","shape":0,"level":"Constant","domainVisibility":"Visible"},
{"kind":"Fresh","name":"CONSTANT_y_","shape":0,"level":"Constant","domainVisibility":"Visible"},
{"kind":"Fresh","name":"z","shape":0,"level":"Constant","domainVisibility":"Visible"},
{"kind":"Fresh","name":"n","shape":0,"level":"Action","domainVisibility":"Visible","location":{"file":"R.tla","startLine":36143,"startColumn":1,"endLine":36143,"endColumn":9}},
{"kind":"Fresh","name":"S","shape":0,"level":"Temporal","domainVisibility":"Visible","location":{"file":"R.tla","startLine":36159,"startColumn":1,"endLine":36159,"endColumn":9}},
{"kind":"Fresh","name":"TEMPORAL_S_","shape":0,"level":"Temporal","domainVisibility":"Visible","location":{"file":"R.tla","startLine":36159,"startColumn":1,"endLine":36159,"endColumn":9}},
{"kind":"Flex","name":"z"},
{"kind":"Flex","name":"S","location":{"file":"R.tla","startLine":36168,"startColumn":1,"endLine":36168,"endColumn":9}},
{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":4}]}]},"visibility":"Visible","time":"Now"},
{"kind":"Fresh","name":"Next","shape":0,"level":"Constant","domain":{"kind":"Tquant","quantifier":"Forall","names":["v"],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"StrongPrime","location":{"file":"R.tla","startLine":36189,"startColumn":1,"endLine":36189,"endColumn":9}},"args":[{"kind":"Ix","index":3,"location":{"file":"R.tla","startLine":36189,"startColumn":1,"endLine":36189,"endColumn":9}}]},"location":{"file":"R.tla","startLine":36187,"startColumn":1,"endLine":36187,"endColumn":9}},"domainVisibility":"Hidden","location":{"file":"R.tla","startLine":36186,"startColumn":1,"endLine":36186,"endColumn":9}},
{"kind":"Fresh","name":"n","shape":0,"level":"Unknown","domainVisibility":"Visible","location":{"file":"R.tla","startLine":36190,"startColumn":1,"endLine":36190,"endColumn":9}}
],"cases":[
{"input":{"context":[0,1,2,3,4],"active":{"kind":"Ix","index":5,"location":{"file":"R.tla","startLine":36144,"startColumn":1,"endLine":36144,"endColumn":9}}},"process":{"error":"TlaProofError: Invalid number of arguments [Failure(\"Invalid number of arguments\")]"},"ptl":{"error":"TlaProofError: Invalid number of arguments [Failure(\"Invalid number of arguments\")]"},"hash":{"output":"hb6311"}},
{"input":{"context":[0,1],"active":{"kind":"Ix","index":1,"location":{"file":"R.tla","startLine":36145,"startColumn":1,"endLine":36145,"endColumn":9}}},"process":{"context":[5,6],"active":{"kind":"Ix","index":1,"location":{"file":"R.tla","startLine":36145,"startColumn":1,"endLine":36145,"endColumn":9}}},"ptl":{"output":"not (h6339f)"},"hash":{"output":"h41529"}},
{"input":{"context":[0,1,2,3,7],"active":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"vars","level":"State","domain":{"kind":"Domain","expression":{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Ix","index":3},"action":{"kind":"Ix","index":2},"location":{"file":"R.tla","startLine":36148,"startColumn":1,"endLine":36148,"endColumn":9}}}},{"name":"x","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Choose","name":"p","body":{"kind":"Tuple","elements":[],"location":{"file":"R.tla","startLine":36152,"startColumn":1,"endLine":36152,"endColumn":9}},"location":{"file":"R.tla","startLine":36151,"startColumn":1,"endLine":36151,"endColumn":9}},"location":{"file":"R.tla","startLine":36147,"startColumn":1,"endLine":36147,"endColumn":9}}},"process":{"error":"TlaProofError: Invalid number of arguments [Failure(\"Invalid number of arguments\")]"},"ptl":{"error":"TlaProofError: Invalid number of arguments [Failure(\"Invalid number of arguments\")]"},"hash":{"output":"ha1d0a"}},
{"input":{"context":[0,1,2,3,4,8],"active":{"kind":"SetSt","name":"n","domain":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":5,"isAtomic":true},{"kind":"Tuple","elements":[]}]},"body":{"kind":"Ix","index":4},"location":{"file":"R.tla","startLine":36153,"startColumn":1,"endLine":36153,"endColumn":9}}},"process":{"error":"TlaProofError: Invalid number of arguments [Failure(\"Invalid number of arguments\")]"},"ptl":{"error":"TlaProofError: Invalid number of arguments [Failure(\"Invalid number of arguments\")]"},"hash":{"output":"h5818e"}},
{"input":{"context":[],"active":{"kind":"Num","integer":"1","fraction":"","location":{"file":"R.tla","startLine":36158,"startColumn":1,"endLine":36158,"endColumn":9}}},"process":{"context":[],"active":{"kind":"Num","integer":"1","fraction":"","location":{"file":"R.tla","startLine":36158,"startColumn":1,"endLine":36158,"endColumn":9}}},"ptl":{"output":"not (hc4ca4)"},"hash":{"output":"hc4ca4"}},
{"input":{"context":[9],"active":{"kind":"Lambda","params":[{"name":"a","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"DOMAIN"},"args":[{"kind":"SetSt","name":"vars","domain":{"kind":"Sub","modal":"Box","action":{"kind":"Ix","index":1},"subscript":{"kind":"Ix","index":2,"location":{"file":"R.tla","startLine":36165,"startColumn":1,"endLine":36165,"endColumn":9}},"location":{"file":"R.tla","startLine":36163,"startColumn":1,"endLine":36163,"endColumn":9}},"body":{"kind":"Ix","index":1},"location":{"file":"R.tla","startLine":36162,"startColumn":1,"endLine":36162,"endColumn":9}}],"location":{"file":"R.tla","startLine":36161,"startColumn":1,"endLine":36161,"endColumn":9}}}},"process":{"context":[10],"active":{"kind":"Lambda","params":[{"name":"Unknown_a_","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"DOMAIN"},"args":[{"kind":"SetSt","name":"CONSTANT_vars_","domain":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj","location":{"file":"R.tla","startLine":36163,"startColumn":1,"endLine":36163,"endColumn":9}},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq","location":{"file":"R.tla","startLine":36165,"startColumn":1,"endLine":36165,"endColumn":9}},"args":[{"kind":"Opaque","name":"TEMPORAL_S_#prime","location":{"file":"R.tla","startLine":36165,"startColumn":1,"endLine":36165,"endColumn":9}},{"kind":"Ix","index":2,"location":{"file":"R.tla","startLine":36165,"startColumn":1,"endLine":36165,"endColumn":9}}],"location":{"file":"R.tla","startLine":36165,"startColumn":1,"endLine":36165,"endColumn":9}}],"location":{"file":"R.tla","startLine":36163,"startColumn":1,"endLine":36163,"endColumn":9}},"body":{"kind":"Ix","index":1},"location":{"file":"R.tla","startLine":36162,"startColumn":1,"endLine":36162,"endColumn":9}}],"location":{"file":"R.tla","startLine":36161,"startColumn":1,"endLine":36161,"endColumn":9}}}},"ptl":{"output":"not (hf13ac)"},"hash":{"output":"he58f5"}},
{"input":{"context":[0,1,2,3,4,8,11,12],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Tsub","modal":"Box","action":{"kind":"Ix","index":3},"subscript":{"kind":"Tuple","elements":[]}}]}},"process":{"error":"TlaProofError: Invalid number of arguments [Failure(\"Invalid number of arguments\")]"},"ptl":{"error":"TlaProofError: Invalid number of arguments [Failure(\"Invalid number of arguments\")]"},"hash":{"output":"hf3c28"}},
{"input":{"context":[0,1,2,3,4,13],"active":{"kind":"SetSt","name":"x","domain":{"kind":"Ix","index":1},"body":{"kind":"Tquant","quantifier":"Forall","names":["v"],"body":{"kind":"Apply","operator":{"kind":"Ix","index":1,"location":{"file":"R.tla","startLine":36183,"startColumn":1,"endLine":36183,"endColumn":9}},"args":[{"kind":"Ix","index":8},{"kind":"Ix","index":5}]}},"location":{"file":"R.tla","startLine":36180,"startColumn":1,"endLine":36180,"endColumn":9}}},"process":{"error":"TlaProofError: Invalid number of arguments [Failure(\"Invalid number of arguments\")]"},"ptl":{"error":"TlaProofError: Invalid number of arguments [Failure(\"Invalid number of arguments\")]"},"hash":{"output":"h1067a"}},
{"input":{"context":[0,1,2,3,4,14,15],"active":{"kind":"Fair","fairness":"Strong","subscript":{"kind":"If","condition":{"kind":"Fcn","bounds":[{"name":"i","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Choose","name":"vars","body":{"kind":"Internal","builtin":"Nat"},"location":{"file":"R.tla","startLine":36194,"startColumn":1,"endLine":36194,"endColumn":9}}}}],"body":{"kind":"Ix","index":1}},"consequent":{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED","location":{"file":"R.tla","startLine":36201,"startColumn":1,"endLine":36201,"endColumn":9}},"args":[{"kind":"If","condition":{"kind":"Ix","index":2,"isAtomic":true},"consequent":{"kind":"Ix","index":6},"alternative":{"kind":"Ix","index":7,"location":{"file":"R.tla","startLine":36201,"startColumn":1,"endLine":36201,"endColumn":9}}}]},"alternative":{"kind":"SetOf","bounds":[{"name":"e","level":"Unknown","domain":{"kind":"Domain","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"DOMAIN"},"args":[{"kind":"Ix","index":6}]}}}],"element":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":11}]}}},"action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq","location":{"file":"R.tla","startLine":36207,"startColumn":1,"endLine":36207,"endColumn":9}},"args":[{"kind":"Ix","index":4,"location":{"file":"R.tla","startLine":36208,"startColumn":1,"endLine":36208,"endColumn":9}},{"kind":"Internal","builtin":"TRUE"}]},"location":{"file":"R.tla","startLine":36191,"startColumn":1,"endLine":36191,"endColumn":9}}},"process":{"error":"TlaProofError: Oops, this seems to be a bug in TLAPM. [Assert_failure]"},"ptl":{"error":"TlaProofError: Invalid number of arguments [Failure(\"Invalid number of arguments\")]"},"hash":{"output":"hddcae"}},
{"input":{"context":[],"active":{"kind":"Lambda","params":[{"name":"a","shape":0}],"body":{"kind":"Choose","name":"Next","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Let","definitions":[{"kind":"Operator","name":"f","body":{"kind":"Choose","name":"Next","body":{"kind":"Ix","index":2,"location":{"file":"R.tla","startLine":36218,"startColumn":1,"endLine":36218,"endColumn":9}},"isAtomic":true}},{"kind":"Operator","name":"f","body":{"kind":"Lambda","params":[{"name":"p0","shape":0},{"name":"p1","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Choose","name":"Next","domain":{"kind":"Ix","index":2},"body":{"kind":"Num","integer":"4","fraction":""},"location":{"file":"R.tla","startLine":36220,"startColumn":1,"endLine":36220,"endColumn":9}}]}}}],"body":{"kind":"Ix","index":2}}]}}}},"process":{"context":[],"active":{"kind":"Lambda","params":[{"name":"Unknown_a_","shape":0}],"body":{"kind":"Choose","name":"CONSTANT_Next_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"hf51b4"},{"kind":"Let","definitions":[{"kind":"Operator","name":"CONSTANT_f_","body":{"kind":"Choose","name":"CONSTANT_Next_","body":{"kind":"Ix","index":2,"location":{"file":"R.tla","startLine":36218,"startColumn":1,"endLine":36218,"endColumn":9}},"isAtomic":true}},{"kind":"Operator","name":"ACTION_f_","body":{"kind":"Lambda","params":[{"name":"Unknown_p0_","shape":0},{"name":"Unknown_p1_","shape":0}],"body":{"kind":"Choose","name":"CONSTANT_Next_","domain":{"kind":"Opaque","name":"Unknown_p0_#prime"},"body":{"kind":"Num","integer":"4","fraction":""},"location":{"file":"R.tla","startLine":36220,"startColumn":1,"endLine":36220,"endColumn":9}}}}],"body":{"kind":"Ix","index":2}}]}}}},"ptl":{"output":"not (hf3bed)"},"hash":{"output":"h881c3"}}
]}"##;

    /// Every sequent processed as the TypeScript processed it, as a whole: each hypothesis and the
    /// goal, with their locations, or the same error.
    #[test]
    fn processes_obligations_as_the_typescript_does() {
        let mut failures = 0;
        let mut count = 0;
        for text in FIXTURES {
            let fixture = read_fixture(text);
            for (index, case) in fixture.cases.iter().enumerate() {
                count += 1;
                let expected = case.field("process");
                let actual = process_obligation(&fixture.input(case));
                let is_same = match (&actual, expected.get("error")) {
                    (Err(error), Some(_)) => describe(error) == expected.text("error"),
                    (Ok(output), None) => {
                        format!("{:?}", output.context)
                            == format!("{:?}", fixture.context(expected))
                            && format!("{:?}", output.active)
                                == format!("{:?}", to_expr(expected.field("active")))
                    }
                    _ => false,
                };
                if !is_same {
                    failures += 1;
                    eprintln!("case {index} differs: {:?}", actual.map(|_| ()));
                }
            }
        }
        assert_eq!(count, 37);
        assert_eq!(failures, 0);
    }

    #[test]
    fn hashes_as_the_typescript_does() {
        let mut failures = 0;
        for text in FIXTURES {
            let fixture = read_fixture(text);
            for case in &fixture.cases {
                let input = fixture.input(case);
                if !is_expected_text(
                    get_hash_name(&input.context, &input.active),
                    case.field("hash"),
                ) {
                    failures += 1;
                }
            }
        }
        assert_eq!(failures, 0);
    }

    #[test]
    fn names_the_prefixes_of_levels() {
        let prefixes = [
            Level::Constant,
            Level::State,
            Level::Action,
            Level::Temporal,
            Level::Unknown,
        ]
        .map(level_prefix);
        assert_eq!(
            prefixes,
            ["CONSTANT", "STATE", "ACTION", "TEMPORAL", "Unknown"]
        );
        assert_eq!(
            LEVEL_NUMBER_PREFIXES,
            ["CONSTANT", "STATE", "ACTION", "TEMPORAL"]
        );
    }
}

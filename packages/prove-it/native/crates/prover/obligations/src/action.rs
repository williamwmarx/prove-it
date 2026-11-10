//! A port of tlapm's Expr.Action. Lambdifying gives each ENABLED and \cdot a LAMBDA over the
//! variables it binds, after expanding the definitions soundness needs expanded. The ExpandENABLED
//! and ExpandCdot frontends then replace each LAMBDA with an existential quantifier.
//! A port of `src/obligations/action.ts`.
//!
//! The TypeScript's `Anonymizer` closes over its instance expander and warning sink; the Rust
//! passes them beside it as an `AnonymizerHost`, which each function here takes with the anonymizer.

use std::cell::RefCell;
use std::rc::Rc;

use crate::anonymize::{Anonymizer, AnonymizerHost};
use crate::errors::{ObligationError, Result};
use crate::expression::{
    Bound, BoundDomain, Builtin, Bullet, Channel, DefnCore, Expr, ExprCore, Hyp, HypCore, Hyps,
    Level, Modal, ObligationWarning, Param, Quantifier, ScopeRef, Warn, adjoin, adjoin_all,
    apply_builtin, at, expr, get_at_prefix, get_error_note, get_location_text, get_param_fresh,
    get_scope_at, is_builtin_apply, map_scoped, strip_props, to_index,
};
use crate::levels::{get_level_info, level_number};
use crate::substitution::{
    Substitution, SubstitutionNode, bump_by, normalize_apply, shift, substitute_expr,
};
use crate::temporal::rewrite_unchanged;

/// Which of ENABLED and \cdot a pass handles, and whether it may expand the definitions that
/// soundness needs expanded, as the AutoUSE directive allows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ActionOptions {
    pub is_enabled: bool,
    pub is_cdot: bool,
    pub is_auto_use: bool,
}

struct FreshNames {
    names: Vec<String>,
    depth: usize,
}

const ENABLED_WRAPPER: &str = "EnabledWrapper";
const CDOT_WRAPPER: &str = "CdotWrapper";

const NESTED_ENABLED: &str = "Nested occurrence of the operator `ENABLED` found in scope of `\\cdot` when expanding `\\cdot`. Using the proof directive `ExpandENABLED` from the module `TLAPS` is expected to avoid this error.For example, writing `BY ExpandENABLED`.";

const NESTED_CDOT: &str = "Nested occurrence of the operator `\\cdot` found in scope of `ENABLED` when expanding `ENABLED`. Using the proof directive `ExpandCdot` from the module `TLAPS` is expected to avoid this error.";

// Unlike auto_expansion_of_defs, tlapm puts a space before "For example" here.
fn get_nested_cdot_spaced() -> String {
    format!("{NESTED_CDOT} For example, writing `BY ExpandCdot`.")
}

// Visit.map_visible_hyp with no state.
fn map_visible_children(
    expression: &Expr,
    map: &mut dyn FnMut(&Expr) -> Result<Expr>,
) -> Result<Expr> {
    map_scoped(
        &(),
        expression,
        &mut |_, child| map(child),
        &mut |_, _| (),
        Hyps::Visible,
    )
}

fn get_hyp(scope: &ScopeRef, index: isize) -> Result<Hyp> {
    get_scope_at(scope, index - 1)
        .map(|found| found.hyp.clone())
        .ok_or_else(ObligationError::assert_failure)
}

/// `isActionOperator`: the builtin when the expression is ENABLED or \cdot.
fn is_action_operator(expression: &Expr) -> Option<Builtin> {
    match expression.core {
        ExprCore::Internal {
            builtin: builtin @ (Builtin::ENABLED | Builtin::Cdot),
        } => Some(builtin),
        _ => None,
    }
}

fn is_wrapper(expression: &Expr) -> bool {
    matches!(&expression.core, ExprCore::Opaque { name } if name == ENABLED_WRAPPER || name == CDOT_WRAPPER)
}

fn is_lambdified(expression: &Expr) -> bool {
    match &expression.core {
        ExprCore::Apply { operator, args } => {
            args.len() == 1
                && matches!(args[0].core, ExprCore::Lambda { .. })
                && (is_action_operator(operator).is_some() || is_wrapper(operator))
        }
        _ => false,
    }
}

fn get_initial_level(level: Option<usize>) -> usize {
    level.map_or(2, |level| level.min(2))
}

fn get_decremented_level(level: Option<usize>) -> Option<usize> {
    level.map(|level| level.saturating_sub(1).max(1))
}

/// The options and the warning sink every pass of this module threads through.
struct Pass<'sink, 'warn> {
    options: ActionOptions,
    on_warning: &'sink mut Warn<'warn>,
}

impl Pass<'_, '_> {
    // auto_expansion_of_defs. ENABLED and the first argument of \cdot need every definition of
    // action level expanded, a prime lowers that bound to 1, and so does the second argument of
    // \cdot.
    fn expand_definitions(
        &mut self,
        scope: &ScopeRef,
        expression: &Expr,
        level: Option<usize>,
    ) -> Result<Expr> {
        if is_lambdified(expression) {
            return Ok(expression.clone());
        }
        if let ExprCore::Sub {
            modal,
            action,
            subscript,
        } = &expression.core
        {
            let action = self.expand_definitions(scope, action, level)?;
            let subscript =
                self.expand_definitions(scope, subscript, get_decremented_level(level))?;
            return Ok(expression.with_core(ExprCore::Sub {
                modal: *modal,
                action,
                subscript,
            }));
        }
        if let ExprCore::Apply { operator, args } = &expression.core
            && let ExprCore::Internal { builtin } = operator.core
        {
            let with_args = |args| {
                expression.with_core(ExprCore::Apply {
                    operator: operator.clone(),
                    args,
                })
            };
            if builtin == Builtin::Cdot && args.len() == 2 {
                if level.is_some() && !self.options.is_cdot {
                    (self.on_warning)(get_error_note(
                        expression.location.as_ref(),
                        &format!("{NESTED_CDOT}For example, writing `BY ExpandCdot`."),
                    ));
                    return Err(ObligationError::prover("Expr.Action"));
                }
                let args = if self.options.is_cdot {
                    vec![
                        self.expand_definitions(scope, &args[0], Some(get_initial_level(level)))?,
                        self.expand_definitions(scope, &args[1], Some(1))?,
                    ]
                } else {
                    vec![
                        self.expand_definitions(scope, &args[0], level)?,
                        self.expand_definitions(scope, &args[1], level)?,
                    ]
                };
                return Ok(with_args(args));
            }
            if builtin == Builtin::ENABLED && args.len() == 1 {
                if level.is_some() && !self.options.is_enabled {
                    (self.on_warning)(get_error_note(expression.location.as_ref(), NESTED_ENABLED));
                    return Err(ObligationError::prover("Expr.Action"));
                }
                let inner_level = if self.options.is_enabled {
                    Some(get_initial_level(level))
                } else {
                    level
                };
                return Ok(with_args(vec![self.expand_definitions(
                    scope,
                    &args[0],
                    inner_level,
                )?]));
            }
            if (builtin == Builtin::Prime || builtin == Builtin::UNCHANGED) && args.len() == 1 {
                return Ok(with_args(vec![self.expand_definitions(
                    scope,
                    &args[0],
                    get_decremented_level(level),
                )?]));
            }
        }
        let head = match &expression.core {
            ExprCore::Apply { operator, .. } if matches!(operator.core, ExprCore::Ix { .. }) => {
                operator
            }
            _ => expression,
        };
        let ExprCore::Ix { index } = head.core else {
            return map_scoped(
                scope,
                expression,
                &mut |inner, child| self.expand_definitions(inner, child, level),
                &mut adjoin,
                Hyps::Visible,
            );
        };
        let Some(level) = level else {
            return Ok(expression.clone());
        };
        let expression_level = get_level_info(scope, expression)?.level;
        let hyp = get_hyp(scope, index)?;
        let get_declaration = |name: &str| {
            format!(
                "The operator `{name}` is declared at:\n{}",
                get_location_text(hyp.location.as_ref())
            )
        };
        if let HypCore::Fresh {
            name,
            shape,
            level: Level::Unknown,
            ..
        } = &hyp.core
        {
            (self.on_warning)(get_error_note(
                expression.location.as_ref(),
                &format!(
                    "Declared operator `{name}` has unknown level and occurs within the scope of `ENABLED` or `\\cdot` where soundness requires expanding expressions of level >= {level}.\nIf a constant operator is substituted for this operator, then the expression that results from applying this declared operator has expression level {expression_level}.\n May need expansion. A declared operator cannot be expanded.\n{}\n and has arity: {shape}",
                    get_declaration(name)
                ),
            ));
            return Err(ObligationError::bug(
                "File \"src/expr/e_action.ml\", line 367, characters 20-26: Assertion failed",
            ));
        }
        if expression_level < level {
            return Ok(expression.clone());
        }
        if expression_level > 2 || matches!(hyp.core, HypCore::Fact { .. }) {
            return Err(ObligationError::assert_failure());
        }
        let definition = match &hyp.core {
            HypCore::Flex { .. } => {
                if !matches!(expression.core, ExprCore::Ix { .. }) {
                    return Err(ObligationError::assert_failure());
                }
                return Ok(expression.clone());
            }
            HypCore::Fresh {
                name,
                shape,
                level: fresh_level,
                ..
            } => {
                let message = format!(
                    "The expression that results from applying the declared operator `{name}` has expression level {expression_level} within the scope of `ENABLED` or `\\cdot` where soundness requires expanding expressions of level >= {level}. A declared operator cannot be expanded.\n{}\n and has level: {}\n and arity: {shape}",
                    get_declaration(name),
                    level_number(*fresh_level)
                );
                (self.on_warning)(get_error_note(expression.location.as_ref(), &message));
                return Err(ObligationError::proof(message));
            }
            HypCore::Defn { definition, .. } => definition,
            HypCore::Fact { .. } => return Err(ObligationError::assert_failure()),
        };
        let (DefnCore::Operator {
            name,
            body: definition_body,
        }
        | DefnCore::Bpragma {
            name,
            body: definition_body,
            ..
        }) = &definition.core
        else {
            return Err(ObligationError::assert_failure());
        };
        if !self.options.is_auto_use {
            let names = if self.options.is_enabled && self.options.is_cdot {
                [
                    "the operators `ENABLED` and `\\cdot`",
                    "the proof directives `ExpandENABLED` and `ExpandCdot`",
                ]
            } else if self.options.is_enabled {
                ["the operator `ENABLED`", "`ExpandENABLED` proof directive"]
            } else {
                ["the operator `\\cdot`", "`ExpandCdot` proof directive"]
            };
            let body = match &definition_body.core {
                ExprCore::Lambda { body, .. } => body,
                _ => definition_body,
            };
            let message = format!(
                "Hidden definition of operator `{name}` needs expansion for soundly expanding {} (using rigid quantification).\nThe expansion of {} has been activated with the {} from the module `TLAPS`.\nThe operator `{name}` is defined at: \n\t{}\nand the operator `{name}` occurs at: \n\t{}\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF {name}` is expected to avoid this error.\n",
                names[0],
                names[0],
                names[1],
                get_location_text(body.location.as_ref()),
                get_location_text(expression.location.as_ref())
            );
            (self.on_warning)(get_error_note(expression.location.as_ref(), &message));
            return Err(ObligationError::prover(message));
        }
        (self.on_warning)(ObligationWarning {
            text: format!(
                "{}[INFO]: Auto-expanding the definition of operator:  {name}\n",
                get_at_prefix(expression.location.as_ref())
            ),
            channel: Channel::Stdout,
        });
        let body = substitute_expr(&shift(index), definition_body)?;
        let expanded = match &expression.core {
            ExprCore::Apply { args, .. } => expr(normalize_apply(&body, args.clone())?),
            _ => strip_props(&body),
        };
        self.expand_definitions(scope, &expanded, Some(level))
    }

    // lambdify_action_operators. A variable met directly binds into current, and one met under a
    // prime into primed. ENABLED A binds the primes of A, and A \cdot B binds those of A and the
    // unprimed variables of B, each as an opaque name such as x#enabled#prime1.
    fn bind_variables(
        &mut self,
        current: Option<&RefCell<FreshNames>>,
        primed: Option<&RefCell<FreshNames>>,
        scope: &ScopeRef,
        expression: &Expr,
    ) -> Result<Expr> {
        let is_in_scope = current.is_some() || primed.is_some();
        if is_lambdified(expression) {
            return Ok(expression.clone());
        }
        if let ExprCore::Apply { operator, args } = &expression.core
            && let ExprCore::Internal { builtin } = operator.core
        {
            if (self.options.is_enabled && builtin == Builtin::ENABLED && args.len() == 1)
                || (self.options.is_cdot && builtin == Builtin::Cdot && args.len() == 2)
            {
                return self.lambdify_operator(current, primed, scope, expression, operator, args);
            }
            if builtin == Builtin::ENABLED && is_in_scope {
                (self.on_warning)(get_error_note(expression.location.as_ref(), NESTED_ENABLED));
                return Err(ObligationError::prover("Expr.Action"));
            }
            if builtin == Builtin::Cdot && is_in_scope {
                (self.on_warning)(get_error_note(
                    expression.location.as_ref(),
                    &get_nested_cdot_spaced(),
                ));
                return Err(ObligationError::prover("Expr.Action"));
            }
            if builtin == Builtin::Prime && args.len() == 1 {
                let arg = self.bind_variables(primed, None, scope, &args[0])?;
                return Ok(if primed.is_some() {
                    arg
                } else {
                    expression.with_core(ExprCore::Apply {
                        operator: operator.clone(),
                        args: vec![arg],
                    })
                });
            }
            if builtin == Builtin::UNCHANGED && is_in_scope {
                return self.bind_variables(
                    current,
                    primed,
                    scope,
                    &expand_propositional(expression)?,
                );
            }
        }
        if matches!(expression.core, ExprCore::Sub { .. }) && is_in_scope {
            return self.bind_variables(current, primed, scope, &expand_propositional(expression)?);
        }
        if let ExprCore::Ix { index } = expression.core {
            let Some(current) = current else {
                return Ok(expression.clone());
            };
            let hyp = get_hyp(scope, index)?;
            let flex_name = match &hyp.core {
                HypCore::Fact { .. } => return Err(ObligationError::assert_failure()),
                HypCore::Flex { name } => name,
                _ => return Ok(expression.clone()),
            };
            let mut fresh = current.borrow_mut();
            let name = format!("{flex_name}#enabled#prime{}", fresh.depth);
            if !fresh.names.contains(&name) {
                fresh.names.push(name.clone());
            }
            return Ok(at(ExprCore::Opaque { name }, expression));
        }
        if let ExprCore::Apply { operator, .. } = &expression.core
            && let ExprCore::Opaque { name } = &operator.core
        {
            (self.on_warning)(get_error_note(
                expression.location.as_ref(),
                &format!("Named operator `{name}` unexpected after anonymization."),
            ));
            return Err(ObligationError::bug(
                "File \"src/expr/e_action.ml\", line 1048, characters 12-18: Assertion failed",
            ));
        }
        map_scoped(
            scope,
            expression,
            &mut |inner, child| self.bind_variables(current, primed, inner, child),
            &mut adjoin,
            Hyps::Visible,
        )
    }

    fn lambdify_operator(
        &mut self,
        current: Option<&RefCell<FreshNames>>,
        primed: Option<&RefCell<FreshNames>>,
        scope: &ScopeRef,
        expression: &Expr,
        operator: &Expr,
        args: &[Expr],
    ) -> Result<Expr> {
        let get_depth =
            |names: Option<&RefCell<FreshNames>>| names.map_or(0, |names| names.borrow().depth);
        let fresh = RefCell::new(FreshNames {
            names: Vec::new(),
            depth: get_depth(current).max(get_depth(primed)) + 1,
        });
        let mut bound = vec![self.bind_variables(current, Some(&fresh), scope, &args[0])?];
        if let Some(second) = args.get(1) {
            bound.push(self.bind_variables(Some(&fresh), primed, scope, second)?);
        }
        let names = fresh.into_inner().names;
        let params = if names.is_empty() {
            vec!["r#0".to_owned()]
        } else {
            get_hashtbl_keys(&names)
        };
        let body = if bound.len() == 1 {
            bound.remove(0)
        } else {
            expr(ExprCore::List {
                bullet: Bullet::And,
                items: bound,
            })
        };
        Ok(at(
            ExprCore::Apply {
                operator: operator.clone(),
                args: vec![expr(ExprCore::Lambda {
                    params: std::iter::once("_".to_owned())
                        .chain(params)
                        .map(|name| Param {
                            name,
                            shape: 0,
                            location: None,
                        })
                        .collect(),
                    body,
                })],
            },
            expression,
        ))
    }

    // replace_action_operators_with_quantifiers: each lambdified ENABLED or \cdot that the frontend
    // expands becomes \E over the parameters of its LAMBDA.
    fn replace_with_quantifiers(
        &mut self,
        scope: &ScopeRef,
        expression: &Expr,
        is_in_scope: bool,
    ) -> Result<Expr> {
        let options = self.options;
        let is_expanded = |builtin| {
            if builtin == Builtin::ENABLED {
                options.is_enabled
            } else {
                options.is_cdot
            }
        };
        if let ExprCore::Apply { operator, args } = &expression.core
            && args.len() == 1
        {
            let lambda = &args[0];
            if let ExprCore::Lambda { params, body } = &lambda.core {
                if let ExprCore::Opaque { name } = &operator.core
                    && ((options.is_enabled && name == ENABLED_WRAPPER)
                        || (options.is_cdot && name == CDOT_WRAPPER))
                {
                    return self.quantify(scope, params, body);
                }
                if let ExprCore::Ix { index } = operator.core
                    && (options.is_enabled || options.is_cdot)
                {
                    let hyp = get_hyp(scope, index)?;
                    let is_wrapper_definition = matches!(
                        &hyp.core,
                        HypCore::Defn { definition, .. }
                            if matches!(&definition.core, DefnCore::Operator { name, .. }
                                if name == ENABLED_WRAPPER || name == CDOT_WRAPPER)
                    );
                    if is_wrapper_definition {
                        return self.quantify(scope, params, body);
                    }
                }
                if is_action_operator(operator).is_some_and(is_expanded) {
                    return self.quantify(scope, params, body);
                }
            }
            if is_action_operator(operator).is_some_and(is_expanded) {
                return self.replace_with_quantifiers(scope, lambda, true);
            }
        }
        if is_builtin_apply(expression, Builtin::ENABLED).is_some() && is_in_scope {
            (self.on_warning)(get_error_note(expression.location.as_ref(), NESTED_ENABLED));
            return Err(ObligationError::prover("Expr.Action"));
        }
        if is_builtin_apply(expression, Builtin::Cdot).is_some() && is_in_scope {
            (self.on_warning)(get_error_note(
                expression.location.as_ref(),
                &get_nested_cdot_spaced(),
            ));
            return Err(ObligationError::prover("Expr.Action"));
        }
        map_scoped(
            scope,
            expression,
            &mut |inner, child| self.replace_with_quantifiers(inner, child, is_in_scope),
            &mut adjoin,
            Hyps::Visible,
        )
    }

    fn quantify(&mut self, scope: &ScopeRef, params: &[Param], body: &Expr) -> Result<Expr> {
        let bounds = params
            .iter()
            .map(|param| Bound {
                name: param.name.clone(),
                level: Level::Constant,
                domain: BoundDomain::NoDomain,
            })
            .collect();
        let fresh: Vec<Hyp> = params.iter().map(get_param_fresh).collect();
        Ok(expr(ExprCore::Quant {
            quantifier: Quantifier::Exists,
            bounds,
            body: self.replace_with_quantifiers(&adjoin_all(scope, &fresh), body, true)?,
        }))
    }
}

// expand_propositional_action_operators: UNCHANGED v, [A]_v and <<A>>_v in terms of primes.
fn expand_propositional(expression: &Expr) -> Result<Expr> {
    if let ExprCore::Apply { args, .. } = &expression.core
        && args.len() == 1
    {
        return Ok(rewrite_unchanged(&args[0]));
    }
    let ExprCore::Sub {
        modal,
        action,
        subscript,
    } = &expression.core
    else {
        return Err(ObligationError::assert_failure());
    };
    let props = expression.props();
    let unchanged = rewrite_unchanged(subscript);
    let second = if *modal == Modal::Box {
        unchanged
    } else {
        apply_builtin(Builtin::Neg, vec![unchanged], &props)
    };
    Ok(apply_builtin(
        if *modal == Modal::Box {
            Builtin::Disj
        } else {
            Builtin::Conj
        },
        vec![action.clone(), second],
        &props,
    ))
}

// ---- Begin: code under OCaml's LGPL-2.1 with its linking exception ----

// OCaml's Hashtbl.hash of a string: caml_hash's MurmurHash3 over the bytes.
// Ported from OCaml's runtime/hash.c, so under OCaml's LGPL-2.1 with its linking exception, not
// MIT (THIRD_PARTY_NOTICES.md).
fn get_hash(text: &str) -> u32 {
    let mix = |hash: u32, data: u32| {
        let word = data
            .wrapping_mul(0xcc9e_2d51)
            .rotate_left(15)
            .wrapping_mul(0x1b87_3593);
        (hash ^ word)
            .rotate_left(13)
            .wrapping_mul(5)
            .wrapping_add(0xe654_6b64)
    };
    let bytes = text.as_bytes();
    let (chunks, tail) = bytes.as_chunks::<4>();
    let mut hash = chunks
        .iter()
        .fold(0, |hash, chunk| mix(hash, u32::from_le_bytes(*chunk)));
    if !tail.is_empty() {
        hash = mix(
            hash,
            tail.iter()
                .rev()
                .fold(0, |word, byte| (word << 8) | u32::from(*byte)),
        );
    }
    // JavaScript's `^` takes the length modulo 2^32.
    hash ^= bytes.len() as u32;
    hash = (hash ^ (hash >> 16)).wrapping_mul(0x85eb_ca6b);
    hash = (hash ^ (hash >> 13)).wrapping_mul(0xc2b2_ae35);
    (hash ^ (hash >> 16)) & 0x3fff_ffff
}

// ---- End: code under OCaml's LGPL-2.1 with its linking exception ----

// The keys of an OCaml Hashtbl.create 16 in Hashtbl.to_seq_keys order. Hashtbl.add prepends to a
// bucket and doubles the buckets once the table holds more than twice their count.
fn get_hashtbl_keys(names: &[String]) -> Vec<String> {
    let get_bucket = |name: &str, count: usize| get_hash(name) as usize & (count - 1);
    let mut buckets: Vec<Vec<String>> = vec![Vec::new(); 16];
    for (index, name) in names.iter().enumerate() {
        let count = buckets.len();
        buckets[get_bucket(name, count)].insert(0, name.clone());
        if index < count * 2 {
            continue;
        }
        let mut resized: Vec<Vec<String>> = vec![Vec::new(); count * 2];
        for key in buckets.into_iter().flatten() {
            resized[get_bucket(&key, count * 2)].push(key);
        }
        buckets = resized;
    }
    buckets.concat()
}

// shift_indices_after_lambdify, a Subst.map_visible_hyp that makes room in each new LAMBDA body
// for its parameters and drops the placeholder parameter.
fn shift_indices(substitution: &Substitution, expression: &Expr) -> Result<Expr> {
    if let ExprCore::Apply { operator, args } = &expression.core
        && is_action_operator(operator).is_some()
    {
        let (1, Some(ExprCore::Lambda { params, body })) =
            (args.len(), args.first().map(|lambda| &lambda.core))
        else {
            return Err(ObligationError::assert_failure());
        };
        // The TypeScript fails with a TypeError on a LAMBDA without parameters, which the parser
        // never builds; the Rust reports an assertion.
        let Some((placeholder, params)) = params.split_first() else {
            return Err(ObligationError::assert_failure());
        };
        if placeholder.name != "_" {
            return Ok(expression.clone());
        }
        let body = shift_indices(
            &Rc::new(SubstitutionNode::Compose {
                outer: substitution.clone(),
                inner: shift(to_index(params.len())),
            }),
            body,
        )?;
        return Ok(expr(ExprCore::Apply {
            operator: operator.clone(),
            args: vec![expr(ExprCore::Lambda {
                params: params.to_vec(),
                body,
            })],
        }));
    }
    match &expression.core {
        ExprCore::Ix { .. } => substitute_expr(substitution, expression),
        ExprCore::Apply { operator, args } => {
            let operator = shift_indices(substitution, operator)?;
            let args = args
                .iter()
                .map(|arg| shift_indices(substitution, arg))
                .collect::<Result<Vec<_>>>()?;
            Ok(at(normalize_apply(&operator, args)?, expression))
        }
        _ => map_scoped(
            substitution,
            expression,
            &mut shift_indices,
            &mut |current, _| bump_by(1, current),
            Hyps::Visible,
        ),
    }
}

// normalize_lambda_param_names.
fn rename_params(is_keeping_names: bool, expression: &Expr) -> Result<Expr> {
    if let ExprCore::Apply { operator, args } = &expression.core
        && let Some(builtin) = is_action_operator(operator)
    {
        // The TypeScript fails with a TypeError on a LAMBDA without parameters, which only a
        // LAMBDA whose sole parameter is named `_` becomes; the Rust reports an assertion.
        let (1, Some(ExprCore::Lambda { params, body })) =
            (args.len(), args.first().map(|lambda| &lambda.core))
        else {
            return Err(ObligationError::assert_failure());
        };
        if params.first().is_none_or(|param| param.name == "_") {
            return Err(ObligationError::assert_failure());
        }
        let name = if builtin == Builtin::Cdot {
            CDOT_WRAPPER
        } else {
            ENABLED_WRAPPER
        };
        return Ok(expr(ExprCore::Apply {
            operator: at(
                ExprCore::Opaque {
                    name: name.to_owned(),
                },
                operator,
            ),
            args: vec![expr(ExprCore::Lambda {
                params: params
                    .iter()
                    .enumerate()
                    .map(|(index, param)| Param {
                        name: if is_keeping_names {
                            param.name.clone()
                        } else {
                            format!("r#{index}")
                        },
                        shape: 0,
                        location: None,
                    })
                    .collect(),
                body: rename_params(is_keeping_names, body)?,
            })],
        }));
    }
    map_visible_children(expression, &mut |child| {
        rename_params(is_keeping_names, child)
    })
}

// check_arity.
fn check_arity(expression: &Expr) -> Result<Expr> {
    if let Some(args) = is_builtin_apply(expression, Builtin::Cdot)
        && args.len() == 1
        && !matches!(args[0].core, ExprCore::Lambda { .. })
    {
        return Err(ObligationError::assert_failure());
    }
    map_visible_children(expression, &mut check_arity)
}

// lambdify_action_operators#expand.
fn lambdify_operators(
    anonymizer: &mut Anonymizer,
    host: &mut dyn AnonymizerHost,
    pass: &mut Pass,
    scope: &ScopeRef,
    expression: &Expr,
    is_keeping_names: bool,
) -> Result<Expr> {
    let bound = pass.bind_variables(None, None, scope, expression)?;
    let shifted = shift_indices(&shift(0), &bound)?;
    rename_params(is_keeping_names, &anonymizer.expr(host, scope, &shifted)?)
}

const LAMBDIFY_ALL: ActionOptions = ActionOptions {
    is_enabled: true,
    is_cdot: true,
    is_auto_use: true,
};

/// `lambdify`. `anonymizer` with `host` is the TypeScript's anonymizer; `options` defaults to
/// every operator with AutoUSE.
pub fn lambdify(
    anonymizer: &mut Anonymizer,
    host: &mut dyn AnonymizerHost,
    on_warning: &mut Warn,
    scope: &ScopeRef,
    expression: &Expr,
    options: Option<ActionOptions>,
) -> Result<Expr> {
    let mut pass = Pass {
        options: options.unwrap_or(LAMBDIFY_ALL),
        on_warning,
    };
    let expanded = pass.expand_definitions(scope, expression, None)?;
    check_arity(&lambdify_operators(
        anonymizer, host, &mut pass, scope, &expanded, false,
    )?)
}

// commute_exists_disjunction: \E x : A \/ B as (\E x : A) \/ (\E x : B), everywhere.
fn commute_exists_disjunction(expression: &Expr) -> Result<Expr> {
    if let ExprCore::Quant {
        quantifier: Quantifier::Exists,
        bounds,
        body,
    } = &expression.core
    {
        let quantify = |item: &Expr| {
            expression.with_core(ExprCore::Quant {
                quantifier: Quantifier::Exists,
                bounds: bounds.clone(),
                body: item.clone(),
            })
        };
        if let ExprCore::List {
            bullet: Bullet::Or,
            items,
        } = &body.core
        {
            return commute_exists_disjunction(&body.with_core(ExprCore::List {
                bullet: Bullet::Or,
                items: items.iter().map(quantify).collect(),
            }));
        }
        if let ExprCore::Apply { operator, args } = &body.core
            && is_builtin_apply(body, Builtin::Disj).is_some()
        {
            if args.len() != 2 {
                return Err(ObligationError::assert_failure());
            }
            return commute_exists_disjunction(&body.with_core(ExprCore::Apply {
                operator: operator.clone(),
                args: args.iter().map(quantify).collect(),
            }));
        }
    }
    map_visible_children(expression, &mut commute_exists_disjunction)
}

/// `expandActionOperators`: the ExpandENABLED and ExpandCdot frontends (expand_action_operators).
pub fn expand_action_operators(
    anonymizer: &mut Anonymizer,
    host: &mut dyn AnonymizerHost,
    on_warning: &mut Warn,
    scope: &ScopeRef,
    expression: &Expr,
    options: ActionOptions,
) -> Result<Expr> {
    let mut pass = Pass {
        options,
        on_warning,
    };
    let expanded = pass.expand_definitions(scope, expression, None)?;
    let lambdified = lambdify_operators(anonymizer, host, &mut pass, scope, &expanded, true)?;
    commute_exists_disjunction(&pass.replace_with_quantifiers(scope, &lambdified, false)?)
}

#[cfg(test)]
mod tests {
    // The expected values come from running `action.ts` under Bun on the same inputs, written and
    // printed in the compact syntax below by a TypeScript twin of this parser and printer.
    use super::*;
    use crate::anonymize::create_anonymizer;
    use crate::expression::{
        Defn, ExprNode, HypNode, Locus, Sequent, Time, Visibility, WhereDefined, hyp,
    };
    use crate::proof::Counter;

    enum Tree {
        Atom(String),
        List(Vec<Tree>),
    }

    fn parse_tree(text: &str) -> Tree {
        let spaced = text.replace('(', " ( ").replace(')', " ) ");
        let tokens: Vec<&str> = spaced.split_whitespace().collect();
        fn read(tokens: &[&str], position: &mut usize) -> Tree {
            let token = tokens[*position];
            *position += 1;
            if token != "(" {
                return Tree::Atom(token.to_owned());
            }
            let mut items = Vec::new();
            while tokens[*position] != ")" {
                items.push(read(tokens, position));
            }
            *position += 1;
            Tree::List(items)
        }
        read(&tokens, &mut 0)
    }

    fn atom(tree: &Tree) -> &str {
        match tree {
            Tree::Atom(text) => text,
            Tree::List(_) => panic!("expected an atom"),
        }
    }

    fn items(tree: &Tree) -> &[Tree] {
        match tree {
            Tree::List(items) => items,
            Tree::Atom(text) => panic!("expected a list, got {text}"),
        }
    }

    fn locus(line: &Tree) -> Option<Locus> {
        let line = atom(line).parse().unwrap();
        Some(Locus {
            file: "M.tla".into(),
            start_line: line,
            start_column: 3,
            end_line: line,
            end_column: 9,
        })
    }

    fn get_builtin(name: &str) -> Builtin {
        use Builtin::*;
        [
            ENABLED, Cdot, Prime, UNCHANGED, Conj, Disj, Neg, Eq, TRUE, FALSE, Implies, BoxTrue,
            Plus, Mem,
        ]
        .into_iter()
        .find(|builtin| builtin.name() == name)
        .unwrap()
    }

    fn to_expr(tree: &Tree) -> Expr {
        let core = match tree {
            Tree::Atom(text) => {
                if let Ok(index) = text.parse() {
                    ExprCore::Ix { index }
                } else if let Some(name) = text.strip_prefix('$') {
                    ExprCore::Opaque {
                        name: name.to_owned(),
                    }
                } else {
                    ExprCore::Internal {
                        builtin: get_builtin(text),
                    }
                }
            }
            Tree::List(list) => {
                let rest = &list[1..];
                let all = |trees: &[Tree]| trees.iter().map(to_expr).collect::<Vec<_>>();
                match atom(&list[0]) {
                    "at" => {
                        let inner = to_expr(&rest[1]);
                        return Rc::new(ExprNode {
                            location: locus(&rest[0]),
                            ..(*inner).clone()
                        });
                    }
                    "app" => ExprCore::Apply {
                        operator: to_expr(&rest[0]),
                        args: all(&rest[1..]),
                    },
                    "lam" => ExprCore::Lambda {
                        params: items(&rest[0])
                            .iter()
                            .map(|param| {
                                let mut parts = atom(param).split(':');
                                Param {
                                    name: parts.next().unwrap().to_owned(),
                                    shape: parts.next().map_or(0, |shape| shape.parse().unwrap()),
                                    location: None,
                                }
                            })
                            .collect(),
                        body: to_expr(&rest[1]),
                    },
                    "and" => ExprCore::List {
                        bullet: Bullet::And,
                        items: all(rest),
                    },
                    "or" => ExprCore::List {
                        bullet: Bullet::Or,
                        items: all(rest),
                    },
                    head @ ("ex" | "all") => ExprCore::Quant {
                        quantifier: if head == "ex" {
                            Quantifier::Exists
                        } else {
                            Quantifier::Forall
                        },
                        bounds: items(&rest[0])
                            .iter()
                            .map(|name| Bound {
                                name: atom(name).to_owned(),
                                level: Level::Constant,
                                domain: BoundDomain::NoDomain,
                            })
                            .collect(),
                        body: to_expr(&rest[1]),
                    },
                    head @ ("box" | "dia") => ExprCore::Sub {
                        modal: if head == "box" {
                            Modal::Box
                        } else {
                            Modal::Dia
                        },
                        action: to_expr(&rest[0]),
                        subscript: to_expr(&rest[1]),
                    },
                    "tup" => ExprCore::Tuple {
                        elements: all(rest),
                    },
                    "if" => ExprCore::If {
                        condition: to_expr(&rest[0]),
                        consequent: to_expr(&rest[1]),
                        alternative: to_expr(&rest[2]),
                    },
                    "seq" => ExprCore::Sequent {
                        sequent: Sequent {
                            context: items(&rest[0]).iter().map(to_hyp).collect(),
                            active: to_expr(&rest[1]),
                        },
                    },
                    other => panic!("unknown form {other}"),
                }
            }
        };
        expr(core)
    }

    fn to_hyp(tree: &Tree) -> Hyp {
        let list = items(tree);
        let rest = &list[1..];
        let name = || atom(&rest[0]).to_owned();
        let defn = |core, visibility| HypCore::Defn {
            definition: Defn {
                core,
                location: None,
            },
            where_defined: WhereDefined::User,
            visibility,
            is_local: false,
            is_constness_unset: false,
        };
        let operator = || DefnCore::Operator {
            name: name(),
            body: to_expr(&rest[1]),
        };
        let core = match atom(&list[0]) {
            "at" => {
                let inner = to_hyp(&rest[1]);
                return Rc::new(HypNode {
                    core: inner.core.clone(),
                    location: locus(&rest[0]),
                });
            }
            "fresh" => HypCore::Fresh {
                name: name(),
                level: match atom(&rest[1]) {
                    "Constant" => Level::Constant,
                    "State" => Level::State,
                    "Action" => Level::Action,
                    "Temporal" => Level::Temporal,
                    _ => Level::Unknown,
                },
                shape: atom(&rest[2]).parse().unwrap(),
                domain: None,
                domain_visibility: Visibility::Visible,
            },
            "flex" => HypCore::Flex { name: name() },
            "def" => defn(operator(), Visibility::Visible),
            "hdef" => defn(operator(), Visibility::Hidden),
            "bpragma" => defn(
                DefnCore::Bpragma {
                    name: name(),
                    body: to_expr(&rest[1]),
                    methods: Vec::new(),
                },
                Visibility::Visible,
            ),
            "recursive" => defn(
                DefnCore::Recursive {
                    name: name(),
                    shape: atom(&rest[1]).parse().unwrap(),
                },
                Visibility::Visible,
            ),
            "fact" => HypCore::Fact {
                expression: to_expr(&rest[0]),
                visibility: Visibility::Visible,
                time: Time::Now,
                use_location: None,
            },
            other => panic!("unknown hypothesis {other}"),
        };
        hyp(core)
    }

    fn show_list(head: &str, items: impl IntoIterator<Item = String>) -> String {
        let mut parts = vec![head.to_owned()];
        parts.extend(items);
        format!("({})", parts.join(" "))
    }

    fn show_names(names: impl Iterator<Item = String>) -> String {
        format!("({})", names.collect::<Vec<_>>().join(" "))
    }

    fn show(expression: &Expr) -> String {
        let all = |items: &[Expr]| items.iter().map(show).collect::<Vec<_>>();
        let core = match &expression.core {
            ExprCore::Ix { index } => index.to_string(),
            ExprCore::Opaque { name } => format!("${name}"),
            ExprCore::Internal { builtin } => builtin.name().to_owned(),
            ExprCore::Apply { operator, args } => {
                show_list("app", std::iter::once(show(operator)).chain(all(args)))
            }
            ExprCore::Lambda { params, body } => {
                let names = show_names(params.iter().map(|param| match param.shape {
                    0 => param.name.clone(),
                    shape => format!("{}:{shape}", param.name),
                }));
                show_list("lam", [names, show(body)])
            }
            ExprCore::List { bullet, items } => {
                show_list(&format!("{bullet:?}").to_lowercase(), all(items))
            }
            ExprCore::Quant {
                quantifier,
                bounds,
                body,
            } => {
                let names = show_names(bounds.iter().map(|bound| {
                    let level = match bound.level {
                        Level::Constant => String::new(),
                        level => format!(":{level:?}"),
                    };
                    let domain = match &bound.domain {
                        BoundDomain::NoDomain => String::new(),
                        BoundDomain::Domain(domain) => format!(":{}", show(domain)),
                        BoundDomain::Ditto => ":ditto".to_owned(),
                    };
                    format!("{}{level}{domain}", bound.name)
                }));
                let head = if *quantifier == Quantifier::Exists {
                    "ex"
                } else {
                    "all"
                };
                show_list(head, [names, show(body)])
            }
            ExprCore::Sub {
                modal,
                action,
                subscript,
            } => {
                let head = if *modal == Modal::Box { "box" } else { "dia" };
                show_list(head, [show(action), show(subscript)])
            }
            ExprCore::Tuple { elements } => show_list("tup", all(elements)),
            ExprCore::If {
                condition,
                consequent,
                alternative,
            } => show_list("if", [show(condition), show(consequent), show(alternative)]),
            ExprCore::Sequent { sequent } => {
                let hyps = show_names(sequent.context.iter().map(show_hyp));
                show_list("seq", [hyps, show(&sequent.active)])
            }
            other => panic!("cannot show {other:?}"),
        };
        let atomic = if expression.is_atomic {
            format!("(atomic {core})")
        } else {
            core
        };
        match &expression.location {
            Some(locus) => format!("(at {} {atomic})", locus.start_line),
            None => atomic,
        }
    }

    fn show_hyp(item: &Hyp) -> String {
        let core = match &item.core {
            HypCore::Fresh {
                name, level, shape, ..
            } => format!("(fresh {name} {level:?} {shape})"),
            HypCore::Flex { name } => format!("(flex {name})"),
            HypCore::Fact { expression, .. } => format!("(fact {})", show(expression)),
            HypCore::Defn {
                definition,
                visibility,
                ..
            } => match &definition.core {
                DefnCore::Recursive { name, shape } => format!("(recursive {name} {shape})"),
                DefnCore::Operator { name, body } => {
                    let head = if *visibility == Visibility::Hidden {
                        "hdef"
                    } else {
                        "def"
                    };
                    format!("({head} {name} {})", show(body))
                }
                DefnCore::Bpragma { name, body, .. } => format!("(bpragma {name} {})", show(body)),
                DefnCore::Instance { .. } => panic!("cannot show an instance"),
            },
        };
        match &item.location {
            Some(locus) => format!("(at {} {core})", locus.start_line),
            None => core,
        }
    }

    fn show_warning(prefix: &str, warning: &ObligationWarning) -> String {
        let channel = match warning.channel {
            Channel::Toolbox => "toolbox",
            Channel::ToolboxOnly => "toolboxOnly",
            Channel::Stderr => "stderr",
            Channel::Stdout => "stdout",
        };
        format!("{prefix}{channel}: {}", warning.text)
    }

    /// The anonymizer's host: the test's `createAnonymizer` has no instance expander, and its
    /// warnings go to the shared list with an `anon ` prefix.
    struct TestHost {
        warnings: Rc<RefCell<Vec<String>>>,
    }

    impl AnonymizerHost for TestHost {
        fn expand_instance(
            &mut self,
            _: &mut Anonymizer,
            _: &ScopeRef,
            _: &Defn,
        ) -> Result<Vec<Defn>> {
            Err(ObligationError::assert_failure())
        }

        fn on_warning(&mut self, warning: ObligationWarning) {
            self.warnings
                .borrow_mut()
                .push(show_warning("anon ", &warning));
        }
    }

    fn show_error(error: &ObligationError) -> String {
        match error {
            ObligationError::Proof {
                message,
                failure,
                exception,
            } => format!(
                "ERR TlaProofError|{message}|{}|{exception}",
                failure.as_deref().unwrap_or("-")
            ),
            other => format!("ERR {}|{}", other.name(), other.message()),
        }
    }

    fn run(function: &str, flags: &str, scope: &str, input: &str) -> (String, Vec<String>) {
        let warnings = Rc::new(RefCell::new(Vec::new()));
        let mut host = TestHost {
            warnings: warnings.clone(),
        };
        let mut on_warning = |warning: ObligationWarning| {
            warnings.borrow_mut().push(show_warning("", &warning));
        };
        let mut anonymizer = create_anonymizer(Rc::new(Counter { value: 0.into() }));
        let hyps: Vec<Hyp> = items(&parse_tree(scope)).iter().map(to_hyp).collect();
        let scope = adjoin_all(&None, &hyps);
        let options = (flags != "default").then(|| ActionOptions {
            is_enabled: flags.as_bytes()[0] == b'e',
            is_cdot: flags.as_bytes()[1] == b'c',
            is_auto_use: flags.as_bytes()[2] == b'a',
        });
        let expression = to_expr(&parse_tree(input));
        let result = if function == "lambdify" {
            lambdify(
                &mut anonymizer,
                &mut host,
                &mut on_warning,
                &scope,
                &expression,
                options,
            )
        } else {
            expand_action_operators(
                &mut anonymizer,
                &mut host,
                &mut on_warning,
                &scope,
                &expression,
                options.unwrap(),
            )
        };
        let shown = result.as_ref().map_or_else(show_error, show);
        (shown, warnings.take())
    }

    #[test]
    fn get_hash_matches_ocaml() {
        for (text, expected) in HASHES {
            assert_eq!(get_hash(text), *expected, "{text:?}");
        }
    }

    #[test]
    fn get_hashtbl_keys_matches_ocaml() {
        for (count, expected) in HASHTBL_KEYS {
            let names: Vec<String> = (0..*count)
                .map(|index| format!("n{index}#enabled#prime1"))
                .collect();
            let keys: Vec<String> = get_hashtbl_keys(&names)
                .iter()
                .map(|name| name[1..name.find('#').unwrap()].to_owned())
                .collect();
            assert_eq!(keys.join(" "), *expected, "{count} names");
        }
    }

    #[test]
    fn lambdify_and_expand_match_typescript() {
        for (function, flags, scope, input, expected, warnings) in CASES {
            let (shown, actual) = run(function, flags, scope, input);
            assert_eq!(shown, *expected, "{function} {flags} {scope} {input}");
            assert_eq!(actual, *warnings, "{function} {flags} {scope} {input}");
        }
    }

    #[rustfmt::skip]
    const HASHES: &[(&str, u32)] = &[
    ("", 0),
    ("a", 721651713),
    ("b", 244624933),
    ("ab", 856662637),
    ("abc", 767105082),
    ("abcd", 65890154),
    ("abcde", 335633756),
    ("abcdef", 926323203),
    ("abcdefg", 577950338),
    ("abcdefgh", 165530820),
    ("x#enabled#prime1", 227812508),
    ("y#enabled#prime1", 573856066),
    ("x#enabled#prime2", 581246164),
    ("r#0", 495701670),
    ("_", 479219308),
    ("EnabledWrapper", 132122125),
    ("CdotWrapper", 633715628),
    ("é", 536833112),
    ("日本語", 1023232576),
    ("😀", 1051995898),
    ("a\u{0000}b", 803343445),
    ("The quick brown fox jumps over the lazy dog", 177794637),
    ("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx", 824198158),
    ("longer_variable_name#enabled#prime12", 1073552321),
    ("v0#enabled#prime1", 109826484),
    ("v1#enabled#prime2", 429103180),
    ("v2#enabled#prime3", 479299574),
    ("v3#enabled#prime1", 439032660),
    ("v4#enabled#prime2", 356092056),
    ("v5#enabled#prime3", 37686928),
    ("v6#enabled#prime1", 519153250),
    ("v7#enabled#prime2", 728725915),
    ("v8#enabled#prime3", 1028576423),
    ("v9#enabled#prime1", 69495949),
    ("v10#enabled#prime2", 757554453),
    ("v11#enabled#prime3", 728693255),
    ("v12#enabled#prime1", 112334500),
    ("v13#enabled#prime2", 671687679),
    ("v14#enabled#prime3", 217448867),
    ("v15#enabled#prime1", 595126654),
    ("v16#enabled#prime2", 930637046),
    ("v17#enabled#prime3", 790532517),
    ("v18#enabled#prime1", 1016420856),
    ("v19#enabled#prime2", 835343648),
    ("v20#enabled#prime3", 454649435),
    ("v21#enabled#prime1", 802320365),
    ("v22#enabled#prime2", 371309651),
    ("v23#enabled#prime3", 790238936),
    ("v24#enabled#prime1", 165703121),
    ("v25#enabled#prime2", 410388339),
    ("v26#enabled#prime3", 139461797),
    ("v27#enabled#prime1", 958641979),
    ("v28#enabled#prime2", 327697074),
    ("v29#enabled#prime3", 908652603),
    ];
    #[rustfmt::skip]
    const HASHTBL_KEYS: &[(usize, &str)] = &[
    (1, "0"),
    (2, "1 0"),
    (16, "9 11 3 1 15 0 6 13 5 12 2 10 4 7 14 8"),
    (32, "22 9 11 3 1 27 28 26 25 24 15 0 30 20 6 19 13 5 18 12 2 23 10 4 31 7 16 29 21 17 14 8"),
    (33, "22 1 27 20 6 19 18 12 23 10 4 31 7 21 17 14 32 9 11 3 28 26 25 24 15 0 30 13 5 2 16 29 8"),
    (34, "22 1 27 33 20 6 19 18 12 23 10 4 31 7 21 17 14 32 9 11 3 28 26 25 24 15 0 30 13 5 2 16 29 8"),
    (65, "22 37 27 33 53 20 18 52 12 34 23 10 31 7 43 17 14 41 3 26 15 48 60 55 38 30 51 54 5 40 1 39 6 19 63 44 4 35 56 21 46 32 9 58 11 61 28 25 24 64 0 62 36 13 57 49 45 2 47 42 16 59 29 8 50"),
    (66, "22 37 27 33 53 20 18 52 12 34 23 10 31 7 43 17 14 41 3 26 15 48 60 55 38 30 51 54 5 40 1 39 6 19 65 63 44 4 35 56 21 46 32 9 58 11 61 28 25 24 64 0 62 36 13 57 49 45 2 47 42 16 59 29 8 50"),
    (100, "22 37 27 33 53 20 75 18 52 92 80 12 34 23 10 31 7 88 81 43 93 17 14 41 3 96 26 15 85 48 60 55 38 30 51 97 54 5 99 79 70 69 84 82 40 1 39 6 74 19 68 65 63 87 44 98 4 35 91 56 71 21 76 46 95 32 9 58 11 94 78 61 28 25 24 64 0 77 62 36 13 86 73 57 49 45 90 2 83 72 47 67 66 42 16 89 59 29 8 50"),
    (140, "22 37 138 105 111 92 80 12 23 31 7 81 109 101 93 14 123 41 96 85 48 60 55 38 30 97 54 5 134 99 117 70 82 1 39 74 65 87 44 132 98 35 119 56 100 21 76 46 126 95 139 58 118 61 25 24 135 36 73 45 90 66 42 110 89 50 120 103 27 33 53 20 75 137 18 124 52 34 10 104 88 43 17 3 26 15 121 51 79 106 102 122 69 127 84 40 113 6 19 68 63 136 125 4 130 115 91 108 71 107 131 116 32 9 11 94 78 28 64 0 77 62 13 129 133 112 86 57 49 2 83 72 47 67 16 114 59 29 8 128"),
    ];
    type Case = (
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        &'static [&'static str],
    );
    #[rustfmt::skip]
    const CASES: &[Case] = &[
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (app Eq (app Prime 2) 1))", "(app $EnabledWrapper (lam (r#0) (app Eq 1 2)))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(at 5 (app (at 6 ENABLED) (and (app Prime 2) (app Prime 1))))", "(app (at 6 $EnabledWrapper) (lam (r#0 r#1) (and 1 2)))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app Cdot (app Eq (app Prime 2) 1) (app Eq (app Prime 1) 2))", "(app $CdotWrapper (lam (r#0) (and (app Eq 1 2) (app Eq (app Prime 2) 1))))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app Cdot (app Prime 2) (app Prime (app Prime 2)))", "(app $CdotWrapper (lam (r#0) (and 1 (app Prime (app Prime 3)))))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (app ENABLED (app Prime 2)))", "(app $EnabledWrapper (lam (r#0) (app $EnabledWrapper (lam (r#0) 1))))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (and (app Prime 2) (app Cdot (app Prime 1) (app Eq 2 1))))", "(app $EnabledWrapper (lam (r#0) (and 1 (app $CdotWrapper (lam (r#0 r#1) (and 1 (app Eq 2 1)))))))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (box (app Prime 2) (tup 2 1)))", "(app $EnabledWrapper (lam (r#0 r#1) (app Disj 1 (and (app Eq 1 4) (app Eq 2 3)))))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (dia (app Prime 2) 1))", "(app $EnabledWrapper (lam (r#0 r#1) (app Conj 1 (app Neg (app Eq 2 3)))))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (app UNCHANGED (tup 2 (tup 1))))", "(app $EnabledWrapper (lam (r#0 r#1) (and (app Eq 1 4) (app Eq 2 3))))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (app Prime 3))", "(app $EnabledWrapper (lam (r#0) 4))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (ex (z) (app Eq (app Prime 3) 1)))", "(app $EnabledWrapper (lam (r#0) (ex (z) (app Eq 2 1))))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (lam (a) 1))", "(app $EnabledWrapper (lam (r#0) 1))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app Cdot (lam (a) 1))", "(app $CdotWrapper (lam (r#0) 1))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app Cdot 1)", "ERR TlaProofError|Oops, this seems to be a bug in TLAPM.|-|Assert_failure", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (app $Foo 1))", "ERR TlaProofError|Oops, this seems to be a bug in TLAPM.|-|File \"src/expr/e_action.ml\", line 1048, characters 12-18: Assertion failed", &["stderr: <unknown location>:\nError: Named operator `Foo` unexpected after anonymization."]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(if (app ENABLED (app Prime 2)) (app Prime 1) (app ENABLED 1))", "(if (app $EnabledWrapper (lam (r#0) 1)) (app Prime 1) (app $EnabledWrapper (lam (r#0) 2)))", &[]),
    ("lambdify", "default", "((flex x) (def A (app Prime 1)))", "(app ENABLED (at 4 1))", "(app $EnabledWrapper (lam (r#0) 1))", &["stdout: File \"M.tla\", line 4, characters 3-8:\n[INFO]: Auto-expanding the definition of operator:  A\n"]),
    ("lambdify", "ec-", "((flex x) (def A (app Prime 1)))", "(app ENABLED (at 4 1))", "ERR TlaProverError|Hidden definition of operator `A` needs expansion for soundly expanding the operators `ENABLED` and `\\cdot` (using rigid quantification).\nThe expansion of the operators `ENABLED` and `\\cdot` has been activated with the the proof directives `ExpandENABLED` and `ExpandCdot` from the module `TLAPS`.\nThe operator `A` is defined at: \n\t<unknown location>\nand the operator `A` occurs at: \n\tFile \"M.tla\", line 4, characters 3-8\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF A` is expected to avoid this error.\n", &["stderr: File \"M.tla\", line 4, characters 3-8:\nError: Hidden definition of operator `A` needs expansion for soundly expanding the operators `ENABLED` and `\\cdot` (using rigid quantification).\nThe expansion of the operators `ENABLED` and `\\cdot` has been activated with the the proof directives `ExpandENABLED` and `ExpandCdot` from the module `TLAPS`.\nThe operator `A` is defined at: \n\t<unknown location>\nand the operator `A` occurs at: \n\tFile \"M.tla\", line 4, characters 3-8\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF A` is expected to avoid this error.\n"]),
    ("lambdify", "e--", "((flex x) (def A (at 7 (app Prime 1))))", "(app ENABLED (at 4 1))", "ERR TlaProverError|Hidden definition of operator `A` needs expansion for soundly expanding the operator `ENABLED` (using rigid quantification).\nThe expansion of the operator `ENABLED` has been activated with the `ExpandENABLED` proof directive from the module `TLAPS`.\nThe operator `A` is defined at: \n\tFile \"M.tla\", line 7, characters 3-8\nand the operator `A` occurs at: \n\tFile \"M.tla\", line 4, characters 3-8\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF A` is expected to avoid this error.\n", &["stderr: File \"M.tla\", line 4, characters 3-8:\nError: Hidden definition of operator `A` needs expansion for soundly expanding the operator `ENABLED` (using rigid quantification).\nThe expansion of the operator `ENABLED` has been activated with the `ExpandENABLED` proof directive from the module `TLAPS`.\nThe operator `A` is defined at: \n\tFile \"M.tla\", line 7, characters 3-8\nand the operator `A` occurs at: \n\tFile \"M.tla\", line 4, characters 3-8\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF A` is expected to avoid this error.\n"]),
    ("lambdify", "-c-", "((flex x) (def A (app Prime 1)))", "(app Cdot 1 1)", "ERR TlaProverError|Hidden definition of operator `A` needs expansion for soundly expanding the operator `\\cdot` (using rigid quantification).\nThe expansion of the operator `\\cdot` has been activated with the `ExpandCdot` proof directive from the module `TLAPS`.\nThe operator `A` is defined at: \n\t<unknown location>\nand the operator `A` occurs at: \n\t<unknown location>\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF A` is expected to avoid this error.\n", &["stderr: <unknown location>:\nError: Hidden definition of operator `A` needs expansion for soundly expanding the operator `\\cdot` (using rigid quantification).\nThe expansion of the operator `\\cdot` has been activated with the `ExpandCdot` proof directive from the module `TLAPS`.\nThe operator `A` is defined at: \n\t<unknown location>\nand the operator `A` occurs at: \n\t<unknown location>\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF A` is expected to avoid this error.\n"]),
    ("lambdify", "e-a", "((flex x) (def A (app Prime 1)))", "(app ENABLED (app Cdot 1 1))", "ERR TlaProverError|Expr.Action", &["stderr: <unknown location>:\nError: Nested occurrence of the operator `\\cdot` found in scope of `ENABLED` when expanding `ENABLED`. Using the proof directive `ExpandCdot` from the module `TLAPS` is expected to avoid this error.For example, writing `BY ExpandCdot`."]),
    ("lambdify", "-ca", "((flex x) (def A (app Prime 1)))", "(app Cdot (app ENABLED 1) 1)", "ERR TlaProverError|Expr.Action", &["stderr: <unknown location>:\nError: Nested occurrence of the operator `ENABLED` found in scope of `\\cdot` when expanding `\\cdot`. Using the proof directive `ExpandENABLED` from the module `TLAPS` is expected to avoid this error.For example, writing `BY ExpandENABLED`."]),
    ("lambdify", "default", "((flex x) (hdef F (lam (p) (and (app Prime 2) 1))))", "(app ENABLED (app 1 (app Prime 2)))", "(app $EnabledWrapper (lam (r#0) (and 1 1)))", &["stdout: <unknown location>:\n[INFO]: Auto-expanding the definition of operator:  F\n"]),
    ("lambdify", "e--", "((flex x) (hdef F (lam (p) (at 8 (and (app Prime 2) 1)))))", "(at 3 (app ENABLED (at 9 (app 1 (app Prime 2)))))", "ERR TlaProverError|Hidden definition of operator `F` needs expansion for soundly expanding the operator `ENABLED` (using rigid quantification).\nThe expansion of the operator `ENABLED` has been activated with the `ExpandENABLED` proof directive from the module `TLAPS`.\nThe operator `F` is defined at: \n\tFile \"M.tla\", line 8, characters 3-8\nand the operator `F` occurs at: \n\tFile \"M.tla\", line 9, characters 3-8\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF F` is expected to avoid this error.\n", &["stderr: File \"M.tla\", line 9, characters 3-8:\nError: Hidden definition of operator `F` needs expansion for soundly expanding the operator `ENABLED` (using rigid quantification).\nThe expansion of the operator `ENABLED` has been activated with the `ExpandENABLED` proof directive from the module `TLAPS`.\nThe operator `F` is defined at: \n\tFile \"M.tla\", line 8, characters 3-8\nand the operator `F` occurs at: \n\tFile \"M.tla\", line 9, characters 3-8\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF F` is expected to avoid this error.\n"]),
    ("lambdify", "default", "((flex x) (bpragma B (app Prime 1)))", "(app ENABLED 1)", "(app $EnabledWrapper (lam (r#0) 1))", &["stdout: <unknown location>:\n[INFO]: Auto-expanding the definition of operator:  B\n"]),
    ("lambdify", "default", "((flex x) (def S (app Plus 1 1)))", "(app ENABLED (app Eq (app Prime 2) 1))", "(app $EnabledWrapper (lam (r#0) (app Eq 1 2)))", &[]),
    ("lambdify", "default", "((flex x) (def T (app BoxTrue 1)))", "(app ENABLED 1)", "ERR TlaProofError|Oops, this seems to be a bug in TLAPM.|-|Assert_failure", &[]),
    ("lambdify", "default", "((flex x) (recursive R 0))", "(app ENABLED 1)", "ERR TlaProofError|Oops, this seems to be a bug in TLAPM.|-|Assert_failure", &[]),
    ("lambdify", "default", "((flex x) (at 2 (fresh F Unknown 1)))", "(app ENABLED (at 4 (app 1 (app Prime 2))))", "ERR TlaProofError|Oops, this seems to be a bug in TLAPM.|-|File \"src/expr/e_action.ml\", line 367, characters 20-26: Assertion failed", &["stderr: File \"M.tla\", line 4, characters 3-8:\nError: Declared operator `F` has unknown level and occurs within the scope of `ENABLED` or `\\cdot` where soundness requires expanding expressions of level >= 2.\nIf a constant operator is substituted for this operator, then the expression that results from applying this declared operator has expression level 2.\n May need expansion. A declared operator cannot be expanded.\nThe operator `F` is declared at:\nFile \"M.tla\", line 2, characters 3-8\n and has arity: 1"]),
    ("lambdify", "default", "((flex x) (at 2 (fresh G Unknown 0)))", "(app ENABLED 1)", "ERR TlaProofError|Oops, this seems to be a bug in TLAPM.|-|File \"src/expr/e_action.ml\", line 367, characters 20-26: Assertion failed", &["stderr: <unknown location>:\nError: Declared operator `G` has unknown level and occurs within the scope of `ENABLED` or `\\cdot` where soundness requires expanding expressions of level >= 2.\nIf a constant operator is substituted for this operator, then the expression that results from applying this declared operator has expression level 0.\n May need expansion. A declared operator cannot be expanded.\nThe operator `G` is declared at:\nFile \"M.tla\", line 2, characters 3-8\n and has arity: 0"]),
    ("lambdify", "default", "((at 2 (fresh v State 0)))", "(app ENABLED (at 4 (app Prime 1)))", "ERR TlaProofError|The expression that results from applying the declared operator `v` has expression level 1 within the scope of `ENABLED` or `\\cdot` where soundness requires expanding expressions of level >= 1. A declared operator cannot be expanded.\nThe operator `v` is declared at:\nFile \"M.tla\", line 2, characters 3-8\n and has level: 1\n and arity: 0|The expression that results from applying the declared operator `v` has expression level 1 within the scope of `ENABLED` or `\\cdot` where soundness requires expanding expressions of level >= 1. A declared operator cannot be expanded.\nThe operator `v` is declared at:\nFile \"M.tla\", line 2, characters 3-8\n and has level: 1\n and arity: 0|Failure(\"The expression that results from applying the declared operator `v` has expression level 1 within the scope of `ENABLED` or `\\\\cdot` where soundness requires expanding expressions of level >= 1. A declared operator cannot be expanded.\\nThe operator `v` is declared at:\\nFile \\\"M.tla\\\", line 2, characters 3-8\\n and has level: 1\\n and arity: 0\")", &["stderr: <unknown location>:\nError: The expression that results from applying the declared operator `v` has expression level 1 within the scope of `ENABLED` or `\\cdot` where soundness requires expanding expressions of level >= 1. A declared operator cannot be expanded.\nThe operator `v` is declared at:\nFile \"M.tla\", line 2, characters 3-8\n and has level: 1\n and arity: 0"]),
    ("lambdify", "default", "((at 2 (fresh a Action 0)))", "(app ENABLED (at 4 1))", "ERR TlaProofError|The expression that results from applying the declared operator `a` has expression level 2 within the scope of `ENABLED` or `\\cdot` where soundness requires expanding expressions of level >= 2. A declared operator cannot be expanded.\nThe operator `a` is declared at:\nFile \"M.tla\", line 2, characters 3-8\n and has level: 2\n and arity: 0|The expression that results from applying the declared operator `a` has expression level 2 within the scope of `ENABLED` or `\\cdot` where soundness requires expanding expressions of level >= 2. A declared operator cannot be expanded.\nThe operator `a` is declared at:\nFile \"M.tla\", line 2, characters 3-8\n and has level: 2\n and arity: 0|Failure(\"The expression that results from applying the declared operator `a` has expression level 2 within the scope of `ENABLED` or `\\\\cdot` where soundness requires expanding expressions of level >= 2. A declared operator cannot be expanded.\\nThe operator `a` is declared at:\\nFile \\\"M.tla\\\", line 2, characters 3-8\\n and has level: 2\\n and arity: 0\")", &["stderr: File \"M.tla\", line 4, characters 3-8:\nError: The expression that results from applying the declared operator `a` has expression level 2 within the scope of `ENABLED` or `\\cdot` where soundness requires expanding expressions of level >= 2. A declared operator cannot be expanded.\nThe operator `a` is declared at:\nFile \"M.tla\", line 2, characters 3-8\n and has level: 2\n and arity: 0"]),
    ("lambdify", "default", "((fresh k Constant 0))", "(app ENABLED (app Prime 1))", "(app $EnabledWrapper (lam (r#0) 2))", &[]),
    ("lambdify", "default", "((flex x) (fact (app Prime 1)))", "(app ENABLED 1)", "ERR TlaProofError|Oops, this seems to be a bug in TLAPM.|-|Assert_failure", &[]),
    ("lambdify", "default", "((flex x))", "(seq ((flex y) (fact (app Prime 1))) (app ENABLED (app Eq (app Prime 2) 1)))", "ERR TlaProofError|Oops, this seems to be a bug in TLAPM.|-|Assert_failure", &[]),
    ("lambdify", "default", "((flex x))", "(app ENABLED (box (app Prime 1) 1))", "(app $EnabledWrapper (lam (r#0) (app Disj 1 (app Eq 1 2))))", &[]),
    ("lambdify", "default", "((flex x))", "(seq ((flex y) (fresh n Constant 0)) (app ENABLED (app Eq (app Prime 3) 2)))", "(seq ((flex y) (fresh n Constant 0)) (app $EnabledWrapper (lam (r#0) (app Eq 1 3))))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (lam (_ a) (app Eq 1 2)))", "(app $EnabledWrapper (lam (r#0) (app Eq 2 3)))", &[]),
    ("lambdify", "default", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED 1 2)", "ERR TlaProofError|Oops, this seems to be a bug in TLAPM.|-|Assert_failure", &[]),
    ("lambdify", "default", "((flex x))", "(box (app ENABLED (app Prime 1)) 1)", "(box (app $EnabledWrapper (lam (r#0) 1)) 1)", &[]),
    ("lambdify", "default", "((flex v0) (flex v1) (flex v2) (flex v3) (flex v4) (flex v5) (flex v6) (flex v7) (flex v8) (flex v9) (flex v10) (flex v11) (flex v12) (flex v13) (flex v14) (flex v15) (flex v16) (flex v17) (flex v18) (flex v19) (flex v20) (flex v21) (flex v22) (flex v23) (flex v24) (flex v25) (flex v26) (flex v27) (flex v28) (flex v29) (flex v30) (flex v31) (flex v32) (flex v33) (flex v34) (flex v35) (flex v36) (flex v37) (flex v38) (flex v39))", "(app ENABLED (and (app Prime 1) (app Prime 2) (app Prime 3) (app Prime 4) (app Prime 5) (app Prime 6) (app Prime 7) (app Prime 8) (app Prime 9) (app Prime 10) (app Prime 11) (app Prime 12) (app Prime 13) (app Prime 14) (app Prime 15) (app Prime 16) (app Prime 17) (app Prime 18) (app Prime 19) (app Prime 20) (app Prime 21) (app Prime 22) (app Prime 23) (app Prime 24) (app Prime 25) (app Prime 26) (app Prime 27) (app Prime 28) (app Prime 29) (app Prime 30) (app Prime 31) (app Prime 32) (app Prime 33) (app Prime 34) (app Prime 35) (app Prime 36) (app Prime 37) (app Prime 38) (app Prime 39) (app Prime 40)))", "(app $EnabledWrapper (lam (r#0 r#1 r#2 r#3 r#4 r#5 r#6 r#7 r#8 r#9 r#10 r#11 r#12 r#13 r#14 r#15 r#16 r#17 r#18 r#19 r#20 r#21 r#22 r#23 r#24 r#25 r#26 r#27 r#28 r#29 r#30 r#31 r#32 r#33 r#34 r#35 r#36 r#37 r#38 r#39) (and 23 12 32 16 34 35 3 7 30 19 31 33 5 8 36 17 1 24 25 18 15 9 26 37 2 20 11 38 6 40 27 21 28 39 29 10 13 22 4 14)))", &[]),
    ("expand", "e--", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (app Eq (app Prime 2) 1))", "(ex (x#enabled#prime1) (app Eq 1 2))", &[]),
    ("expand", "ec-", "((fresh c Constant 0) (flex x) (flex y))", "(app Cdot (app Eq (app Prime 2) 1) (app Eq (app Prime 1) 2))", "(ex (x#enabled#prime1) (and (app Eq 1 2) (app Eq (app Prime 2) 1)))", &[]),
    ("expand", "-c-", "((fresh c Constant 0) (flex x) (flex y))", "(app Cdot (app Prime 2) (app ENABLED (app Prime 1)))", "ERR TlaProverError|Expr.Action", &["stderr: <unknown location>:\nError: Nested occurrence of the operator `ENABLED` found in scope of `\\cdot` when expanding `\\cdot`. Using the proof directive `ExpandENABLED` from the module `TLAPS` is expected to avoid this error.For example, writing `BY ExpandENABLED`."]),
    ("expand", "e--", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (app Cdot (app Prime 2) 1))", "ERR TlaProverError|Expr.Action", &["stderr: <unknown location>:\nError: Nested occurrence of the operator `\\cdot` found in scope of `ENABLED` when expanding `ENABLED`. Using the proof directive `ExpandCdot` from the module `TLAPS` is expected to avoid this error.For example, writing `BY ExpandCdot`."]),
    ("expand", "-c-", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (app Prime 2))", "ERR TlaProofError|Oops, this seems to be a bug in TLAPM.|-|Assert_failure", &[]),
    ("expand", "e--", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (or (app Prime 2) (app Prime 1) (app Eq 2 1)))", "(or (ex (y#enabled#prime1 x#enabled#prime1) 1) (ex (y#enabled#prime1 x#enabled#prime1) 2) (ex (y#enabled#prime1 x#enabled#prime1) (app Eq 4 3)))", &[]),
    ("expand", "e--", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (app Disj (app Prime 2) (app Disj (app Prime 1) 3)))", "(app Disj (ex (y#enabled#prime1 x#enabled#prime1) 1) (app Disj (ex (y#enabled#prime1 x#enabled#prime1) 2) (ex (y#enabled#prime1 x#enabled#prime1) 5)))", &[]),
    ("expand", "ec-", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (and (app Prime 2) (app Cdot (app Prime 1) 2)))", "(ex (x#enabled#prime1) (and 1 (ex (x#enabled#prime2 y#enabled#prime2) (and 1 2))))", &[]),
    ("expand", "e-a", "((flex x) (def A (app Prime 1)))", "(app ENABLED (app Eq 1 2))", "(ex (x#enabled#prime1) (app Eq 1 3))", &["stdout: <unknown location>:\n[INFO]: Auto-expanding the definition of operator:  A\n"]),
    ("expand", "e--", "((flex x) (def A (app Prime 1)))", "(app ENABLED (app Eq 1 2))", "ERR TlaProverError|Hidden definition of operator `A` needs expansion for soundly expanding the operator `ENABLED` (using rigid quantification).\nThe expansion of the operator `ENABLED` has been activated with the `ExpandENABLED` proof directive from the module `TLAPS`.\nThe operator `A` is defined at: \n\t<unknown location>\nand the operator `A` occurs at: \n\t<unknown location>\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF A` is expected to avoid this error.\n", &["stderr: <unknown location>:\nError: Hidden definition of operator `A` needs expansion for soundly expanding the operator `ENABLED` (using rigid quantification).\nThe expansion of the operator `ENABLED` has been activated with the `ExpandENABLED` proof directive from the module `TLAPS`.\nThe operator `A` is defined at: \n\t<unknown location>\nand the operator `A` occurs at: \n\t<unknown location>\nUsing the proof directive `AutoUSE` from the module `TLAPS`, or `BY DEF A` is expected to avoid this error.\n"]),
    ("expand", "ec-", "((flex x) (def EnabledWrapper TRUE))", "(app 1 (lam (r) (app Eq 2 3)))", "(ex (r) (app Eq 2 3))", &[]),
    ("expand", "ec-", "((flex x) (def Other TRUE))", "(app 1 (lam (r) (app Eq 2 3)))", "(app 1 (lam (r) (app Eq 2 3)))", &[]),
    ("expand", "e--", "((fresh c Constant 0) (flex x) (flex y))", "(app $EnabledWrapper (lam (r) (app Eq 3 1)))", "ERR TlaProofError|Operator \"EnabledWrapper\" not found|Expr.Anon: 4|Failure(\"Expr.Anon: 4\")", &["anon stderr: <unknown location>:\nError: Operator \"EnabledWrapper\" not found"]),
    ("expand", "e--", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (lam (a b) (app Eq 1 2)))", "(ex (a b) (app Eq 1 2))", &[]),
    ("expand", "e--", "((fresh c Constant 0) (flex x) (flex y))", "(app ENABLED (app Prime 3))", "(ex (r#0) 4)", &[]),
    ("expand", "ec-", "((flex x))", "(seq ((flex y) (fact (app ENABLED (app Prime 1)))) (app ENABLED (app Eq (app Prime 2) 1)))", "(seq ((flex y) (fact (ex (y#enabled#prime1) 1))) (ex (y#enabled#prime1) (app Eq 1 2)))", &[]),
    ("expand", "ec-", "((flex v0) (flex v1) (flex v2) (flex v3) (flex v4) (flex v5) (flex v6) (flex v7) (flex v8) (flex v9) (flex v10) (flex v11) (flex v12) (flex v13) (flex v14) (flex v15) (flex v16) (flex v17) (flex v18) (flex v19) (flex v20) (flex v21) (flex v22) (flex v23) (flex v24) (flex v25) (flex v26) (flex v27) (flex v28) (flex v29) (flex v30) (flex v31) (flex v32) (flex v33) (flex v34) (flex v35) (flex v36) (flex v37) (flex v38) (flex v39))", "(app ENABLED (or (app Prime 1) (app Prime 2) (app Prime 3) (app Prime 4) (app Prime 5)))", "(or (ex (v36#enabled#prime1 v38#enabled#prime1 v35#enabled#prime1 v37#enabled#prime1 v39#enabled#prime1) 1) (ex (v36#enabled#prime1 v38#enabled#prime1 v35#enabled#prime1 v37#enabled#prime1 v39#enabled#prime1) 4) (ex (v36#enabled#prime1 v38#enabled#prime1 v35#enabled#prime1 v37#enabled#prime1 v39#enabled#prime1) 2) (ex (v36#enabled#prime1 v38#enabled#prime1 v35#enabled#prime1 v37#enabled#prime1 v39#enabled#prime1) 5) (ex (v36#enabled#prime1 v38#enabled#prime1 v35#enabled#prime1 v37#enabled#prime1 v39#enabled#prime1) 3))", &[]),
    ];
}

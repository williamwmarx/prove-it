//! A port of tlapm's Expr.LevelComparison, the LevelComparison frontend: it proves an obligation
//! whose goal is a visible fact, or the goal of a visible ASSUME/PROVE fact, with identifiers
//! renamed to identifiers of no higher level, each renamed one declared by the fact.
//! A port of `src/prover/prep/level-comparison.ts`.

use std::cmp::Ordering;

use crate::errors::{ObligationError, Result};
use crate::expression::{
    Bound, BoundDomain, Builtin, Defn, DefnCore, ExceptPoint, Expr, ExprCore, Field, Hyp, HypCore,
    InstanceDefinition, Level, Param, ScopeRef, Selector, Sequent, Visibility, adjoin, adjoin_all,
    expr, get_bound_fresh, get_bounded_fresh, get_fresh, get_hyp_name, get_local_defn,
    get_param_fresh, get_scope_at, get_scope_hyps, hyp, to_index,
};
use crate::levels::get_level_info;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DeclarationKind {
    Level(Level),
    Variable,
    Definition,
}

struct Declaration {
    name: String,
    kind: DeclarationKind,
    level: i64,
}

/// `RANKS`.
fn get_rank(kind: DeclarationKind) -> Option<i64> {
    match kind {
        DeclarationKind::Level(Level::Constant) => Some(0),
        DeclarationKind::Level(Level::State) => Some(1),
        DeclarationKind::Level(Level::Action) => Some(2),
        DeclarationKind::Level(Level::Temporal) => Some(3),
        _ => None,
    }
}

// The lists match item by item, and tlapm compares the items before it finds a missing one.
fn is_pairwise<Item>(
    left: &[Item],
    right: &[Item],
    mut is_same_item: impl FnMut(&Item, &Item) -> Result<bool>,
) -> Result<bool> {
    for (index, item) in left.iter().enumerate() {
        let Some(other) = right.get(index) else {
            return Ok(false);
        };
        if !is_same_item(item, other)? {
            return Ok(false);
        }
    }
    Ok(left.len() == right.len())
}

/// JavaScript's `<` on strings, which compares UTF-16 code units.
fn compare_utf16(left: &str, right: &str) -> Ordering {
    left.encode_utf16().cmp(right.encode_utf16())
}

// Util.Coll.Sm built from a list, where the first entry of a name wins, in key order.
fn get_sorted_fields<'a>(
    fields: impl Iterator<Item = (&'a str, &'a Expr)>,
) -> Vec<(&'a str, &'a Expr)> {
    let mut sorted: Vec<(&str, &Expr)> = Vec::new();
    for (name, value) in fields {
        if !sorted.iter().any(|entry| entry.0 == name) {
            sorted.push((name, value));
        }
    }
    sorted.sort_by(|first, second| compare_utf16(first.0, second.0));
    sorted
}

fn get_declaration(scope: &ScopeRef, index: isize) -> Result<Declaration> {
    let hyp_scope = get_scope_at(scope, index - 1).ok_or_else(ObligationError::assert_failure)?;
    match &hyp_scope.hyp.core {
        HypCore::Fresh { name, level, .. } => {
            let kind = DeclarationKind::Level(*level);
            Ok(Declaration {
                name: name.clone(),
                kind,
                level: get_rank(kind).unwrap_or(-1),
            })
        }
        HypCore::Flex { name } => Ok(Declaration {
            name: name.clone(),
            kind: DeclarationKind::Variable,
            level: 1,
        }),
        HypCore::Defn { definition, .. } => match &definition.core {
            DefnCore::Operator { name, body } => {
                let level = get_level_info(&hyp_scope.rest, body)?.level;
                Ok(Declaration {
                    name: name.clone(),
                    kind: DeclarationKind::Definition,
                    level: i64::try_from(level).map_err(|_| ObligationError::assert_failure())?,
                })
            }
            _ => Err(ObligationError::assert_failure()),
        },
        HypCore::Fact { .. } => Err(ObligationError::assert_failure()),
    }
}

fn bind_bounds(scope: &ScopeRef, bounds: &[Bound]) -> ScopeRef {
    adjoin_all(
        scope,
        &bounds.iter().map(get_bound_fresh).collect::<Vec<_>>(),
    )
}

fn bind_params(scope: &ScopeRef, params: &[Param]) -> ScopeRef {
    adjoin_all(
        scope,
        &params.iter().map(get_param_fresh).collect::<Vec<_>>(),
    )
}

fn bind_definitions(scope: &ScopeRef, definitions: &[Defn]) -> ScopeRef {
    let hyps = definitions
        .iter()
        .map(|definition| get_local_defn(definition.clone()))
        .collect::<Vec<_>>();
    adjoin_all(scope, &hyps)
}

fn bind_flexible(scope: &ScopeRef, names: &[String]) -> ScopeRef {
    let hyps = names
        .iter()
        .map(|name| hyp(HypCore::Flex { name: name.clone() }))
        .collect::<Vec<_>>();
    adjoin_all(scope, &hyps)
}

fn bind_args(scope: &ScopeRef, args: &[String]) -> ScopeRef {
    let hyps = args
        .iter()
        .map(|name| get_fresh(name, Level::Unknown, 0))
        .collect::<Vec<_>>();
    adjoin_all(scope, &hyps)
}

fn get_instance_fields(instance: &InstanceDefinition) -> Vec<(&str, &Expr)> {
    get_sorted_fields(
        instance
            .substitutions
            .iter()
            .map(|entry| (entry.name.as_str(), &entry.expression)),
    )
}

fn get_record_fields(fields: &[Field]) -> Vec<(&str, &Expr)> {
    get_sorted_fields(
        fields
            .iter()
            .map(|field| (field.name.as_str(), &field.value)),
    )
}

/// A binder's name, domain and body: CHOOSE's or a set filter's.
struct Binder<'a> {
    name: &'a str,
    domain: Option<&'a Expr>,
    body: &'a Expr,
}

// level_comparison#compare: the expressions match up to a renaming that maps each name one way,
// and the fact's context declares each name it changes.
struct Comparison {
    /// Insertion-ordered, as the TypeScript's `Map`.
    renaming: Vec<(String, String)>,
}

impl Comparison {
    fn is_same_index(
        &mut self,
        left_scope: &ScopeRef,
        right_scope: &ScopeRef,
        left_index: isize,
        right_index: isize,
    ) -> Result<bool> {
        let left = get_declaration(left_scope, left_index)?;
        let right = get_declaration(right_scope, right_index)?;
        if left.kind == DeclarationKind::Level(Level::Unknown) {
            return Ok(left_index == right_index);
        }
        if left.kind == DeclarationKind::Variable || left.kind == DeclarationKind::Definition {
            return Ok(left.name == right.name && right.kind == left.kind);
        }
        let is_lower = get_rank(right.kind).is_some_and(|rank| rank <= left.level)
            || (right.kind == DeclarationKind::Definition && right.level <= left.level);
        if !is_lower {
            return Ok(false);
        }
        if let Some(entry) = self.renaming.iter().find(|entry| entry.0 == left.name) {
            return Ok(entry.1 == right.name);
        }
        self.renaming.push((left.name, right.name));
        Ok(true)
    }

    fn is_same_definition(
        &mut self,
        left_scope: &ScopeRef,
        right_scope: &ScopeRef,
        left: &Defn,
        right: &Defn,
    ) -> Result<bool> {
        match (&left.core, &right.core) {
            (
                DefnCore::Operator {
                    body: left_body, ..
                },
                DefnCore::Operator {
                    body: right_body, ..
                },
            )
            | (
                DefnCore::Bpragma {
                    body: left_body, ..
                },
                DefnCore::Bpragma {
                    body: right_body, ..
                },
            ) => self.is_same(left_scope, right_scope, left_body, right_body),
            (
                DefnCore::Instance {
                    instance: left_instance,
                    ..
                },
                DefnCore::Instance {
                    instance: right_instance,
                    ..
                },
            ) => {
                let left_args = &left_instance.args;
                let right_args = &right_instance.args;
                Ok(is_pairwise(left_args, right_args, |left_arg, right_arg| {
                    Ok(left_arg == right_arg)
                })? && left_instance.module == right_instance.module
                    && self.is_same_fields(
                        &bind_args(left_scope, left_args),
                        &bind_args(right_scope, right_args),
                        &get_instance_fields(left_instance),
                        &get_instance_fields(right_instance),
                    )?)
            }
            _ => Ok(false),
        }
    }

    fn is_same_fields(
        &mut self,
        left_scope: &ScopeRef,
        right_scope: &ScopeRef,
        left: &[(&str, &Expr)],
        right: &[(&str, &Expr)],
    ) -> Result<bool> {
        is_pairwise(left, right, |left_field, right_field| {
            Ok(left_field.0 == right_field.0
                && self.is_same(left_scope, right_scope, left_field.1, right_field.1)?)
        })
    }

    fn is_same_bounds(
        &mut self,
        left_scope: &ScopeRef,
        right_scope: &ScopeRef,
        left: &[Bound],
        right: &[Bound],
    ) -> Result<bool> {
        is_pairwise(left, right, |left_bound, right_bound| {
            if left_bound.level != right_bound.level {
                return Ok(false);
            }
            match (&left_bound.domain, &right_bound.domain) {
                (BoundDomain::Domain(left_domain), BoundDomain::Domain(right_domain)) => {
                    self.is_same(left_scope, right_scope, left_domain, right_domain)
                }
                (BoundDomain::NoDomain, BoundDomain::NoDomain)
                | (BoundDomain::Ditto, BoundDomain::Ditto) => Ok(true),
                _ => Ok(false),
            }
        })
    }

    fn is_same_hyp(
        &mut self,
        left_scope: &ScopeRef,
        right_scope: &ScopeRef,
        left: &Hyp,
        right: &Hyp,
    ) -> Result<bool> {
        match (&left.core, &right.core) {
            (
                HypCore::Fresh {
                    level: left_level,
                    shape: left_shape,
                    domain: left_domain,
                    ..
                },
                HypCore::Fresh {
                    level: right_level,
                    shape: right_shape,
                    domain: right_domain,
                    ..
                },
            ) => {
                if left_level != right_level || left_shape != right_shape {
                    return Ok(false);
                }
                match (left_domain, right_domain) {
                    (Some(left_domain), Some(right_domain)) => {
                        self.is_same(left_scope, right_scope, left_domain, right_domain)
                    }
                    _ => Ok(left_domain.is_none() && right_domain.is_none()),
                }
            }
            (HypCore::Flex { .. }, HypCore::Flex { .. }) => Ok(true),
            (
                HypCore::Defn {
                    definition: left_definition,
                    is_local: left_is_local,
                    ..
                },
                HypCore::Defn {
                    definition: right_definition,
                    is_local: right_is_local,
                    ..
                },
            ) => Ok(self.is_same_definition(
                left_scope,
                right_scope,
                left_definition,
                right_definition,
            )? && left_is_local == right_is_local),
            (
                HypCore::Fact {
                    expression: left_expression,
                    ..
                },
                HypCore::Fact {
                    expression: right_expression,
                    ..
                },
            ) => self.is_same(left_scope, right_scope, left_expression, right_expression),
            _ => Ok(false),
        }
    }

    fn is_same_context(
        &mut self,
        left_scope: &ScopeRef,
        right_scope: &ScopeRef,
        left: &[Hyp],
        right: &[Hyp],
    ) -> Result<bool> {
        let (Some((left_first, left_rest)), Some((right_first, right_rest))) =
            (left.split_first(), right.split_first())
        else {
            return Ok(left.len() == right.len());
        };
        Ok(
            self.is_same_hyp(left_scope, right_scope, left_first, right_first)?
                && self.is_same_context(
                    &adjoin(left_scope, left_first),
                    &adjoin(right_scope, right_first),
                    left_rest,
                    right_rest,
                )?,
        )
    }

    fn is_same_binder(
        &mut self,
        left_scope: &ScopeRef,
        right_scope: &ScopeRef,
        left: &Binder,
        right: &Binder,
    ) -> Result<bool> {
        let (Some(left_domain), Some(right_domain)) = (left.domain, right.domain) else {
            return Ok(left.domain.is_none()
                && right.domain.is_none()
                && self.is_same(
                    &adjoin(left_scope, &get_fresh(left.name, Level::Constant, 0)),
                    &adjoin(right_scope, &get_fresh(right.name, Level::Constant, 0)),
                    left.body,
                    right.body,
                )?);
        };
        Ok(
            self.is_same(left_scope, right_scope, left_domain, right_domain)?
                && self.is_same(
                    &adjoin(
                        left_scope,
                        &get_bounded_fresh(left.name, left_domain.clone()),
                    ),
                    &adjoin(
                        right_scope,
                        &get_bounded_fresh(right.name, right_domain.clone()),
                    ),
                    left.body,
                    right.body,
                )?,
        )
    }

    fn is_same_list(
        &mut self,
        left_scope: &ScopeRef,
        right_scope: &ScopeRef,
        left: &[Expr],
        right: &[Expr],
    ) -> Result<bool> {
        is_pairwise(left, right, |left_inner, right_inner| {
            self.is_same(left_scope, right_scope, left_inner, right_inner)
        })
    }

    fn is_same_selectors(
        &mut self,
        left_scope: &ScopeRef,
        right_scope: &ScopeRef,
        left: &[Selector],
        right: &[Selector],
    ) -> Result<bool> {
        for (index, selector) in left.iter().enumerate() {
            let Some(other) = right.get(index) else {
                continue;
            };
            let is_same = match (selector, other) {
                (Selector::Number(value), Selector::Number(other_value)) => value == other_value,
                (Selector::Instance(args), Selector::Instance(other_args)) => {
                    self.is_same_list(left_scope, right_scope, args, other_args)?
                }
                (
                    Selector::Label { label, args },
                    Selector::Label {
                        label: other_label,
                        args: other_args,
                    },
                ) => {
                    label == other_label
                        && self.is_same_list(left_scope, right_scope, args, other_args)?
                }
                _ => std::mem::discriminant(selector) == std::mem::discriminant(other),
            };
            if !is_same {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn is_same(
        &mut self,
        left_scope: &ScopeRef,
        right_scope: &ScopeRef,
        left: &Expr,
        right: &Expr,
    ) -> Result<bool> {
        if let ExprCore::Parens { expression, .. } = &left.core {
            return self.is_same(left_scope, right_scope, expression, right);
        }
        if let ExprCore::Parens { expression, .. } = &right.core {
            return self.is_same(left_scope, right_scope, left, expression);
        }
        Ok(match (&left.core, &right.core) {
            (ExprCore::Ix { index: left_index }, ExprCore::Ix { index: right_index }) => {
                self.is_same_index(left_scope, right_scope, *left_index, *right_index)?
            }
            (ExprCore::Opaque { name: left_name }, ExprCore::Opaque { name: right_name }) => {
                left_name == right_name
            }
            (
                ExprCore::Internal {
                    builtin: left_builtin,
                },
                ExprCore::Internal {
                    builtin: right_builtin,
                },
            ) => left_builtin == right_builtin,
            (
                ExprCore::Lambda {
                    params: left_params,
                    body: left_body,
                },
                ExprCore::Lambda {
                    params: right_params,
                    body: right_body,
                },
            ) => {
                left_params.len() == right_params.len()
                    && self.is_same(
                        &bind_params(left_scope, left_params),
                        &bind_params(right_scope, right_params),
                        left_body,
                        right_body,
                    )?
            }
            (
                ExprCore::Apply {
                    operator: left_operator,
                    args: left_args,
                },
                ExprCore::Apply {
                    operator: right_operator,
                    args: right_args,
                },
            ) => {
                self.is_same(left_scope, right_scope, left_operator, right_operator)?
                    && self.is_same_list(left_scope, right_scope, left_args, right_args)?
            }
            (
                ExprCore::Sequent {
                    sequent: left_sequent,
                },
                ExprCore::Sequent {
                    sequent: right_sequent,
                },
            ) => {
                self.is_same_context(
                    left_scope,
                    right_scope,
                    &left_sequent.context,
                    &right_sequent.context,
                )? && self.is_same(
                    &adjoin_all(left_scope, &left_sequent.context),
                    &adjoin_all(right_scope, &right_sequent.context),
                    &left_sequent.active,
                    &right_sequent.active,
                )?
            }
            (
                ExprCore::Bang {
                    expression: left_expression,
                    selectors: left_selectors,
                },
                ExprCore::Bang {
                    expression: right_expression,
                    selectors: right_selectors,
                },
            ) => {
                if !self.is_same(left_scope, right_scope, left_expression, right_expression)? {
                    return Ok(false);
                }
                let is_prefix = self.is_same_selectors(
                    left_scope,
                    right_scope,
                    left_selectors,
                    right_selectors,
                )?;
                // List.for_all2 raises when the lists differ in length after a matching prefix.
                if is_prefix && left_selectors.len() != right_selectors.len() {
                    return Err(ObligationError::bug("Invalid_argument"));
                }
                is_prefix
            }
            (
                ExprCore::With {
                    expression: left_expression,
                    ..
                },
                ExprCore::With {
                    expression: right_expression,
                    ..
                },
            ) => self.is_same(left_scope, right_scope, left_expression, right_expression)?,
            (
                ExprCore::Let {
                    definitions: left_definitions,
                    body: left_body,
                },
                ExprCore::Let {
                    definitions: right_definitions,
                    body: right_body,
                },
            ) => {
                is_pairwise(
                    left_definitions,
                    right_definitions,
                    |left_definition, right_definition| {
                        self.is_same_definition(
                            left_scope,
                            right_scope,
                            left_definition,
                            right_definition,
                        )
                    },
                )? && self.is_same(
                    &bind_definitions(left_scope, left_definitions),
                    &bind_definitions(right_scope, right_definitions),
                    left_body,
                    right_body,
                )?
            }
            (
                ExprCore::If {
                    condition: left_condition,
                    consequent: left_consequent,
                    alternative: left_alternative,
                },
                ExprCore::If {
                    condition: right_condition,
                    consequent: right_consequent,
                    alternative: right_alternative,
                },
            ) => {
                self.is_same(left_scope, right_scope, left_condition, right_condition)?
                    && self.is_same(left_scope, right_scope, left_consequent, right_consequent)?
                    && self.is_same(left_scope, right_scope, left_alternative, right_alternative)?
            }
            (
                ExprCore::List {
                    bullet: left_bullet,
                    items: left_items,
                },
                ExprCore::List {
                    bullet: right_bullet,
                    items: right_items,
                },
            ) => {
                left_bullet == right_bullet
                    && self.is_same_list(left_scope, right_scope, left_items, right_items)?
            }
            // tlapm binds the goal's bound names as the fact's.
            (
                ExprCore::Quant {
                    quantifier: left_quantifier,
                    bounds: left_bounds,
                    body: left_body,
                },
                ExprCore::Quant {
                    quantifier: right_quantifier,
                    bounds: right_bounds,
                    body: right_body,
                },
            ) => {
                left_quantifier == right_quantifier
                    && self.is_same_bounds(left_scope, right_scope, left_bounds, right_bounds)?
                    && self.is_same(
                        &bind_bounds(left_scope, left_bounds),
                        &bind_bounds(right_scope, left_bounds),
                        left_body,
                        right_body,
                    )?
            }
            (
                ExprCore::Tquant {
                    quantifier: left_quantifier,
                    names: left_names,
                    body: left_body,
                },
                ExprCore::Tquant {
                    quantifier: right_quantifier,
                    names: right_names,
                    body: right_body,
                },
            ) => {
                left_quantifier == right_quantifier
                    && is_pairwise(left_names, right_names, |left_name, right_name| {
                        Ok(left_name == right_name)
                    })?
                    && self.is_same(
                        &bind_flexible(left_scope, left_names),
                        &bind_flexible(right_scope, right_names),
                        left_body,
                        right_body,
                    )?
            }
            (
                ExprCore::Choose {
                    name: left_name,
                    domain: left_domain,
                    body: left_body,
                },
                ExprCore::Choose {
                    name: right_name,
                    domain: right_domain,
                    body: right_body,
                },
            ) => self.is_same_binder(
                left_scope,
                right_scope,
                &Binder {
                    name: left_name,
                    domain: left_domain.as_ref(),
                    body: left_body,
                },
                &Binder {
                    name: right_name,
                    domain: right_domain.as_ref(),
                    body: right_body,
                },
            )?,
            (
                ExprCore::SetSt {
                    name: left_name,
                    domain: left_domain,
                    body: left_body,
                },
                ExprCore::SetSt {
                    name: right_name,
                    domain: right_domain,
                    body: right_body,
                },
            ) => self.is_same_binder(
                left_scope,
                right_scope,
                &Binder {
                    name: left_name,
                    domain: Some(left_domain),
                    body: left_body,
                },
                &Binder {
                    name: right_name,
                    domain: Some(right_domain),
                    body: right_body,
                },
            )?,
            (
                ExprCore::SetOf {
                    element: left_element,
                    bounds: left_bounds,
                },
                ExprCore::SetOf {
                    element: right_element,
                    bounds: right_bounds,
                },
            ) => {
                self.is_same(
                    &bind_bounds(left_scope, left_bounds),
                    &bind_bounds(right_scope, right_bounds),
                    left_element,
                    right_element,
                )? && self.is_same_bounds(left_scope, right_scope, left_bounds, right_bounds)?
            }
            (
                ExprCore::SetEnum {
                    elements: left_elements,
                },
                ExprCore::SetEnum {
                    elements: right_elements,
                },
            )
            | (
                ExprCore::Tuple {
                    elements: left_elements,
                },
                ExprCore::Tuple {
                    elements: right_elements,
                },
            )
            | (
                ExprCore::Product {
                    factors: left_elements,
                },
                ExprCore::Product {
                    factors: right_elements,
                },
            ) => self.is_same_list(left_scope, right_scope, left_elements, right_elements)?,
            (
                ExprCore::Arrow {
                    domain: left_domain,
                    range: left_range,
                },
                ExprCore::Arrow {
                    domain: right_domain,
                    range: right_range,
                },
            ) => {
                self.is_same(left_scope, right_scope, left_domain, right_domain)?
                    && self.is_same(left_scope, right_scope, left_range, right_range)?
            }
            (
                ExprCore::Fcn {
                    bounds: left_bounds,
                    body: left_body,
                },
                ExprCore::Fcn {
                    bounds: right_bounds,
                    body: right_body,
                },
            ) => {
                self.is_same_bounds(left_scope, right_scope, left_bounds, right_bounds)?
                    && self.is_same(
                        &bind_bounds(left_scope, left_bounds),
                        &bind_bounds(right_scope, right_bounds),
                        left_body,
                        right_body,
                    )?
            }
            (
                ExprCore::FcnApp {
                    function: left_function,
                    args: left_args,
                },
                ExprCore::FcnApp {
                    function: right_function,
                    args: right_args,
                },
            ) => {
                let left_items = std::iter::once(left_function.clone())
                    .chain(left_args.iter().cloned())
                    .collect::<Vec<_>>();
                let right_items = std::iter::once(right_function.clone())
                    .chain(right_args.iter().cloned())
                    .collect::<Vec<_>>();
                self.is_same_list(left_scope, right_scope, &left_items, &right_items)?
            }
            (
                ExprCore::Rect {
                    fields: left_fields,
                },
                ExprCore::Rect {
                    fields: right_fields,
                },
            )
            | (
                ExprCore::Record {
                    fields: left_fields,
                },
                ExprCore::Record {
                    fields: right_fields,
                },
            ) => self.is_same_fields(
                left_scope,
                right_scope,
                &get_record_fields(left_fields),
                &get_record_fields(right_fields),
            )?,
            (
                ExprCore::Except {
                    function: left_function,
                    specs: left_specs,
                },
                ExprCore::Except {
                    function: right_function,
                    specs: right_specs,
                },
            ) => {
                self.is_same(left_scope, right_scope, left_function, right_function)?
                    && is_pairwise(left_specs, right_specs, |left_spec, right_spec| {
                        Ok(is_pairwise(
                            &left_spec.trail,
                            &right_spec.trail,
                            |left_point, right_point| match (left_point, right_point) {
                                (ExceptPoint::Dot(left_field), ExceptPoint::Dot(right_field)) => {
                                    Ok(left_field == right_field)
                                }
                                (
                                    ExceptPoint::Apply(left_expression),
                                    ExceptPoint::Apply(right_expression),
                                ) => self.is_same(
                                    left_scope,
                                    right_scope,
                                    left_expression,
                                    right_expression,
                                ),
                                _ => Ok(false),
                            },
                        )? && self.is_same(
                            left_scope,
                            right_scope,
                            &left_spec.value,
                            &right_spec.value,
                        )?)
                    })?
            }
            (
                ExprCore::Dot {
                    expression: left_expression,
                    field: left_field,
                },
                ExprCore::Dot {
                    expression: right_expression,
                    field: right_field,
                },
            ) => {
                self.is_same(left_scope, right_scope, left_expression, right_expression)?
                    && left_field == right_field
            }
            (
                ExprCore::Sub {
                    modal: left_modal,
                    action: left_action,
                    subscript: left_subscript,
                },
                ExprCore::Sub {
                    modal: right_modal,
                    action: right_action,
                    subscript: right_subscript,
                },
            )
            | (
                ExprCore::Tsub {
                    modal: left_modal,
                    action: left_action,
                    subscript: left_subscript,
                },
                ExprCore::Tsub {
                    modal: right_modal,
                    action: right_action,
                    subscript: right_subscript,
                },
            ) => {
                left_modal == right_modal
                    && self.is_same(left_scope, right_scope, left_action, right_action)?
                    && self.is_same(left_scope, right_scope, left_subscript, right_subscript)?
            }
            (
                ExprCore::Fair {
                    fairness: left_fairness,
                    subscript: left_subscript,
                    action: left_action,
                },
                ExprCore::Fair {
                    fairness: right_fairness,
                    subscript: right_subscript,
                    action: right_action,
                },
            ) => {
                left_fairness == right_fairness
                    && self.is_same(left_scope, right_scope, left_subscript, right_subscript)?
                    && self.is_same(left_scope, right_scope, left_action, right_action)?
            }
            // Like E_eq, tlapm compares only the first arms.
            (
                ExprCore::Case {
                    arms: left_arms,
                    other: left_other,
                },
                ExprCore::Case {
                    arms: right_arms,
                    other: right_other,
                },
            ) => {
                let is_same_arm = match (left_arms.first(), right_arms.first()) {
                    (Some(left_arm), Some(right_arm)) => {
                        self.is_same(
                            left_scope,
                            right_scope,
                            &left_arm.condition,
                            &right_arm.condition,
                        )? && self.is_same(
                            left_scope,
                            right_scope,
                            &left_arm.body,
                            &right_arm.body,
                        )?
                    }
                    (left_arm, right_arm) => left_arm.is_none() && right_arm.is_none(),
                };
                if !is_same_arm {
                    return Ok(false);
                }
                match (left_other, right_other) {
                    (Some(left_other), Some(right_other)) => {
                        self.is_same(left_scope, right_scope, left_other, right_other)?
                    }
                    _ => left_other.is_none() && right_other.is_none(),
                }
            }
            (ExprCore::String { value: left_value }, ExprCore::String { value: right_value }) => {
                left_value == right_value
            }
            (
                ExprCore::Num {
                    integer: left_integer,
                    fraction: left_fraction,
                },
                ExprCore::Num {
                    integer: right_integer,
                    fraction: right_fraction,
                },
            ) => left_integer == right_integer && left_fraction == right_fraction,
            (
                ExprCore::At {
                    is_except: left_is_except,
                },
                ExprCore::At {
                    is_except: right_is_except,
                },
            ) => left_is_except == right_is_except,
            _ => false,
        })
    }
}

fn compare(fact_scope: &ScopeRef, goal_scope: &ScopeRef, fact: &Expr, goal: &Expr) -> Result<bool> {
    let mut comparison = Comparison {
        renaming: Vec::new(),
    };
    let is_match = comparison.is_same(fact_scope, goal_scope, fact, goal)?;
    let fact_hyps = get_scope_hyps(fact_scope);
    let mut is_declared = true;
    for entry in &comparison.renaming {
        if entry.0 == entry.1 {
            continue;
        }
        let mut is_found = false;
        for hyp in &fact_hyps {
            match &hyp.core {
                HypCore::Fact { .. } => continue,
                HypCore::Defn { definition, .. }
                    if !matches!(definition.core, DefnCore::Operator { .. }) =>
                {
                    return Err(ObligationError::assert_failure());
                }
                _ => is_found = is_found || get_hyp_name(hyp) == Some(entry.0.as_str()),
            }
        }
        is_declared = is_declared && is_found;
    }
    Ok(is_match && is_declared)
}

/// check_level_change: the first visible fact that matches proves the goal, which becomes TRUE.
/// When none does, tlapm records the obligation as not tried.
pub fn check_level_change(sequent: &Sequent) -> Result<Sequent> {
    let goal_scope = adjoin_all(&None, &sequent.context);
    let mut is_proved = false;
    for (index, hyp) in sequent.context.iter().enumerate() {
        let HypCore::Fact {
            expression: fact,
            visibility: Visibility::Visible,
            ..
        } = &hyp.core
        else {
            continue;
        };
        let fact_scope = get_scope_at(&goal_scope, to_index(sequent.context.len() - index));
        let is_match = match &fact.core {
            ExprCore::Sequent { sequent: inner } => compare(
                &adjoin_all(&fact_scope, &inner.context),
                &goal_scope,
                &inner.active,
                &sequent.active,
            )?,
            _ => compare(&fact_scope, &goal_scope, fact, &sequent.active)?,
        };
        if is_match {
            is_proved = true;
            break;
        }
    }
    if !is_proved {
        return Err(ObligationError::prover(
            "LevelComparison proof directive did not succeed.\n",
        ));
    }
    Ok(Sequent {
        context: sequent.context.clone(),
        active: expr(ExprCore::Internal {
            builtin: Builtin::TRUE,
        }),
    })
}

#[cfg(test)]
mod tests {
    use crate::prep::fingerprint::tests::check_cases;

    /// Each case: the outcomes `level-comparison.ts` (and the other Prep modules) give, then the
    /// sequent, as the TypeScript prints them under Bun.
    const CASES: &str = r##"
{"fp":"ffb3293bedffa059cebbcdcf5f20a7fc","lc":"ok","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"c","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Flex","name":"v"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":2}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":3}]}}
{"fp":"862d73914e437f63bc7198c0e9b2096c","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"c","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Flex","name":"v"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":2}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":2}]}}
{"fp":"5eb7c811add1ad02496ab71ea6ce23b9","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"c","shape":0,"level":"State","domainVisibility":"Visible"},{"kind":"Flex","name":"v"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":2}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":2}]}}
{"fp":"930f3cd8a8f6e6e9a4f6df7f5993aca3","lc":"ok","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"c","shape":0,"level":"State","domainVisibility":"Visible"},{"kind":"Fresh","name":"d","shape":0,"level":"State","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":3}]}}
{"fp":"e9afcf1153dcf0e8d5c355ce30db4fd3","lc":"ok","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"c","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"x","shape":0,"level":"State","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":2}]}}
{"fp":"9713b4bedbae8c5dfa3b5c37d169d099","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"c","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"x","shape":0,"level":"Unknown","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":2}]}}
{"fp":"58570972cedcc419912e06b576e41843","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"c","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Opaque","name":"a"},"visibility":"Hidden","time":"Now"}],"active":{"kind":"Opaque","name":"a"}}
{"fp":"ac54eb01f2add052150f67002afeec94","lc":"ok","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"D","body":{"kind":"Opaque","name":"a"}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Fresh","name":"c","shape":0,"level":"Action","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":1}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Ix","index":3},"args":[{"kind":"Ix","index":3}]}}
{"fp":"2abd48ba6cb9003ec3271068199c48ad","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"D","body":{"kind":"Opaque","name":"a"}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Fresh","name":"c","shape":0,"level":"Action","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":1}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":3}]}}
{"fp":"a16c3f0ec09434e7f39f90807336ac23","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"D","body":{"kind":"Opaque","name":"a"},"methods":[]},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Fresh","name":"c","shape":0,"level":"Action","domainVisibility":"Visible"},{"kind":"Fresh","name":"d","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Ix","index":2},"visibility":"Visible","time":"Now"}],"active":{"kind":"Ix","index":1}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Invalid_argument","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"c","shape":0,"level":"Temporal","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Bang","expression":{"kind":"Ix","index":1},"selectors":[{"kind":"Number","value":1}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Bang","expression":{"kind":"Ix","index":2},"selectors":[{"kind":"Number","value":1},{"kind":"Down"}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"c","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Bang","expression":{"kind":"Ix","index":1},"selectors":[{"kind":"Number","value":1}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Bang","expression":{"kind":"Ix","index":2},"selectors":[{"kind":"Number","value":2},{"kind":"Down"}]}}
{"fp":"2e85ef4e67a9ae94c6a5fd87a1a3e2c3","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}},"visibility":"Visible","time":"Now"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"y","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}}
{"fp":"4a2c2e663cf8f78211ad48f4271a91c6","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Record","fields":[{"name":"b","value":{"kind":"Ix","index":1}},{"name":"a","value":{"kind":"Ix","index":1}},{"name":"a","value":{"kind":"Opaque","name":"z"}}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Record","fields":[{"name":"a","value":{"kind":"Ix","index":1}},{"name":"b","value":{"kind":"Ix","index":1}}]}}
{"fp":"3119501611445b5e7ba928931cab1d07","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Record","fields":[{"name":"é","value":{"kind":"Ix","index":1}},{"name":"😀","value":{"kind":"Ix","index":1}},{"name":"￿","value":{"kind":"Ix","index":1}}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Record","fields":[{"name":"￿","value":{"kind":"Ix","index":1}},{"name":"😀","value":{"kind":"Ix","index":1}},{"name":"é","value":{"kind":"Ix","index":1}}]}}
{"fp":"012a111fdb96ad8e6c36debdf3b50d9a","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Case","arms":[{"condition":{"kind":"Ix","index":1},"body":{"kind":"Ix","index":1}},{"condition":{"kind":"Ix","index":1},"body":{"kind":"Ix","index":1}}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Case","arms":[{"condition":{"kind":"Ix","index":1},"body":{"kind":"Ix","index":1}}]}}
{"fp":"f02226a07f075b370e50b76c31eacc75","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Choose","name":"c","domain":{"kind":"Ix","index":1},"body":{"kind":"Ix","index":1}},"visibility":"Visible","time":"Now"}],"active":{"kind":"Choose","name":"d","domain":{"kind":"Ix","index":1},"body":{"kind":"Ix","index":1}}}
{"fp":"2bfb5df6ef8705333aa32d6fa4170e5c","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Choose","name":"c","domain":{"kind":"Ix","index":1},"body":{"kind":"Ix","index":1}},"visibility":"Visible","time":"Now"}],"active":{"kind":"Choose","name":"d","body":{"kind":"Ix","index":1}}}
{"fp":"7bcc9776a77816274c5a44fedb85f679","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Let","definitions":[{"kind":"Operator","name":"L","body":{"kind":"Ix","index":1}}],"body":{"kind":"Ix","index":1}},"visibility":"Visible","time":"Now"}],"active":{"kind":"Let","definitions":[{"kind":"Operator","name":"L","body":{"kind":"Ix","index":1}}],"body":{"kind":"Ix","index":1}}}
{"fp":"57d12240e88756f4382334d30c7d0d32","lc":"ok","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Tquant","quantifier":"Forall","names":["v"],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}},"visibility":"Visible","time":"Now"}],"active":{"kind":"Tquant","quantifier":"Forall","names":["v"],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}}}
{"fp":"e4f8045292a0659439d17fd87b71106f","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Except","function":{"kind":"Ix","index":1},"specs":[{"trail":[{"kind":"Dot","field":"a"}],"value":{"kind":"Ix","index":1}}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Except","function":{"kind":"Ix","index":1},"specs":[{"trail":[{"kind":"Dot","field":"a"}],"value":{"kind":"Ix","index":1}}]}}
{"fp":"5c531b3c71201d28d63fdd2deb83995e","lc":"ok","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Lambda","params":[{"name":"p","shape":0}],"body":{"kind":"Ix","index":1}},"visibility":"Visible","time":"Now"}],"active":{"kind":"Lambda","params":[{"name":"q","shape":0}],"body":{"kind":"Ix","index":1}}}
{"fp":"9f48f2aa863b177f7fc0f196c93e6e9a","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"Q","body":{"kind":"Ix","index":1}},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Ix","index":1}}},"visibility":"Visible","time":"Now"}],"active":{"kind":"Ix","index":1}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Defn","definition":{"kind":"Instance","name":"I","instance":{"args":[],"module":"M","substitutions":[]}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Fresh","name":"T","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Ix","index":3},"visibility":"Visible","time":"Now"}],"active":{"kind":"Ix","index":2}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fact","expression":{"kind":"Ix","index":0},"visibility":"Visible","time":"Now"}],"active":{"kind":"Ix","index":0}}
{"fp":"32e75b71917693cd0b0d96630c6b2103","lc":"ok","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"F","body":{"kind":"Lambda","params":[{"name":"a","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Num","integer":"2","fraction":""}]},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":3}]},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":4}]},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":5},{"kind":"Ix","index":5}]},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":7},{"kind":"Ix","index":7}]}}
{"fp":"359556c4fa6ea4147627e472bd4a0c8d","lc":"ok","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
{"fp":"359556c4fa6ea4147627e472bd4a0c8d","lc":"ok","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
"##;

    #[test]
    fn matches_the_typescript() {
        assert_eq!(check_cases(CASES), 28);
    }
}

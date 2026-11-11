//! The copies an INSTANCE makes of the definitions of the module it instantiates, as
//! `src/instances.ts` makes them: each with the instance's substitutions put in for the module's
//! declarations, its parameters added, and the names it binds renamed where a substitution would
//! capture them. Under ENABLED, a copy primes the variables of a step as the instance's variables
//! renamed, as TLC evaluates ENABLED through an instance.

use std::cell::RefCell;
use std::rc::Rc;

use crate::ast::*;
use crate::errors::SyntaxError;
use crate::hash::{FastMap, FastSet};
use crate::ordered_map::OrderedMap;
use crate::resolve::{Result, Tables, get_arity, get_bound_names, get_pattern_names, is_before};

/// A node like `expression`, with another kind, keeping what resolution wrote on it.
pub fn rebuild(expression: &Expression, kind: ExpressionKind) -> Expr {
    Rc::new(Expression {
        kind,
        location: expression.location.clone(),
        resolved: expression.resolved.clone(),
    })
}

/// A copy of a name, an `Identifier`, `Apply` or `OperatorReference`, that names `name`, as
/// spreading the TypeScript node with a new `name` or `operator` makes it.
pub fn with_reference(expression: &Expression, name: Name, args: Option<Vec<Expr>>) -> Expr {
    let kind = match (&expression.kind, args) {
        (ExpressionKind::Apply { .. }, Some(args)) => replace_args(&expression.kind, args),
        _ => expression.kind.clone(),
    };
    let copy = rebuild(expression, kind);
    *copy.resolved.key.borrow_mut() = Some(name);
    copy
}

pub fn replace_args(kind: &ExpressionKind, new_args: Vec<Expr>) -> ExpressionKind {
    match kind {
        ExpressionKind::Apply {
            operator,
            spelling,
            argument_counts,
            arguments_range,
            selector_ranges,
            argument_ranges,
            ..
        } => ExpressionKind::Apply {
            operator: operator.clone(),
            spelling: spelling.clone(),
            args: new_args,
            argument_counts: argument_counts.clone(),
            arguments_range: arguments_range.clone(),
            selector_ranges: selector_ranges.clone(),
            argument_ranges: argument_ranges.clone(),
        },
        other => other.clone(),
    }
}

pub fn identifier(name: Name, location: &Location) -> Expr {
    Rc::new(Expression::new(
        ExpressionKind::Identifier {
            name,
            spelling: None,
            selector_ranges: None,
        },
        location.clone(),
    ))
}

pub fn apply(operator: Name, args: Vec<Expr>, location: &Location) -> Expr {
    Rc::new(Expression::new(
        ExpressionKind::Apply {
            operator,
            spelling: None,
            args,
            argument_counts: None,
            arguments_range: None,
            selector_ranges: None,
            argument_ranges: None,
        },
        location.clone(),
    ))
}

/// `createLocalIdentifier`.
pub fn local_identifier(name: Name, location: &Location) -> Expr {
    let expression = identifier(name, location);
    expression.resolved.is_local.set(true);
    expression
}

/// `createLocalArguments`.
pub fn local_arguments(params: &[OperatorParam], location: &Location) -> Vec<Expr> {
    params
        .iter()
        .map(|param| local_identifier(param.name.clone(), location))
        .collect()
}

pub fn param(name: Name, arity: usize) -> OperatorParam {
    OperatorParam {
        name,
        arity,
        location: None,
    }
}

/// An operator definition the front end makes, as an object literal in TypeScript.
pub fn operator_definition(
    name: Name,
    params: Vec<OperatorParam>,
    body: Expr,
    is_local: bool,
    location: &Location,
) -> Definition {
    Definition {
        name,
        kind: DefinitionKind::Operator {
            params,
            body_range: None,
        },
        body,
        is_local,
        is_recursive: false,
        location: location.clone(),
        is_self_referential: Default::default(),
    }
}

pub fn let_expression(definitions: Vec<Rc<Definition>>, body: Expr, location: &Location) -> Expr {
    Rc::new(Expression::new(
        ExpressionKind::Let {
            definitions,
            instances: None,
            recursive: Vec::new(),
            body,
        },
        location.clone(),
    ))
}

/// `renameLocals`: renames the names bound outside `expression` that it refers to.
pub fn rename_locals(
    expression: &Expr,
    names: &FastMap<Name, Name>,
    bound: &FastSet<Name>,
    tables: &Tables,
) -> Expr {
    let mapped = map_children(expression, tables, &mut |child, child_bound| {
        Ok(if child_bound.is_empty() {
            rename_locals(child, names, bound, tables)
        } else {
            let mut inner = bound.clone();
            inner.extend(child_bound.iter().cloned());
            rename_locals(child, names, &inner, tables)
        })
    })
    .unwrap_or_else(|_| expression.clone());
    match &mapped.kind {
        ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. }
            if mapped.is_locally_resolved() =>
        {
            let name = mapped.reference().unwrap_or_default();
            if bound.contains(&name) {
                return mapped;
            }
            let renamed = names.get(&name).cloned().unwrap_or(name);
            with_reference(&mapped, renamed, None)
        }
        _ => mapped,
    }
}

type Map<'a> = dyn FnMut(&Expr, &[Name]) -> Result<Expr> + 'a;

fn map_bounds(bounds: &[Bound], map: &mut Map) -> Result<Vec<Bound>> {
    bounds
        .iter()
        .map(|bound| {
            Ok(Bound {
                pattern: bound.pattern.clone(),
                set: map(&bound.set, &[])?,
            })
        })
        .collect()
}

/// `mapDefinition`: a copy of a definition with its body, and a function's bounds, mapped.
pub fn map_definition(
    definition: &Rc<Definition>,
    tables: &Tables,
    map: &mut Map,
) -> Result<Rc<Definition>> {
    let mapped = match &definition.kind {
        DefinitionKind::Function { bounds } => {
            let bounds = map_bounds(bounds, map)?;
            let body = map(&definition.body, &get_bound_names(&bounds))?;
            Definition {
                kind: DefinitionKind::Function { bounds },
                body,
                ..(**definition).clone()
            }
        }
        DefinitionKind::Operator { params, .. } => {
            let names: Vec<Name> = params.iter().map(|param| param.name.clone()).collect();
            Definition {
                body: map(&definition.body, &names)?,
                ..(**definition).clone()
            }
        }
    };
    Ok(tables.with_source_name(Rc::new(mapped), definition))
}

fn map_all(expressions: &[Expr], map: &mut Map) -> Result<Vec<Expr>> {
    expressions.iter().map(|child| map(child, &[])).collect()
}

/// `mapChildren`: a copy of a node with its children mapped, each with the names the node binds
/// in it, in the order the TypeScript object literals evaluate them. A leaf is itself.
pub fn map_children(expression: &Expr, tables: &Tables, map: &mut Map) -> Result<Expr> {
    let kind = match &expression.kind {
        ExpressionKind::Number { .. }
        | ExpressionKind::Decimal { .. }
        | ExpressionKind::String { .. }
        | ExpressionKind::Identifier { .. }
        | ExpressionKind::OperatorReference { .. }
        | ExpressionKind::ExceptAt => return Ok(expression.clone()),
        ExpressionKind::Apply { args, .. } => replace_args(&expression.kind, map_all(args, map)?),
        ExpressionKind::Lambda {
            params,
            param_ranges,
            body,
            operator,
        } => ExpressionKind::Lambda {
            params: params.clone(),
            param_ranges: param_ranges.clone(),
            body: map(body, params)?,
            operator: operator.clone(),
        },
        ExpressionKind::Junction {
            is_and,
            operands,
            is_bulleted,
            prefix_ends,
        } => ExpressionKind::Junction {
            is_and: *is_and,
            operands: map_all(operands, map)?,
            is_bulleted: *is_bulleted,
            prefix_ends: prefix_ends.clone(),
        },
        ExpressionKind::Prime(inner) => ExpressionKind::Prime(map(inner, &[])?),
        ExpressionKind::Unchanged(inner) => ExpressionKind::Unchanged(map(inner, &[])?),
        ExpressionKind::Enabled(inner) => ExpressionKind::Enabled(map(inner, &[])?),
        ExpressionKind::Always(inner) => ExpressionKind::Always(map(inner, &[])?),
        ExpressionKind::Eventually(inner) => ExpressionKind::Eventually(map(inner, &[])?),
        ExpressionKind::If {
            condition,
            consequent,
            alternative,
        } => ExpressionKind::If {
            condition: map(condition, &[])?,
            consequent: map(consequent, &[])?,
            alternative: map(alternative, &[])?,
        },
        ExpressionKind::Case { arms, other } => {
            let arms = arms
                .iter()
                .map(|arm| {
                    Ok(CaseArm {
                        condition: map(&arm.condition, &[])?,
                        body: map(&arm.body, &[])?,
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            let other = other.as_ref().map(|other| map(other, &[])).transpose()?;
            ExpressionKind::Case { arms, other }
        }
        ExpressionKind::Let {
            definitions,
            instances,
            recursive,
            body,
        } => {
            let names: Vec<Name> = definitions
                .iter()
                .map(|definition| definition.name.clone())
                .collect();
            let definitions = definitions
                .iter()
                .map(|definition| {
                    map_definition(definition, tables, &mut |child, bound| {
                        let mut all = names.clone();
                        all.extend(bound.iter().cloned());
                        map(child, &all)
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            ExpressionKind::Let {
                definitions,
                instances: instances.clone(),
                recursive: recursive.clone(),
                body: map(body, &names)?,
            }
        }
        ExpressionKind::Quantified {
            quantifier,
            bounds,
            body,
        } => {
            let mapped = map_bounds(bounds, map)?;
            ExpressionKind::Quantified {
                quantifier: *quantifier,
                body: map(body, &get_bound_names(bounds))?,
                bounds: mapped,
            }
        }
        ExpressionKind::FunctionConstruction { bounds, body } => {
            let mapped = map_bounds(bounds, map)?;
            ExpressionKind::FunctionConstruction {
                body: map(body, &get_bound_names(bounds))?,
                bounds: mapped,
            }
        }
        ExpressionKind::UnboundedQuantifier {
            quantifier,
            names,
            name_ranges,
            is_temporal,
            body,
        } => ExpressionKind::UnboundedQuantifier {
            quantifier: *quantifier,
            names: names.clone(),
            name_ranges: name_ranges.clone(),
            is_temporal: *is_temporal,
            body: map(body, names)?,
        },
        ExpressionKind::Choose { pattern, set, body } => {
            let set = set.as_ref().map(|set| map(set, &[])).transpose()?;
            ExpressionKind::Choose {
                pattern: pattern.clone(),
                set,
                body: map(body, &get_pattern_names(pattern))?,
            }
        }
        ExpressionKind::SetEnumeration(elements) => {
            ExpressionKind::SetEnumeration(map_all(elements, map)?)
        }
        ExpressionKind::Tuple(elements) => ExpressionKind::Tuple(map_all(elements, map)?),
        ExpressionKind::SetFilter { bound, predicate } => {
            let set = map(&bound.set, &[])?;
            ExpressionKind::SetFilter {
                bound: Bound {
                    pattern: bound.pattern.clone(),
                    set,
                },
                predicate: map(predicate, &get_pattern_names(&bound.pattern))?,
            }
        }
        ExpressionKind::SetMap {
            expression: mapped,
            bounds,
        } => {
            let new_bounds = map_bounds(bounds, map)?;
            ExpressionKind::SetMap {
                expression: map(mapped, &get_bound_names(bounds))?,
                bounds: new_bounds,
            }
        }
        ExpressionKind::FunctionSet { domain, range } => ExpressionKind::FunctionSet {
            domain: map(domain, &[])?,
            range: map(range, &[])?,
        },
        ExpressionKind::Record { is_set, fields } => ExpressionKind::Record {
            is_set: *is_set,
            fields: fields
                .iter()
                .map(|field| {
                    Ok(RecordField {
                        value: map(&field.value, &[])?,
                        ..field.clone()
                    })
                })
                .collect::<Result<Vec<_>>>()?,
        },
        ExpressionKind::Except { function, updates } => {
            let function = map(function, &[])?;
            let updates = updates
                .iter()
                .map(|update| {
                    let path = update
                        .path
                        .iter()
                        .map(|step| {
                            Ok(match step {
                                ExceptPathStep::Index(args) => {
                                    ExceptPathStep::Index(map_all(args, map)?)
                                }
                                ExceptPathStep::Field(name) => ExceptPathStep::Field(name.clone()),
                            })
                        })
                        .collect::<Result<Vec<_>>>()?;
                    Ok(ExceptUpdate {
                        path,
                        value: map(&update.value, &[])?,
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            ExpressionKind::Except { function, updates }
        }
        ExpressionKind::FunctionApplication { function, args } => {
            ExpressionKind::FunctionApplication {
                function: map(function, &[])?,
                args: map_all(args, map)?,
            }
        }
        ExpressionKind::Bracket(args) => ExpressionKind::Bracket(map_all(args, map)?),
        ExpressionKind::FieldAccess { record, field } => ExpressionKind::FieldAccess {
            record: map(record, &[])?,
            field: field.clone(),
        },
        ExpressionKind::Product(factors) => ExpressionKind::Product(map_all(factors, map)?),
        ExpressionKind::Action {
            is_box,
            action,
            subscript,
        } => ExpressionKind::Action {
            is_box: *is_box,
            action: map(action, &[])?,
            subscript: map(subscript, &[])?,
        },
        ExpressionKind::Fairness {
            is_strong,
            subscript,
            action,
            enabled,
        } => ExpressionKind::Fairness {
            is_strong: *is_strong,
            subscript: map(subscript, &[])?,
            action: map(action, &[])?,
            enabled: enabled.clone(),
        },
        ExpressionKind::Label {
            name,
            params,
            param_ranges,
            body,
        } => ExpressionKind::Label {
            name: name.clone(),
            params: params.clone(),
            param_ranges: param_ranges.clone(),
            body: map(body, &[])?,
        },
        ExpressionKind::Subexpression {
            selectors,
            selector_ranges,
            argument_ranges,
        } => ExpressionKind::Subexpression {
            selectors: selectors
                .iter()
                .map(|selector| {
                    Ok(match selector {
                        Selector::Name { name, args } => Selector::Name {
                            name: name.clone(),
                            args: map_all(args, map)?,
                        },
                        Selector::Bound(args) => Selector::Bound(map_all(args, map)?),
                        other => other.clone(),
                    })
                })
                .collect::<Result<Vec<_>>>()?,
            selector_ranges: selector_ranges.clone(),
            argument_ranges: argument_ranges.clone(),
        },
    };
    Ok(rebuild(expression, kind))
}

pub type GetDefinition<'a> = Box<dyn Fn(&str) -> Option<Rc<Definition>> + 'a>;

pub type AddDefinition<'a> =
    Box<dyn Fn(&Name, &Name, &mut dyn FnMut(&Name) -> Result<Rc<Definition>>) -> Result<Name> + 'a>;

/// What an INSTANCE puts in place of the instantiated module's declarations, and how it adds the
/// copies of its definitions to the environment (`Instantiation`).
pub struct Instantiation<'a> {
    pub params: Vec<OperatorParam>,
    pub substitutions: OrderedMap<Name, Expr>,
    pub variables: FastSet<Name>,
    pub get_definition: GetDefinition<'a>,
    pub is_parameterized: Box<dyn Fn(&str) -> bool + 'a>,
    /// Adds the copy of a definition, with its source's key and its name, under the key it
    /// returns, making the copy with `create` once it has the key.
    #[allow(clippy::type_complexity)]
    pub add_definition: Box<
        dyn Fn(&Name, &Name, &mut dyn FnMut(&Name) -> Result<Rc<Definition>>) -> Result<Name> + 'a,
    >,
    pub create_name: Box<dyn Fn(&str) -> Name + 'a>,
}

/// LAMBDA is a keyword, so no name bound inside the instance can capture it.
const LAMBDA_NAME: &str = "LAMBDA";

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Normal = 0,
    Enabled = 1,
    Primed = 2,
}

/// The rewrite of each mode (`Rewrite`): the copies each keeps, by the key of the definition.
pub struct Instantiator<'a> {
    instantiation: Instantiation<'a>,
    substituted_names: FastSet<Name>,
    copies: [RefCell<FastMap<Name, Name>>; 3],
    tables: &'a Tables,
}

type Bindings = FastMap<Name, Name>;

fn get_free_names(
    expression: &Expr,
    bound: &FastSet<Name>,
    tables: &Tables,
    names: &mut Vec<Name>,
) {
    if let Some(name) = expression.reference()
        && !bound.contains(&name)
    {
        names.push(name);
    }
    let _ = map_children(expression, tables, &mut |child, child_bound| {
        if child_bound.is_empty() {
            get_free_names(child, bound, tables, names);
        } else {
            let mut inner = bound.clone();
            inner.extend(child_bound.iter().cloned());
            get_free_names(child, &inner, tables, names);
        }
        Ok(child.clone())
    });
}

fn bind_names(bound: &Bindings, names: &[Name], rename: &mut dyn FnMut(&Name) -> Name) -> Bindings {
    let mut inner = bound.clone();
    for name in names {
        let renamed = rename(name);
        inner.insert(name.clone(), renamed);
    }
    inner
}

fn rename_pattern(pattern: &BoundPattern, rename: &mut dyn FnMut(&Name) -> Name) -> BoundPattern {
    match pattern {
        BoundPattern::Name { name, .. } => BoundPattern::Name {
            name: rename(name),
            ranges: Vec::new(),
        },
        BoundPattern::Tuple { names, .. } => BoundPattern::Tuple {
            names: names.iter().map(&mut *rename).collect(),
            ranges: Vec::new(),
        },
    }
}

fn rename_bounds(bounds: &[Bound], rename: &mut dyn FnMut(&Name) -> Name) -> Vec<Bound> {
    bounds
        .iter()
        .map(|bound| Bound {
            pattern: rename_pattern(&bound.pattern, rename),
            set: bound.set.clone(),
        })
        .collect()
}

fn rename_params(definition: &Definition, rename: &mut dyn FnMut(&Name) -> Name) -> Definition {
    match &definition.kind {
        DefinitionKind::Function { bounds } => Definition {
            kind: DefinitionKind::Function {
                bounds: rename_bounds(bounds, rename),
            },
            ..definition.clone()
        },
        DefinitionKind::Operator { params, body_range } => Definition {
            kind: DefinitionKind::Operator {
                params: params
                    .iter()
                    .map(|item| param(rename(&item.name), item.arity))
                    .collect(),
                body_range: body_range.clone(),
            },
            ..definition.clone()
        },
    }
}

/// `getEnabledVariableName`.
pub fn get_enabled_variable_name(name: &str) -> Name {
    Rc::from(format!("{name}@ENABLED"))
}

impl<'a> Instantiator<'a> {
    /// `createInstantiation`.
    pub fn new(instantiation: Instantiation<'a>, tables: &'a Tables) -> Instantiator<'a> {
        let mut names = Vec::new();
        for expression in instantiation.substitutions.values() {
            tables.add_substitution(expression);
            get_free_names(expression, &FastSet::default(), tables, &mut names);
        }
        Instantiator {
            substituted_names: names.into_iter().collect(),
            instantiation,
            copies: Default::default(),
            tables,
        }
    }

    pub fn get_key(&self, key: &Name) -> Result<Name> {
        Ok(self
            .get_copy(Mode::Normal, key)?
            .unwrap_or_else(|| key.clone()))
    }

    pub fn get_qualified_key(&self, key: &Name) -> Result<Name> {
        if let Some(copy) = self.get_copy(Mode::Normal, key)? {
            return Ok(copy);
        }
        let Some(definition) = (self.instantiation.get_definition)(key) else {
            return Ok(key.clone());
        };
        (self.instantiation.add_definition)(key, &definition.name, &mut |_| {
            Ok(self.with_instance_params(&definition, &definition.location))
        })
    }

    /// `createRenamer`: renames a name a substitution mentions, once per copy.
    fn create_renamer(&self) -> impl FnMut(&Name) -> Name + '_ {
        let mut renamed: FastMap<Name, Name> = FastMap::default();
        move |name: &Name| {
            if !self.substituted_names.contains(name) {
                return name.clone();
            }
            let fresh = renamed
                .get(name)
                .cloned()
                .unwrap_or_else(|| (self.instantiation.create_name)(name));
            renamed.insert(name.clone(), fresh.clone());
            fresh
        }
    }

    fn get_copy(&self, mode: Mode, key: &Name) -> Result<Option<Name>> {
        if (self.instantiation.is_parameterized)(key) {
            self.copy_definition(mode, key).map(Some)
        } else {
            Ok(None)
        }
    }

    fn with_instance_params(
        &self,
        definition: &Rc<Definition>,
        location: &Location,
    ) -> Rc<Definition> {
        let params = &self.instantiation.params;
        if params.is_empty() {
            return definition.clone();
        }
        Rc::new(match &definition.kind {
            DefinitionKind::Operator {
                params: own,
                body_range,
            } => Definition {
                kind: DefinitionKind::Operator {
                    params: params.iter().chain(own).cloned().collect(),
                    body_range: body_range.clone(),
                },
                ..(**definition).clone()
            },
            DefinitionKind::Function { .. } => Definition {
                is_local: definition.is_local,
                location: definition.location.clone(),
                ..operator_definition(
                    definition.name.clone(),
                    params.clone(),
                    let_expression(
                        vec![definition.clone()],
                        local_identifier(definition.name.clone(), location),
                        location,
                    ),
                    definition.is_local,
                    location,
                )
            },
        })
    }

    fn copy_definition(&self, mode: Mode, key: &Name) -> Result<Name> {
        if let Some(cached) = self.copies[mode as usize].borrow().get(key) {
            return Ok(cached.clone());
        }
        let Some(definition) = (self.instantiation.get_definition)(key) else {
            return Ok(key.clone());
        };
        (self.instantiation.add_definition)(key, &definition.name, &mut |copy_key| {
            self.copies[mode as usize]
                .borrow_mut()
                .insert(key.clone(), copy_key.clone());
            let mut rename = self.create_renamer();
            let mapped = map_definition(&definition, self.tables, &mut |child, bound| {
                let bindings = bind_names(&Bindings::default(), bound, &mut rename);
                self.substitute(child, mode, &bindings)
            })?;
            let renamed = rename_params(&mapped, &mut rename);
            Ok(self.with_instance_params(&Rc::new(renamed), &definition.location))
        })
    }

    fn get_instance_operator(&self, key: Name, arity: usize, location: &Location) -> Expr {
        let names: Vec<Name> = (0..arity)
            .map(|index| Rc::from(format!("argument{index}")))
            .collect();
        let mut args = local_arguments(&self.instantiation.params, location);
        args.extend(
            names
                .iter()
                .map(|name| local_identifier(name.clone(), location)),
        );
        Rc::new(Expression::new(
            ExpressionKind::Lambda {
                params: names,
                param_ranges: None,
                body: apply(key, args, location),
                operator: None,
            },
            location.clone(),
        ))
    }

    fn is_variable(&self, expression: &Expression, bound: &Bindings) -> bool {
        matches!(expression.kind, ExpressionKind::Identifier { .. })
            && expression.reference().is_some_and(|name| {
                !bound.contains_key(&name)
                    && !expression.is_locally_resolved()
                    && self.instantiation.variables.contains(&name)
            })
    }

    fn get_unchanged_variables(
        &self,
        expression: &Expression,
        bound: &Bindings,
    ) -> Option<Vec<Name>> {
        match &expression.kind {
            ExpressionKind::Tuple(elements) => {
                let names = elements
                    .iter()
                    .map(|element| self.get_unchanged_variables(element, bound))
                    .collect::<Option<Vec<_>>>()?;
                Some(names.into_iter().flatten().collect())
            }
            ExpressionKind::Identifier { .. } => {
                let name = expression.reference()?;
                if self.is_variable(expression, bound) {
                    return Some(vec![name]);
                }
                let definition = if expression.is_locally_resolved() {
                    None
                } else {
                    (self.instantiation.get_definition)(&name)
                };
                match definition.as_deref() {
                    Some(
                        definition @ Definition {
                            kind: DefinitionKind::Operator { params, .. },
                            ..
                        },
                    ) if params.is_empty() => {
                        self.get_unchanged_variables(&definition.body, &Bindings::default())
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn substitute_in_enabled(
        &self,
        expression: &Expr,
        mode: Mode,
        bound: &Bindings,
    ) -> Result<Option<Expr>> {
        let location = &expression.location;
        match mode {
            Mode::Normal => Ok(None),
            Mode::Primed => Ok(self.is_variable(expression, bound).then(|| {
                identifier(
                    get_enabled_variable_name(&expression.reference().unwrap_or_default()),
                    location,
                )
            })),
            Mode::Enabled => match &expression.kind {
                ExpressionKind::Prime(inner) => Ok(Some(rebuild(
                    expression,
                    ExpressionKind::Prime(self.substitute(inner, Mode::Primed, bound)?),
                ))),
                ExpressionKind::Action {
                    is_box: false,
                    action,
                    subscript,
                } => {
                    let action = self.substitute(action, mode, bound)?;
                    let primed = Rc::new(Expression::new(
                        ExpressionKind::Prime(self.substitute(subscript, Mode::Primed, bound)?),
                        location.clone(),
                    ));
                    let unprimed = self.substitute(subscript, mode, bound)?;
                    Ok(Some(Rc::new(Expression::new(
                        ExpressionKind::Junction {
                            is_and: true,
                            operands: vec![
                                action,
                                apply(Rc::from("#"), vec![primed, unprimed], location),
                            ],
                            is_bulleted: false,
                            prefix_ends: None,
                        },
                        location.clone(),
                    ))))
                }
                ExpressionKind::Unchanged(inner) => {
                    let Some(names) = self.get_unchanged_variables(inner, bound) else {
                        return Ok(None);
                    };
                    let operands = names
                        .iter()
                        .map(|name| {
                            let primed = Rc::new(Expression::new(
                                ExpressionKind::Prime(identifier(
                                    get_enabled_variable_name(name),
                                    location,
                                )),
                                location.clone(),
                            ));
                            let value =
                                self.substitute(&identifier(name.clone(), location), mode, bound)?;
                            Ok(apply(Rc::from("="), vec![primed, value], location))
                        })
                        .collect::<Result<Vec<_>>>()?;
                    Ok(Some(Rc::new(Expression::new(
                        ExpressionKind::Junction {
                            is_and: true,
                            operands,
                            is_bulleted: false,
                            prefix_ends: None,
                        },
                        location.clone(),
                    ))))
                }
                _ => Ok(None),
            },
        }
    }

    fn substitute(&self, expression: &Expr, mode: Mode, bound: &Bindings) -> Result<Expr> {
        let instantiation = &self.instantiation;
        let params = &instantiation.params;
        let location = &expression.location;
        let is_free = |name: &Name| !bound.contains_key(name) && !expression.is_locally_resolved();
        match &expression.kind {
            ExpressionKind::Enabled(inner) if mode == Mode::Normal => {
                return Ok(rebuild(
                    expression,
                    ExpressionKind::Enabled(self.substitute(inner, Mode::Enabled, bound)?),
                ));
            }
            ExpressionKind::Fairness {
                is_strong,
                subscript,
                action,
                enabled,
            } if mode == Mode::Normal => {
                let new_subscript = self.substitute(subscript, mode, bound)?;
                let new_action = self.substitute(action, mode, bound)?;
                let step = enabled.clone().unwrap_or_else(|| {
                    Rc::new(Expression::new(
                        ExpressionKind::Action {
                            is_box: false,
                            action: action.clone(),
                            subscript: subscript.clone(),
                        },
                        location.clone(),
                    ))
                });
                return Ok(rebuild(
                    expression,
                    ExpressionKind::Fairness {
                        is_strong: *is_strong,
                        subscript: new_subscript,
                        action: new_action,
                        enabled: Some(self.substitute(&step, Mode::Enabled, bound)?),
                    },
                ));
            }
            _ => {}
        }
        if let Some(enabled) = self.substitute_in_enabled(expression, mode, bound)? {
            return Ok(enabled);
        }
        match &expression.kind {
            ExpressionKind::Identifier { .. } => {
                let name = expression.reference().unwrap_or_default();
                if is_free(&name) {
                    if let Some(replacement) = instantiation.substitutions.get(&name) {
                        return Ok(replacement.clone());
                    }
                    let Some(copy) = self.get_copy(mode, &name)? else {
                        return Ok(expression.clone());
                    };
                    if params.is_empty() {
                        return Ok(with_reference(expression, copy, None));
                    }
                    if let Some(definition) = (instantiation.get_definition)(&name)
                        && get_arity(&definition) > 0
                    {
                        return Ok(self.get_instance_operator(
                            copy,
                            get_arity(&definition),
                            location,
                        ));
                    }
                    return Ok(apply(copy, local_arguments(params, location), location));
                }
            }
            ExpressionKind::Apply { args, .. } => {
                let operator = expression.reference().unwrap_or_default();
                if is_free(&operator) {
                    let args = args
                        .iter()
                        .map(|arg| self.substitute(arg, mode, bound))
                        .collect::<Result<Vec<_>>>()?;
                    let replacement = instantiation.substitutions.get(&operator);
                    if let Some(replacement) = replacement {
                        match &replacement.kind {
                            ExpressionKind::Identifier { .. }
                            | ExpressionKind::OperatorReference { .. } => {
                                let copy = with_reference(
                                    expression,
                                    replacement.reference().unwrap_or_default(),
                                    Some(args),
                                );
                                copy.resolved.is_local.set(
                                    matches!(replacement.kind, ExpressionKind::Identifier { .. })
                                        && replacement.resolved.is_local.get(),
                                );
                                return Ok(copy);
                            }
                            ExpressionKind::Apply {
                                args: replacement_args,
                                ..
                            } => {
                                let all = replacement_args.iter().cloned().chain(args).collect();
                                let copy = with_reference(
                                    expression,
                                    replacement.reference().unwrap_or_default(),
                                    Some(all),
                                );
                                copy.resolved
                                    .is_local
                                    .set(replacement.resolved.is_local.get());
                                return Ok(copy);
                            }
                            ExpressionKind::Lambda {
                                params: lambda_params,
                                body,
                                ..
                            } => {
                                let definition = operator_definition(
                                    Rc::from(LAMBDA_NAME),
                                    lambda_params
                                        .iter()
                                        .map(|name| param(name.clone(), 0))
                                        .collect(),
                                    body.clone(),
                                    true,
                                    &replacement.location,
                                );
                                let call =
                                    with_reference(expression, Rc::from(LAMBDA_NAME), Some(args));
                                call.resolved.is_local.set(true);
                                return Ok(let_expression(
                                    vec![Rc::new(definition)],
                                    call,
                                    location,
                                ));
                            }
                            _ => {
                                return Err(SyntaxError::new(format!(
                                    "The operator {operator} can only be substituted by an operator at line {}, column {}",
                                    location.line, location.column
                                ))
                                .into());
                            }
                        }
                    }
                    let Some(copy) = self.get_copy(mode, &operator)? else {
                        return Ok(rebuild(expression, replace_args(&expression.kind, args)));
                    };
                    let all = local_arguments(params, location)
                        .into_iter()
                        .chain(args)
                        .collect();
                    return Ok(with_reference(expression, copy, Some(all)));
                }
            }
            ExpressionKind::OperatorReference { .. } => {
                let operator = expression.reference().unwrap_or_default();
                if is_free(&operator) {
                    let Some(copy) = self.get_copy(mode, &operator)? else {
                        return Ok(expression.clone());
                    };
                    let definition = (instantiation.get_definition)(&operator);
                    if !params.is_empty()
                        && let Some(definition) = definition
                    {
                        return Ok(self.get_instance_operator(
                            copy,
                            get_arity(&definition),
                            location,
                        ));
                    }
                    return Ok(with_reference(expression, copy, None));
                }
            }
            _ => {}
        }
        let mut rename = self.create_renamer();
        let mapped = map_children(expression, self.tables, &mut |child, names| {
            if names.is_empty() {
                self.substitute(child, mode, bound)
            } else {
                self.substitute(child, mode, &bind_names(bound, names, &mut rename))
            }
        })?;
        Ok(self.rename_names(&mapped, bound, &mut rename))
    }

    /// `renameNames`: a copy of a node with the names it refers to renamed as they are bound, and
    /// the names it binds renamed where a substitution would capture them.
    fn rename_names(
        &self,
        expression: &Expr,
        bound: &Bindings,
        rename: &mut dyn FnMut(&Name) -> Name,
    ) -> Expr {
        let get_bound_name = |name: &Name| bound.get(name).cloned().unwrap_or_else(|| name.clone());
        let kind = match &expression.kind {
            ExpressionKind::Identifier { .. }
            | ExpressionKind::Apply { .. }
            | ExpressionKind::OperatorReference { .. } => {
                let name = expression.reference().unwrap_or_default();
                return with_reference(expression, get_bound_name(&name), None);
            }
            ExpressionKind::Label {
                name,
                params,
                param_ranges,
                body,
            } => ExpressionKind::Label {
                name: name.clone(),
                params: params.iter().map(get_bound_name).collect(),
                param_ranges: param_ranges.clone(),
                body: body.clone(),
            },
            ExpressionKind::Lambda {
                params,
                param_ranges,
                body,
                operator,
            } => ExpressionKind::Lambda {
                params: params.iter().map(&mut *rename).collect(),
                param_ranges: param_ranges.clone(),
                body: body.clone(),
                operator: operator.clone(),
            },
            ExpressionKind::Let {
                definitions,
                instances,
                recursive,
                body,
            } => ExpressionKind::Let {
                recursive: recursive
                    .iter()
                    .map(|declaration| {
                        Rc::new(Declaration {
                            name: rename(&declaration.name),
                            ..(**declaration).clone()
                        })
                    })
                    .collect(),
                definitions: definitions
                    .iter()
                    .map(|definition| {
                        let renamed = Definition {
                            name: rename(&definition.name),
                            ..rename_params(definition, rename)
                        };
                        self.tables.with_source_name(Rc::new(renamed), definition)
                    })
                    .collect(),
                instances: instances.clone(),
                body: body.clone(),
            },
            ExpressionKind::Quantified {
                quantifier,
                bounds,
                body,
            } => ExpressionKind::Quantified {
                quantifier: *quantifier,
                bounds: rename_bounds(bounds, rename),
                body: body.clone(),
            },
            ExpressionKind::FunctionConstruction { bounds, body } => {
                ExpressionKind::FunctionConstruction {
                    bounds: rename_bounds(bounds, rename),
                    body: body.clone(),
                }
            }
            ExpressionKind::SetMap {
                expression: mapped,
                bounds,
            } => ExpressionKind::SetMap {
                expression: mapped.clone(),
                bounds: rename_bounds(bounds, rename),
            },
            ExpressionKind::UnboundedQuantifier {
                quantifier,
                names,
                name_ranges,
                is_temporal,
                body,
            } => ExpressionKind::UnboundedQuantifier {
                quantifier: *quantifier,
                names: names.iter().map(&mut *rename).collect(),
                name_ranges: name_ranges.clone(),
                is_temporal: *is_temporal,
                body: body.clone(),
            },
            ExpressionKind::Choose { pattern, set, body } => ExpressionKind::Choose {
                pattern: rename_pattern(pattern, rename),
                set: set.clone(),
                body: body.clone(),
            },
            ExpressionKind::SetFilter { bound, predicate } => ExpressionKind::SetFilter {
                bound: Bound {
                    pattern: rename_pattern(&bound.pattern, rename),
                    set: bound.set.clone(),
                },
                predicate: predicate.clone(),
            },
            _ => return expression.clone(),
        };
        rebuild(expression, kind)
    }
}

fn has_let_instance(expression: &Expression) -> bool {
    matches!(
        expression.kind,
        ExpressionKind::Let {
            instances: Some(_),
            ..
        }
    ) || expression
        .children()
        .iter()
        .any(|child| has_let_instance(child))
}

/// Puts the definitions an INSTANCE in a LET makes before the first definition after it.
type Instantiate<'a> =
    dyn FnMut(&Rc<Instance>, &[Rc<Definition>]) -> Result<Vec<Rc<Definition>>> + 'a;

fn expand_let_instances(
    expression: &Expr,
    instantiate: &mut Instantiate,
    lets: &[Rc<Definition>],
    tables: &Tables,
) -> Result<Expr> {
    let mut visible: Vec<Rc<Definition>> = lets.to_vec();
    if let ExpressionKind::Let { definitions, .. } = &expression.kind {
        visible.extend(definitions.iter().cloned());
    }
    let mapped = map_children(expression, tables, &mut |child, _| {
        expand_let_instances(child, instantiate, &visible, tables)
    })?;
    let ExpressionKind::Let {
        definitions,
        instances: Some(instances),
        recursive,
        body,
    } = &mapped.kind
    else {
        return Ok(mapped);
    };
    let mut current = definitions.clone();
    for instance in instances {
        let index = current
            .iter()
            .position(|definition| {
                is_before(instance.location.position(), definition.location.position())
            })
            .unwrap_or(current.len());
        let added = instantiate(instance, &visible)?;
        current.splice(index..index, added);
    }
    Ok(rebuild(
        &mapped,
        ExpressionKind::Let {
            definitions: current,
            instances: Some(instances.clone()),
            recursive: recursive.clone(),
            body: body.clone(),
        },
    ))
}

/// A named theorem's statement is linked as its definition.
fn get_unnamed_statement(theorem: &Theorem) -> Option<&Expr> {
    match (&theorem.name, &theorem.statement) {
        (None, Statement::Expression(expression)) => Some(expression),
        _ => None,
    }
}

/// `withLetInstances`: the module with the definitions each INSTANCE in a LET makes put in the
/// LET.
pub fn with_let_instances(
    module: &Rc<Module>,
    instantiate: &mut Instantiate,
    tables: &Tables,
) -> Result<Rc<Module>> {
    let has_let_instances = module
        .definitions
        .iter()
        .any(|definition| has_let_instance(&definition.body))
        || module
            .assumptions
            .iter()
            .any(|assumption| has_let_instance(&assumption.expression))
        || module.theorems.iter().any(|theorem| {
            get_unnamed_statement(theorem).is_some_and(|statement| has_let_instance(statement))
        });
    if !has_let_instances {
        return Ok(module.clone());
    }
    let definitions = module
        .definitions
        .iter()
        .map(|definition| {
            map_definition(definition, tables, &mut |child, _| {
                expand_let_instances(child, instantiate, &[], tables)
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let assumptions = module
        .assumptions
        .iter()
        .map(|assumption| {
            Ok(Rc::new(Assumption {
                expression: expand_let_instances(&assumption.expression, instantiate, &[], tables)?,
                ..(**assumption).clone()
            }))
        })
        .collect::<Result<Vec<_>>>()?;
    let theorems = module
        .theorems
        .iter()
        .map(|theorem| {
            Ok(match get_unnamed_statement(theorem) {
                None => theorem.clone(),
                Some(statement) => Rc::new(Theorem {
                    statement: Statement::Expression(expand_let_instances(
                        statement,
                        instantiate,
                        &[],
                        tables,
                    )?),
                    ..(**theorem).clone()
                }),
            })
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(Rc::new(Module {
        definitions,
        assumptions,
        theorems,
        ..(**module).clone()
    }))
}

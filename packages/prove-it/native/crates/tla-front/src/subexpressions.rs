//! Names that select a subexpression, such as `Op(1)!lab(2)!1` or `Inv!P1`, rewritten as the
//! expressions they select, as `src/subexpressions.ts` rewrites them before resolution: the part
//! selected, under the LETs it is in, applied to the arguments the name gives the operators and
//! labels it passes through.

use std::rc::Rc;

use crate::ast::*;
use crate::errors::{FrontError, SanyError, SyntaxError, format_range};
use crate::hash::{FastMap, FastSet};
use crate::instances::{apply, let_expression, map_children, map_definition, param};
use crate::resolve::{
    Result, Tables, get_arity, get_binder, get_name_selectors, get_operand_index, get_operands,
    get_selector_ranges,
};

type Lookup<'a> = dyn Fn(&str) -> Option<Rc<Definition>> + 'a;

struct Selection {
    params: Vec<OperatorParam>,
    args: Vec<Expr>,
    lets: Vec<Vec<Rc<Definition>>>,
    location: Location,
}

const SELECTION_NAME: &str = "$subexpression";

fn create_error(message: &str, location: &Location) -> FrontError {
    SyntaxError::new(format!(
        "{message} at line {}, column {}",
        location.line, location.column
    ))
    .into()
}

fn find_label(
    expression: &Expr,
    name: &str,
    lets: &[Vec<Rc<Definition>>],
) -> Option<(Expr, Vec<Vec<Rc<Definition>>>)> {
    match &expression.kind {
        ExpressionKind::Label { name: label, .. } => {
            (&**label == name).then(|| (expression.clone(), lets.to_vec()))
        }
        ExpressionKind::Let {
            definitions, body, ..
        } => {
            let mut inner = lets.to_vec();
            inner.push(definitions.clone());
            find_label(body, name, &inner)
        }
        ExpressionKind::Lambda { .. } => None,
        _ => expression
            .children()
            .iter()
            .find_map(|child| find_label(child, name, lets)),
    }
}

fn wrap_lets(body: Expr, lets: &[Vec<Rc<Definition>>], location: &Location) -> Expr {
    lets.iter().rev().fold(body, |inner, definitions| {
        let_expression(definitions.clone(), inner, location)
    })
}

fn local_name(name: Name, location: &Location) -> Expr {
    let expression = crate::instances::identifier(name, location);
    expression.resolved.is_local.set(true);
    expression
}

fn create_application(selection: &Selection, body: Expr) -> Result<Expr> {
    let location = &selection.location;
    let wrapped = wrap_lets(body, &selection.lets, location);
    if selection.params.is_empty() {
        return Ok(wrapped);
    }
    if selection.args.is_empty() {
        if selection.params.iter().any(|param| param.arity > 0) {
            return Err(create_error(
                "Selected an operator with operator parameters as an argument",
                location,
            ));
        }
        return Ok(Rc::new(Expression::new(
            ExpressionKind::Lambda {
                params: selection
                    .params
                    .iter()
                    .map(|param| param.name.clone())
                    .collect(),
                param_ranges: None,
                body: wrapped,
                operator: None,
            },
            location.clone(),
        )));
    }
    if selection.args.len() != selection.params.len() {
        return Err(create_error(
            &format!(
                "The subexpression requires {} arguments but received {}",
                selection.params.len(),
                selection.args.len()
            ),
            location,
        ));
    }
    let definition = crate::instances::operator_definition(
        Rc::from(SELECTION_NAME),
        selection.params.clone(),
        wrapped,
        true,
        location,
    );
    let call = apply(Rc::from(SELECTION_NAME), selection.args.clone(), location);
    call.resolved.is_local.set(true);
    Ok(let_expression(vec![Rc::new(definition)], call, location))
}

fn apply_definition(definition: &Definition, selection: Selection) -> Result<Expr> {
    let location = selection.location.clone();
    let params: Vec<OperatorParam> = match &definition.kind {
        DefinitionKind::Operator { params, .. } => params
            .iter()
            .enumerate()
            .map(|(index, own)| {
                param(
                    Rc::from(format!("{}${}", own.name, selection.params.len() + index)),
                    own.arity,
                )
            })
            .collect(),
        DefinitionKind::Function { .. } => Vec::new(),
    };
    let args: Vec<Expr> = params
        .iter()
        .map(|param| local_name(param.name.clone(), &location))
        .collect();
    let reference = if args.is_empty() {
        local_name(definition.name.clone(), &location)
    } else {
        let call = apply(definition.name.clone(), args, &location);
        call.resolved.is_local.set(true);
        call
    };
    let mut all = selection.params.clone();
    all.extend(params);
    create_application(
        &Selection {
            params: all,
            ..selection
        },
        reference,
    )
}

fn get_argument_ranges(expression: &Expression) -> Option<&[Option<Range>]> {
    match &expression.kind {
        ExpressionKind::Apply {
            argument_ranges, ..
        } => argument_ranges.as_deref(),
        ExpressionKind::Subexpression {
            argument_ranges, ..
        } => Some(argument_ranges),
        _ => None,
    }
}

struct Found {
    definition: Rc<Definition>,
    args: Vec<Expr>,
}

/// `Generator.selectorToNode` reports the first part of a name that selects nothing, after it
/// analyzes the arguments of the parts before, and goes on after the name. An operator or a label
/// must be given all its arguments, except in a name that an operator argument may select whole.
struct Selector<'a> {
    selectors: &'a [crate::ast::Selector],
    lookup: &'a Lookup<'a>,
    reference: &'a Expr,
    is_operator: bool,
    tables: &'a Tables,
    selection: Selection,
    index: usize,
    current: Option<Expr>,
    is_failed: bool,
}

impl Selector<'_> {
    fn report(&mut self, range: Option<Range>, message: String) -> Result<()> {
        let Some(range) = range else {
            return Err(create_error(&message, &self.reference.location));
        };
        let args = self.selectors[..self.index]
            .iter()
            .flat_map(|selector| selector.args().to_vec())
            .collect();
        self.tables.set_error(
            self.reference,
            args,
            SanyError {
                location: format_range(&range),
                message,
            },
        );
        self.is_failed = true;
        Ok(())
    }

    fn find_definition(
        &mut self,
        local: Option<&[Rc<Definition>]>,
    ) -> Result<(Rc<Definition>, Name, Vec<Expr>, usize)> {
        let mut names: Vec<Name> = Vec::new();
        let mut args: Vec<Expr> = Vec::new();
        while self.index < self.selectors.len() {
            let crate::ast::Selector::Name {
                name,
                args: own_args,
            } = &self.selectors[self.index]
            else {
                return Err(create_error(
                    "Expected an operator name",
                    &self.reference.location,
                ));
            };
            names.push(name.clone());
            args.extend(own_args.iter().cloned());
            let joined: Name = Rc::from(names.join("!"));
            let definition = match local {
                Some(local) => local
                    .iter()
                    .find(|candidate| self.tables.get_source_name(candidate) == joined)
                    .cloned(),
                None => (self.lookup)(&joined),
            };
            if let Some(definition) = definition {
                let earlier = args.len() - own_args.len();
                return Ok((definition, joined, args, earlier));
            }
            self.index += 1;
        }
        Err(create_error(
            &format!("Unknown operator {}", names.join("!")),
            &self.reference.location,
        ))
    }

    fn enter_definition(&mut self, local: Option<&[Rc<Definition>]>) -> Result<Option<Found>> {
        let (definition, name, args, earlier) = self.find_definition(local)?;
        let arity = get_arity(&definition);
        let is_last = self.index == self.selectors.len() - 1;
        if args.len() != arity && (!self.is_operator || !args.is_empty()) {
            let range = get_argument_ranges(self.reference)
                .and_then(|ranges| ranges.get(self.index).cloned().flatten())
                .or_else(|| self.reference.location.range.clone());
            self.report(
                range,
                format!(
                    "The operator {name} requires {} arguments.",
                    arity as i64 - earlier as i64
                ),
            )?;
            return Ok(None);
        }
        if is_last {
            return Ok(Some(Found { definition, args }));
        }
        let DefinitionKind::Operator { params, .. } = &definition.kind else {
            return Err(create_error(
                &format!("Cannot select a subexpression of {}", definition.name),
                &self.reference.location,
            ));
        };
        self.selection.params.extend(params.iter().cloned());
        self.selection.args.extend(args);
        self.current = Some(definition.body.clone());
        self.index += 1;
        Ok(None)
    }

    fn follow_labels(&mut self) -> Result<()> {
        while self.index < self.selectors.len() && !self.is_failed {
            let crate::ast::Selector::Name { name, args } = &self.selectors[self.index] else {
                return Ok(());
            };
            let range = get_selector_ranges(self.reference)
                .and_then(|ranges| ranges.get(self.index))
                .cloned();
            let found = self
                .current
                .as_ref()
                .and_then(|current| find_label(current, name, &[]));
            let Some((label, lets)) = found else {
                return self.report(range, format!("Cannot find label `{name}'."));
            };
            let ExpressionKind::Label { params, body, .. } = &label.kind else {
                return Ok(());
            };
            if !self.is_operator && args.len() != params.len() {
                return self.report(
                    range,
                    format!("Label `{name}' used with wrong number of arguments."),
                );
            }
            self.selection.lets.extend(lets);
            self.selection
                .params
                .extend(params.iter().map(|name| param(name.clone(), 0)));
            self.selection.args.extend(args.iter().cloned());
            self.current = Some(body.clone());
            self.index += 1;
        }
        Ok(())
    }

    fn select_operand(&mut self, selector: &crate::ast::Selector) -> Result<()> {
        let location = self.reference.location.clone();
        let Some(current) = self.current.clone() else {
            return Err(create_error("Subexpression selection failed", &location));
        };
        if matches!(selector, crate::ast::Selector::Colon) {
            return Ok(());
        }
        match &current.kind {
            ExpressionKind::Label { body, .. } => {
                self.current = Some(body.clone());
                return self.select_operand(selector);
            }
            ExpressionKind::Let {
                definitions, body, ..
            } => {
                let is_first = matches!(
                    selector,
                    crate::ast::Selector::Operand(operand) if get_operand_index(operand, 1) == Some(0)
                );
                if !is_first {
                    return Err(create_error(
                        "A LET/IN expression has only one operand",
                        &location,
                    ));
                }
                self.selection.lets.push(definitions.clone());
                self.current = Some(body.clone());
                return Ok(());
            }
            _ => {}
        }
        let binder = get_binder(&current);
        if let Some(binder) = &binder
            && matches!(
                selector,
                crate::ast::Selector::Bound(_) | crate::ast::Selector::At
            )
        {
            self.selection
                .params
                .extend(binder.names.iter().map(|name| param(name.clone(), 0)));
            if let crate::ast::Selector::Bound(args) = selector {
                self.selection.args.extend(args.iter().cloned());
            }
            self.current = Some(binder.body.clone());
            return Ok(());
        }
        if let (ExpressionKind::Case { arms, other }, crate::ast::Selector::Operand(operand)) =
            (&current.kind, selector)
        {
            let mut all: Vec<(Option<Expr>, Expr)> = arms
                .iter()
                .map(|arm| (Some(arm.condition.clone()), arm.body.clone()))
                .collect();
            if let Some(other) = other {
                all.push((None, other.clone()));
            }
            let arm = get_operand_index(operand, all.len()).map(|index| all[index].clone());
            let next = self.selectors.get(self.index + 1);
            let (Some(arm), Some(crate::ast::Selector::Operand(next))) = (arm, next) else {
                return Err(create_error(
                    "A subexpression of CASE must have the form !i!j",
                    &location,
                ));
            };
            self.index += 1;
            let chosen = match get_operand_index(next, 2) {
                Some(0) => arm.0,
                Some(1) => Some(arm.1),
                _ => None,
            };
            let Some(chosen) = chosen else {
                return Err(create_error("Nonexistent CASE operand", &location));
            };
            self.current = Some(chosen);
            return Ok(());
        }
        let crate::ast::Selector::Operand(operand) = selector else {
            return Err(create_error("Unexpected subexpression selector", &location));
        };
        let operands = match binder {
            Some(binder) => Some(binder.sets),
            None => get_operands(&current),
        };
        let chosen = operands.and_then(|operands| {
            get_operand_index(operand, operands.len()).map(|index| operands[index].clone())
        });
        let Some(chosen) = chosen else {
            return Err(create_error(
                "Nonexistent operand specified by the selector",
                &location,
            ));
        };
        self.current = Some(chosen);
        Ok(())
    }

    fn select(mut self) -> Result<Expr> {
        let first = self.enter_definition(None)?;
        if self.is_failed {
            return Ok(self.reference.clone());
        }
        if let Some(first) = first {
            let selection = Selection {
                args: first.args,
                ..self.selection
            };
            return apply_definition(&first.definition, selection);
        }
        self.follow_labels()?;
        while self.index < self.selectors.len() && !self.is_failed {
            let selector = &self.selectors[self.index];
            if let crate::ast::Selector::Name { .. } = selector {
                while let Some(ExpressionKind::Label { body, .. }) =
                    self.current.as_ref().map(|current| &current.kind)
                {
                    self.current = Some(body.clone());
                }
                let Some(ExpressionKind::Let { definitions, .. }) =
                    self.current.as_ref().map(|current| &current.kind)
                else {
                    return Err(create_error(
                        "A name selector here must be from a LET clause",
                        &self.reference.location,
                    ));
                };
                let definitions = definitions.clone();
                self.selection.lets.push(definitions.clone());
                let last = self.enter_definition(Some(&definitions))?;
                if self.is_failed {
                    return Ok(self.reference.clone());
                }
                if let Some(last) = last {
                    let mut args = self.selection.args.clone();
                    args.extend(last.args);
                    let selection = Selection {
                        args,
                        ..self.selection
                    };
                    return apply_definition(&last.definition, selection);
                }
                self.follow_labels()?;
                continue;
            }
            self.select_operand(selector)?;
            self.index += 1;
        }
        if self.is_failed {
            return Ok(self.reference.clone());
        }
        let Some(current) = self.current.clone() else {
            return Err(create_error(
                "Subexpression selection failed",
                &self.reference.location,
            ));
        };
        create_application(&self.selection, current)
    }
}

/// A name such as `Op(1)!lab(2)` whose first parts name a definition selects part of it.
fn get_qualified_selectors(
    name: &str,
    args: &[Expr],
    counts: Option<&[usize]>,
    lookup: &Lookup,
) -> Option<Vec<crate::ast::Selector>> {
    if !name.contains('!') || lookup(name).is_some() {
        return None;
    }
    let parts: Vec<&str> = name.split('!').collect();
    let is_selected = (0..parts.len()).any(|index| lookup(&parts[..=index].join("!")).is_some());
    is_selected.then(|| get_name_selectors(name, args, counts))
}

/// `containsReference`: a name that may select a subexpression.
pub fn contains_reference(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Subexpression { .. } => true,
        ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. }
            if expression
                .reference()
                .is_some_and(|name| name.contains('!')) =>
        {
            true
        }
        _ => expression
            .children()
            .iter()
            .any(|child| contains_reference(child)),
    }
}

/// A reference that starts with a name `is_goal` holds for, such as a theorem whose statement is
/// an ASSUME/PROVE, stays for name resolution to check. `is_operator` holds where an operator may
/// be given, as the argument of an operator that may take one.
fn resolve_subexpressions(
    expression: &Expr,
    lookup: &Lookup,
    is_goal: &dyn Fn(&str) -> bool,
    is_operator: bool,
    tables: &Tables,
) -> Result<Expr> {
    if !contains_reference(expression) {
        return Ok(expression.clone());
    }
    if let ExpressionKind::Let { definitions, .. } = &expression.kind {
        let local = |name: &str| {
            definitions
                .iter()
                .find(|definition| &*definition.name == name)
                .cloned()
                .or_else(|| lookup(name))
        };
        let mapped = map_children(expression, tables, &mut |child, _| {
            resolve_subexpressions(child, &local, is_goal, false, tables)
        })?;
        let ExpressionKind::Let {
            definitions,
            instances: Some(instances),
            body,
        } = &mapped.kind
        else {
            return Ok(mapped);
        };
        let instances = instances
            .iter()
            .map(|instance| resolve_instance(instance, &local, is_goal, tables))
            .collect::<Result<Vec<_>>>()?;
        return Ok(crate::instances::rebuild(
            &mapped,
            ExpressionKind::Let {
                definitions: definitions.clone(),
                instances: Some(instances),
                body: body.clone(),
            },
        ));
    }
    let mapped = match &expression.kind {
        ExpressionKind::Apply { args, .. } => {
            let callee = lookup(&expression.reference().unwrap_or_default());
            let args = args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    let takes_operator = match callee.as_deref().map(|callee| &callee.kind) {
                        Some(DefinitionKind::Operator { params, .. }) => {
                            params.get(index).is_none_or(|param| param.arity != 0)
                        }
                        _ => true,
                    };
                    resolve_subexpressions(arg, lookup, is_goal, takes_operator, tables)
                })
                .collect::<Result<Vec<_>>>()?;
            crate::instances::rebuild(
                expression,
                crate::instances::replace_args(&expression.kind, args),
            )
        }
        _ => map_children(expression, tables, &mut |child, _| {
            resolve_subexpressions(child, lookup, is_goal, false, tables)
        })?,
    };
    let selectors = match &mapped.kind {
        ExpressionKind::Subexpression { selectors, .. } => Some(selectors.clone()),
        ExpressionKind::Identifier { .. } => {
            get_qualified_selectors(&mapped.reference().unwrap_or_default(), &[], None, lookup)
        }
        ExpressionKind::Apply {
            args,
            argument_counts,
            ..
        } => get_qualified_selectors(
            &mapped.reference().unwrap_or_default(),
            args,
            argument_counts.as_deref(),
            lookup,
        ),
        _ => None,
    };
    let Some(selectors) = selectors else {
        return Ok(mapped);
    };
    if let Some(crate::ast::Selector::Name { name, .. }) = selectors.first()
        && is_goal(name)
    {
        return Ok(mapped);
    }
    let selected = Selector {
        selectors: &selectors,
        lookup,
        reference: &mapped,
        is_operator,
        tables,
        selection: Selection {
            params: Vec::new(),
            args: Vec::new(),
            lets: Vec::new(),
            location: mapped.location.clone(),
        },
        index: 0,
        current: None,
        is_failed: false,
    }
    .select()?;
    if !Rc::ptr_eq(&selected, &mapped) {
        tables.add_selection(&selected);
    }
    Ok(selected)
}

fn resolve_instance(
    instance: &Rc<Instance>,
    lookup: &Lookup,
    is_goal: &dyn Fn(&str) -> bool,
    tables: &Tables,
) -> Result<Rc<Instance>> {
    let substitutions = instance
        .substitutions
        .iter()
        .map(|substitution| {
            Ok(InstanceSubstitution {
                expression: resolve_subexpressions(
                    &substitution.expression,
                    lookup,
                    is_goal,
                    true,
                    tables,
                )?,
                ..substitution.clone()
            })
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(Rc::new(Instance {
        substitutions,
        ..(**instance).clone()
    }))
}

/// `createLookup`: the definitions by name, the last of a name winning.
fn create_lookup(definitions: &[Rc<Definition>]) -> FastMap<Name, Rc<Definition>> {
    definitions
        .iter()
        .map(|definition| (definition.name.clone(), definition.clone()))
        .collect()
}

pub fn resolve_instance_subexpressions(
    instance: &Rc<Instance>,
    module: &Module,
    tables: &Tables,
) -> Result<Rc<Instance>> {
    let by_name = create_lookup(&module.definitions);
    resolve_instance(
        instance,
        &|name| by_name.get(name).cloned(),
        &|_| false,
        tables,
    )
}

/// `resolveModuleSubexpressions`: `Generator.selectorToNode` resolves a name in a theorem, a
/// proof, or a fact as it does in a definition.
pub fn resolve_module_subexpressions(
    module: &Rc<Module>,
    available: &[Rc<Definition>],
    tables: &Tables,
) -> Result<Rc<Module>> {
    let all: Vec<Rc<Definition>> = available
        .iter()
        .chain(&module.definitions)
        .cloned()
        .collect();
    let by_name = create_lookup(&all);
    let lookup = |name: &str| by_name.get(name).cloned();
    let goals: FastSet<Name> = module
        .theorems
        .iter()
        .filter_map(|theorem| match (&theorem.name, &theorem.statement) {
            (Some(name), Statement::AssumeProve(_)) => Some(name.clone()),
            _ => None,
        })
        .collect();
    let is_goal = |name: &str| goals.contains(name);
    // A name in a theorem, a proof, or a fact may also start with a step, a theorem, or a symbol
    // that no definition names.
    let is_proof_goal = |name: &str| is_goal(name) || lookup(name).is_none();
    let context = ProofContext {
        lookup: &lookup,
        is_goal: &is_proof_goal,
        tables,
    };
    let theorems = module
        .theorems
        .iter()
        .map(|theorem| {
            let statement = match (&theorem.name, &theorem.statement) {
                (Some(_), Statement::Expression(_)) => theorem.statement.clone(),
                _ => context.statement(&theorem.statement)?,
            };
            Ok(Rc::new(Theorem {
                statement,
                proof: context.proof(theorem.proof.as_ref())?,
                ..(**theorem).clone()
            }))
        })
        .collect::<Result<Vec<_>>>()?;
    let uses = module
        .uses
        .iter()
        .map(|use_or_hide| {
            Ok(Rc::new(UseOrHide {
                facts: context.facts(&use_or_hide.facts)?,
                ..(**use_or_hide).clone()
            }))
        })
        .collect::<Result<Vec<_>>>()?;
    let has_references = module.definitions.iter().any(|definition| {
        contains_reference(&definition.body)
            || matches!(&definition.kind, DefinitionKind::Function { bounds }
                if bounds.iter().any(|bound| contains_reference(&bound.set)))
    }) || module
        .assumptions
        .iter()
        .any(|assumption| contains_reference(&assumption.expression));
    if !has_references {
        return Ok(Rc::new(Module {
            theorems,
            uses,
            ..(**module).clone()
        }));
    }
    let definitions = module
        .definitions
        .iter()
        .map(|definition| {
            map_definition(definition, tables, &mut |child, _| {
                resolve_subexpressions(child, &lookup, &is_goal, false, tables)
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let assumptions = module
        .assumptions
        .iter()
        .map(|assumption| {
            Ok(Rc::new(Assumption {
                expression: resolve_subexpressions(
                    &assumption.expression,
                    &lookup,
                    &is_goal,
                    false,
                    tables,
                )?,
                ..(**assumption).clone()
            }))
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(Rc::new(Module {
        theorems,
        uses,
        definitions,
        assumptions,
        ..(**module).clone()
    }))
}

struct ProofContext<'a> {
    lookup: &'a Lookup<'a>,
    is_goal: &'a dyn Fn(&str) -> bool,
    tables: &'a Tables,
}

impl ProofContext<'_> {
    fn expression(&self, expression: &Expr) -> Result<Expr> {
        resolve_subexpressions(expression, self.lookup, self.is_goal, false, self.tables)
    }

    fn facts(&self, facts: &[Fact]) -> Result<Vec<Fact>> {
        facts
            .iter()
            .map(|fact| {
                Ok(match fact {
                    Fact::Expression(expression) => Fact::Expression(self.expression(expression)?),
                    Fact::Module { .. } => fact.clone(),
                })
            })
            .collect()
    }

    fn bounds(&self, bounds: &[Bound]) -> Result<Vec<Bound>> {
        bounds
            .iter()
            .map(|bound| {
                Ok(Bound {
                    pattern: bound.pattern.clone(),
                    set: self.expression(&bound.set)?,
                })
            })
            .collect()
    }

    fn assume_prove(&self, assume_prove: &AssumeProve) -> Result<AssumeProve> {
        let assumptions = assume_prove
            .assumptions
            .iter()
            .map(|assumption| {
                Ok(match assumption {
                    Assumed::NewSymbol(symbol) => Assumed::NewSymbol(NewSymbol {
                        set: symbol
                            .set
                            .as_ref()
                            .map(|set| self.expression(set))
                            .transpose()?,
                        ..symbol.clone()
                    }),
                    Assumed::AssumeProve(inner) => Assumed::AssumeProve(self.assume_prove(inner)?),
                    Assumed::Expression(expression) => {
                        Assumed::Expression(self.expression(expression)?)
                    }
                })
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(AssumeProve {
            assumptions,
            conclusion: self.expression(&assume_prove.conclusion)?,
            location: assume_prove.location.clone(),
        })
    }

    fn statement(&self, statement: &Statement) -> Result<Statement> {
        Ok(match statement {
            Statement::AssumeProve(assume_prove) => {
                Statement::AssumeProve(self.assume_prove(assume_prove)?)
            }
            Statement::Expression(expression) => {
                Statement::Expression(self.expression(expression)?)
            }
        })
    }

    fn instance(&self, instance: &Rc<Instance>) -> Result<Rc<Instance>> {
        resolve_instance(instance, self.lookup, self.is_goal, self.tables)
    }

    fn step(&self, body: &StepBody) -> Result<StepBody> {
        Ok(match body {
            StepBody::UseOrHide(use_or_hide) => StepBody::UseOrHide(UseOrHide {
                facts: self.facts(&use_or_hide.facts)?,
                ..use_or_hide.clone()
            }),
            StepBody::Instance(instance) => StepBody::Instance(self.instance(instance)?),
            StepBody::Define {
                definitions,
                location,
            } => StepBody::Define {
                definitions: definitions
                    .iter()
                    .map(|definition| {
                        Ok(match definition {
                            DefinitionUnit::Instance(instance) => {
                                DefinitionUnit::Instance(self.instance(instance)?)
                            }
                            DefinitionUnit::Definition(definition) => DefinitionUnit::Definition(
                                map_definition(definition, self.tables, &mut |child, _| {
                                    self.expression(child)
                                })?,
                            ),
                        })
                    })
                    .collect::<Result<Vec<_>>>()?,
                location: location.clone(),
            },
            StepBody::Have(expression) => StepBody::Have(self.expression(expression)?),
            StepBody::Case(expression) => StepBody::Case(self.expression(expression)?),
            StepBody::Witness(expressions) => StepBody::Witness(
                expressions
                    .iter()
                    .map(|expression| self.expression(expression))
                    .collect::<Result<Vec<_>>>()?,
            ),
            StepBody::Take {
                names,
                name_ranges,
                bounds,
            } => StepBody::Take {
                names: names.clone(),
                name_ranges: name_ranges.clone(),
                bounds: self.bounds(bounds)?,
            },
            StepBody::Pick {
                names,
                name_ranges,
                bounds,
                body,
            } => StepBody::Pick {
                names: names.clone(),
                name_ranges: name_ranges.clone(),
                bounds: self.bounds(bounds)?,
                body: self.expression(body)?,
            },
            StepBody::Assert {
                is_suffices,
                statement,
            } => StepBody::Assert {
                is_suffices: *is_suffices,
                statement: self.statement(statement)?,
            },
            StepBody::Qed => StepBody::Qed,
        })
    }

    fn proof(&self, proof: Option<&Proof>) -> Result<Option<Proof>> {
        let Some(proof) = proof else {
            return Ok(None);
        };
        let kind = match &proof.kind {
            ProofKind::By {
                is_only,
                facts,
                defs,
                keyword,
            } => ProofKind::By {
                is_only: *is_only,
                facts: self.facts(facts)?,
                defs: defs.clone(),
                keyword: keyword.clone(),
            },
            ProofKind::Steps { level, steps } => ProofKind::Steps {
                level: *level,
                steps: steps
                    .iter()
                    .map(|step| {
                        Ok(ProofStep {
                            body: self.step(&step.body)?,
                            proof: self.proof(step.proof.as_deref())?.map(Box::new),
                            ..step.clone()
                        })
                    })
                    .collect::<Result<Vec<_>>>()?,
            },
            _ => return Ok(Some(proof.clone())),
        };
        Ok(Some(Proof {
            kind,
            location: proof.location.clone(),
        }))
    }
}

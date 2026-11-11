//! What TLCGet("spec") records of a specification besides its actions: the parts TLC's spec
//! processing finds, each with the name it gives the part and where the part is written, as
//! `getSpecDescription` in `spec-description.ts` describes them.

use std::rc::Rc;

use crate::ast::*;
use crate::config::ModelConfig;
use crate::dependencies::{DefinitionFacts, Level};
use crate::environment::Environment;
use crate::errors::FrontError;
use crate::eval::Evaluator;
use crate::resolve::Result;
use crate::spec::{
    Binding, Scope, ScopeOf, bind_definitions, bind_operator_arguments, get_definition, get_level,
    lookup_scope,
};

pub const UNNAMED_ACTION: &str = "UnnamedAction";

/// A part of the specification: the name TLC gives it, and where it is written.
pub struct Part {
    pub name: Name,
    pub location: Location,
    /// Whether a LET defines the part, which TLC names by the LET and takes whole.
    pub is_let: bool,
}

/// `SpecDescription`, without the actions, which the engine splits.
#[derive(Default)]
pub struct Description {
    pub inits: Vec<Part>,
    pub temporals: Vec<Part>,
    pub invariants: Vec<Part>,
    pub implied_inits: Vec<Part>,
    pub implied_actions: Vec<Part>,
    pub implied_temporals: Vec<Part>,
    pub variables: Vec<Part>,
    pub action_constraints: Vec<Part>,
    pub constraints: Vec<Part>,
}

/// An operator an expression applies (`resolveClosure`): its name, parameters, body and scope.
struct Closure {
    name: Name,
    params: Vec<OperatorParam>,
    body: Expr,
    scope: Option<Rc<Scope>>,
}

struct Describer<'a> {
    environment: &'a Environment,
    facts: &'a DefinitionFacts,
    evaluator: &'a Evaluator<'a>,
    description: Description,
}

fn part(name: &str, expression: &Expr) -> Part {
    Part {
        name: Rc::from(name),
        location: expression.location.clone(),
        is_let: false,
    }
}

/// `getSpecDescription` without the actions, and the variables and constraints
/// `getSpecificationValue` adds.
pub fn describe(
    config: &ModelConfig,
    environment: &Environment,
    facts: &DefinitionFacts,
    evaluator: &Evaluator,
) -> Result<Description> {
    let mut describer = Describer {
        environment,
        facts,
        evaluator,
        description: Description::default(),
    };
    if let Some(name) = &config.specification
        && let Some(definition) = describer.get_operator_definition(name)?
    {
        describer.describe_specification(&definition.body, None)?;
    }
    if let Some(name) = &config.init
        && let Some(definition) = get_definition(name, environment)
        && matches!(definition.kind, DefinitionKind::Operator { .. })
    {
        let init = part(name, &definition.body);
        describer.description.inits.push(init);
    }
    for name in &config.invariants {
        if let Some(definition) = describer.get_operator_definition(name)? {
            let invariant = part(name, &definition.body);
            describer.description.invariants.push(invariant);
        }
    }
    for name in &config.properties {
        if let Some(definition) = describer.get_operator_definition(name)? {
            describer.describe_property(name, &definition.body, None)?;
        }
    }
    let definitions = |describer: &Describer, names: &[String]| -> Result<Vec<Part>> {
        let mut parts = Vec::new();
        for name in names {
            if let Some(definition) = describer.get_operator_definition(name)? {
                parts.push(Part {
                    name: definition.name.clone(),
                    location: definition.location.clone(),
                    is_let: false,
                });
            }
        }
        Ok(parts)
    };
    describer.description.action_constraints = definitions(&describer, &config.action_constraints)?;
    describer.description.constraints = definitions(&describer, &config.constraints)?;
    describer.description.variables = environment
        .variables
        .iter()
        .zip(&environment.variable_locations)
        .map(|(name, location)| Part {
            name: name.clone(),
            location: location.clone(),
            is_let: false,
        })
        .collect();
    Ok(describer.description)
}

impl Describer<'_> {
    fn level(&self, expression: &Expr, scope: Option<&Rc<Scope>>) -> Level {
        get_level(expression, scope, self.environment, self.facts, &[])
    }

    // `isEvaluable`: whether the expression has a value, which the front end may not know.
    fn is_evaluable(&self, expression: &Expr) -> Result<bool> {
        match self.evaluator.evaluate(expression, None) {
            Ok(_) => Ok(true),
            Err(FrontError::Evaluation(_)) => Ok(false),
            Err(error) => Err(error),
        }
    }

    // `isConstantValue`.
    fn is_constant_value(&self, definition: &Rc<Definition>) -> Result<bool> {
        let is_operator = matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty());
        let is_literal = matches!(
            definition.body.kind,
            ExpressionKind::Number { .. } | ExpressionKind::String { .. }
        );
        if !is_operator || is_literal || !self.facts.is_constant_level(definition, self.environment)
        {
            return Ok(false);
        }
        self.is_evaluable(&definition.body)
    }

    // `getOperatorDefinition`.
    fn get_operator_definition(&self, name: &str) -> Result<Option<Rc<Definition>>> {
        let Some(definition) = get_definition(name, self.environment) else {
            return Ok(None);
        };
        if !matches!(definition.kind, DefinitionKind::Operator { .. })
            || self.is_constant_value(definition)?
        {
            return Ok(None);
        }
        Ok(Some(definition.clone()))
    }

    // `isConstantDefinition`.
    fn is_constant_definition(&self, closure: &Closure) -> Result<bool> {
        match get_definition(&closure.name, self.environment) {
            Some(definition) if Rc::ptr_eq(&definition.body, &closure.body) => {
                self.is_constant_value(definition)
            }
            _ => Ok(false),
        }
    }

    // `getThunk`: what a name a LET or an argument binds stands for.
    fn get_thunk(
        &self,
        expression: &Expr,
        scope: Option<&Rc<Scope>>,
    ) -> Option<(Expr, Option<Rc<Scope>>)> {
        if !matches!(expression.kind, ExpressionKind::Identifier { .. })
            || !expression.is_locally_resolved()
        {
            return None;
        }
        match lookup_scope(scope, &expression.reference()?) {
            Some((node, Binding::Thunk { expression, scope })) => {
                Some((expression.clone(), scope.resolve(node)))
            }
            _ => None,
        }
    }

    // `resolveClosure`.
    fn resolve_closure(&self, expression: &Expr, scope: Option<&Rc<Scope>>) -> Option<Closure> {
        if !matches!(
            expression.kind,
            ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. }
        ) {
            return None;
        }
        let name = expression.reference()?;
        if expression.is_locally_resolved() {
            return match lookup_scope(scope, &name) {
                Some((
                    node,
                    Binding::Closure {
                        name,
                        params,
                        body,
                        scope,
                    },
                )) => Some(Closure {
                    name: name.clone(),
                    params: params.clone(),
                    body: body.clone(),
                    scope: scope.resolve(node),
                }),
                _ => None,
            };
        }
        if self.environment.constants.contains_key(&name)
            || self.environment.variable_index.contains_key(&name)
        {
            return None;
        }
        let definition = get_definition(&name, self.environment)?;
        match &definition.kind {
            DefinitionKind::Operator { params, .. } => Some(Closure {
                name: definition.name.clone(),
                params: params.clone(),
                body: definition.body.clone(),
                scope: None,
            }),
            DefinitionKind::Function { .. } => None,
        }
    }

    fn arguments(expression: &Expr) -> &[Expr] {
        match &expression.kind {
            ExpressionKind::Apply { args, .. } => args,
            _ => &[],
        }
    }

    // `describeSpecification`, without the next-state relation, which the engine splits.
    fn describe_specification(
        &mut self,
        expression: &Expr,
        scope: Option<&Rc<Scope>>,
    ) -> Result<()> {
        if let ExpressionKind::Let {
            definitions, body, ..
        } = &expression.kind
        {
            let bound = bind_definitions(definitions, scope)?;
            return self.describe_specification(body, bound.as_ref());
        }
        if let Some((thunk, thunk_scope)) = self.get_thunk(expression, scope) {
            // TLC names a state predicate a LET defines by its name, where it's written.
            if let Some(name) = expression.reference()
                && let Some((
                    _,
                    Binding::Thunk {
                        scope: ScopeOf::Own,
                        ..
                    },
                )) = lookup_scope(scope, &name)
                && self.level(&thunk, thunk_scope.as_ref()) == Level::Variable
            {
                self.description.inits.push(Part {
                    is_let: true,
                    ..part(&name, &thunk)
                });
                return Ok(());
            }
            return self.describe_specification(&thunk, thunk_scope.as_ref());
        }
        let called = self.resolve_closure(expression, scope);
        if let Some(called) = &called {
            if self.is_constant_definition(called)? {
                return Ok(());
            }
            if called.params.is_empty() {
                if self.level(&called.body, called.scope.as_ref()) == Level::Variable {
                    let init = part(&called.name, &called.body);
                    self.description.inits.push(init);
                    return Ok(());
                }
                return self.describe_specification(&called.body, called.scope.as_ref());
            }
            let args = Self::arguments(expression);
            if matches!(expression.kind, ExpressionKind::Apply { .. })
                && called.params.len() == args.len()
            {
                let bound = bind_operator_arguments(
                    &called.params,
                    args,
                    called.scope.clone(),
                    scope,
                    self.environment,
                )?;
                return self.describe_specification(&called.body, bound.as_ref());
            }
        }
        match &expression.kind {
            ExpressionKind::Junction {
                is_and: true,
                operands,
                ..
            } => {
                for operand in operands {
                    self.describe_specification(operand, scope)?;
                }
                return Ok(());
            }
            ExpressionKind::Always(inner) => {
                if !matches!(inner.kind, ExpressionKind::Action { is_box: true, .. }) {
                    let temporal = part(UNNAMED_ACTION, expression);
                    self.description.temporals.push(temporal);
                }
                return Ok(());
            }
            _ => {}
        }
        match self.level(expression, scope) {
            Level::Constant | Level::Variable => {
                let init = part(UNNAMED_ACTION, expression);
                self.description.inits.push(init);
            }
            Level::Temporal => {
                let temporal = part(UNNAMED_ACTION, expression);
                self.description.temporals.push(temporal);
            }
            Level::Action => {}
        }
        Ok(())
    }

    // `describeProperty`.
    fn describe_property(
        &mut self,
        name: &str,
        expression: &Expr,
        scope: Option<&Rc<Scope>>,
    ) -> Result<()> {
        if let ExpressionKind::Let {
            definitions, body, ..
        } = &expression.kind
        {
            let bound = bind_definitions(definitions, scope)?;
            return self.describe_property(name, body, bound.as_ref());
        }
        if let Some((thunk, thunk_scope)) = self.get_thunk(expression, scope) {
            return self.describe_property(name, &thunk, thunk_scope.as_ref());
        }
        if let Some(called) = self.resolve_closure(expression, scope) {
            if self.is_constant_definition(&called)? {
                return Ok(());
            }
            let args = Self::arguments(expression);
            if called.params.len() == args.len() {
                let bound = if matches!(expression.kind, ExpressionKind::Apply { .. }) {
                    bind_operator_arguments(
                        &called.params,
                        args,
                        called.scope.clone(),
                        scope,
                        self.environment,
                    )?
                } else {
                    called.scope.clone()
                };
                return self.describe_property(name, &called.body, bound.as_ref());
            }
        }
        match &expression.kind {
            ExpressionKind::Quantified {
                quantifier: Quantifier::Forall,
                bounds,
                body,
            } => match self.evaluator.get_bindings(bounds, scope) {
                Ok(bindings) => {
                    for binding in bindings {
                        self.describe_property(name, body, binding.as_ref())?;
                    }
                    return Ok(());
                }
                Err(FrontError::Evaluation(_)) => {}
                Err(error) => return Err(error),
            },
            ExpressionKind::Junction {
                is_and: true,
                operands,
                ..
            } => {
                for operand in operands {
                    self.describe_property(name, operand, scope)?;
                }
                return Ok(());
            }
            ExpressionKind::Always(inner) => {
                let described = if matches!(inner.kind, ExpressionKind::Action { is_box: true, .. })
                {
                    (&mut self.description.implied_actions, inner)
                } else if self.level(inner, scope) < Level::Action {
                    (&mut self.description.invariants, inner)
                } else {
                    (&mut self.description.implied_temporals, expression)
                };
                described.0.push(part(name, described.1));
                return Ok(());
            }
            _ => {}
        }
        match self.level(expression, scope) {
            Level::Constant | Level::Variable => {
                self.description.implied_inits.push(part(name, expression));
            }
            Level::Temporal => {
                self.description
                    .implied_temporals
                    .push(part(name, expression));
            }
            Level::Action => {}
        }
        Ok(())
    }
}

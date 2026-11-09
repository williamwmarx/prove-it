//! What the model section of the IR reads of a spec before the search: the scopes an instance's
//! definitions are read in, and a formula's level, as `liveness.ts`'s `getLevel` computes it.

use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::*;
use crate::config::ConfigValue;
use crate::dependencies::{DefinitionFacts, Level};
use crate::environment::Environment;
use crate::errors::{FrontError, describe_range};
use crate::eval::Evaluator;
use crate::instances::map_children;
use crate::levels::{self, ACTION_LEVEL};
use crate::resolve::{Result, Tables};
use tla_ir::PredicateForm;

/// `Scope`: a name bound to a value, an expression or an operator, in front of the scope it
/// extends. The front end evaluates nothing, so a value is a literal or a configuration's.
pub struct Scope {
    pub name: Name,
    pub binding: Binding,
    pub parent: Option<Rc<Scope>>,
}

/// The scope a thunk or a closure is read in: a LET definition's is the node that binds it.
#[derive(Clone)]
pub enum ScopeOf {
    Own,
    Other(Option<Rc<Scope>>),
}

pub enum Binding {
    Value(ConfigValue),
    /// `Thunk`: an expression read in a scope.
    Thunk {
        expression: Expr,
        scope: ScopeOf,
    },
    /// An operator `Closure`.
    Closure {
        name: Name,
        params: Vec<OperatorParam>,
        body: Expr,
        scope: ScopeOf,
    },
}

impl ScopeOf {
    /// The scope this reads, from the node whose binding holds it.
    pub fn resolve(&self, node: &Rc<Scope>) -> Option<Rc<Scope>> {
        match self {
            ScopeOf::Own => Some(node.clone()),
            ScopeOf::Other(scope) => scope.clone(),
        }
    }
}

/// `lookupScope`: the binding of a name, with the node that holds it.
pub fn lookup_scope<'a>(
    mut scope: Option<&'a Rc<Scope>>,
    name: &str,
) -> Option<(&'a Rc<Scope>, &'a Binding)> {
    while let Some(current) = scope {
        if &*current.name == name {
            return Some((current, &current.binding));
        }
        scope = current.parent.as_ref();
    }
    None
}

/// `getDefinition`: a definition by name, through the model's substitutions.
pub fn get_definition<'a>(name: &str, environment: &'a Environment) -> Option<&'a Rc<Definition>> {
    let key = environment
        .substitutions
        .get(name)
        .map_or(name, |key| &**key);
    environment.definitions.get(key)
}

/// `getLevel` (`liveness.ts`): the level of a formula read in a scope, with the names a binder in
/// it shadows read as constants.
pub fn get_level(
    expression: &Expr,
    scope: Option<&Rc<Scope>>,
    environment: &Environment,
    facts: &DefinitionFacts,
    shadowed: &[Name],
) -> Level {
    let get_binding_level = |name: &str| {
        let (node, binding) = lookup_scope(scope, name)?;
        Some(match binding {
            Binding::Value(_) => Level::Constant,
            Binding::Thunk { expression, scope } => get_level(
                expression,
                scope.resolve(node).as_ref(),
                environment,
                facts,
                &[],
            ),
            Binding::Closure { body, scope, .. } => {
                get_level(body, scope.resolve(node).as_ref(), environment, facts, &[])
            }
        })
    };
    let get_global_level = |name: &str| {
        if environment.variable_index.contains_key(name) {
            return Some(Level::Variable);
        }
        if environment.constants.contains_key(name) {
            return Some(Level::Constant);
        }
        if let Some(definition) = get_definition(name, environment) {
            return Some(facts.get_definition_level(definition, environment));
        }
        let key = environment
            .substitutions
            .get(name)
            .map_or(name, |key| &**key);
        let builtin = environment.builtins.get(key)?;
        Some(if builtin.flags & 1 != 0 && builtin.flags & 2 == 0 {
            Level::Variable
        } else {
            Level::Constant
        })
    };
    let get_name_level = |node: &Expr| {
        let name = node.reference().unwrap_or_default();
        if shadowed.contains(&name) {
            return Level::Constant;
        }
        if node.is_locally_resolved() {
            get_binding_level(&name)
                .or_else(|| get_global_level(&name))
                .unwrap_or(Level::Constant)
        } else {
            get_global_level(&name)
                .or_else(|| get_binding_level(&name))
                .unwrap_or(Level::Constant)
        }
    };
    let get_children_level = |node: &Expr| {
        let mut level = Level::Constant;
        let tables = Tables::default();
        let _ = map_children(node, &tables, &mut |child, bound| {
            let child_level = if bound.is_empty() {
                get_level(child, scope, environment, facts, shadowed)
            } else {
                let shadowed: Vec<Name> = shadowed.iter().chain(bound).cloned().collect();
                get_level(child, scope, environment, facts, &shadowed)
            };
            level = level.max(child_level);
            Ok(child.clone())
        });
        level
    };
    match &expression.kind {
        ExpressionKind::Prime(_) | ExpressionKind::Unchanged(_) | ExpressionKind::Action { .. } => {
            Level::Action
        }
        ExpressionKind::Enabled(_) => Level::Variable,
        ExpressionKind::Always(_)
        | ExpressionKind::Eventually(_)
        | ExpressionKind::Fairness { .. } => Level::Temporal,
        ExpressionKind::UnboundedQuantifier {
            is_temporal: true, ..
        } => Level::Temporal,
        ExpressionKind::Identifier { .. } | ExpressionKind::OperatorReference { .. } => {
            get_name_level(expression)
        }
        ExpressionKind::Apply { operator, .. } => match &**operator {
            "~>" | "-+->" => Level::Temporal,
            "\\cdot" => Level::Action,
            _ => get_name_level(expression).max(get_children_level(expression)),
        },
        _ => get_children_level(expression),
    }
}

/// What `expandTemporal` gives: a conjunct with the scope it reads and the name TLC gives it.
pub struct Expanded {
    pub expression: Expr,
    pub scope: Option<Rc<Scope>>,
    pub name: Option<Name>,
}

/// `getSpecification`: the initial predicate, the next-state action, the scope they read, and
/// the temporal conjuncts of the specification.
pub struct Specification {
    pub init: Option<Expr>,
    pub next: Option<Expr>,
    pub scope: Option<Rc<Scope>>,
    pub temporals: Vec<Expanded>,
}

const START: Location = Location {
    line: 0,
    column: 0,
    range: None,
};

/// `createIdentifier`.
pub fn create_identifier(name: &str) -> Expr {
    Rc::new(Expression::new(
        ExpressionKind::Identifier {
            name: Rc::from(name),
            spelling: None,
            selector_ranges: None,
        },
        START,
    ))
}

fn not_yet(reason: &str) -> FrontError {
    FrontError::NotYet(reason.to_owned())
}

/// What `expandTemporal` reads.
pub struct Expansion<'a> {
    pub environment: &'a Environment,
    pub facts: &'a DefinitionFacts,
    pub version: TlcVersion,
    /// Whether TLC expands the formula as a property, which unrolls each \A over a constant set.
    pub is_property: bool,
    /// Whether the formula is the specification's, of which TLC keeps a definition that is a
    /// state predicate whole, as one initial predicate (`SpecProcessor.processConfigSpec`).
    pub is_specification: bool,
    /// What computes the sets a property's \A ranges over, without which it is `NotYet`.
    pub evaluator: Option<&'a Evaluator<'a>>,
}

impl Expansion<'_> {
    fn level(&self, expression: &Expr, scope: Option<&Rc<Scope>>) -> Level {
        get_level(expression, scope, self.environment, self.facts, &[])
    }

    fn is_substituted(&self, definition: &Rc<Definition>) -> bool {
        self.environment.is_substituted(definition)
    }

    /// `expandTemporal`.
    pub fn expand(
        &self,
        expression: &Expr,
        scope: Option<&Rc<Scope>>,
        expanding: &[*const Definition],
        is_substituted: bool,
        name: Option<Name>,
    ) -> Result<Vec<Expanded>> {
        match &expression.kind {
            ExpressionKind::Junction {
                is_and: true,
                operands,
                ..
            } => {
                let mut expanded = Vec::new();
                for operand in operands {
                    let name = Some(Rc::from(describe_range(operand)));
                    expanded.extend(self.expand(
                        operand,
                        scope,
                        expanding,
                        is_substituted,
                        name,
                    )?);
                }
                return Ok(expanded);
            }
            ExpressionKind::Label { body, .. } => {
                return self.expand(body, scope, expanding, is_substituted, name);
            }
            ExpressionKind::Let {
                definitions, body, ..
            } => {
                let bound = bind_definitions(definitions, scope)?;
                return self.expand(body, bound.as_ref(), expanding, is_substituted, name);
            }
            ExpressionKind::Identifier { name: written, .. } => {
                let reference = expression.reference().unwrap_or_default();
                let binding = if expression.is_locally_resolved() {
                    lookup_scope(scope, &reference)
                } else {
                    None
                };
                if let Some((node, Binding::Thunk { expression, scope })) = binding {
                    let scope = scope.resolve(node);
                    return self.expand(
                        expression,
                        scope.as_ref(),
                        expanding,
                        is_substituted,
                        name,
                    );
                }
                let definition = if self.environment.constants.contains_key(&reference) {
                    None
                } else {
                    get_definition(&reference, self.environment)
                };
                if let Some(definition) = definition.filter(|definition| {
                    binding.is_none()
                        && matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                        && self.facts.get_definition_level(definition, self.environment)
                            > Level::Constant
                }) {
                    if expanding.contains(&Rc::as_ptr(definition)) {
                        // TLC recurses until its stack overflows.
                        return Err(FrontError::StackOverflow);
                    }
                    if self.is_specification
                        && self.facts.get_definition_level(definition, self.environment)
                            == Level::Variable
                    {
                        return Ok(vec![Expanded {
                            expression: definition.body.clone(),
                            scope: None,
                            name: Some(written.clone()),
                        }]);
                    }
                    let expanding = [expanding, &[Rc::as_ptr(definition)]].concat();
                    return self.expand(
                        &definition.body,
                        None,
                        &expanding,
                        is_substituted || self.is_substituted(definition),
                        // `opNode.getName()`: the name as written, `A!Safe` for an instance's.
                        Some(written.clone()),
                    );
                }
            }
            ExpressionKind::Apply { operator, args, .. }
                if self.version != TlcVersion::V1_7_4
                    && (self.is_property || self.level(expression, scope) == Level::Temporal) =>
            {
                let definition = if expression.is_locally_resolved() {
                    None
                } else {
                    get_definition(operator, self.environment)
                };
                if let Some((params, body, closure_scope)) =
                    resolve_apply_operator(expression, scope, self.environment)
                    && params.len() == args.len()
                    && !definition.is_some_and(|definition| definition.is_recursive)
                    && !is_substituted
                {
                    let bound = bind_operator_arguments(
                        &params,
                        args,
                        closure_scope,
                        scope,
                        self.environment,
                    )?;
                    return self.expand(
                        &body,
                        bound.as_ref(),
                        expanding,
                        is_substituted
                            || definition.is_some_and(|definition| self.is_substituted(definition)),
                        // An instance copy's application is named by its key.
                        Some(expression.reference().unwrap_or_else(|| operator.clone())),
                    );
                }
            }
            // TLC unrolls a property's \A over constant sets, and stops at a tautology.
            ExpressionKind::Quantified {
                quantifier: Quantifier::Forall,
                bounds,
                body,
            } if self.is_property
                && bounds
                    .iter()
                    .all(|bound| self.level(&bound.set, scope) == Level::Constant) =>
            {
                let Some(evaluator) = self.evaluator else {
                    return Err(not_yet("a property's \\A that TLC unrolls"));
                };
                let mut expanded = Vec::new();
                for binding in evaluator.get_bindings(bounds, scope)? {
                    expanded.extend(self.expand(
                        body,
                        binding.as_ref(),
                        expanding,
                        is_substituted,
                        Some(Rc::from(describe_range(body))),
                    )?);
                }
                if expanded.is_empty() {
                    return Err(not_yet("a property TLC finds a tautology"));
                }
                return Ok(expanded);
            }
            _ => {}
        }
        Ok(vec![Expanded {
            expression: expression.clone(),
            scope: scope.cloned(),
            name,
        }])
    }
}

/// `bindDefinitions`, for a LET, where each definition reads the scope that binds it.
pub(crate) fn bind_definitions(
    definitions: &[Rc<Definition>],
    scope: Option<&Rc<Scope>>,
) -> Result<Option<Rc<Scope>>> {
    let mut bound = scope.cloned();
    for definition in definitions {
        let binding = match &definition.kind {
            DefinitionKind::Function { .. } => {
                return Err(not_yet("a LET function in a temporal formula"));
            }
            DefinitionKind::Operator { params, .. } if !params.is_empty() => Binding::Closure {
                name: definition.name.clone(),
                params: params.clone(),
                body: definition.body.clone(),
                scope: ScopeOf::Own,
            },
            DefinitionKind::Operator { .. } => Binding::Thunk {
                expression: definition.body.clone(),
                scope: ScopeOf::Own,
            },
        };
        bound = Some(Rc::new(Scope {
            name: definition.name.clone(),
            binding,
            parent: bound,
        }));
    }
    Ok(bound)
}

/// `resolveApplyOperator`, for a closure: its parameters, body and scope.
pub(crate) fn resolve_apply_operator(
    expression: &Expr,
    scope: Option<&Rc<Scope>>,
    environment: &Environment,
) -> Option<(Vec<OperatorParam>, Expr, Option<Rc<Scope>>)> {
    let name = expression.reference()?;
    let local = || match lookup_scope(scope, &name) {
        Some((
            node,
            Binding::Closure {
                params,
                body,
                scope,
                ..
            },
        )) => Some((params.clone(), body.clone(), scope.resolve(node))),
        _ => None,
    };
    let global = || {
        let definition = get_definition(&name, environment)?;
        match &definition.kind {
            DefinitionKind::Operator { params, .. } => {
                Some((params.clone(), definition.body.clone(), None))
            }
            DefinitionKind::Function { .. } => None,
        }
    };
    if expression.is_locally_resolved() {
        local()
    } else {
        global().or_else(local)
    }
}

/// `bindOperatorArguments`: each parameter bound as `compileArgumentBinder` binds it.
pub(crate) fn bind_operator_arguments(
    params: &[OperatorParam],
    args: &[Expr],
    closure_scope: Option<Rc<Scope>>,
    scope: Option<&Rc<Scope>>,
    environment: &Environment,
) -> Result<Option<Rc<Scope>>> {
    let mut bound = closure_scope;
    for (param, argument) in params.iter().zip(args) {
        if param.arity > 0 {
            bound = Some(Rc::new(Scope {
                name: param.name.clone(),
                binding: bind_operator_argument(argument, scope, environment)?,
                parent: bound,
            }));
            continue;
        }
        let thunk = || Binding::Thunk {
            expression: argument.clone(),
            scope: ScopeOf::Other(scope.cloned()),
        };
        let binding = match &argument.kind {
            ExpressionKind::String { value } => {
                Binding::Value(ConfigValue::String(value.to_string()))
            }
            ExpressionKind::Number { value, .. } if is_tlc_integer(*value) => {
                Binding::Value(ConfigValue::Number(*value))
            }
            ExpressionKind::Identifier { .. } => {
                let reference = argument.reference().unwrap_or_default();
                let global = if argument.is_locally_resolved() {
                    None
                } else {
                    find_global_name(&reference, environment)?
                };
                match global {
                    Some(GlobalName::Value(value)) => Binding::Value(value),
                    Some(GlobalName::Other) => thunk(),
                    None => match lookup_scope(scope, &reference) {
                        Some((_, Binding::Value(value))) => Binding::Value(value.clone()),
                        Some((node, Binding::Thunk { expression, scope })) => Binding::Thunk {
                            expression: expression.clone(),
                            scope: ScopeOf::Other(scope.resolve(node)),
                        },
                        _ => thunk(),
                    },
                }
            }
            _ => thunk(),
        };
        bound = Some(Rc::new(Scope {
            name: param.name.clone(),
            binding,
            parent: bound,
        }));
    }
    Ok(bound)
}

/// `evaluateOperatorArgument`: a LAMBDA, or the operator an argument names, as a closure.
fn bind_operator_argument(
    argument: &Expr,
    scope: Option<&Rc<Scope>>,
    environment: &Environment,
) -> Result<Binding> {
    let not_closure = || not_yet("an operator argument that isn't a definition");
    let name = match &argument.kind {
        ExpressionKind::Lambda { params, body, .. } => {
            return Ok(Binding::Closure {
                name: Rc::from("LAMBDA"),
                params: params
                    .iter()
                    .map(|name| OperatorParam {
                        name: name.clone(),
                        arity: 0,
                        location: None,
                    })
                    .collect(),
                body: body.clone(),
                scope: ScopeOf::Other(scope.cloned()),
            });
        }
        ExpressionKind::OperatorReference { .. } | ExpressionKind::Identifier { .. } => {
            argument.reference().ok_or_else(not_closure)?
        }
        _ => return Err(not_closure()),
    };
    if argument.is_locally_resolved() || get_definition(&name, environment).is_none() {
        return match lookup_scope(scope, &name) {
            Some((
                node,
                Binding::Closure {
                    name,
                    params,
                    body,
                    scope,
                },
            )) => Ok(Binding::Closure {
                name: name.clone(),
                params: params.clone(),
                body: body.clone(),
                scope: ScopeOf::Other(scope.resolve(node)),
            }),
            _ => Err(not_closure()),
        };
    }
    match get_definition(&name, environment).map(|definition| (definition, &definition.kind)) {
        Some((definition, DefinitionKind::Operator { params, .. })) => Ok(Binding::Closure {
            name: definition.name.clone(),
            params: params.clone(),
            body: definition.body.clone(),
            scope: ScopeOf::Other(None),
        }),
        _ => Err(not_closure()),
    }
}

enum GlobalName {
    Value(ConfigValue),
    Other,
}

/// `findGlobalName`, for an argument: a configuration's value, or something else global.
fn find_global_name(name: &str, environment: &Environment) -> Result<Option<GlobalName>> {
    if environment.variable_index.contains_key(name) {
        return Ok(Some(GlobalName::Other));
    }
    if let Some(value) = environment.constants.get(name) {
        return Ok(Some(GlobalName::Value(value.clone())));
    }
    if let Some(target) = environment.substitutions.get(name) {
        return find_global_name(target, environment);
    }
    if environment.definitions.contains_key(name) {
        return Ok(Some(GlobalName::Other));
    }
    match environment.builtins.get(name) {
        Some(builtin) if builtin.arity == 0 && builtin.flags & 1 == 0 => match name {
            "TRUE" => Ok(Some(GlobalName::Value(ConfigValue::Boolean(true)))),
            "FALSE" => Ok(Some(GlobalName::Value(ConfigValue::Boolean(false)))),
            _ => Err(not_yet(
                "a builtin's value as an argument to a temporal formula",
            )),
        },
        _ => Ok(None),
    }
}

fn is_tlc_integer(value: f64) -> bool {
    value.fract() == 0.0 && value >= f64::from(i32::MIN) && value <= f64::from(i32::MAX)
}

/// `getConfigOperator`: the definition the configuration names, without arguments.
fn get_config_operator<'a>(
    kind: &str,
    name: &str,
    environment: &'a Environment,
) -> Result<&'a Rc<Definition>> {
    let Some(definition) = get_definition(name, environment) else {
        return Err(FrontError::Config(format!(
            "The {kind} {name} specified in the configuration file\nis not defined in the specification."
        )));
    };
    if matches!(&definition.kind, DefinitionKind::Operator { params, .. } if !params.is_empty()) {
        return Err(FrontError::Config(
            if kind == "name" || kind == "property" {
                format!("TLC requires {name} not to take any argument.")
            } else {
                format!("TLC requires {kind} not to take any argument, but one was given: {name}")
            },
        ));
    }
    Ok(definition)
}

/// `getConstantValue`: the value TLC computed at startup for a constant definition, or none for
/// a literal, which stays an operator, or a definition that fails to evaluate.
fn get_constant_value(
    name: &str,
    definition: &Rc<Definition>,
    environment: &Environment,
    facts: &DefinitionFacts,
    evaluator: Option<&Evaluator>,
    is_deferrable: bool,
) -> Result<Option<ConfigValue>> {
    let is_literal = matches!(
        definition.body.kind,
        ExpressionKind::Number { .. } | ExpressionKind::String { .. }
    );
    if !facts.is_constant_level(definition, environment) || is_literal {
        return Ok(None);
    }
    let Some(evaluator) = evaluator else {
        return Err(not_yet("a constant definition the configuration names"));
    };
    match evaluator.evaluate(&create_identifier(name), None) {
        Ok(value) => Ok(Some(value)),
        Err(FrontError::Evaluation(_)) => Ok(None),
        // The engine's startup checks what the evaluator can't compute (`Startup::predicates`).
        // TLC rejects any value of a definition that isn't a predicate, which the front end then
        // can't tell from one that fails to evaluate.
        Err(FrontError::NotYet(_)) if is_deferrable => {
            evaluator.defer();
            Ok(None)
        }
        Err(error) => Err(error),
    }
}

/// `formatValue` of the values TLC's configuration errors show, or `NotYet` for another.
fn format_config_value(value: &ConfigValue) -> Result<String> {
    match value {
        ConfigValue::Boolean(value) => Ok(if *value { "TRUE" } else { "FALSE" }.to_owned()),
        ConfigValue::Number(number) if number.fract() == 0.0 => Ok(format!("{number}")),
        _ => Err(not_yet("a configuration error that shows a value")),
    }
}

/// `isConstantTrue`, for a conjunct that is a constant name: TLC drops one that is TRUE, and
/// rejects the spec for any other value.
fn is_constant_true(
    name: &str,
    item: &Expanded,
    usage: &str,
    evaluator: Option<&Evaluator>,
) -> Result<bool> {
    let evaluator = evaluator.ok_or_else(|| not_yet("a constant conjunct of the specification"))?;
    match evaluator.evaluate(&item.expression, item.scope.as_ref())? {
        ConfigValue::Boolean(true) => Ok(true),
        ConfigValue::Boolean(false) => Err(FrontError::Config(format!(
            "The spec is trivially false because {name} is false."
        ))),
        value => Err(FrontError::Config(format!(
            "The operator {name}, which equals {},\ncannot be used as a {usage}",
            format_config_value(&value)?
        ))),
    }
}

/// `getConfigDefinition`.
fn get_config_definition(
    kind: &str,
    name: &str,
    environment: &Environment,
    facts: &DefinitionFacts,
    evaluator: Option<&Evaluator>,
) -> Result<()> {
    let definition = get_config_operator(kind, name, environment)?;
    if get_constant_value(name, definition, environment, facts, evaluator, false)?.is_some() {
        return Err(FrontError::Config(format!(
            "The {kind} {name} cannot be a constant."
        )));
    }
    Ok(())
}

/// Where the configuration's SPECIFICATION reaches its next-state relation through a definition an
/// INSTANCE with substitutions copies, the location of the first such INSTANCE on the way to
/// `[][Next]_v`: TLC then takes the whole relation as one unnamed action there
/// (`describeSpecification` in `spec-description.ts`). None for a model without one, or whose
/// specification reaches its next-state relation directly.
pub fn get_next_substitution(
    config: &crate::config::ModelConfig,
    environment: &Environment,
    facts: &DefinitionFacts,
) -> Result<Option<Location>> {
    let Some(name) = &config.specification else {
        return Ok(None);
    };
    let Some(definition) = get_definition(name, environment) else {
        return Ok(None);
    };
    let key = environment
        .root_symbols
        .get(name.as_str())
        .map_or_else(|| name.as_str().into(), |symbol| symbol.key.clone());
    let substitution = environment
        .instance_actions
        .get(&key)
        .map(|action| action.location.clone());
    let mut found = None;
    find_next(
        &definition.body,
        None,
        substitution,
        environment,
        facts,
        &mut found,
    )?;
    Ok(found.flatten())
}

// The next-state relation `describeSpecification` finds in a specification, with the substitution
// it reaches it through: the first it finds, as TLC allows one.
fn find_next(
    expression: &Expr,
    scope: Option<&Rc<Scope>>,
    substitution: Option<Location>,
    environment: &Environment,
    facts: &DefinitionFacts,
    found: &mut Option<Option<Location>>,
) -> Result<()> {
    if found.is_some() {
        return Ok(());
    }
    let recurse = |inner: &Expr, inner_scope: Option<&Rc<Scope>>, substitution, found: &mut _| {
        find_next(inner, inner_scope, substitution, environment, facts, found)
    };
    match &expression.kind {
        ExpressionKind::Let {
            definitions, body, ..
        } => {
            let bound = bind_definitions(definitions, scope)?;
            return recurse(body, bound.as_ref(), substitution, found);
        }
        ExpressionKind::Label { body, .. } => return recurse(body, scope, substitution, found),
        ExpressionKind::Junction {
            is_and: true,
            operands,
            ..
        } => {
            for operand in operands {
                recurse(operand, scope, substitution.clone(), found)?;
            }
            return Ok(());
        }
        ExpressionKind::Always(inner) => {
            if matches!(inner.kind, ExpressionKind::Action { is_box: true, .. }) {
                *found = Some(substitution);
            }
            return Ok(());
        }
        _ => {}
    }
    if expression.is_locally_resolved()
        && let Some(name) = expression.reference()
        && let Some((
            node,
            Binding::Thunk {
                expression: bound,
                scope: bound_scope,
            },
        )) = lookup_scope(scope, &name)
    {
        let bound_scope = bound_scope.resolve(node);
        return recurse(bound, bound_scope.as_ref(), substitution, found);
    }
    let args: &[Expr] = match &expression.kind {
        ExpressionKind::Apply { args, .. } => args,
        ExpressionKind::Identifier { .. } => &[],
        _ => return Ok(()),
    };
    let Some(name) = expression.reference() else {
        return Ok(());
    };
    if !expression.is_locally_resolved()
        && (environment.constants.contains_key(&name)
            || environment.variable_index.contains_key(&name))
    {
        return Ok(());
    }
    let Some((params, body, closure_scope)) =
        resolve_apply_operator(expression, scope, environment)
    else {
        return Ok(());
    };
    if params.is_empty() {
        // A definition of constant level holds no next-state relation, and one of variable
        // level is an initial predicate.
        if get_level(&body, closure_scope.as_ref(), environment, facts, &[]) <= Level::Variable {
            return Ok(());
        }
        let instance = (!expression.is_locally_resolved())
            .then(|| environment.instance_actions.get(&name))
            .flatten()
            .map(|action| action.location.clone());
        return recurse(
            &body,
            closure_scope.as_ref(),
            substitution.or(instance),
            found,
        );
    }
    if params.len() != args.len() {
        return Ok(());
    }
    let bound = bind_operator_arguments(&params, args, closure_scope, scope, environment)?;
    recurse(&body, bound.as_ref(), substitution, found)
}

/// `getInvariants` (`search.ts`): TLC's checks of the invariants the configuration names, which
/// it makes before it reads the specification. It returns the invariants that are constants equal
/// to TRUE, which TLC warns about, or none where the engine checks one the evaluator can't compute.
pub fn check_invariants(
    config: &crate::config::ModelConfig,
    environment: &Environment,
    facts: &DefinitionFacts,
    evaluator: &Evaluator,
) -> Result<Option<Vec<Name>>> {
    let analyzer = environment.create_level_analyzer(&[]);
    let mut constant_true = Vec::new();
    for name in &config.invariants {
        let Some(definition) =
            get_config_predicate("invariant", name, environment, facts, Some(evaluator))?
        else {
            constant_true.push(Rc::from(name.as_str()));
            continue;
        };
        let levels = analyzer.analyze_definition(definition, &levels::Scope::default())?;
        if levels.data.level >= ACTION_LEVEL {
            // SANY's level check can give a definition levels of parameters it doesn't have
            // (LevelNode.java, 590ff), which TLC notes.
            let note = if levels.data.has_params() {
                "\nNote that a bug can cause TLC to incorrectly report this error.\nIf you believe your TLA+ or PlusCal specification to be correct,\nplease check if this bug described in LevelNode.java starting at line 590ff affects you."
            } else {
                ""
            };
            return Err(FrontError::Config(format!(
                "The invariant {name} is not a state predicate (one with no primes or temporal operators).{note}"
            )));
        }
    }
    Ok((!evaluator.is_deferring()).then_some(constant_true))
}

/// `getSpecification` (`search.ts`).
pub fn get_specification(
    config: &crate::config::ModelConfig,
    environment: &Environment,
    facts: &DefinitionFacts,
    version: TlcVersion,
    evaluator: Option<&Evaluator>,
) -> Result<Specification> {
    let Some(specification) = &config.specification else {
        let operator = |name: &Option<String>, description: &str| {
            name.as_deref()
                .map(|name| {
                    get_config_definition(description, name, environment, facts, None)
                        .map(|()| create_identifier(name))
                })
                .transpose()
        };
        return Ok(Specification {
            init: operator(&config.init, "initial predicate")?,
            next: operator(&config.next, "next state action")?,
            scope: None,
            temporals: Vec::new(),
        });
    };
    if config.init.is_some() || config.next.is_some() {
        return Err(FrontError::Config(
            "The configuration file cannot specify both INIT/NEXT and SPECIFICATION fields."
                .to_owned(),
        ));
    }
    let definition = get_config_operator("name", specification, environment)?;
    if let Some(value) = get_constant_value(
        specification,
        definition,
        environment,
        facts,
        evaluator,
        false,
    )? {
        return Err(FrontError::Config(format!(
            "The value of {specification} is equal to {}",
            format_config_value(&value)?
        )));
    }
    let expansion = Expansion {
        environment,
        facts,
        version,
        is_property: false,
        is_specification: true,
        evaluator: None,
    };
    let mut init_conjuncts = Vec::new();
    let mut next_actions = Vec::new();
    let mut temporals = Vec::new();
    for item in expansion.expand(&definition.body, None, &[], false, None)? {
        let level = || {
            get_level(
                &item.expression,
                item.scope.as_ref(),
                environment,
                facts,
                &[],
            )
        };
        match &item.expression.kind {
            ExpressionKind::Identifier { name, .. }
                if level() == Level::Constant
                    && is_constant_true(name, &item, "spec", evaluator)? =>
            {
                continue;
            }
            ExpressionKind::UnboundedQuantifier {
                is_temporal: true, ..
            } => return Err(not_yet("temporal quantification in the specification")),
            ExpressionKind::Always(inner) => match &inner.kind {
                ExpressionKind::Action {
                    is_box: true,
                    action,
                    ..
                } => {
                    next_actions.push((action.clone(), item.scope.clone()));
                    continue;
                }
                _ if get_level(inner, item.scope.as_ref(), environment, facts, &[])
                    < Level::Action =>
                {
                    // TLC accepts the spec and fails when it builds the tableau of the temporal
                    // formulas.
                    return Err(FrontError::Evaluation(format!(
                        "TLC cannot handle the temporal formula {}",
                        describe_range(inner)
                    )));
                }
                _ => {}
            },
            _ => {}
        }
        match level() {
            Level::Temporal => temporals.push(item),
            Level::Action => {
                return Err(FrontError::Config(format!(
                    "TLC cannot handle the action-level conjunct of the specification {specification}"
                )));
            }
            _ => init_conjuncts.push((item.expression, item.scope)),
        }
    }
    if next_actions.len() > 1 {
        return Err(FrontError::Config(format!(
            "The specification {specification} must contain at most one [][Next]_vars"
        )));
    }
    let items: Vec<&(Expr, Option<Rc<Scope>>)> =
        init_conjuncts.iter().chain(&next_actions).collect();
    let get_name = |index: usize| -> Name { Rc::from(format!("$specification{index}")) };
    let scope = items
        .iter()
        .enumerate()
        .fold(None, |parent, (index, (expression, scope))| match scope {
            None => parent,
            Some(scope) => Some(Rc::new(Scope {
                name: get_name(index),
                binding: Binding::Thunk {
                    expression: expression.clone(),
                    scope: ScopeOf::Other(Some(scope.clone())),
                },
                parent,
            })),
        });
    let get_reference = |index: usize| -> Expr {
        let (expression, scope) = items[index];
        if scope.is_none() {
            return expression.clone();
        }
        let reference = Expression::new(
            ExpressionKind::Identifier {
                name: get_name(index),
                spelling: None,
                selector_ranges: None,
            },
            expression.location.clone(),
        );
        reference.resolved.is_local.set(true);
        Rc::new(reference)
    };
    Ok(Specification {
        init: (!init_conjuncts.is_empty()).then(|| {
            Rc::new(Expression::new(
                ExpressionKind::Junction {
                    is_and: true,
                    operands: (0..init_conjuncts.len()).map(get_reference).collect(),
                    is_bulleted: false,
                    prefix_ends: None,
                },
                START,
            ))
        }),
        next: (!next_actions.is_empty()).then(|| get_reference(init_conjuncts.len())),
        scope,
        temporals,
    })
}

/// A conjunct of a property, with the name TLC gives it and the scope it reads.
pub struct Property {
    pub name: Name,
    pub expression: Expr,
    pub scope: Option<Rc<Scope>>,
}

/// `[][A]_v` in a property, which TLC checks of each step.
pub struct ActionProperty {
    pub name: Name,
    pub action: Expr,
    pub subscript: Expr,
    pub scope: Option<Rc<Scope>>,
}

/// `getProperties` (`search.ts`).
#[derive(Default)]
pub struct Properties {
    pub initial_predicates: Vec<Property>,
    pub invariants: Vec<Property>,
    pub action_properties: Vec<ActionProperty>,
    pub liveness: Vec<Property>,
    /// The properties TLC warns are state formulas, which it checks only on the initial states.
    pub state_level: Vec<Name>,
}

/// `getConfigPredicate`: the definition of what the configuration names, or none for a constant
/// whose value is TRUE.
fn get_config_predicate<'a>(
    kind: &str,
    name: &str,
    environment: &'a Environment,
    facts: &DefinitionFacts,
    evaluator: Option<&Evaluator>,
) -> Result<Option<&'a Rc<Definition>>> {
    let (definition, value) = match environment.constants.get(name) {
        Some(value) => (None, Some(value.clone())),
        None => {
            let definition = get_config_operator(kind, name, environment)?;
            let value = get_constant_value(name, definition, environment, facts, evaluator, true)?;
            (Some(definition), value)
        }
    };
    match value {
        None => Ok(definition),
        Some(ConfigValue::Boolean(true)) => Ok(None),
        Some(value) => Err(FrontError::Config(format!(
            "The {kind} of {name} is equal to {}",
            format_config_value(&value)?
        ))),
    }
}

const BOOK: &str = "https://lamport.azurewebsites.net/tla/book.html";

/// `getActionPropertyMessage`: TLC's error for a property that is an action, which says how to
/// make `[A]_v`, `<<A>>_v` or another action a temporal formula.
fn get_action_property_message(name: &str, conjunct: &Expr) -> String {
    let at = describe_range(conjunct);
    let advice = match conjunct.kind {
        ExpressionKind::Action { is_box: true, .. } => format!(
            "To check that action {name} holds in *every* step of the behavior, define a temporal property by applying the \"always\" temporal operator ([]) to the formula at {at} (compare page 90 of Specifying Systems at {BOOK})."
        ),
        ExpressionKind::Action { is_box: false, .. } => format!(
            "To check that infinitely many {name} steps occur, define a temporal property by applying the \"always eventually\" temporal operator combination ([]<>) to the formula at {at} (compare page 91 of Specifying Systems at {BOOK})."
        ),
        _ => format!(
            "To check that action {name} holds in *every* step of the behavior, define a temporal property: Let A be the formula at {at}; rewrite A as [][A]_v, where v is a state function (typically the tuple of variables) (compare page 90 of Specifying Systems at {BOOK})."
        ),
    };
    format!(
        "The formula {name} at {at} is an action-level formula (i.e., it contains no temporal operators). Only temporal-level (or state-level) formulas are allowed under PROPERTY or PROPERTIES. {advice}"
    )
}

pub fn get_properties(
    config: &crate::config::ModelConfig,
    environment: &Environment,
    facts: &DefinitionFacts,
    version: TlcVersion,
    evaluator: Option<&Evaluator>,
) -> Result<Properties> {
    let mut properties = Properties::default();
    let expansion = Expansion {
        environment,
        facts,
        version,
        is_property: version != TlcVersion::V1_7_4,
        is_specification: false,
        evaluator,
    };
    for name in &config.properties {
        let Some(definition) =
            get_config_predicate("property", name, environment, facts, evaluator)?
        else {
            continue;
        };
        let name: Name = Rc::from(name.as_str());
        if get_level(&definition.body, None, environment, facts, &[]) == Level::Variable {
            properties.state_level.push(name.clone());
        }
        for item in expansion.expand(&definition.body, None, &[], false, None)? {
            let level = |expression: &Expr| {
                get_level(expression, item.scope.as_ref(), environment, facts, &[])
            };
            let conjunct = &item.expression;
            if let ExpressionKind::Identifier { name, .. } = &conjunct.kind
                && level(conjunct) == Level::Constant
                && is_constant_true(name, &item, "property", evaluator)?
            {
                continue;
            }
            let part_name = item.name.clone().unwrap_or_else(|| name.clone());
            if let ExpressionKind::Always(body) = &conjunct.kind {
                if let ExpressionKind::Action {
                    is_box: true,
                    action,
                    subscript,
                } = &body.kind
                {
                    properties.action_properties.push(ActionProperty {
                        name: part_name,
                        action: action.clone(),
                        subscript: subscript.clone(),
                        scope: item.scope,
                    });
                    continue;
                }
                if level(body) <= Level::Variable {
                    // TLC names the invariant by the operator the property asserts always holds,
                    // when it applies the operator to no arguments.
                    let is_identifier = matches!(body.kind, ExpressionKind::Identifier { .. });
                    let reference = body.reference().unwrap_or_default();
                    let operator = (is_identifier && !body.is_locally_resolved())
                        .then(|| get_definition(&reference, environment))
                        .flatten();
                    properties.invariants.push(Property {
                        name: operator.map_or_else(
                            || {
                                if is_identifier {
                                    reference.clone()
                                } else {
                                    part_name
                                }
                            },
                            |operator| operator.name.clone(),
                        ),
                        expression: body.clone(),
                        scope: item.scope,
                    });
                    continue;
                }
            }
            match level(conjunct) {
                Level::Constant | Level::Variable => properties.initial_predicates.push(Property {
                    name: part_name,
                    expression: item.expression,
                    scope: item.scope,
                }),
                Level::Action => {
                    return Err(FrontError::Config(get_action_property_message(
                        &part_name, conjunct,
                    )));
                }
                Level::Temporal => properties.liveness.push(Property {
                    name: name.clone(),
                    expression: item.expression,
                    scope: item.scope,
                }),
            }
        }
    }
    Ok(properties)
}

/// `createSearch`'s checks of what the configuration names after the specification and its
/// properties: the constraints, the RL reward and periodic operators, the possible predicates,
/// and, for a spec with variables, the SYMMETRY and VIEW.
pub fn check_search_config(
    config: &crate::config::ModelConfig,
    environment: &Environment,
    facts: &DefinitionFacts,
    evaluator: &Evaluator,
) -> Result<()> {
    let evaluator = Some(evaluator);
    for name in &config.constraints {
        get_config_predicate("constraint", name, environment, facts, evaluator)?;
    }
    for name in &config.action_constraints {
        get_config_predicate("action constraint", name, environment, facts, evaluator)?;
    }
    if let Some(name) = &config.rl_reward {
        get_config_operator("rlreward", name, environment)?;
    }
    if let Some(name) = &config.periodic {
        get_config_operator("periodic", name, environment)?;
    }
    for (index, name) in config.possible.iter().enumerate() {
        if config.possible[..index].contains(name) {
            return Err(FrontError::Config(format!(
                "_POSSIBLE lists {name} more than once"
            )));
        }
        get_config_definition("possible", name, environment, facts, evaluator)?;
        if get_level(&create_identifier(name), None, environment, facts, &[]) == Level::Temporal {
            return Err(FrontError::Config(format!(
                "The possible of {name} is equal to a temporal formula; only state- and action-level predicates are supported"
            )));
        }
    }
    if environment.variables.is_empty() {
        return Ok(());
    }
    if let Some(name) = &config.symmetry {
        // `getSymmetryGroup` reads the definition by its name, without the substitutions.
        let definition = environment.definitions.get(name.as_str());
        if definition.is_none() && !environment.constants.contains_key(name.as_str()) {
            return Err(FrontError::Config(format!(
                "The symmetry function {name} specified in the configuration file\nis not defined in the specification."
            )));
        }
        if !definition.is_some_and(|definition| {
            matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
        }) {
            return Err(FrontError::Evaluation(format!(
                "{}The symmetry function {name} must specify a set of permutations.",
                crate::errors::UNEXPECTED_EXCEPTION
            )));
        }
    }
    if let Some(name) = &config.view {
        get_config_operator("view function", name, environment)?;
    }
    Ok(())
}

/// `getConstantPredicates`: the constant definitions the configuration names, which TLC
/// evaluates as it reads the configuration, in its order, each with how TLC rejects its value and
/// what the configuration names it as.
pub fn get_constant_predicates(
    config: &crate::config::ModelConfig,
    environment: &Environment,
    facts: &DefinitionFacts,
) -> Vec<(PredicateForm, &'static str, String, Rc<Definition>)> {
    let named = |form: PredicateForm, kind: &'static str, names: &[String]| {
        names
            .iter()
            .map(|name| (form, kind, name.clone()))
            .collect::<Vec<_>>()
    };
    let optional = |name: &Option<String>| name.iter().cloned().collect::<Vec<_>>();
    let specification = match &config.specification {
        None => [
            named(
                PredicateForm::Definition,
                "initial predicate",
                &optional(&config.init),
            ),
            named(
                PredicateForm::Definition,
                "next state action",
                &optional(&config.next),
            ),
        ]
        .concat(),
        Some(name) => named(
            PredicateForm::Specification,
            "name",
            std::slice::from_ref(name),
        ),
    };
    [
        named(PredicateForm::Predicate, "invariant", &config.invariants),
        specification,
        named(PredicateForm::Predicate, "property", &config.properties),
        named(PredicateForm::Predicate, "constraint", &config.constraints),
        named(
            PredicateForm::Predicate,
            "action constraint",
            &config.action_constraints,
        ),
        named(PredicateForm::Definition, "possible", &config.possible),
    ]
    .concat()
    .into_iter()
    .filter_map(|(form, kind, name)| {
        if environment.constants.contains_key(name.as_str()) {
            return None;
        }
        let definition = get_definition(&name, environment)?;
        let is_evaluated = matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
            && facts.is_constant_level(definition, environment)
            && !matches!(
                definition.body.kind,
                ExpressionKind::Number { .. } | ExpressionKind::String { .. }
            );
        is_evaluated.then(|| (form, kind, name, definition.clone()))
    })
    .collect()
}

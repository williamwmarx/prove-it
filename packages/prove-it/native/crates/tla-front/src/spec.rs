//! What the model section of the IR reads of a spec before the search: the scopes an instance's
//! definitions are read in, and a formula's level, as `liveness.ts`'s `getLevel` computes it.

use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::*;
use crate::config::ConfigValue;
use crate::dependencies::{DefinitionFacts, Level};
use crate::environment::Environment;
use crate::errors::{FrontError, TAUTOLOGY, describe_range, format_range};
use crate::eval::Evaluator;
use crate::hash::FastMap;
use crate::instances::map_children;
use crate::levels::{self, ACTION_LEVEL};
use crate::resolve::{Result, Tables};
use crate::tlc_messages::{is_eval_exception, with_unexpected_exception};
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
    /// A value an operator's argument written as a literal gives, which reads as `Value`; TLC
    /// holds the argument as the expression, which some of its analyses read
    /// (`SubscriptCollector`).
    Literal {
        value: ConfigValue,
        expression: Expr,
    },
    /// `Thunk`: an expression read in a scope.
    Thunk {
        expression: Expr,
        scope: ScopeOf,
    },
    /// An operator `Closure`.
    Closure {
        name: Name,
        is_recursive: bool,
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

/// `Specs.getLevel`: the level of a formula read in a scope, with the names a binder in it
/// shadows read as constants. SANY's level of the formula, where an application counts the
/// arguments whose parameters the operator's body reads (`OpDefNode.levelCheck` weights a
/// parameter 1 where the body's level parameters hold it), and each parameter the level depends
/// on looked up in the scope to the argument it is bound to, read in the argument's own scope.
pub fn get_level(
    expression: &Expr,
    scope: Option<&Rc<Scope>>,
    environment: &Environment,
    facts: &DefinitionFacts,
    shadowed: &[Name],
) -> Level {
    get_level_inner(
        expression,
        scope,
        environment,
        facts,
        shadowed,
        &levels::Scope::default(),
        &LevelWalk::new(environment),
    )
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum LevelIdentity {
    Binding(*const Scope),
    Definition(*const Definition),
}

type LevelMemoKey = *const Definition;

/// The levels SANY gives an operator, where its level check accepts the operator.
type OperatorLevels = Option<Rc<levels::OperatorLevels>>;

struct LevelWalk<'a> {
    active: std::cell::RefCell<Vec<LevelIdentity>>,
    memo: std::cell::RefCell<std::collections::HashMap<LevelMemoKey, Level>>,
    cycles: std::cell::Cell<u64>,
    /// SANY's level check, whose weights tell which arguments an application counts.
    analyzer: levels::LevelAnalyzer<'a>,
    /// The LET definition each node a LET binds holds, with the scope SANY checks it in.
    let_definitions: std::cell::RefCell<FastMap<*const Scope, (Rc<Definition>, levels::Scope)>>,
    /// The levels of a closure bound around the formula, a LAMBDA or an operator passed as an
    /// argument, by its body.
    closure_levels: std::cell::RefCell<FastMap<*const Expression, OperatorLevels>>,
}

impl<'a> LevelWalk<'a> {
    fn new(environment: &'a Environment) -> LevelWalk<'a> {
        LevelWalk {
            active: Default::default(),
            memo: Default::default(),
            cycles: Default::default(),
            analyzer: environment.create_unsubstituted_level_analyzer(),
            let_definitions: Default::default(),
            closure_levels: Default::default(),
        }
    }

    /// The scope SANY checks the levels of what a node binds in: a LET definition's, or the
    /// module's for a binding the caller made around the formula.
    fn get_lexical_scope(&self, node: &Rc<Scope>) -> levels::Scope {
        self.let_definitions
            .borrow()
            .get(&Rc::as_ptr(node))
            .map(|(_, lexical)| lexical.clone())
            .unwrap_or_default()
    }

    /// Keeps each definition a LET bound, with the scope SANY checks it in: the node that binds
    /// it, as `bind_definitions` makes one per definition, innermost last.
    fn record_let(
        &self,
        bound: Option<&Rc<Scope>>,
        definitions: &[Rc<Definition>],
        lexical: &levels::Scope,
    ) {
        let mut node = bound;
        let mut recorded = self.let_definitions.borrow_mut();
        for definition in definitions.iter().rev() {
            let Some(current) = node else {
                break;
            };
            recorded.insert(Rc::as_ptr(current), (definition.clone(), lexical.clone()));
            node = current.parent.as_ref();
        }
    }

    /// The levels of a definition, checked in the module's scope as SANY checks it.
    fn get_definition_levels(&self, definition: &Rc<Definition>) -> OperatorLevels {
        self.analyzer
            .analyze_definition(definition, &levels::Scope::default())
            .ok()
    }

    /// The levels of the operator a node binds: a LET definition's in the scope of its LET, or
    /// a closure's with its parameters bound, where the formula's caller made the binding.
    fn get_binding_levels(
        &self,
        node: &Rc<Scope>,
        name: &Name,
        params: &[OperatorParam],
        body: &Expr,
    ) -> OperatorLevels {
        if let Some((definition, lexical)) = self.let_definitions.borrow().get(&Rc::as_ptr(node)) {
            return self.analyzer.analyze_definition(definition, lexical).ok();
        }
        let key = Rc::as_ptr(body);
        if let Some(levels) = self.closure_levels.borrow().get(&key) {
            return levels.clone();
        }
        let levels = self
            .analyzer
            .analyze_closure(name, params, body, &levels::Scope::default())
            .ok()
            .map(Rc::new);
        self.closure_levels.borrow_mut().insert(key, levels.clone());
        levels
    }
}

fn get_level_inner(
    expression: &Expr,
    scope: Option<&Rc<Scope>>,
    environment: &Environment,
    facts: &DefinitionFacts,
    shadowed: &[Name],
    lexical: &levels::Scope,
    walk: &LevelWalk,
) -> Level {
    let get_binding_level = |name: &str| {
        let (node, binding) = lookup_scope(scope, name)?;
        Some(match binding {
            Binding::Value(_) | Binding::Literal { .. } => Level::Constant,
            Binding::Thunk { expression, scope } => {
                let body_shadowed = Vec::new();
                let identity = LevelIdentity::Binding(Rc::as_ptr(node));
                if walk.active.borrow().contains(&identity) {
                    walk.cycles.set(walk.cycles.get().saturating_add(1));
                    // TLC binds an operator being visited to the constant IntValue.One. A
                    // non-operator lazy argument has no such sentinel.
                    if matches!(scope, ScopeOf::Own) {
                        Level::Constant
                    } else {
                        Level::Temporal
                    }
                } else {
                    walk.active.borrow_mut().push(identity);
                    let level = get_level_inner(
                        expression,
                        scope.resolve(node).as_ref(),
                        environment,
                        facts,
                        &body_shadowed,
                        &walk.get_lexical_scope(node),
                        walk,
                    );
                    walk.active.borrow_mut().pop();
                    level
                }
            }
            Binding::Closure {
                name, body, scope, ..
            } => {
                let body_shadowed: Vec<_> = shadowed
                    .iter()
                    .cloned()
                    .chain(std::iter::once(name.clone()))
                    .collect();
                let identity = LevelIdentity::Binding(Rc::as_ptr(node));
                if walk.active.borrow().contains(&identity) {
                    walk.cycles.set(walk.cycles.get().saturating_add(1));
                    Level::Constant
                } else {
                    walk.active.borrow_mut().push(identity);
                    let level = get_level_inner(
                        body,
                        scope.resolve(node).as_ref(),
                        environment,
                        facts,
                        &body_shadowed,
                        &walk.get_lexical_scope(node),
                        walk,
                    );
                    walk.active.borrow_mut().pop();
                    level
                }
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
                get_level_inner(child, scope, environment, facts, shadowed, lexical, walk)
            } else {
                let shadowed: Vec<Name> = shadowed.iter().chain(bound).cloned().collect();
                let lexical = lexical.bind_names(bound);
                get_level_inner(child, scope, environment, facts, &shadowed, &lexical, walk)
            };
            level = level.max(child_level);
            Ok(child.clone())
        });
        level
    };
    let user_operator_level = || {
        let name = expression.reference()?;
        if shadowed.contains(&name) {
            return None;
        }
        // A standard module's operator the front end implements, which SANY levels by the
        // module's definition of it.
        let standard = || {
            let definition = environment.get_standard_definition(&name)?;
            match &definition.kind {
                DefinitionKind::Operator { params, .. } => {
                    Some((params.clone(), definition.body.clone(), None))
                }
                DefinitionKind::Function { .. } => None,
            }
        };
        let (params, body, closure_scope) =
            resolve_apply_operator(expression, scope, environment).or_else(standard)?;
        let global_definition = || {
            get_definition(&name, environment)
                .cloned()
                .or_else(|| environment.get_standard_definition(&name))
        };
        // TLC retains the caller context while visiting a global operator body. A local closure
        // instead carries the lexical scope in which it was created.
        let is_global = !expression.is_locally_resolved() && global_definition().is_some();
        let body_scope = if is_global {
            scope
        } else {
            closure_scope.as_ref()
        };
        let formal_names: Vec<Name> = params.iter().map(|param| param.name.clone()).collect();
        let mut body_shadowed = if is_global {
            Vec::new()
        } else {
            shadowed.to_vec()
        };
        if !is_global && let Some((_, Binding::Closure { name, .. })) = lookup_scope(scope, &name) {
            body_shadowed.push(name.clone());
        }
        body_shadowed.extend(formal_names.iter().cloned());
        // The sentinel belongs to the resolved operator, not its possibly shared body. A
        // local binding also identifies its lexical context; a global definition's body names
        // nothing of its caller's scope, so only recursion visits it again while it is active,
        // whatever scope a LET of the caller's body adds.
        let (identity, memo_key, levels, body_lexical) = if is_global {
            let definition = global_definition()?;
            let key = Rc::as_ptr(&definition);
            (
                LevelIdentity::Definition(key),
                Some(key),
                walk.get_definition_levels(&definition),
                levels::Scope::default().bind_parameters(&params),
            )
        } else {
            let (node, _) = lookup_scope(scope, &name)?;
            (
                LevelIdentity::Binding(Rc::as_ptr(node)),
                None,
                walk.get_binding_levels(node, &name, &params, &body),
                walk.get_lexical_scope(node).bind_parameters(&params),
            )
        };
        if walk.active.borrow().contains(&identity) {
            walk.cycles.set(walk.cycles.get().saturating_add(1));
            // The operator lookup is bound to IntValue.One, but ordinary arguments still
            // contribute their bounds in the caller below.
            return Some((params, Level::Constant, levels));
        }
        let can_memo = closure_scope.is_none() && scope.is_none() && params.is_empty() && is_global;
        if can_memo
            && let Some(key) = memo_key
            && let Some(&level) = walk.memo.borrow().get(&key)
        {
            return Some((params, level, levels));
        }
        let cycles_before = walk.cycles.get();
        walk.active.borrow_mut().push(identity);
        let level = get_level_inner(
            &body,
            body_scope,
            environment,
            facts,
            &body_shadowed,
            &body_lexical,
            walk,
        );
        walk.active.borrow_mut().pop();
        if can_memo
            && walk.cycles.get() == cycles_before
            && let Some(key) = memo_key
        {
            walk.memo.borrow_mut().insert(key, level);
        }
        Some((params, level, levels))
    };
    match &expression.kind {
        ExpressionKind::Prime(_) | ExpressionKind::Unchanged(_) | ExpressionKind::Action { .. } => {
            Level::Action
        }
        // `getLevelBound` sees an OpArgNode, rather than traversing its operator body.
        ExpressionKind::Lambda { .. } | ExpressionKind::OperatorReference { .. } => Level::Constant,
        ExpressionKind::Enabled(_) => Level::Variable,
        ExpressionKind::Always(_)
        | ExpressionKind::Eventually(_)
        | ExpressionKind::Fairness { .. } => Level::Temporal,
        ExpressionKind::UnboundedQuantifier {
            is_temporal: true, ..
        } => Level::Temporal,
        ExpressionKind::Identifier { .. } => {
            user_operator_level().map_or_else(|| get_name_level(expression), |(_, level, _)| level)
        }
        ExpressionKind::Apply { operator, args, .. } => match &**operator {
            "~>" | "-+->" => Level::Temporal,
            "\\cdot" => Level::Action,
            _ => match user_operator_level() {
                Some((params, mut level, levels)) if params.len() == args.len() => {
                    for (index, (param, argument)) in params.iter().zip(args).enumerate() {
                        // `OpApplNode.levelCheck` takes the operands of weight 1, those whose
                        // parameter the body's level parameters hold, so `F(x')` with `F(p) ==
                        // x = 0` is state-level. An operator the level check doesn't accept
                        // counts every argument.
                        if levels
                            .as_ref()
                            .is_some_and(|levels| !levels.is_argument_counted(index))
                        {
                            continue;
                        }
                        if param.arity == 0 {
                            level = level.max(get_level_inner(
                                argument,
                                scope,
                                environment,
                                facts,
                                shadowed,
                                lexical,
                                walk,
                            ));
                        } else {
                            // `Specs.getLevel` takes SANY's level, which counts the level of an
                            // operator argument that the body applies (`getLevelParams`), where
                            // the body's walk reads the parameter as a constant.
                            level = level.max(match &argument.kind {
                                ExpressionKind::Lambda { .. } => get_children_level(argument),
                                ExpressionKind::OperatorReference { .. } => {
                                    get_name_level(argument)
                                }
                                _ => get_level_inner(
                                    argument,
                                    scope,
                                    environment,
                                    facts,
                                    shadowed,
                                    lexical,
                                    walk,
                                ),
                            });
                        }
                    }
                    level
                }
                _ => get_name_level(expression).max(get_children_level(expression)),
            },
        },
        // `LetInNode.levelCheck` takes the body's level: a definition the body doesn't apply
        // counts for nothing, and one it applies counts through its application.
        ExpressionKind::Let {
            definitions, body, ..
        } => match bind_definitions(definitions, scope) {
            Ok(bound) => {
                let inner = lexical.bind_definitions(definitions);
                walk.record_let(bound.as_ref(), definitions, &inner);
                get_level_inner(
                    body,
                    bound.as_ref(),
                    environment,
                    facts,
                    shadowed,
                    &inner,
                    walk,
                )
            }
            Err(_) => get_children_level(expression),
        },
        _ => get_children_level(expression),
    }
}

/// What `expandTemporal` gives: a conjunct with the scope it reads and the name TLC gives it.
pub struct Expanded {
    /// Whether expansion passed through the sole configured property name.
    pub is_property_fairness: bool,
    /// Whether TLC wraps the conjunct in nonempty INSTANCE substitutions.
    pub has_substitutions: bool,
    pub expression: Expr,
    pub scope: Option<Rc<Scope>>,
    pub name: Option<Name>,
}

/// `getSpecification`: the initial predicate, the next-state action, the scope they read, and
/// the temporal conjuncts of the specification.
pub struct Specification {
    /// The syntactic property provenance test of SpecProcessor warning 2258.
    pub is_fairness_tautology: bool,
    pub init: Option<Expr>,
    pub next: Option<Expr>,
    /// Whether Tool.getActions reaches a formal parameter where it casts its symbol to OpDefNode.
    pub has_action_parameter_cast: bool,
    /// Whether Tool.getActions reaches a variable where it casts its declaration to OpDefNode, in
    /// a `[][A]_v` the engine doesn't see the scope of (`ActionSplitFailure::Variable`).
    pub has_action_variable_cast: bool,
    /// Whether the first failure Tool.getActions meets is a declared constant the configuration
    /// substitutes a definition for, whose declaration it casts to OpDefNode
    /// (`ActionSplitFailure::Constant`), which the engine declines where TLC fails so.
    pub has_action_constant_cast: bool,
    /// Why the front end can't tell whether the first failure Tool.getActions may meet, a
    /// substituted constant applied to an argument TLC evaluates as it splits the action, fails
    /// or shows (`ActionSplitFailure::UnknownArgument`).
    pub action_unknown_argument: Option<&'static str>,
    pub scope: Option<Rc<Scope>>,
    pub temporals: Vec<Expanded>,
    /// What TLC finds of the subscript of each `[][Next]_v` of the specification, in order, which
    /// it warns of.
    pub subscripts: Vec<SubscriptCheck>,
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

const UNCERTIFIED_EMPTY_UNROLL: &str =
    "a property's \\A emptiness is not certified for TLC's context";

fn not_yet(reason: &str) -> FrontError {
    FrontError::NotYet(reason.to_owned())
}

/// What `expandTemporal` reads.
pub struct Expansion<'a> {
    /// The sole configured property, whose calls TLC tags in the specification.
    pub fairness_property: Option<&'a str>,
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
    /// Whether it unrolled a property's \A, which it does with the substitutions of the INSTANCEs
    /// it went through bound, where TLC leaves them unbound and may take the \A whole.
    pub is_unrolled: std::cell::Cell<bool>,
    /// Whether every enclosing unroll has pure domains with the same meaning in TLC's context.
    pub unroll_is_independent: std::cell::Cell<bool>,
    pub has_action_substitutions: std::cell::Cell<bool>,
    label_probe: std::cell::Cell<bool>,
    /// The bindings the expansion is in, each the scope that holds it and its expression: one
    /// reached again in its own expansion, as a LET's `RECURSIVE F` with `F == F /\ ...`, recurses
    /// until TLC's stack overflows, as a global definition does.
    expanding_bindings: std::cell::RefCell<Vec<(*const Scope, *const Expr)>>,
}

impl Expansion<'_> {
    fn level(&self, expression: &Expr, scope: Option<&Rc<Scope>>) -> Level {
        get_level(expression, scope, self.environment, self.facts, &[])
    }

    fn is_substituted(&self, definition: &Rc<Definition>) -> bool {
        self.environment.is_substituted(definition)
    }

    fn unroll_domain_is_independent(
        &self,
        expression: &Expr,
        scope: Option<&Rc<Scope>>,
        bound: &[Name],
        visiting: &mut Vec<*const Expression>,
        is_substituted: bool,
    ) -> bool {
        if visiting.len() >= 256
            || visiting.contains(&Rc::as_ptr(expression))
            || (is_substituted && self.environment.tables.is_substitution(expression))
        {
            return false;
        }
        visiting.push(Rc::as_ptr(expression));
        let result = (|| {
            let name = expression.reference().unwrap_or_default();
            if !bound.contains(&name) {
                if !expression.is_locally_resolved()
                    && get_definition(&name, self.environment).is_none()
                    && !self.environment.constants.contains_key(name.as_ref())
                    && !self
                        .environment
                        .operator_constants
                        .contains_key(name.as_ref())
                {
                    let builtin = self
                        .environment
                        .substitutions
                        .get(name.as_ref())
                        .unwrap_or(&name);
                    if self
                        .environment
                        .builtins
                        .get(builtin.as_ref())
                        .is_some_and(|builtin| {
                            crate::dependencies::is_impure_builtin(
                                builtin.name.as_ref(),
                                self.environment,
                            ) || builtin.flags
                                & (tla_ir::Builtin::TABLE
                                    | tla_ir::Builtin::DECLINED
                                    | tla_ir::Builtin::EXTERNAL_CLASS
                                    | 128) as u32
                                != 0
                        })
                    {
                        return false;
                    }
                }
                match &expression.kind {
                    ExpressionKind::Identifier { .. } => {
                        let definition = get_definition(&name, self.environment);
                        if (expression.is_locally_resolved() || definition.is_none())
                            && let Some((node, binding)) = lookup_scope(scope, &name)
                        {
                            return match binding {
                                Binding::Value(_) => true,
                                Binding::Literal { expression, .. } => self
                                    .unroll_domain_is_independent(
                                        expression,
                                        scope,
                                        bound,
                                        visiting,
                                        is_substituted,
                                    ),
                                Binding::Thunk { expression, scope } => self
                                    .unroll_domain_is_independent(
                                        expression,
                                        scope.resolve(node).as_ref(),
                                        bound,
                                        visiting,
                                        is_substituted,
                                    ),
                                Binding::Closure { .. } => false,
                            };
                        }
                        if let Some(definition) = definition {
                            if self.environment.has_java_override_index
                                || (is_substituted
                                    && !self.unroll_definition_is_independent(definition, &name))
                            {
                                return false;
                            }
                            return self.unroll_domain_is_independent(
                                &definition.body,
                                None,
                                bound,
                                visiting,
                                is_substituted,
                            );
                        }
                        return self.environment.constants.contains_key(name.as_ref())
                            || self.environment.builtins.contains_key(name.as_ref());
                    }
                    ExpressionKind::Apply { operator, args, .. } => {
                        let definition = get_definition(&name, self.environment);
                        if expression.is_locally_resolved() {
                            let Some((
                                node,
                                Binding::Closure {
                                    name: closure_name,
                                    params,
                                    body,
                                    scope: closure_scope,
                                    ..
                                },
                            )) = lookup_scope(scope, &name)
                            else {
                                return false;
                            };
                            if is_substituted && name != *operator && closure_name != operator {
                                return false;
                            }
                            let names: Vec<_> = bound
                                .iter()
                                .cloned()
                                .chain(params.iter().map(|param| param.name.clone()))
                                .collect();
                            if !self.unroll_domain_is_independent(
                                body,
                                closure_scope.resolve(node).as_ref(),
                                &names,
                                visiting,
                                is_substituted,
                            ) {
                                return false;
                            }
                        } else if let Some(definition) = definition {
                            if self.environment.has_java_override_index
                                || (is_substituted
                                    && (!self.unroll_definition_is_independent(definition, &name)
                                        || (name != *operator
                                            && self
                                                .environment
                                                .tables
                                                .get_source_name(definition)
                                                != *operator)))
                            {
                                return false;
                            }
                            let DefinitionKind::Operator { params, .. } = &definition.kind else {
                                return false;
                            };
                            let names: Vec<_> = bound
                                .iter()
                                .cloned()
                                .chain(params.iter().map(|param| param.name.clone()))
                                .collect();
                            if !self.unroll_domain_is_independent(
                                &definition.body,
                                None,
                                &names,
                                visiting,
                                is_substituted,
                            ) {
                                return false;
                            }
                        } else if !self.environment.builtins.contains_key(operator.as_ref())
                            && !(name == *operator
                                && self
                                    .environment
                                    .operator_constants
                                    .contains_key(name.as_ref()))
                        {
                            return false;
                        }
                        return args.iter().all(|arg| {
                            self.unroll_domain_is_independent(
                                arg,
                                scope,
                                bound,
                                visiting,
                                is_substituted,
                            )
                        });
                    }
                    ExpressionKind::OperatorReference { .. } => return false,
                    _ => {}
                }
            }
            let comprehension_bounds = match &expression.kind {
                ExpressionKind::SetFilter { bound, .. } => Some(std::slice::from_ref(bound)),
                ExpressionKind::SetMap { bounds, .. } => Some(bounds.as_slice()),
                _ => None,
            };
            if let Some(bounds) = comprehension_bounds
                && bounds.iter().all(|domain| {
                    self.unroll_domain_is_independent(
                        &domain.set,
                        scope,
                        bound,
                        visiting,
                        is_substituted,
                    )
                })
                && self.evaluator.is_some_and(|evaluator| {
                    evaluator
                        .get_bindings(bounds, scope)
                        .is_ok_and(|bindings| bindings.is_empty())
                })
            {
                // An empty comprehension never evaluates its predicate or mapped value.
                return true;
            }
            if let ExpressionKind::If {
                condition,
                consequent,
                alternative,
            } = &expression.kind
            {
                if !self.unroll_domain_is_independent(
                    condition,
                    scope,
                    bound,
                    visiting,
                    is_substituted,
                ) {
                    return false;
                }
                let Some(evaluator) = self.evaluator else {
                    return false;
                };
                return match evaluator.is_true(condition, scope) {
                    Ok(true) => self.unroll_domain_is_independent(
                        consequent,
                        scope,
                        bound,
                        visiting,
                        is_substituted,
                    ),
                    Ok(false) => self.unroll_domain_is_independent(
                        alternative,
                        scope,
                        bound,
                        visiting,
                        is_substituted,
                    ),
                    Err(_) => false,
                };
            }
            let mut independent = true;
            let tables = Tables::default();
            let _ = map_children(expression, &tables, &mut |child, names| {
                let bound: Vec<_> = bound.iter().chain(names).cloned().collect();
                independent &= self.unroll_domain_is_independent(
                    child,
                    scope,
                    &bound,
                    visiting,
                    is_substituted,
                );
                Ok(child.clone())
            });
            independent
        })();
        visiting.pop();
        result
    }

    fn unroll_definition_is_independent(&self, definition: &Rc<Definition>, name: &str) -> bool {
        let source = self.environment.tables.get_source_name(definition);
        if source.as_ref() == name {
            return true;
        }
        !self
            .environment
            .constants
            .keys()
            .chain(self.environment.operator_constants.keys())
            .chain(self.environment.substitutions.keys())
            .any(|key| {
                key.as_ref() != name
                    && (key == &source
                        || self
                            .environment
                            .definitions
                            .get(key)
                            .is_some_and(|original| {
                                original.location == definition.location
                                    && self.environment.tables.get_source_name(original) == source
                            }))
            })
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
        let had_action_substitutions = self.has_action_substitutions.get();
        let local_substitution = expression.is_locally_resolved()
            && expression.reference().is_some_and(|name| {
                if !name.contains('!') && !name.contains(crate::resolve::KEY_SEPARATOR) {
                    return false;
                }
                let Some((
                    node,
                    Binding::Closure {
                        scope: ScopeOf::Own,
                        ..
                    },
                )) = lookup_scope(scope, &name)
                else {
                    return false;
                };
                let mut current = Some(node);
                while let Some(node) = current {
                    // instantiateLocally binds SubstIn declarations as C#0, unlike its
                    // copied operators, whose generated keys contain KEY_SEPARATOR.
                    if node.name.contains('#') && !node.name.contains(crate::resolve::KEY_SEPARATOR)
                    {
                        return true;
                    }
                    current = node.parent.as_ref();
                }
                false
            });
        self.has_action_substitutions
            .set(had_action_substitutions || is_substituted || local_substitution);
        let independent = self.unroll_is_independent.get();
        if self.is_property
            && let ExpressionKind::Quantified {
                quantifier: Quantifier::Forall,
                bounds,
                ..
            } = &expression.kind
        {
            self.unroll_is_independent.set(
                independent
                    && bounds.iter().all(|bound| {
                        self.unroll_domain_is_independent(
                            &bound.set,
                            scope,
                            &[],
                            &mut Vec::new(),
                            is_substituted,
                        )
                    }),
            );
        }
        let expanded = self.expand_inner(expression, scope, expanding, is_substituted, name);
        self.unroll_is_independent.set(independent);
        self.has_action_substitutions.set(had_action_substitutions);
        let mut expanded = expanded?;
        if self.is_specification
            && let ExpressionKind::Identifier { name, .. } = &expression.kind
            && self.fairness_property == Some(name.as_ref())
            && ((!expression.is_locally_resolved()
                && get_definition(
                    &expression.reference().unwrap_or_default(),
                    self.environment,
                )
                .is_some())
                || lookup_scope(scope, &expression.reference().unwrap_or_default()).is_none())
        {
            for item in &mut expanded {
                item.is_property_fairness = true;
            }
        }
        Ok(expanded)
    }

    /// Recover a source zero-argument operator name without decomposing its substituted body.
    fn synthetic_property_name(&self, expression: &Expr) -> Option<Name> {
        let mut current = expression.clone();
        let mut visited = std::collections::HashSet::new();
        loop {
            let (source, header) = self.environment.tables.synthetic_zero_arity(&current)?;
            let ExpressionKind::Identifier { name, .. } = &source.kind else {
                return None;
            };
            let ExpressionKind::Apply { operator, args, .. } = &current.kind else {
                return None;
            };
            let DefinitionKind::Operator {
                params: original, ..
            } = &header.kind
            else {
                return None;
            };
            if !original.is_empty()
                || self.environment.has_java_override_index
                || self
                    .environment
                    .java_overrides
                    .iter()
                    .any(|entry| entry.is_matched && entry.operator == name.as_ref())
                || self.environment.substitutions.contains_key(operator)
                || self.environment.constants.contains_key(operator)
                || self
                    .environment
                    .configured_value_bindings
                    .contains(operator)
            {
                return None;
            }
            let before = self.environment.pre_override_headers.get(operator)?;
            let actual = get_definition(operator, self.environment)?;
            if !Rc::ptr_eq(before, actual)
                || actual.is_recursive
                || !visited.insert(Rc::as_ptr(actual))
            {
                return None;
            }
            let DefinitionKind::Operator { params, .. } = &actual.kind else {
                return None;
            };
            if params.len() != args.len() {
                return None;
            }
            match &header.body.kind {
                ExpressionKind::Identifier { .. } => current = actual.body.clone(),
                ExpressionKind::Apply { operator, .. }
                    if operator.as_ref() == "="
                        && !header.body.is_locally_resolved()
                        && !self.environment.substitutions.contains_key(operator)
                        && matches!(&actual.body.kind, ExpressionKind::Apply { operator, .. } if operator.as_ref() == "=") =>
                {
                    return Some(name.clone());
                }
                _ => return None,
            }
        }
    }

    fn expand_inner(
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
                if self.label_probe.get() {
                    return self.expand(body, scope, expanding, is_substituted, name);
                }
                if self.is_property && self.environment.has_java_override_index {
                    // The old transparent-label path already declines an unproved empty
                    // unroll. Keeping the label must not bypass that boundary in liveness.
                    let unrolled = self.is_unrolled.get();
                    let independent = self.unroll_is_independent.get();
                    let substitutions = self.has_action_substitutions.get();
                    self.label_probe.set(true);
                    let legacy = self.expand(body, scope, expanding, is_substituted, name.clone());
                    self.label_probe.set(false);
                    self.is_unrolled.set(unrolled);
                    self.unroll_is_independent.set(independent);
                    self.has_action_substitutions.set(substitutions);
                    if let Err(FrontError::NotYet(reason)) = legacy
                        && reason == UNCERTIFIED_EMPTY_UNROLL
                    {
                        return Err(not_yet(UNCERTIFIED_EMPTY_UNROLL));
                    }
                }
            }
            ExpressionKind::Let {
                definitions,
                instances,
                body,
                ..
            } => {
                // The front end evaluates what a parameterized INSTANCE in a LET makes as of
                // constant level, so an argument naming a variable fails where TLC reads it.
                if self.is_specification
                    && instances
                        .iter()
                        .flatten()
                        .any(|instance| !instance.params.is_empty())
                {
                    return Err(not_yet(
                        "a parameterized INSTANCE in a LET of the specification",
                    ));
                }
                let bound = bind_definitions(definitions, scope)?;
                return self.expand(body, bound.as_ref(), expanding, is_substituted, name);
            }
            ExpressionKind::Identifier { name: written, .. } => {
                let reference = expression.reference().unwrap_or_default();
                // The definitions an INSTANCE in a LET makes are the LET's, which the copies'
                // bodies name by keys no global definition has.
                let binding = if expression.is_locally_resolved()
                    || get_definition(&reference, self.environment).is_none()
                {
                    lookup_scope(scope, &reference)
                } else {
                    None
                };
                if let Some((node, Binding::Thunk { expression, scope })) = binding {
                    let key: (*const Scope, *const Expr) = (Rc::as_ptr(node), expression);
                    if self.expanding_bindings.borrow().contains(&key) {
                        // TLC recurses until its stack overflows.
                        return Err(FrontError::StackOverflow);
                    }
                    self.expanding_bindings.borrow_mut().push(key);
                    let expanded = (|| {
                        let is_let_definition = matches!(scope, ScopeOf::Own);
                        let name = if is_let_definition {
                            Some(written.clone())
                        } else {
                            name
                        };
                        let scope = scope.resolve(node);
                        // `processConfigSpec` takes a LET's definition without parameters as the
                        // `OpDefNode` it is, whose body it takes whole where `getLevelBound` finds it
                        // of state level, the argument a parameter in it reads (`S(y) == LET D == y
                        // IN Init /\ D`, `Spec == S(x = 1 /\ x)`) unsplit, worded at the body where
                        // it comes to a definition (`S(G)`). A body that comes to another name is left
                        // to the reading of such a name, and one the expansion doesn't split reads as
                        // the expansion reads it.
                        let read = read_through(expression, scope.as_ref());
                        let is_definition = names_global_definition(&read, self.environment);
                        if self.is_specification
                            && !self.is_property
                            && is_let_definition
                            && (is_definition
                                || !matches!(read.kind, ExpressionKind::Identifier { .. }))
                            && self.level(expression, scope.as_ref()) == Level::Variable
                        {
                            let expanded = self.expand(
                                expression,
                                scope.as_ref(),
                                expanding,
                                is_substituted,
                                name.clone(),
                            );
                            if let Ok(expanded) = expanded
                                && expanded.len() == 1
                                && !is_definition
                            {
                                return Ok(expanded);
                            }
                            return Ok(vec![Expanded {
                                is_property_fairness: false,
                                has_substitutions: self.has_action_substitutions.get(),
                                expression: expression.clone(),
                                scope,
                                name,
                            }]);
                        }
                        self.expand(expression, scope.as_ref(), expanding, is_substituted, name)
                    })();
                    self.expanding_bindings.borrow_mut().pop();
                    return expanded;
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
                    let expanding = [expanding, &[Rc::as_ptr(definition)]].concat();
                    let expanded = self.expand(
                        &definition.body,
                        None,
                        &expanding,
                        is_substituted || self.is_substituted(definition),
                        // `opNode.getName()`: the name as written, `A!Safe` for an instance's.
                        Some(written.clone()),
                    )?;
                    // The body is walked all the same, so one that names itself overflows.
                    if self.is_specification
                        && self.facts.get_definition_level(definition, self.environment)
                            == Level::Variable
                    {
                        return Ok(vec![Expanded {
                            is_property_fairness: false,
                            has_substitutions: self.has_action_substitutions.get(),
                            expression: definition.body.clone(),
                            scope: None,
                            name: Some(written.clone()),
                        }]);
                    }
                    return Ok(expanded);
                }
            }
            ExpressionKind::Apply { operator, args, .. }
                if self.version != TlcVersion::V1_7_4
                    && (self.is_property || self.is_specification) =>
            {
                let definition = if expression.is_locally_resolved() {
                    None
                } else {
                    get_definition(operator, self.environment)
                };
                let recursive_local = (expression.is_locally_resolved() || definition.is_none())
                    && lookup_scope(scope, &expression.reference().unwrap_or_default())
                        .is_some_and(|(_, binding)| match binding {
                            Binding::Closure { is_recursive, .. } => *is_recursive,
                            _ => false,
                        });
                if let Some((params, body, closure_scope)) =
                    resolve_apply_operator(expression, scope, self.environment)
                    && params.len() == args.len()
                    && !definition.is_some_and(|definition| definition.is_recursive)
                    && !recursive_local
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
                // Within an INSTANCE's substitutions TLC splits the body of a definition the
                // copy names without arguments (`processConfigSpec`), where the copy of a
                // parameterized INSTANCE applies it to the instance's parameters, which the
                // front end doesn't tell from arguments written there.
                if self.is_specification
                    && is_substituted
                    && !args.is_empty()
                    && definition.is_some_and(|definition| {
                        self.facts
                            .get_definition_level(definition, self.environment)
                            == Level::Temporal
                    })
                {
                    return Err(not_yet(
                        "a temporal definition a parameterized INSTANCE's specification applies",
                    ));
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
                match evaluator.get_temporal_bindings(bounds, scope) {
                    // `processConfigProps` leaves a \A whose sets fail with a TLCRuntimeException
                    // to the liveness checker, and an EvalException escapes TLC's startup.
                    Err(FrontError::Evaluation(message)) if !is_eval_exception(&message) => {}
                    bindings => {
                        let mut expanded = Vec::new();
                        for binding in bindings.map_err(with_unexpected_exception)? {
                            expanded.extend(self.expand(
                                body,
                                binding.as_ref(),
                                expanding,
                                is_substituted,
                                Some(Rc::from(describe_range(body))),
                            )?);
                        }
                        self.is_unrolled.set(true);
                        if expanded.is_empty() {
                            if !self.unroll_is_independent.get() {
                                return Err(not_yet(UNCERTIFIED_EMPTY_UNROLL));
                            }
                            return Err(FrontError::Evaluation(TAUTOLOGY.to_owned()));
                        }
                        return Ok(expanded);
                    }
                }
            }
            // `processConfigProps` computes the sets of a property's \A whatever their level, and
            // an EvalException escapes TLC's startup before a set that reads the state fails.
            ExpressionKind::Quantified {
                quantifier: Quantifier::Forall,
                bounds,
                ..
            } if self.is_property
                && let Some(evaluator) = self.evaluator
                && let Err(FrontError::Evaluation(message)) =
                    evaluator.get_temporal_bindings(bounds, scope)
                && is_eval_exception(&message) =>
            {
                return Err(with_unexpected_exception(FrontError::Evaluation(message)));
            }
            _ => {}
        }
        let name = if self.is_property && is_substituted {
            self.synthetic_property_name(expression).or(name)
        } else {
            name
        };
        Ok(vec![Expanded {
            is_property_fairness: false,
            has_substitutions: self.has_action_substitutions.get(),
            expression: expression.clone(),
            scope: scope.cloned(),
            name,
        }])
    }
}

/// The expression an operator's parameter or a LET's definition without parameters reads, through
/// any number of them, or the expression itself where it is no such name.
fn read_through(expression: &Expr, scope: Option<&Rc<Scope>>) -> Expr {
    let mut current = (expression.clone(), scope.cloned());
    for _ in 0..64 {
        if !matches!(current.0.kind, ExpressionKind::Identifier { .. }) {
            break;
        }
        let Some(reference) = current.0.reference() else {
            break;
        };
        match lookup_scope(current.1.as_ref(), &reference) {
            Some((node, Binding::Thunk { expression, scope })) => {
                current = (expression.clone(), scope.resolve(node));
            }
            Some((_, Binding::Literal { expression, .. })) => {
                current = (expression.clone(), None);
            }
            _ => break,
        }
    }
    current.0
}

/// Whether the expression names a definition of the environment, not a name a scope binds.
fn names_global_definition(expression: &Expr, environment: &Environment) -> bool {
    matches!(expression.kind, ExpressionKind::Identifier { .. })
        && !expression.is_locally_resolved()
        && expression
            .reference()
            .is_some_and(|reference| get_definition(&reference, environment).is_some())
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
                is_recursive: definition.is_recursive,
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
            ExpressionKind::String { value } => Binding::Literal {
                value: ConfigValue::String(value.to_string()),
                expression: argument.clone(),
            },
            ExpressionKind::Number { value, .. } if is_tlc_integer(*value) => Binding::Literal {
                value: ConfigValue::Number(*value),
                expression: argument.clone(),
            },
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
                        Some((_, Binding::Literal { value, expression })) => Binding::Literal {
                            value: value.clone(),
                            expression: expression.clone(),
                        },
                        // A LET definition whose body is a literal TLC holds as the literal's
                        // value (`processConstants`), which the argument's LazyValue reads.
                        Some((
                            _,
                            Binding::Thunk {
                                expression,
                                scope: ScopeOf::Own,
                            },
                        )) if let Some(value) = get_literal(expression) => Binding::Value(value),
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

/// Whether a LET definition is what an INSTANCE in the LET substitutes for a declaration
/// (`instantiateLocally`), named `v#0`, which no definition written in the spec can be named, and
/// unlike the copies of its definitions, keyed `vars@Inner#0.1`.
fn is_substitution(definition: &Definition) -> bool {
    definition.name.contains('#') && !definition.name.contains(crate::resolve::KEY_SEPARATOR)
}

/// The value of a literal TLC holds as a value: a string, or a number within its integers.
fn get_literal(expression: &Expr) -> Option<ConfigValue> {
    match &expression.kind {
        ExpressionKind::String { value } => Some(ConfigValue::String(value.to_string())),
        ExpressionKind::Number { value, .. } if is_tlc_integer(*value) => {
            Some(ConfigValue::Number(*value))
        }
        _ => None,
    }
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
                is_recursive: false,
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
                    is_recursive,
                    params,
                    body,
                    scope,
                },
            )) => Ok(Binding::Closure {
                name: name.clone(),
                is_recursive: *is_recursive,
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
            is_recursive: definition.is_recursive,
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
    let definition = environment
        .config_opdef_header(name)
        .map(crate::environment::ConfigOpDefHeader::definition)
        .or_else(|| get_definition(name, environment));
    let Some(definition) = definition else {
        // `defns` holds a standard module's operator too: the Java method that overrides it, which
        // TLC reports as the value of the name (`<Java Method: ...>`), or its definition.
        if environment.builtins.contains_key(name) {
            return Err(not_yet(
                "a name the configuration gives that is an operator of a standard module",
            ));
        }
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

/// `NotYet` for the value of a name the configuration substitutes a definition for, but TRUE,
/// which TLC checks as the operator it holds the name as: it computed the definition under the
/// definition's own name, and checks the name where the front end would check its value
/// (`SpecProcessor.processSpec`).
fn check_unsubstituted(name: &str, value: &ConfigValue, environment: &Environment) -> Result<()> {
    if environment.substitutions.contains_key(name) && *value != ConfigValue::Boolean(true) {
        return Err(not_yet(
            "a name the configuration substitutes a definition for whose value isn't TRUE",
        ));
    }
    Ok(())
}

/// Whether `defns` keeps the OpDefNode of a 0-ary definition K the configuration substitutes
/// for a declared constant (`CONSTANT J <- K`). `processConstantDefns` takes the modules in the
/// order SANY finishes them, each one's constants (its own and those it extends) before its
/// definitions. The first loop over constants to meet J computes K and sets the value on K
/// (`opDef.setToolObject`) without putting it in `defns`; a loop over definitions that then meets
/// K looks it up to that value, which is no OpDefNode, and puts nothing in `defns` either. The
/// configuration's checks then take K as an operator and evaluate its body
/// (`processConfigInvariants`, `processModelConstraints` and the rest), with no constant-level
/// warning or TLC_CONFIG_ID_HAS_VALUE. Only where the loop over the definitions of K's module
/// comes first does `defns` hold K's value: K of a module the root extends, where J is declared
/// in a module SANY finishes after it. A K or a J the front end can't place in a module declines.
fn is_computed_as_substitute(
    name: &str,
    definition: &Rc<Definition>,
    environment: &Environment,
) -> Result<bool> {
    // A name that is itself a declared constant J is J's entry in `defns`, K's OpDefNode, which
    // TLC evaluates as an operator wherever the configuration names J.
    if !matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
        || environment.constants.contains_key(name)
        || environment
            .root_constants
            .iter()
            .any(|constant| &*constant.name == name)
    {
        return Ok(false);
    }
    let substituted: Vec<&Rc<Declaration>> = environment
        .root_constants
        .iter()
        .filter(|constant| {
            constant.arity == 0
                && environment
                    .substitutions
                    .get(&constant.name)
                    .and_then(|target| environment.definitions.get(target))
                    .is_some_and(|target| Rc::ptr_eq(target, definition))
        })
        .collect();
    if substituted.is_empty() {
        return Ok(false);
    }
    let is_root = environment
        .root_symbols
        .get(name)
        .is_some_and(|symbol| &*symbol.key == name);
    if is_root {
        return Ok(true);
    }
    let unplaced = || {
        not_yet(
            "a definition of another module the configuration names and substitutes for a \
             constant, which the front end can't place in the modules' order",
        )
    };
    // The module that defines K, and the first module that declares one of the J.
    let place = |is_in: &dyn Fn(&Module) -> bool| -> Result<usize> {
        let mut places = environment
            .modules
            .iter()
            .enumerate()
            .filter(|(_, module)| is_in(module))
            .map(|(index, _)| index);
        match (places.next(), places.next()) {
            (Some(index), None) => Ok(index),
            _ => Err(unplaced()),
        }
    };
    let defined = place(&|module| {
        module
            .definitions
            .iter()
            .any(|candidate| Rc::ptr_eq(&candidate.body, &definition.body))
    })?;
    let declared = substituted
        .iter()
        .map(|constant| {
            place(&|module| {
                module
                    .constants
                    .iter()
                    .any(|declared| declared.name == constant.name)
            })
        })
        .collect::<Result<Vec<usize>>>()?;
    Ok(declared
        .into_iter()
        .min()
        .is_some_and(|first| first <= defined))
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
    // `processConstantDefns` computes none that `getLevelBound` finds names a name spelled as a
    // variable (`getVarLoc`), which the configuration's checks then take as an operator.
    if !facts.is_constant_level(definition, environment)
        || is_literal
        || crate::startup::get_definition_level_bound(environment, definition) > 0
        || is_computed_as_substitute(name, definition, environment)?
    {
        return Ok(None);
    }
    let Some(evaluator) = evaluator else {
        return Err(not_yet("a constant definition the configuration names"));
    };
    match evaluator.evaluate(&create_identifier(name), None) {
        Ok(value) => {
            check_unsubstituted(name, &value, environment)?;
            Ok(Some(value))
        }
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

/// `Value#toString` of the values TLC's configuration errors show: a boolean, an integer, or a
/// string, a model value or a set of them where TLC holds them as written, which `expression`, the
/// definition TLC evaluated, or none for a configuration's value, writes as literals. `NotYet` for
/// another value, such as an interval or a record, whose text depends on how TLC built it.
fn format_config_value(
    value: &ConfigValue,
    expression: Option<&Expr>,
    evaluator: Option<&Evaluator>,
) -> Result<String> {
    fn is_literal(expression: &Expr) -> bool {
        match &expression.kind {
            ExpressionKind::Number { .. } | ExpressionKind::String { .. } => true,
            ExpressionKind::SetEnumeration(elements) => elements.iter().all(is_literal),
            _ => false,
        }
    }
    fn format(value: &ConfigValue) -> String {
        match value {
            ConfigValue::Boolean(value) => if *value { "TRUE" } else { "FALSE" }.to_owned(),
            ConfigValue::Number(number) => format!("{number}"),
            // `StringValue.PrintVersion`.
            ConfigValue::String(text) => format!(
                "\"{}\"",
                text.chars()
                    .map(|character| match character {
                        '"' => "\\\"".to_owned(),
                        '\\' => "\\\\".to_owned(),
                        '\t' => "\\t".to_owned(),
                        '\n' => "\\n".to_owned(),
                        '\u{c}' => "\\f".to_owned(),
                        '\r' => "\\r".to_owned(),
                        _ => character.to_string(),
                    })
                    .collect::<String>()
            ),
            ConfigValue::ModelValue(name) => name.clone(),
            ConfigValue::Set(elements) => format!(
                "{{{}}}",
                elements.iter().map(format).collect::<Vec<_>>().join(", ")
            ),
            ConfigValue::Record(_) => unreachable!("a record has no literal"),
        }
    }
    fn is_plain(value: &ConfigValue) -> bool {
        match value {
            ConfigValue::Number(number) => number.fract() == 0.0,
            ConfigValue::Set(elements) => elements.iter().all(is_plain),
            ConfigValue::Record(_) => false,
            _ => true,
        }
    }
    match value {
        ConfigValue::Boolean(_) => return Ok(format(value)),
        ConfigValue::Number(number) if number.fract() == 0.0 => return Ok(format(value)),
        _ => {}
    }
    match evaluator {
        // `SetEnumValue#toString` normalizes the set first.
        Some(evaluator) if is_plain(value) && expression.is_none_or(is_literal) => {
            Ok(format(&evaluator.order.normalize(value)?))
        }
        _ => Err(not_yet("a configuration error that shows a value")),
    }
}

/// Whether an expression refers to a name, directly or through the definitions it applies.
fn reaches_name(expression: &Expr, name: &str, environment: &Environment) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut pending = vec![expression.clone()];
    while let Some(expression) = pending.pop() {
        if let Some(reference) = expression.reference()
            && !expression.is_locally_resolved()
        {
            if &*reference == name {
                return true;
            }
            if let Some(definition) = get_definition(&reference, environment)
                && seen.insert(Rc::as_ptr(definition) as usize)
            {
                pending.push(definition.body.clone());
            }
        }
        pending.extend(expression.children());
    }
    false
}

/// `isConstantTrue`, for a conjunct that is a constant name: TLC drops one that is TRUE, and
/// rejects the spec for any other value. The engine's startup checks a conjunct of the
/// specification the evaluator can't compute, which a definition of the root module names, and
/// one whose computation fails: TLC keeps the definition of a constant it fails to compute as it
/// starts (`processConstantDefns`), and checks its body with the initial predicate
/// (`processConfigSpec`).
fn is_constant_true(
    name: &str,
    item: &Expanded,
    usage: &str,
    environment: &Environment,
    evaluator: Option<&Evaluator>,
) -> Result<bool> {
    let evaluator = evaluator.ok_or_else(|| not_yet("a constant conjunct of the specification"))?;
    let value = match evaluator.evaluate(&item.expression, item.scope.as_ref()) {
        Err(FrontError::NotYet(_) | FrontError::Evaluation(_))
            if usage == "spec"
                && item.scope.is_none()
                && !item.expression.is_locally_resolved()
                && get_definition(name, environment).is_some_and(|definition| {
                    matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                }) =>
        {
            evaluator.defer_conjunct(Rc::from(name));
            return Ok(true);
        }
        value => value?,
    };
    check_unsubstituted(name, &value, environment)?;
    match value {
        ConfigValue::Boolean(true) => Ok(true),
        ConfigValue::Boolean(false) => Err(FrontError::Config(format!(
            "The spec is trivially false because {name} is false."
        ))),
        value => Err(FrontError::Config(format!(
            "The operator {name}, which equals {},\ncannot be used as a {usage}",
            format_config_value(&value, Some(&item.expression), Some(evaluator))?
        ))),
    }
}

/// Whether the definition `name` selects has a module-scoped value, which TLC's selector doesn't
/// read.
fn is_scoped_selection(name: &str, environment: &Environment) -> bool {
    let key = environment
        .root_symbols
        .get(name)
        .map_or_else(|| Rc::from(name), |symbol| symbol.key.clone());
    environment.scoped_selected_values.contains_key(&key)
}

/// A definition K the configuration selects, whose module-scoped value `K = [M] v` the
/// environment left out (`check_selected_scoped_values`). TLC's selector walks K's body as
/// written, but `processConstantDefns` doesn't compute a K of constant level, as `lookup` gives v
/// rather than K's node, so `defns` keeps the node. Where the front end would compute K at
/// startup, the selector then reads what TLC reads only where the two agree:
///
/// - a numeral or string body, which `Tool.eval` reads as v (`getToolObject` of the literal), as
///   INIT, whose `getInitStates` rejects the literal itself without evaluating it, or as an
///   INVARIANT or a PROPERTY where v isn't a boolean, which TLC rejects as it does the literal,
///   in words that show the literal's location, not its value;
/// - a body whose evaluation fails, which TLC swallows at startup and keeps as the node too;
/// - a pure body equal to TRUE as a (ACTION_)CONSTRAINT, which TLC accepts both as the value TRUE
///   and as a node it evaluates to TRUE, or as a PROPERTY, whose body `get_config_predicate`
///   then walks as `processConfigProps` does.
///
/// It declines another K of constant level: TLC's INIT or NEXT takes it as a predicate, not as
/// a constant, its INVARIANT doesn't warn of a TRUE one, it doesn't report another value, and it
/// shows the effects of evaluating it as it checks the states, not at startup. It declines any K
/// of constant level whose value the environment kept, which the front end would read for K.
fn check_scoped_selection(
    kind: &str,
    name: &str,
    definition: &Rc<Definition>,
    environment: &Environment,
    facts: &DefinitionFacts,
    evaluator: Option<&Evaluator>,
) -> Result<()> {
    let key = environment
        .root_symbols
        .get(name)
        .map_or_else(|| Rc::from(name), |symbol| symbol.key.clone());
    let Some(value) = environment.scoped_selected_values.get(&key) else {
        return Ok(());
    };
    if !facts.is_constant_level(definition, environment) {
        return Ok(());
    }
    let declined = || {
        Err(not_yet(
            "a module-scoped configuration value of a constant definition the configuration also selects",
        ))
    };
    // The environment kept v for what else reads it, so the front end would read v for K too,
    // but where `get_config_predicate` walks a PROPERTY's body.
    let is_kept = environment.is_scoped_selection_kept;
    if (is_kept && (kind != "property" || environment.is_scoped_selection_let_instanced))
        || facts.is_impure_definition(definition, environment)
    {
        return declined();
    }
    if matches!(
        definition.body.kind,
        ExpressionKind::Number { .. } | ExpressionKind::String { .. }
    ) {
        let is_read = match kind {
            "initial predicate" => false,
            "invariant" | "property" => matches!(value, ConfigValue::Boolean(_)),
            _ => true,
        };
        // An unnamed INSTANCE's copy (`Name@Root#n`) has a SubstInNode body, whose location TLC
        // shows where it rejects the literal.
        return if !is_read && !key.contains('#') {
            Ok(())
        } else {
            declined()
        };
    }
    let Some(evaluator) = evaluator else {
        return declined();
    };
    let evaluated = if is_kept {
        evaluator.evaluate(&definition.body, None)
    } else {
        evaluator.evaluate(&create_identifier(name), None)
    };
    match evaluated {
        Err(FrontError::Evaluation(_)) => Ok(()),
        Ok(ConfigValue::Boolean(true))
            if matches!(kind, "property" | "constraint" | "action constraint") =>
        {
            Ok(())
        }
        _ => declined(),
    }
}

/// `getConfigDefinition`.
fn get_config_definition(
    kind: &str,
    name: &str,
    environment: &Environment,
    facts: &DefinitionFacts,
    evaluator: Option<&Evaluator>,
    is_deferrable: bool,
) -> Result<()> {
    let assigned = environment.configured_value_bindings.contains(name);
    let definition = if assigned {
        None
    } else {
        let definition = get_config_operator(kind, name, environment)?;
        check_scoped_selection(kind, name, definition, environment, facts, evaluator)?;
        // A constant next-state action TLC keeps as an operator names each step it takes by
        // the body's expression (`TRUE line 4, col 6 to ...`), which the engine's actions don't.
        if kind == "next state action"
            && facts.is_constant_level(definition, environment)
            && is_computed_as_substitute(name, definition, environment)?
        {
            return Err(not_yet(
                "a constant next-state action the configuration substitutes for a constant",
            ));
        }
        Some(definition)
    };
    if assigned
        || get_constant_value(
            name,
            definition.expect("an operator"),
            environment,
            facts,
            evaluator,
            is_deferrable,
        )?
        .is_some()
    {
        // TLC computes the constant definitions, and shows what they print, before it rejects
        // the name (`processConstantDefns`).
        let is_impure = environment.definitions.values().any(|definition| {
            matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && facts.is_impure_definition(definition, environment)
        });
        if is_impure {
            return Err(not_yet(
                "a constant INIT or NEXT after a definition TLC computes with its effects",
            ));
        }
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
    is_warning_enabled: bool,
) -> Result<Option<Vec<Name>>> {
    let analyzer = environment.create_level_analyzer(&[]);
    let mut constant_true = Vec::new();
    for name in &config.invariants {
        // TLC warns about each invariant that is a TRUE constant as it reaches it, before an
        // error in a later one.
        let warned = |error| match error {
            FrontError::Config(_) if is_warning_enabled && !constant_true.is_empty() => {
                FrontError::Warned(
                    crate::model::get_constant_invariant_warnings(&constant_true),
                    Box::new(error),
                )
            }
            error => error,
        };
        // An invariant of TLC's command line (`-inv`), which TLC checks as it is, without the
        // configuration's checks of a constant or of its level: the front end follows one that
        // reads the state and is no action or temporal formula.
        if is_command_line_invariant(name) {
            let Some(definition) = get_definition(name, environment) else {
                return Err(not_yet(
                    "-inv of an expression the front end doesn't define",
                ));
            };
            let levels = analyzer.analyze_definition(definition, &levels::Scope::default())?;
            if levels.data.level >= ACTION_LEVEL {
                return Err(not_yet("-inv of an action or a temporal formula"));
            }
            continue;
        }
        let Some(definition) =
            get_config_predicate("invariant", name, environment, facts, Some(evaluator))
                .map_err(warned)?
        else {
            constant_true.push(Rc::from(name.as_str()));
            continue;
        };
        // `processConfigInvariants` reads the levels SANY gave the definition, where a declared
        // constant the configuration substitutes a definition for is still the declaration.
        let is_substituted = environment
            .root_constants
            .iter()
            .any(|declaration| environment.substitutions.contains_key(&*declaration.name));
        let substituted = analyzer.analyze_definition(definition, &levels::Scope::default());
        let mut levels = match substituted {
            Ok(levels) => levels,
            Err(error) if !is_substituted => return Err(error),
            // A substitute SANY's level check never sees, such as a temporal formula under
            // ENABLED, which TLC meets only as it evaluates the invariant.
            Err(_) => environment
                .create_unsubstituted_level_analyzer()
                .analyze_definition(definition, &levels::Scope::default())?,
        };
        if is_substituted {
            let sany = environment
                .create_unsubstituted_level_analyzer()
                .analyze_definition(definition, &levels::Scope::default())?;
            // An invariant TLC admits by SANY's level whose substitute is an action or a
            // temporal formula, TLC evaluates as it is, of the state alone: it fails on a primed
            // variable as on a temporal operator it reaches.
            levels = sany;
        }
        if levels.data.level >= ACTION_LEVEL {
            // SANY's level check can give a definition levels of parameters it doesn't have
            // (LevelNode.java, 590ff), which TLC notes.
            let note = if levels.data.has_params() {
                "\nNote that a bug can cause TLC to incorrectly report this error.\nIf you believe your TLA+ or PlusCal specification to be correct,\nplease check if this bug described in LevelNode.java starting at line 590ff affects you."
            } else {
                ""
            };
            return Err(warned(FrontError::Config(format!(
                "The invariant {name} is not a state predicate (one with no primes or temporal operators).{note}"
            ))));
        }
    }
    Ok((!evaluator.is_deferring()).then_some(constant_true))
}

/// The LET definitions named so, of any definition's body, once each, and whether a LET's
/// definition without parameters is a name of one.
fn get_let_definitions(name: &str, environment: &Environment) -> (Vec<Rc<Definition>>, bool) {
    let mut found: Vec<Rc<Definition>> = Vec::new();
    let mut is_named = false;
    let mut seen = crate::hash::FastSet::default();
    let mut pending: Vec<Expr> = environment
        .definitions
        .values()
        .map(|definition| definition.body.clone())
        .collect();
    while let Some(expression) = pending.pop() {
        if !seen.insert(Rc::as_ptr(&expression) as usize) {
            continue;
        }
        if let ExpressionKind::Let { definitions, .. } = &expression.kind {
            for definition in definitions {
                if &*definition.name == name
                    && !found.iter().any(|other| Rc::ptr_eq(other, definition))
                {
                    found.push(definition.clone());
                }
                is_named |= matches!(&definition.body.kind,
                    ExpressionKind::Identifier { name: named, .. } if &**named == name)
                    && definition.body.is_locally_resolved();
            }
        }
        pending.extend(expression.children());
    }
    (found, is_named)
}

/// Whether an invariant is one the checker added for TLC's command line (`-inv`, `-invlevel`),
/// by the name TLC gives it (`TLCDebuggerExpression.process`).
pub fn is_command_line_invariant(name: &str) -> bool {
    name.starts_with("__DebuggerExpr__")
}

/// `getSpecification` (`search.ts`).
pub fn get_specification(
    config: &crate::config::ModelConfig,
    environment: &Environment,
    facts: &DefinitionFacts,
    version: TlcVersion,
    evaluator: Option<&Evaluator>,
) -> Result<Specification> {
    let mut subscripts = Vec::new();
    read_specification(
        config,
        environment,
        facts,
        version,
        evaluator,
        &mut subscripts,
    )
}

/// `get_specification`, which gives the subscripts it read in `subscripts` as it fails too: TLC
/// warns of each as it reads it, before an error after it.
pub fn read_specification(
    config: &crate::config::ModelConfig,
    environment: &Environment,
    facts: &DefinitionFacts,
    version: TlcVersion,
    evaluator: Option<&Evaluator>,
    subscripts: &mut Vec<SubscriptCheck>,
) -> Result<Specification> {
    let Some(specification) = &config.specification else {
        let operator = |name: &Option<String>, description: &str| {
            name.as_deref()
                .map(|name| {
                    get_config_definition(description, name, environment, facts, evaluator, true)
                        .map(|()| create_identifier(name))
                })
                .transpose()
        };
        // `processConfigSpec` takes the body of the definition NEXT names, which
        // `Tool.getActions` splits.
        let failure = config
            .next
            .as_deref()
            .and_then(|name| get_definition(name, environment))
            .filter(|definition| {
                matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
            })
            .and_then(|definition| {
                action_split_failure(&definition.body, None, environment, evaluator, 0)
            });
        return Ok(Specification {
            has_action_parameter_cast: false,
            has_action_variable_cast: false,
            has_action_constant_cast: matches!(failure, Some(ActionSplitFailure::Constant)),
            action_unknown_argument: match failure {
                Some(ActionSplitFailure::UnknownArgument(reason)) => Some(reason),
                _ => None,
            },
            is_fairness_tautology: false,
            init: operator(&config.init, "initial predicate")?,
            next: operator(&config.next, "next state action")?,
            scope: None,
            temporals: Vec::new(),
            subscripts: Vec::new(),
        });
    };
    if config.init.is_some() || config.next.is_some() {
        return Err(FrontError::Config(
            "The configuration file cannot specify both INIT/NEXT and SPECIFICATION fields."
                .to_owned(),
        ));
    }
    if environment
        .configured_value_bindings
        .contains(specification.as_str())
        && !get_definition(specification, environment).is_some_and(|definition| {
            facts.is_constant_level(definition, environment)
                && !matches!(
                    definition.body.kind,
                    ExpressionKind::Number { .. } | ExpressionKind::String { .. }
                )
        })
    {
        if environment.definitions.values().any(|definition| {
            matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && facts.is_impure_definition(definition, environment)
        }) {
            return Err(not_yet(
                "a configured SPECIFICATION value after a definition TLC computes with its effects",
            ));
        }
        let value = if let Some(value) = environment
            .constants
            .get(specification.as_str())
            .or_else(|| environment.operator_constants.get(specification.as_str()))
        {
            format_config_value(value, None, evaluator)?
        } else if let Some(rows) = environment
            .builtins
            .get(specification.as_str())
            .and_then(|builtin| builtin.table.as_ref())
        {
            let rows = rows
                .iter()
                .map(|(arguments, value)| {
                    let values = arguments
                        .iter()
                        .chain(std::iter::once(value))
                        .map(|value| format_config_value(value, None, evaluator))
                        .collect::<Result<Vec<_>>>()?;
                    Ok(format!("<{}>", values.join(", ")))
                })
                .collect::<Result<Vec<_>>>()?;
            format!("{{ {}}}", rows.join(", "))
        } else {
            return Err(not_yet("the initial value of the configured SPECIFICATION"));
        };
        return Err(FrontError::Config(format!(
            "The value of {specification} is equal to {value}"
        )));
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
            format_config_value(&value, Some(&definition.body), evaluator)?
        )));
    }
    let expansion = Expansion {
        fairness_property: (config.properties.len() == 1).then(|| config.properties[0].as_str()),
        environment,
        facts,
        version,
        is_property: false,
        is_specification: true,
        evaluator: None,
        is_unrolled: std::cell::Cell::new(false),
        unroll_is_independent: std::cell::Cell::new(!environment.has_java_override_index),
        has_action_substitutions: std::cell::Cell::new(false),
        label_probe: std::cell::Cell::new(false),
        expanding_bindings: std::cell::RefCell::new(Vec::new()),
    };
    let mut init_conjuncts = Vec::new();
    let mut next_actions = Vec::new();
    let mut has_action_parameter_cast = false;
    let mut has_action_variable_cast = false;
    let mut has_action_constant_cast = false;
    let mut action_unknown_argument = None;
    let mut temporals = Vec::new();
    let startup = crate::startup::get_startup_model(environment);
    // TLC prints the warnings of a subscript as it reads it, before an error in a later conjunct.
    let read = (|| -> Result<()> {
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
            // `processConfigSpec` takes a conjunct that names a variable as the value it looks
            // the name up to, its declaration, which it rejects by the declaration's location.
            // A definition whose body is such a conjunct is a state predicate it takes whole.
            // A LET around the conjunct binds other names only.
            let mut relocated = None;
            if let ExpressionKind::Identifier { name, .. } = &item.expression.kind {
                let is_bound = item.expression.is_locally_resolved()
                    || lookup_scope(item.scope.as_ref(), name).is_some();
                let variable = environment
                    .variable_index
                    .get(&*item.expression.reference().unwrap_or_default())
                    .and_then(|&index| environment.variable_locations[index].range.as_ref());
                if !is_bound
                    && !item.has_substitutions
                    && let Some(range) = variable
                {
                    // The conjunct is the body of a definition without parameters, which TLC
                    // takes whole, where `getSpecification` names it by that definition; one it
                    // names by a definition with parameters or by where it is written TLC
                    // reached by inlining the operator it applies (`getOpContext`) and looking
                    // its parameter up to the argument (a `LazyValue`).
                    let is_looked_up = match item.name.as_deref() {
                        None => true,
                        Some(written) if written.starts_with("line ") => true,
                        Some(written) => match (
                            lookup_scope(item.scope.as_ref(), written).map(|(_, binding)| binding),
                            get_definition(written, environment).map(|definition| &definition.kind),
                        ) {
                            // A LET's definition, which the expansion names as it reads it.
                            (Some(Binding::Closure { params, .. }), _) => !params.is_empty(),
                            (
                                Some(Binding::Thunk {
                                    scope: ScopeOf::Own,
                                    ..
                                }),
                                _,
                            ) => false,
                            (None, Some(DefinitionKind::Operator { params, .. })) => {
                                !params.is_empty()
                            }
                            // A LET's definition the expansion read the conjunct in, whose
                            // scope the conjunct's isn't (`S(y) == LET D == y IN Init /\ D`):
                            // one with parameters TLC looks up as above, and one without it
                            // takes whole, wording a failure of the conjunct at the body, the
                            // parameter it looked up, which the expansion holds the argument
                            // for. Where another LET's definition names it (`E == D`), the
                            // expansion names the inner one, and TLC words it at the outer's
                            // body, so that declines.
                            _ => match get_let_definitions(written, environment) {
                                (definitions, false) => match definitions.as_slice() {
                                    [definition]
                                        if matches!(&definition.kind,
                                        DefinitionKind::Operator { params, .. } if !params.is_empty()) =>
                                    {
                                        true
                                    }
                                    [definition]
                                        if matches!(&definition.kind,
                                        DefinitionKind::Operator { params, .. } if params.is_empty())
                                            && matches!(
                                                definition.body.kind,
                                                ExpressionKind::Identifier { .. }
                                            )
                                            && definition.body.is_locally_resolved() =>
                                    {
                                        relocated = Some(definition.body.location.clone());
                                        false
                                    }
                                    _ => {
                                        return Err(not_yet(
                                            "a conjunct of the specification that names a variable through a definition the front end doesn't find",
                                        ));
                                    }
                                },
                                _ => {
                                    return Err(not_yet(
                                        "a conjunct of the specification that names a variable through a definition the front end doesn't find",
                                    ));
                                }
                            },
                        },
                    };
                    if is_looked_up {
                        return Err(FrontError::Config(format!(
                            "The operator {name}, which equals {},\ncannot be used as a spec",
                            format_range(range)
                        )));
                    }
                }
                // An operator's parameter TLC looks up to its argument, which may be a variable
                // it then rejects (`P(a) == a`, `Spec == Init /\ P(x) /\ ...`), and a conjunct
                // an INSTANCE's substitutions may make one.
                let names_definition = |expression: &Expr| {
                    matches!(expression.kind, ExpressionKind::Identifier { .. })
                        && !expression.is_locally_resolved()
                        && environment
                            .definitions
                            .contains_key(&*expression.reference().unwrap_or_default())
                };
                // A LET's definition taken whole reads, through the parameters, an expression that
                // is no name.
                let may_name_variable = if is_bound {
                    !matches!(
                        lookup_scope(item.scope.as_ref(), name),
                        Some((_, Binding::Thunk { expression, .. })) if names_definition(expression)
                    ) && matches!(
                        read_through(&item.expression, item.scope.as_ref()).kind,
                        ExpressionKind::Identifier { .. }
                    )
                } else {
                    item.has_substitutions && !names_definition(&item.expression)
                };
                if may_name_variable && level() == Level::Variable {
                    return Err(not_yet(
                        "a conjunct of the specification that may name a variable through a parameter or an INSTANCE",
                    ));
                }
            }
            let mut item = item;
            if let Some(location) = relocated {
                item.expression = Rc::new(Expression {
                    location,
                    ..(*item.expression).clone()
                });
            }
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
                        && is_constant_true(name, &item, "spec", environment, evaluator)? =>
                {
                    continue;
                }
                ExpressionKind::UnboundedQuantifier {
                    is_temporal: true, ..
                } => return Err(FrontError::Evaluation(
                    "TLC does not support temporal existential, nor universal, quantification over state variables.".to_owned(),
                )),
                ExpressionKind::Always(inner) => match &inner.kind {
                    ExpressionKind::Action {
                        is_box: true,
                        action,
                        subscript,
                    } => {
                        let collector = SubscriptCollector {
                            environment,
                            startup: &startup,
                            evaluator,
                            depth: std::cell::Cell::default(),
                            is_overflowed: std::cell::Cell::default(),
                        };
                        subscripts.push(collector.check(subscript, item.scope.as_ref())?);
                        if !item.has_substitutions {
                            let failure =
                                action_split_failure(
                                    action,
                                    item.scope.as_ref(),
                                    environment,
                                    evaluator,
                                    0,
                                );
                            has_action_parameter_cast |=
                                matches!(failure, Some(ActionSplitFailure::FormalParameter));
                            // The engine declines a variable it finds TLC splits to as TLC builds
                            // its `Tool`, but sees `A` only as the name of the scope the front end
                            // binds around it, so the front end declines that.
                            has_action_variable_cast |= item.scope.is_some()
                                && matches!(failure, Some(ActionSplitFailure::Variable));
                            has_action_constant_cast |=
                                matches!(failure, Some(ActionSplitFailure::Constant));
                            if let Some(ActionSplitFailure::UnknownArgument(reason)) = failure {
                                action_unknown_argument.get_or_insert(reason);
                            }
                        }
                        next_actions.push((action.clone(), item.scope.clone()));
                        // TLC fails at the second next-state relation, reading nothing after it.
                        if next_actions.len() > 1 {
                            break;
                        }
                        continue;
                    }
                    _ if !matches!(
                        inner.kind,
                        ExpressionKind::Let { .. }
                            | ExpressionKind::Label { .. }
                            | ExpressionKind::Number { .. }
                            | ExpressionKind::String { .. }
                    ) && get_level(inner, item.scope.as_ref(), environment, facts, &[])
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
                        "TLC cannot handle this conjunct of the spec:\n{}",
                        describe_range(&item.expression)
                    )));
                }
                // TLC levels PickSuccessor as an action (its Java method's minLevel), and rejects a
                // conjunct that reaches it.
                _ if reaches_name(&item.expression, "PickSuccessor", environment) => {
                    return Err(not_yet("PickSuccessor in a conjunct of the specification"));
                }
                _ => init_conjuncts.push((item.expression, item.scope)),
            }
        }
        Ok(())
    })();
    read?;
    if next_actions.len() > 1 {
        // `processConfigSpec`: EC.TLC_CANT_HANDLE_TOO_MANY_NEXT_STATE_RELS.
        return Err(FrontError::Config(
            "The specification contains more than one conjunct of the form [][Next]_v,\nbut TLC can handle only specifications with one next-state relation.".to_owned(),
        ));
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
    let is_fairness_tautology = !temporals.is_empty()
        && temporals.iter().all(|item| {
            item.is_property_fairness && !matches!(item.expression.kind, ExpressionKind::Always(_))
        });
    Ok(Specification {
        has_action_parameter_cast,
        has_action_variable_cast,
        has_action_constant_cast,
        action_unknown_argument,
        is_fairness_tautology,
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
        subscripts: subscripts.clone(),
    })
}

fn action_argument_level(
    expression: &Expr,
    scope: Option<&Rc<Scope>>,
    environment: &Environment,
) -> Option<u8> {
    let mut frames = Vec::new();
    let mut current = scope;
    while let Some(frame) = current {
        frames.push(frame);
        current = frame.parent.as_ref();
    }
    let mut syntactic = levels::Scope::default();
    for frame in frames.into_iter().rev() {
        let operator = match &frame.binding {
            Binding::Thunk {
                expression,
                scope: ScopeOf::Own,
            } => Some((Vec::new(), expression.clone())),
            Binding::Closure {
                params,
                body,
                scope: ScopeOf::Own,
                ..
            } => Some((params.clone(), body.clone())),
            _ => None,
        };
        if let Some((params, body)) = operator {
            let definition = Rc::new(crate::instances::operator_definition(
                frame.name.clone(),
                params,
                body.clone(),
                true,
                &body.location,
            ));
            syntactic = syntactic.bind_definitions(&[definition]);
        } else {
            let arity = match &frame.binding {
                Binding::Closure { params, .. } => params.len(),
                _ => 0,
            };
            syntactic = syntactic.bind_parameters(&[OperatorParam {
                name: frame.name.clone(),
                arity,
                location: None,
            }]);
        }
    }
    environment
        .create_level_analyzer(&[])
        .analyze(expression, &syntactic)
        .ok()
        .map(|data| data.level)
}

/// Why the front end declines a substituted constant applied as the next-state action to an
/// argument it can't tell TLC evaluates without fail as it splits the action.
pub(crate) const UNKNOWN_ARGUMENT: &str = "a substituted constant applied as the next-state action to an argument the front end can't tell TLC evaluates without fail as it splits the action";

/// Why the front end declines a substituted constant applied as the next-state action to an
/// argument that prints or draws, which TLC evaluates once as it splits the action, binding the
/// value it then reads, or where it fails.
pub(crate) const SHOWN_ARGUMENT: &str = "a substituted constant applied as the next-state action to an argument that prints or draws, which TLC evaluates once as it splits the action";

enum ActionSplitFailure {
    FormalParameter,
    /// A variable, whose declaration `getActionsAppl` casts to OpDefNode.
    Variable,
    /// A declared constant the configuration substitutes a definition for, whose declaration
    /// `getActionsAppl` casts to OpDefNode where it doesn't split the definition.
    Constant,
    /// A substituted constant applied to an argument whose evaluation as `getActionsAppl`
    /// evaluates it the front end can't follow, with why: whether it fails, so that TLC casts,
    /// or what it prints or draws there.
    UnknownArgument(&'static str),
    Other,
}

// `getActionsAppl` of a declared constant of the root module the configuration substitutes a
// name for (`C <- Op`), or `None` for any other name. `processConstants` gives the constant what
// `defns` holds for the name: a definition's OpDefNode, which TLC splits with the arguments bound
// where they are all of constant level, inside a try; or a value, as of another constant or a
// Java method. Where it doesn't split the definition, or the split fails, TLC casts the
// constant's own declaration, an OpDeclNode, to OpDefNode: a ClassCastException only an
// enclosing operator's application or \E catches.
fn substituted_constant_split_failure(
    expression: &Expr,
    name: &Name,
    scope: Option<&Rc<Scope>>,
    environment: &Environment,
    evaluator: Option<&Evaluator>,
    depth: usize,
) -> Option<Option<ActionSplitFailure>> {
    if !environment
        .root_constants
        .iter()
        .any(|declaration| declaration.name == *name)
    {
        return None;
    }
    let target = environment.substitutions.get(name)?;
    let cast = Some(Some(ActionSplitFailure::Constant));
    let definition = match get_definition(name, environment) {
        Some(definition)
            if !environment.builtins.contains_key(target)
                && !environment.configured_value_bindings.contains(target) =>
        {
            definition
        }
        _ => return cast,
    };
    let args: &[Expr] = match &expression.kind {
        ExpressionKind::Apply { args, .. } => args,
        _ => &[],
    };
    let DefinitionKind::Operator { params, .. } = &definition.kind else {
        // A function's definition has no formal parameters to bind an argument to.
        return if args.is_empty() { Some(None) } else { cast };
    };
    if params.len() != args.len()
        || args.iter().any(|arg| {
            action_argument_level(arg, scope, environment)
                .is_some_and(|level| level > levels::CONSTANT_LEVEL)
        })
    {
        return cast;
    }
    // TLC evaluates each argument inside the try as it starts, so one that fails (`C(1 \div 0)`)
    // is a cast too. One that prints or draws there doesn't fail: TLC binds what it drew or
    // printed once to the parameter and splits the body. The engine shows that only where the
    // argument is a draw that can't fail, the body never reads its parameter, and every other
    // draw in the spec shows nothing of what it draws either (`count_hidden_draws`), so that
    // the draw TLC makes as it starts, which moves on the generator the initial states and the
    // assumptions draw from, shows nowhere; any other such argument declines (`SHOWN_ARGUMENT`).
    // One the front end doesn't compute it takes for one that doesn't fail only where it is
    // built of what can't fail (`C(Nat)`, `C(<<1>>[1])`, `is_unfailing_argument`); of another
    // (`C(Len(1))`, `C(CHOOSE n \in Nat : n > 2)`) it can't tell whether TLC casts, and declines
    // (`UNKNOWN_ARGUMENT`).
    let is_unread_draw = |param: &OperatorParam, arg: &Expr| {
        is_infallible_draw(arg, environment)
            && !is_named_in(&definition.body, &param.name)
            && count_all_draws(environment) == count_hidden_draws(environment)
    };
    if args.iter().any(|arg| {
        evaluator.is_some_and(|evaluator| {
            evaluator
                .evaluate(arg, scope)
                .is_err_and(|error| !matches!(error, FrontError::NotYet(_)))
        })
    }) {
        return cast;
    }
    if params.iter().zip(args).any(|(param, arg)| {
        !is_unread_draw(param, arg)
            && crate::lower::reaches_in(arg, environment, &crate::lower::SHOWN_EFFECTS, None)
    }) {
        return Some(Some(ActionSplitFailure::UnknownArgument(SHOWN_ARGUMENT)));
    }
    if params.iter().zip(args).any(|(param, arg)| {
        !is_unread_draw(param, arg)
            && !is_unfailing_argument(arg, scope, environment, &[], &[], 0)
            && evaluator.is_none_or(|evaluator| {
                matches!(evaluator.evaluate(arg, scope), Err(FrontError::NotYet(_)))
            })
    }) {
        return Some(Some(ActionSplitFailure::UnknownArgument(UNKNOWN_ARGUMENT)));
    }
    // An argument the front end binds no value to (a builtin's, as `C(Nat)`) the body reads as
    // the expression; an operator's argument it can't bind leaves the body unknown, which it
    // takes for one that splits, as the engine did before.
    let bound = match bind_operator_arguments(params, args, None, scope, environment) {
        Ok(bound) => bound,
        Err(_) if params.iter().all(|param| param.arity == 0) => {
            params
                .iter()
                .zip(args)
                .fold(None, |parent, (param, argument)| {
                    Some(Rc::new(Scope {
                        name: param.name.clone(),
                        binding: Binding::Thunk {
                            expression: argument.clone(),
                            scope: ScopeOf::Other(scope.cloned()),
                        },
                        parent,
                    }))
                })
        }
        Err(_) => return Some(None),
    };
    Some(
        action_split_failure(
            &definition.body,
            bound.as_ref(),
            environment,
            evaluator,
            depth + 1,
        )
        .map(|failure| match failure {
            ActionSplitFailure::UnknownArgument(_) => failure,
            _ => ActionSplitFailure::Constant,
        }),
    )
}

// Whether TLC evaluates an expression of constant level without fail, as it evaluates a
// substituted constant's argument splitting the next-state action (`Tool.eval`):
// - a literal integer or string, TRUE, FALSE, BOOLEAN, STRING, Nat or Int;
// - a tuple, set enumeration, record, set of records, set of functions, product, SUBSET or Seq
//   of such, which TLC builds without comparing or looking into the parts (`SubsetValue`,
//   `SetOfFcnsValue` are lazy);
// - `{x \in S : P}` and `[x \in S |-> e]` over Nat or Int, which aren't `Reducible`, so that
//   TLC keeps them lazy and evaluates neither P nor e (`SetPredValue`, `FcnLambdaValue`), and the
//   union of such a set with one of the others (`SetCupValue`);
// - the length of a tuple of such, and a sum or difference of such lengths and literals;
// - an element of a tuple of such at an index it writes within the tuple, a field of a record of
//   such it writes, or the value at an integer it writes of a function of one bound variable over
//   Nat or Int whose body is such or the variable;
// - a LET of such, where a function the LET defines over such sets is lazy (`makeRecursive`)
//   and another definition's body is such;
// - a definition of no parameters whose body is such, and a bound parameter that holds a value or
//   is such.
// `bound` holds the names of function constructors' bound variables, and `lets` the definitions
// of the LETs around.
fn is_unfailing_argument(
    expression: &Expr,
    scope: Option<&Rc<Scope>>,
    environment: &Environment,
    bound: &[Name],
    lets: &[Rc<Definition>],
    depth: usize,
) -> bool {
    if depth >= 64 {
        return false;
    }
    let recurse = |expression: &Expr| {
        is_unfailing_argument(expression, scope, environment, bound, lets, depth + 1)
    };
    let integer = |expression: &Expr| get_written_integer(expression, environment);
    let standard = |expression: &Expr, modules: &[&str]| {
        get_standard_builtin(expression, environment, modules)
    };
    let operands_of = |expression: &Expr| -> Vec<Expr> {
        match &expression.kind {
            ExpressionKind::Apply { args, .. } => args.clone(),
            _ => Vec::new(),
        }
    };
    // Nat or Int, which TLC doesn't hold as `Reducible`.
    let is_infinite = |set: &Expr| {
        operands_of(set).is_empty()
            && standard(set, &["Naturals", "Integers"])
                .is_some_and(|name| matches!(&*name, "Nat" | "Int"))
    };
    // A small integer, of a literal, a tuple's length, or a sum or difference of such.
    fn is_small_integer(
        expression: &Expr,
        is_unfailing: &dyn Fn(&Expr) -> bool,
        environment: &Environment,
        depth: usize,
    ) -> bool {
        if depth >= 16 {
            return false;
        }
        match &expression.kind {
            ExpressionKind::Number { value, .. } => value.fract() == 0.0 && value.abs() < 1e6,
            ExpressionKind::Apply { args, .. } => {
                match (
                    get_standard_builtin(
                        expression,
                        environment,
                        &["Naturals", "Integers", "Sequences"],
                    )
                    .as_deref(),
                    &args[..],
                ) {
                    (Some("+" | "-"), [left, right]) => {
                        is_small_integer(left, is_unfailing, environment, depth + 1)
                            && is_small_integer(right, is_unfailing, environment, depth + 1)
                    }
                    (Some("Len"), [tuple]) => {
                        matches!(tuple.kind, ExpressionKind::Tuple(_)) && is_unfailing(tuple)
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }
    match &expression.kind {
        ExpressionKind::Number { .. } => integer(expression).is_some(),
        ExpressionKind::String { .. } => true,
        ExpressionKind::Tuple(items)
        | ExpressionKind::SetEnumeration(items)
        | ExpressionKind::Product(items) => items.iter().all(recurse),
        ExpressionKind::Record { fields, .. } => fields.iter().all(|field| recurse(&field.value)),
        ExpressionKind::FunctionSet { domain, range } => recurse(domain) && recurse(range),
        ExpressionKind::Label { body, .. } => recurse(body),
        ExpressionKind::SetFilter { bound: each, .. } => is_infinite(&each.set),
        ExpressionKind::FunctionConstruction { bounds, body } => {
            let mut inner = bound.to_vec();
            for each in bounds {
                match &each.pattern {
                    BoundPattern::Name { name, .. } => inner.push(name.clone()),
                    BoundPattern::Tuple { .. } => return false,
                }
            }
            bounds.iter().all(|each| recurse(&each.set))
                && (bounds.iter().any(|each| is_infinite(&each.set))
                    || is_unfailing_argument(body, scope, environment, &inner, lets, depth + 1))
        }
        ExpressionKind::Let {
            definitions,
            instances: None,
            body,
            ..
        } => {
            let mut inner = lets.to_vec();
            inner.extend(definitions.iter().cloned());
            is_unfailing_argument(body, scope, environment, bound, &inner, depth + 1)
        }
        ExpressionKind::FieldAccess { record, field } => match &record.kind {
            ExpressionKind::Record {
                is_set: false,
                fields,
            } => {
                fields.iter().any(|each| each.name == *field)
                    && fields.iter().all(|field| recurse(&field.value))
            }
            _ => false,
        },
        ExpressionKind::FunctionApplication { function, args } => {
            let [index] = &args[..] else {
                return false;
            };
            let Some(index) = integer(index) else {
                return false;
            };
            // The function as written, through the LET definitions and the definitions of no
            // parameters that name it.
            let mut function = function.clone();
            let mut defined = None;
            for _ in 0..16 {
                let ExpressionKind::Identifier { name, .. } = &function.kind else {
                    break;
                };
                let definition = if function.is_locally_resolved() {
                    lets.iter()
                        .rev()
                        .find(|definition| definition.name == *name)
                        .cloned()
                } else if !environment.builtins.contains_key(name)
                    && !environment.substitutions.contains_key(name)
                    && !environment.configured_value_bindings.contains(name)
                {
                    get_definition(name, environment).cloned()
                } else {
                    None
                };
                match definition.as_ref().map(|definition| &definition.kind) {
                    Some(DefinitionKind::Operator { params, .. }) if params.is_empty() => {
                        function = definition.as_ref().unwrap().body.clone();
                    }
                    Some(DefinitionKind::Function { bounds }) => {
                        defined = Some((bounds.clone(), definition.as_ref().unwrap().body.clone()));
                        break;
                    }
                    _ => return false,
                }
            }
            let (bounds, body) = match (&function.kind, defined) {
                (_, Some(defined)) => defined,
                (ExpressionKind::Tuple(items), None) => {
                    return index >= 1.0
                        && index <= items.len() as f64
                        && items.iter().all(recurse);
                }
                (ExpressionKind::FunctionConstruction { bounds, body }, None) => {
                    (bounds.clone(), body.clone())
                }
                _ => return false,
            };
            let [
                Bound {
                    pattern: BoundPattern::Name { name, .. },
                    set,
                },
            ] = &bounds[..]
            else {
                return false;
            };
            let is_in_domain = match standard(set, &["Naturals", "Integers"]).as_deref() {
                Some("Nat") if is_infinite(set) => index >= 0.0,
                Some("Int") if is_infinite(set) => true,
                _ => get_written_integers(set, environment)
                    .is_some_and(|values| values.contains(&index)),
            };
            let mut inner = bound.to_vec();
            inner.push(name.clone());
            is_in_domain
                && is_unfailing_argument(&body, scope, environment, &inner, lets, depth + 1)
        }
        ExpressionKind::Identifier { name, .. } | ExpressionKind::Apply { operator: name, .. }
            if expression.is_locally_resolved() =>
        {
            if matches!(expression.kind, ExpressionKind::Apply { .. }) {
                return false;
            }
            if bound.contains(name) {
                return true;
            }
            if let Some(definition) = lets
                .iter()
                .rev()
                .find(|definition| definition.name == *name)
            {
                return match &definition.kind {
                    DefinitionKind::Function { bounds } => {
                        bounds.iter().all(|each| recurse(&each.set))
                    }
                    DefinitionKind::Operator { params, .. } => {
                        params.is_empty() && recurse(&definition.body)
                    }
                };
            }
            match lookup_scope(scope, name) {
                Some((_, Binding::Value(_) | Binding::Literal { .. })) => true,
                Some((
                    _,
                    Binding::Thunk {
                        expression,
                        scope: ScopeOf::Other(outer),
                    },
                )) => is_unfailing_argument(
                    expression,
                    outer.as_ref(),
                    environment,
                    &[],
                    &[],
                    depth + 1,
                ),
                _ => false,
            }
        }
        ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. } => {
            let operands = operands_of(expression);
            if let Some(name) = standard(expression, &["Naturals", "Integers", "Sequences"]) {
                return match (&*name, &operands[..]) {
                    ("TRUE" | "FALSE" | "BOOLEAN" | "STRING" | "Nat" | "Int", []) => true,
                    ("SUBSET" | "Seq", [set]) => recurse(set),
                    ("\\cup", [left, right]) => {
                        (is_infinite(left) || is_infinite(right)) && recurse(left) && recurse(right)
                    }
                    ("\\", [left, right]) => is_infinite(left) && recurse(right),
                    ("..", [_, _]) => {
                        get_written_integers(expression, environment).is_some()
                            || operands
                                .iter()
                                .all(|operand| is_small_integer(operand, &recurse, environment, 0))
                    }
                    ("\\o", [left, right]) => {
                        matches!(left.kind, ExpressionKind::Tuple(_))
                            && matches!(right.kind, ExpressionKind::Tuple(_))
                            && recurse(left)
                            && recurse(right)
                    }
                    ("Head" | "Tail", [tuple]) => {
                        matches!(&tuple.kind, ExpressionKind::Tuple(items) if !items.is_empty())
                            && recurse(tuple)
                    }
                    ("Append", [tuple, item]) => {
                        matches!(tuple.kind, ExpressionKind::Tuple(_))
                            && recurse(tuple)
                            && recurse(item)
                    }
                    ("+" | "-" | "Len", _) => {
                        is_small_integer(expression, &recurse, environment, 0)
                    }
                    _ => false,
                };
            }
            let Some(name) = expression.reference() else {
                return false;
            };
            operands.is_empty()
                && !environment.builtins.contains_key(&name)
                && !environment.substitutions.contains_key(&name)
                && !environment.configured_value_bindings.contains(&name)
                && get_definition(&name, environment).is_some_and(|definition| {
                    matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                        && is_unfailing_argument(&definition.body, None, environment, &[], &[], depth + 1)
                })
        }
        _ => false,
    }
}

// The name of the builtin an expression applies, where it is TLC's own or the standard module's
// among `modules` that defines it, and not one the spec or the configuration redefines.
fn get_standard_builtin(
    expression: &Expr,
    environment: &Environment,
    modules: &[&str],
) -> Option<Name> {
    if expression.is_locally_resolved() {
        return None;
    }
    let name = expression.reference()?;
    let is_builtin = environment
        .builtins
        .get(&name)
        .is_some_and(|builtin| builtin.name == name && builtin.table.is_none())
        && !environment.substitutions.contains_key(&name)
        && !environment.configured_value_bindings.contains(&name)
        && environment.definitions.get(&name).is_none_or(|definition| {
            definition
                .location
                .range
                .as_ref()
                .is_some_and(|range| modules.contains(&&*range.module))
        });
    is_builtin.then_some(name)
}

// The integer an expression writes, of a literal or a sum or difference of such, small enough
// that TLC's arithmetic doesn't overflow.
fn get_written_integer(expression: &Expr, environment: &Environment) -> Option<f64> {
    match &expression.kind {
        ExpressionKind::Number { value, .. } if value.fract() == 0.0 && value.abs() < 1e6 => {
            Some(*value)
        }
        ExpressionKind::Apply { args, .. } => {
            let name = get_standard_builtin(expression, environment, &["Naturals", "Integers"])?;
            match (&*name, &args[..]) {
                ("-.", [operand]) => Some(-get_written_integer(operand, environment)?),
                ("+", [left, right]) => Some(
                    get_written_integer(left, environment)?
                        + get_written_integer(right, environment)?,
                ),
                ("-", [left, right]) => Some(
                    get_written_integer(left, environment)?
                        - get_written_integer(right, environment)?,
                ),
                _ => None,
            }
        }
        _ => None,
    }
}

// The integers of a set an expression writes, of a set enumeration of written integers or an
// interval of two, where TLC builds it without fail and draws from it as from any.
fn get_written_integers(expression: &Expr, environment: &Environment) -> Option<Vec<f64>> {
    let mut values = Vec::new();
    match &expression.kind {
        ExpressionKind::SetEnumeration(elements) => {
            for element in elements {
                let value = get_written_integer(element, environment)?;
                if !values.contains(&value) {
                    values.push(value);
                }
            }
        }
        ExpressionKind::Apply { args, .. } => {
            let name = get_standard_builtin(expression, environment, &["Naturals", "Integers"])?;
            let ("..", [low, high]) = (&*name, &args[..]) else {
                return None;
            };
            let (low, high) = (
                get_written_integer(low, environment)?,
                get_written_integer(high, environment)?,
            );
            if high - low > 1e4 {
                return None;
            }
            let mut value = low;
            while value <= high {
                values.push(value);
                value += 1.0;
            }
        }
        _ => return None,
    }
    Some(values)
}

// Whether an argument is a draw of TLC's or the Randomization module's that can't fail: an
// element of a nonempty set of integers it writes (`get_written_integers`), as
// `RandomElement({1, 2})` or `RandomElement(1..4)`; a subset of such a set, empty too, of a
// size it writes, not negative (`RandomSubset(1, {1, 2})`, `RandomSubset(1, {})`):
// `SubsetEnumerator` draws as many indices as it is asked for, more than the set has too, and
// fails at none; such a draw's TLCEval, or its union with a set of integers it writes.
fn is_infallible_draw(arg: &Expr, environment: &Environment) -> bool {
    let ExpressionKind::Apply { args, .. } = &arg.kind else {
        return false;
    };
    let module = match arg.reference().as_deref() {
        Some("TLCEval" | "RandomElement") => "TLC",
        Some("RandomSubset") => "Randomization",
        _ => "",
    };
    match (
        get_standard_builtin(arg, environment, &[module]).as_deref(),
        &args[..],
    ) {
        (Some("TLCEval"), [inner]) => is_infallible_draw(inner, environment),
        (Some("RandomElement"), [set]) => {
            get_written_integers(set, environment).is_some_and(|values| !values.is_empty())
                || matches!(&set.kind, ExpressionKind::Apply { args, .. }
                    if args.len() == 1
                        && get_standard_builtin(set, environment, &[]).as_deref() == Some("SUBSET")
                        && get_written_integers(&args[0], environment).is_some())
        }
        (Some("RandomSubset"), [size, set]) => {
            get_written_integer(size, environment).is_some_and(|size| size >= 0.0)
                && get_written_integers(set, environment).is_some()
        }
        (Some("\\cup"), [left, right]) => {
            (is_infallible_draw(left, environment)
                && get_written_integers(right, environment).is_some())
                || (get_written_integers(left, environment).is_some()
                    && is_infallible_draw(right, environment))
        }
        _ => {
            // A sum or difference of a draw of an integer and a written integer or another such
            // draw.
            let is_drawn_integer = |operand: &Expr| {
                matches!(
                    operand.reference().as_deref(),
                    Some("RandomElement" | "TLCEval")
                ) && is_infallible_draw(operand, environment)
                    && !matches!(&operand.kind, ExpressionKind::Apply { args, .. }
                    if args.first().is_some_and(|set| {
                        get_standard_builtin(set, environment, &[]).as_deref() == Some("SUBSET")
                    }))
            };
            match (
                get_standard_builtin(arg, environment, &["Naturals", "Integers"]).as_deref(),
                &args[..],
            ) {
                (Some("+" | "-"), [left, right]) => {
                    (is_drawn_integer(left) || get_written_integer(left, environment).is_some())
                        && (is_drawn_integer(right)
                            || get_written_integer(right, environment).is_some())
                        && (is_drawn_integer(left) || is_drawn_integer(right))
                }
                _ => false,
            }
        }
    }
}

// How many of the applications of a builtin that draws the spec writes, counted as
// `count_all_draws` counts them, show nothing of what they draw: those within an argument that
// is an infallible draw (`is_infallible_draw`) of a substituted constant's application, whose
// definition's body never names the parameter; and an element of a set it writes of one
// integer (`RandomElement({0})`), which draws that integer whatever the generator gives.
fn count_hidden_draws(environment: &Environment) -> usize {
    let count = |root: &Expr| {
        let mut count = 0;
        let mut pending = vec![root.clone()];
        while let Some(expression) = pending.pop() {
            if let ExpressionKind::Apply { args, .. } = &expression.kind
                && !expression.is_locally_resolved()
                && let Some(name) = expression.reference()
            {
                if get_standard_builtin(&expression, environment, &["TLC"]).as_deref()
                    == Some("RandomElement")
                    && let [set] = &args[..]
                    && matches!(set.kind, ExpressionKind::SetEnumeration(_))
                    && get_written_integers(set, environment)
                        .is_some_and(|values| values.len() == 1)
                {
                    count += 1;
                    continue;
                }
                let params = environment
                    .root_constants
                    .iter()
                    .any(|declaration| declaration.name == name)
                    .then(|| environment.substitutions.get(&name))
                    .flatten()
                    .filter(|target| {
                        !environment.builtins.contains_key(*target)
                            && !environment.configured_value_bindings.contains(*target)
                    })
                    .and_then(|_| get_definition(&name, environment))
                    .and_then(|definition| match &definition.kind {
                        DefinitionKind::Operator { params, .. } if params.len() == args.len() => {
                            Some((params.clone(), definition.body.clone()))
                        }
                        _ => None,
                    });
                if let Some((params, body)) = params {
                    for (param, arg) in params.iter().zip(args) {
                        if !is_named_in(&body, &param.name) && is_infallible_draw(arg, environment)
                        {
                            count += crate::lower::count_draws(arg);
                        } else {
                            pending.push(arg.clone());
                        }
                    }
                    continue;
                }
            }
            pending.extend(expression.children());
        }
        count
    };
    // A definition TLC computes as it starts, before it splits the next-state action
    // (`processConstantDefns`), whose body is a draw that can't fail, so that TLC doesn't compute
    // it again, draws before that draw.
    let startup: std::collections::HashSet<usize> = environment
        .startup_definitions
        .iter()
        .map(|definition| Rc::as_ptr(definition) as usize)
        .collect();
    let is_drawn_first = |definition: &Rc<Definition>| {
        startup.contains(&(Rc::as_ptr(definition) as usize))
            && matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
            && crate::startup::get_definition_level_bound(environment, definition) == 0
            && is_infallible_draw(&definition.body, environment)
    };
    let mut seen = std::collections::HashSet::new();
    environment
        .definitions
        .values()
        .chain(environment.pre_override_headers.values())
        .filter(|definition| seen.insert(Rc::as_ptr(definition) as usize))
        .map(|definition| {
            if is_drawn_first(definition) {
                return crate::lower::count_draws(&definition.body);
            }
            count(&definition.body)
                + match &definition.kind {
                    DefinitionKind::Function { bounds } => {
                        bounds.iter().map(|bound| count(&bound.set)).sum()
                    }
                    DefinitionKind::Operator { .. } => 0,
                }
        })
        .chain(
            environment
                .assumptions
                .iter()
                .map(|assumption| count(&assumption.expression)),
        )
        .sum()
}

// How many applications of a builtin that draws the spec writes anywhere: in each of its
// definitions, read or not, and in its assumptions.
fn count_all_draws(environment: &Environment) -> usize {
    let mut seen = std::collections::HashSet::new();
    environment
        .definitions
        .values()
        .chain(environment.pre_override_headers.values())
        .filter(|definition| seen.insert(Rc::as_ptr(definition) as usize))
        .map(|definition| {
            crate::lower::count_draws(&definition.body)
                + match &definition.kind {
                    DefinitionKind::Function { bounds } => bounds
                        .iter()
                        .map(|bound| crate::lower::count_draws(&bound.set))
                        .sum(),
                    DefinitionKind::Operator { .. } => 0,
                }
        })
        .chain(
            environment
                .assumptions
                .iter()
                .map(|assumption| crate::lower::count_draws(&assumption.expression)),
        )
        .sum()
}

// Whether an expression names `name` anywhere within it.
fn is_named_in(expression: &Expr, name: &Name) -> bool {
    let mut pending = vec![expression.clone()];
    while let Some(expression) = pending.pop() {
        if let ExpressionKind::Identifier { name: written, .. }
        | ExpressionKind::Apply {
            operator: written, ..
        }
        | ExpressionKind::OperatorReference {
            operator: written, ..
        } = &expression.kind
            && (written == name || expression.reference().as_ref() == Some(name))
        {
            return true;
        }
        pending.extend(expression.children());
    }
    false
}

fn action_split_failure(
    expression: &Expr,
    scope: Option<&Rc<Scope>>,
    environment: &Environment,
    evaluator: Option<&Evaluator>,
    depth: usize,
) -> Option<ActionSplitFailure> {
    if depth >= 256 || environment.tables.is_selection(expression) {
        return None;
    }
    let recurse = |expression, scope| {
        action_split_failure(expression, scope, environment, evaluator, depth + 1)
    };
    match &expression.kind {
        ExpressionKind::Label { body, .. } => recurse(body, scope),
        ExpressionKind::Let {
            definitions, body, ..
        } => {
            let bound = bind_definitions(definitions, scope).ok()?;
            recurse(body, bound.as_ref())
        }
        ExpressionKind::Junction {
            is_and: false,
            operands,
            ..
        } => operands.iter().find_map(|operand| recurse(operand, scope)),
        ExpressionKind::Number { .. }
        | ExpressionKind::Decimal { .. }
        | ExpressionKind::String { .. } => Some(ActionSplitFailure::Other),
        ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. } => {
            let name = expression.reference().unwrap_or_default();
            if !expression.is_locally_resolved()
                && let Some(failure) = substituted_constant_split_failure(
                    expression,
                    &name,
                    scope,
                    environment,
                    evaluator,
                    depth,
                )
            {
                return failure;
            }
            if !expression.is_locally_resolved() && get_definition(&name, environment).is_some() {
                return None;
            }
            let Some((node, binding)) = lookup_scope(scope, &name) else {
                return environment
                    .variable_index
                    .contains_key(name.as_ref())
                    .then_some(ActionSplitFailure::Variable);
            };
            match binding {
                Binding::Thunk {
                    scope: ScopeOf::Own,
                    ..
                }
                | Binding::Closure {
                    scope: ScopeOf::Own,
                    ..
                } => None,
                Binding::Value(_) | Binding::Literal { .. } | Binding::Thunk { .. } => {
                    Some(ActionSplitFailure::FormalParameter)
                }
                Binding::Closure {
                    params,
                    body,
                    scope: closure_scope,
                    ..
                } => {
                    let ExpressionKind::Apply { args, .. } = &expression.kind else {
                        return None;
                    };
                    if args.iter().any(|arg| {
                        action_argument_level(arg, scope, environment)
                            .is_some_and(|level| level > levels::CONSTANT_LEVEL)
                    }) {
                        return Some(ActionSplitFailure::FormalParameter);
                    }
                    let bound = bind_operator_arguments(
                        params,
                        args,
                        closure_scope.resolve(node),
                        scope,
                        environment,
                    )
                    .ok()?;
                    // A failure splitting the actual operator's body is caught, but its
                    // fallback then casts the original formal symbol and fails again.
                    recurse(body, bound.as_ref()).map(|failure| match failure {
                        ActionSplitFailure::UnknownArgument(_) => failure,
                        _ => ActionSplitFailure::FormalParameter,
                    })
                }
            }
        }
        _ => None,
    }
}

/// What `processConfigSpec` finds of the subscript of `[][Next]_v`: that it can't tell whether it
/// holds every state variable, or the variables it doesn't hold.
#[derive(Clone, Debug)]
pub enum SubscriptCheck {
    Undetermined,
    Missing(Vec<Name>),
    /// What the front end can't tell, with why: the warnings, which a check that prints none
    /// doesn't need.
    Unknown(&'static str),
}

impl SubscriptCheck {
    pub fn is_warned(&self) -> bool {
        !matches!(self, SubscriptCheck::Missing(missing) if missing.is_empty())
    }
}

/// Why the front end can't follow a subscript as TLC reads it.
struct Unfollowed(&'static str);

/// How deep the collector reads before it takes the reading for one that doesn't end, far deeper
/// than a subscript's operators nest, and short of the front end's stack.
const MAXIMUM_SUBSCRIPT_DEPTH: usize = 256;

/// Why the collector stops where an operator leads back to itself: TLC's collector reads it again
/// and again, overflowing its stack, a StackOverflowError it doesn't catch, whatever -nowarning
/// says.
const RECURSIVE_SUBSCRIPT: &str = "a subscript of [][Next]_v that an operator leads back to itself, which TLC reads until its stack overflows";

/// `processConfigSpec`'s `SubscriptCollector`: the state variables in the subscript of
/// `[][Next]_v`, through tuples, the operators it applies and the definitions it names, where TLC
/// holds them as operators. Any other builtin it ignores, and anything but an operator's
/// application it can't read, a number or a string, after which TLC warns that it can't tell.
struct SubscriptCollector<'a, 'b> {
    environment: &'a Environment,
    startup: &'a crate::startup::StartupModel,
    evaluator: Option<&'a Evaluator<'b>>,
    /// How deep the reading is.
    depth: std::cell::Cell<usize>,
    /// Whether a reading went deeper than any that ends.
    is_overflowed: std::cell::Cell<bool>,
}

impl SubscriptCollector<'_, '_> {
    /// What TLC finds of the subscript.
    fn check(&self, subscript: &Expr, scope: Option<&Rc<Scope>>) -> Result<SubscriptCheck> {
        let mut found = Vec::new();
        match self.enter(subscript, scope, &mut found) {
            Ok(true) => {}
            Ok(false) => return Ok(SubscriptCheck::Undetermined),
            Err(Unfollowed(RECURSIVE_SUBSCRIPT)) => return Err(not_yet(RECURSIVE_SUBSCRIPT)),
            Err(Unfollowed(reason)) => return Ok(SubscriptCheck::Unknown(reason)),
        }
        Ok(SubscriptCheck::Missing(
            self.environment
                .variables
                .iter()
                .filter(|variable| !found.contains(*variable))
                .cloned()
                .collect(),
        ))
    }

    /// Whether an expression of constant level evaluates without fail, which TLC then holds as a
    /// value as it starts: literals, tuples, set enumerations and records of such, what Print and
    /// PrintT print of such, and definitions of such.
    fn is_total(&self, expression: &Expr) -> bool {
        // A definition that names itself, which TLC computes until its stack overflows, as its
        // collector reads one.
        if self.depth.get() >= MAXIMUM_SUBSCRIPT_DEPTH {
            self.is_overflowed.set(true);
            return false;
        }
        self.depth.set(self.depth.get() + 1);
        let is_total = self.is_total_once(expression);
        self.depth.set(self.depth.get() - 1);
        is_total
    }

    /// `is_total`, where a definition that names itself is a reading that doesn't end.
    fn total(&self, expression: &Expr) -> std::result::Result<bool, Unfollowed> {
        let is_total = self.is_total(expression);
        if self.is_overflowed.get() {
            return Err(Unfollowed(RECURSIVE_SUBSCRIPT));
        }
        Ok(is_total)
    }

    fn is_total_once(&self, expression: &Expr) -> bool {
        match &expression.kind {
            ExpressionKind::Number { .. } | ExpressionKind::String { .. } => true,
            ExpressionKind::Tuple(items) | ExpressionKind::SetEnumeration(items) => {
                items.iter().all(|item| self.is_total(item))
            }
            ExpressionKind::Record {
                is_set: false,
                fields,
            } => fields.iter().all(|field| self.is_total(&field.value)),
            ExpressionKind::Label { body, .. } => self.is_total(body),
            ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. } => {
                if expression.is_locally_resolved() {
                    return false;
                }
                let Some(name) = expression.reference() else {
                    return false;
                };
                let args: &[Expr] = match &expression.kind {
                    ExpressionKind::Apply { args, .. } => args,
                    _ => &[],
                };
                if self.environment.builtins.contains_key(&name) {
                    return match (&*name, args) {
                        ("TRUE" | "FALSE", []) => true,
                        ("Print", [_, _]) | ("PrintT", [_]) => {
                            args.iter().all(|argument| self.is_total(argument))
                        }
                        _ => false,
                    };
                }
                args.is_empty()
                    && get_definition(&name, self.environment).is_some_and(|definition| {
                        matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                            && self.is_total(&definition.body)
                    })
            }
            _ => false,
        }
    }

    // `enter`: false where TLC gives up on the subscript.
    fn enter(
        &self,
        expression: &Expr,
        scope: Option<&Rc<Scope>>,
        found: &mut Vec<Name>,
    ) -> std::result::Result<bool, Unfollowed> {
        // The collector reads every expression a finite spec gives it but where an operator leads
        // back to itself, so a reading this deep is one that doesn't end.
        if self.depth.get() >= MAXIMUM_SUBSCRIPT_DEPTH {
            return Err(Unfollowed(RECURSIVE_SUBSCRIPT));
        }
        self.depth.set(self.depth.get() + 1);
        let entered = self.enter_once(expression, scope, found);
        self.depth.set(self.depth.get() - 1);
        entered
    }

    fn enter_once(
        &self,
        expression: &Expr,
        scope: Option<&Rc<Scope>>,
        found: &mut Vec<Name>,
    ) -> std::result::Result<bool, Unfollowed> {
        let environment = self.environment;
        if environment.tables.selection_location(expression).is_some() {
            return Ok(true);
        }
        match &expression.kind {
            ExpressionKind::Number { .. }
            | ExpressionKind::Decimal { .. }
            | ExpressionKind::String { .. }
            | ExpressionKind::ExceptAt => return Ok(false),
            ExpressionKind::Tuple(items) => {
                for item in items {
                    if !self.enter(item, scope, found)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            ExpressionKind::Let {
                definitions, body, ..
            } => {
                // TLC's collector binds no LET definition: it looks one up as it looks up any
                // operator, so a function definition, whose body is a function constructor, a
                // builtin it ignores, reads as a value would.
                let mut bound = scope.cloned();
                for definition in definitions {
                    let binding = match &definition.kind {
                        DefinitionKind::Function { .. } => {
                            Binding::Value(ConfigValue::Boolean(true))
                        }
                        DefinitionKind::Operator { params, .. } if !params.is_empty() => {
                            Binding::Closure {
                                name: definition.name.clone(),
                                is_recursive: definition.is_recursive,
                                params: params.clone(),
                                body: definition.body.clone(),
                                scope: ScopeOf::Own,
                            }
                        }
                        // What an INSTANCE in the LET substitutes for a declaration, which TLC
                        // binds as a LazyValue of the substitution (`SubstInKind`), so a literal
                        // there is one it reads, not one it holds.
                        DefinitionKind::Operator { .. } if is_substitution(definition) => {
                            Binding::Thunk {
                                expression: definition.body.clone(),
                                scope: ScopeOf::Other(scope.cloned()),
                            }
                        }
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
                return self.enter(body, bound.as_ref(), found);
            }
            ExpressionKind::Label { body, .. } => return self.enter(body, scope, found),
            ExpressionKind::Subexpression { .. } => {
                return Err(Unfollowed(
                    "a subexpression name in the subscript of [][Next]_v",
                ));
            }
            ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. } => {}
            // TLC ignores the other builtins.
            _ => return Ok(true),
        }
        let Some(name) = expression.reference() else {
            return Ok(true);
        };
        // TLC reads a name bound in the context through the LazyValue of its expression. The
        // definitions an INSTANCE in a LET makes are the LET's, which the copies' bodies name by
        // keys no global definition, variable or constant has.
        let is_scoped = expression.is_locally_resolved()
            || (get_definition(&name, environment).is_none()
                && !environment.variable_index.contains_key(&name)
                && !environment.constants.contains_key(&name)
                && !environment.builtins.contains_key(&name));
        if is_scoped && let Some((node, binding)) = lookup_scope(scope, &name) {
            match binding {
                // A LET definition whose body is a literal TLC holds as the literal's value
                // (`processConstants`), which the collector ignores.
                Binding::Thunk {
                    expression: bound,
                    scope: ScopeOf::Own,
                } if matches!(
                    bound.kind,
                    ExpressionKind::Number { .. } | ExpressionKind::String { .. }
                ) =>
                {
                    return Ok(true);
                }
                Binding::Thunk {
                    expression: bound,
                    scope: bound_scope,
                } => {
                    let bound_scope = bound_scope.resolve(node);
                    return self.enter(bound, bound_scope.as_ref(), found);
                }
                Binding::Literal { expression, .. } => return self.enter(expression, None, found),
                // A value TLC holds as one: a quantifier's element, or a constant's.
                Binding::Value(_) => return Ok(true),
                Binding::Closure { .. } => {}
            }
        }
        if !expression.is_locally_resolved() {
            if environment.variable_index.contains_key(&name) {
                found.push(name);
                return Ok(true);
            }
            // A constant or a definition the configuration gives a value TLC holds as the value.
            if environment.constants.contains_key(&name) {
                return Ok(true);
            }
            if let Some(target) = environment.substitutions.get(&name) {
                // TLC gives a declared constant or a definition the configuration substitutes the
                // OpDefNode of what substitutes it (`processConstants`), which the collector
                // enters as an operator, whatever TLC computed of either as it started.
                // The node is the substitute's own, never the value of its body, a literal too.
                let unfollowed = Unfollowed(
                    "a subscript of [][Next]_v that names what the configuration substitutes",
                );
                // A builtin, which TLC holds as its Java method's value, the collector ignores, as
                // it ignores a builtin the subscript names.
                if environment.builtins.contains_key(target) {
                    return Ok(true);
                }
                let Some(definition) = environment.definitions.get(target) else {
                    return Err(unfollowed);
                };
                // A function definition's body is a function constructor, a builtin it ignores.
                let DefinitionKind::Operator { params, .. } = &definition.kind else {
                    return Ok(true);
                };
                let args: &[Expr] = match &expression.kind {
                    ExpressionKind::Apply { args, .. } => args,
                    _ => &[],
                };
                if params.len() != args.len() {
                    return Err(unfollowed);
                }
                let bound = bind_operator_arguments(params, args, None, scope, environment)
                    .map_err(|_| {
                        Unfollowed("an operator's arguments the front end doesn't bind")
                    })?;
                return self.enter(&definition.body, bound.as_ref(), found);
            }
        }
        let Some((params, body, closure_scope)) =
            resolve_apply_operator(expression, scope, environment)
        else {
            // A builtin, which TLC ignores, or a function definition, a builtin's application
            // where TLC doesn't hold its value. A name an INSTANCE substitutes, which TLC reads
            // through the substitution's value, the front end doesn't follow.
            if environment.builtins.contains_key(&name)
                || get_definition(&name, environment).is_some()
            {
                return Ok(true);
            }
            return Err(Unfollowed(
                "a name in the subscript of [][Next]_v that the front end doesn't follow",
            ));
        };
        // `lookup` gives an operator without a value of its own its body's, which TLC gives
        // every literal (`processConstants`), so the collector ignores an operator whose body is
        // one, a LAMBDA's included.
        if get_literal(&body).is_some() {
            return Ok(true);
        }
        if params.is_empty() {
            if !expression.is_locally_resolved()
                && let Some(definition) = get_definition(&name, environment)
            {
                match self.startup.read(definition) {
                    crate::startup::Read::Literal => return Ok(true),
                    // TLC computes the definition as it starts: where that succeeds it holds the
                    // value, which the collector ignores, and where it fails, the operator, whose
                    // body it enters. Of constant level, the body holds no variable, so the two
                    // differ only where the body reaches what the collector gives up at.
                    crate::startup::Read::Attempted => {
                        let computed = match self.evaluator {
                            Some(evaluator) => match evaluator.evaluate(&body, None) {
                                Ok(_) => Some(true),
                                Err(FrontError::Evaluation(_)) => Some(false),
                                Err(_) => None,
                            },
                            None => None,
                        };
                        return match computed {
                            Some(true) => Ok(true),
                            Some(false) => self.enter(&body, closure_scope.as_ref(), found),
                            None if self.total(&body)? => Ok(true),
                            None => {
                                match self.enter(&body, closure_scope.as_ref(), &mut Vec::new()) {
                                    Ok(true) => Ok(true),
                                    Err(Unfollowed(RECURSIVE_SUBSCRIPT)) => {
                                        Err(Unfollowed(RECURSIVE_SUBSCRIPT))
                                    }
                                    _ => Err(Unfollowed(
                                        "a definition in the subscript of [][Next]_v that TLC may compute as it starts",
                                    )),
                                }
                            }
                        };
                    }
                    crate::startup::Read::Operator => {}
                }
            }
            return self.enter(&body, closure_scope.as_ref(), found);
        }
        let ExpressionKind::Apply { args, .. } = &expression.kind else {
            return Ok(true);
        };
        if params.len() != args.len() {
            return Ok(true);
        }
        let bound = bind_operator_arguments(&params, args, closure_scope, scope, environment)
            .map_err(|_| Unfollowed("an operator's arguments the front end doesn't bind"))?;
        self.enter(&body, bound.as_ref(), found)
    }
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
    pub wrapper: Expr,
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
    /// Whether a property's \A was unrolled, as `Expansion::is_unrolled`.
    pub is_unrolled: bool,
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
    // A numeral or string K that only a PROPERTY selects, defined in a module the root extends,
    // keeps a TRUE scoped value under K's key (`Name@Module`), not its name
    // (`check_selected_scoped_values`): `processConfigProps` takes the literal as an implied
    // initial predicate, which `Tool.eval` reads as the value (`getToolObject` of the literal).
    let key = environment
        .root_symbols
        .get(name)
        .map(|symbol| symbol.key.clone())
        .filter(|key| **key != *name);
    let kept_literal = key.as_ref().and_then(|key| {
        let value = environment.constants.get(key)?;
        let definition = environment.definitions.get(key)?;
        (kind == "property"
            && matches!(value, ConfigValue::Boolean(true))
            && !environment.scoped_selected_values.contains_key(key)
            && matches!(
                definition.body.kind,
                ExpressionKind::Number { .. } | ExpressionKind::String { .. }
            ))
        .then(|| value.clone())
    });
    let (definition, value) = match environment.constants.get(name).cloned().or(kept_literal) {
        Some(value) => (None, Some(value)),
        None => {
            let definition = get_config_operator(kind, name, environment)?;
            check_scoped_selection(kind, name, definition, environment, facts, evaluator)?;
            // `processConfigProps` walks the body of a K whose scoped value `defns` doesn't
            // hold, as it does a definition above constant level: it unrolls a \A and stops at
            // one over the empty set (`EC.TLC_LIVE_FORMULA_TAUTOLOGY`).
            let value = if kind == "property" && is_scoped_selection(name, environment) {
                None
            } else {
                get_constant_value(name, definition, environment, facts, evaluator, true)?
            };
            (Some(definition), value)
        }
    };
    match value {
        None => Ok(definition),
        Some(ConfigValue::Boolean(true)) => Ok(None),
        Some(value) => Err(FrontError::Config(format!(
            "The {kind} of {name} is equal to {}",
            format_config_value(
                &value,
                definition.map(|definition| &definition.body),
                evaluator
            )?
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

/// The level SANY gives a definition, where the configuration substitutes a definition for a
/// declared constant of the root module and that substitute changes the definition's level, or
/// none where no substitute changes it.
fn get_substituted_level_change(
    definition: &Rc<Definition>,
    environment: &Environment,
) -> Option<Result<u8>> {
    let is_substituted = environment
        .root_constants
        .iter()
        .any(|declaration| environment.substitutions.contains_key(&*declaration.name));
    if !is_substituted {
        return None;
    }
    let scope = levels::Scope::default();
    let sany = environment
        .create_unsubstituted_level_analyzer()
        .analyze_definition(definition, &scope)
        .map(|levels| levels.data.level);
    let substituted = environment
        .create_level_analyzer(&[])
        .analyze_definition(definition, &scope)
        .map(|levels| levels.data.level);
    match (sany, substituted) {
        (Ok(sany), Ok(substituted)) if sany == substituted => None,
        (sany, _) => Some(sany),
    }
}

pub fn get_properties(
    config: &crate::config::ModelConfig,
    environment: &Environment,
    facts: &DefinitionFacts,
    version: TlcVersion,
    evaluator: Option<&Evaluator>,
) -> Result<Properties> {
    let with_warnings = |error, properties: &Properties| {
        if properties.state_level.is_empty() {
            error
        } else {
            FrontError::Warned(
                crate::model::get_search_warnings(&[], &[], &properties.state_level),
                Box::new(error),
            )
        }
    };
    let mut properties = Properties::default();
    let expansion = Expansion {
        fairness_property: None,
        environment,
        facts,
        version,
        is_property: version != TlcVersion::V1_7_4,
        is_specification: false,
        evaluator,
        is_unrolled: std::cell::Cell::new(false),
        unroll_is_independent: std::cell::Cell::new(!environment.has_java_override_index),
        has_action_substitutions: std::cell::Cell::new(false),
        label_probe: std::cell::Cell::new(false),
        expanding_bindings: std::cell::RefCell::new(Vec::new()),
    };
    for name in &config.properties {
        let Some(definition) =
            get_config_predicate("property", name, environment, facts, evaluator)
                .map_err(|error| with_warnings(error, &properties))?
        else {
            continue;
        };
        // `processConfigProps` takes a function definition's constructor as an implied initial
        // predicate, which TLC rejects as it checks the initial states.
        if matches!(definition.kind, DefinitionKind::Function { .. }) {
            return Err(not_yet(
                "a function definition the configuration names as a PROPERTY",
            ));
        }
        let name: Name = Rc::from(name.as_str());
        // `processConfig` warns about a state-level property by `OpDefNode.getLevel`, the level
        // SANY gave the definition, where a declared constant the configuration substitutes a
        // definition for is still the declaration. Only `processConfigProps`'s `getLevelBound`
        // sees the substitute, so one that changes the property's level changes the error that
        // follows, not the warning.
        let is_state_level = match get_substituted_level_change(definition, environment) {
            Some(Ok(sany_level)) => sany_level == levels::VARIABLE_LEVEL,
            Some(Err(_)) => {
                return Err(with_warnings(
                    not_yet("a property SANY's level check rejects before its substitute"),
                    &properties,
                ));
            }
            None => get_level(&definition.body, None, environment, facts, &[]) == Level::Variable,
        };
        if is_state_level {
            properties.state_level.push(name.clone());
        }
        let expanded = expansion
            .expand(&definition.body, None, &[], false, None)
            .map_err(|error| with_warnings(error, &properties))?;
        for item in expanded {
            let level = |expression: &Expr| {
                get_level(expression, item.scope.as_ref(), environment, facts, &[])
            };
            let conjunct = &item.expression;
            if let ExpressionKind::Identifier { name, .. } = &conjunct.kind
                && level(conjunct) == Level::Constant
                && is_constant_true(name, &item, "property", environment, evaluator)
                    .map_err(|error| with_warnings(error, &properties))?
            {
                continue;
            }
            // A property `getLevelBound` takes for a state's, as it names a name spelled as a
            // variable, which `processConstantDefns` didn't compute: `processConfigProps` takes
            // each conjunct it unrolls to as a predicate of the initial states, which one of
            // constant level the evaluator computes TRUE, without an effect (it computes none),
            // holds in.
            if level(conjunct) == Level::Constant
                && crate::startup::get_definition_level_bound(environment, definition) > 0
                && evaluator.is_some_and(|evaluator| {
                    matches!(
                        evaluator.evaluate(conjunct, item.scope.as_ref()),
                        Ok(ConfigValue::Boolean(true))
                    )
                })
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
                        wrapper: body.clone(),
                        action: action.clone(),
                        subscript: subscript.clone(),
                        scope: item.scope,
                    });
                    continue;
                }
                // `processConfigProps` takes the operand of [] as an invariant where
                // `getLevelBound` finds it below action level. That bound counts an operator's
                // every argument and a LET's every definition, so `[](F(x'))` with `F(p) == x =
                // 0` is a temporal property, whose operand the liveness checker then takes as
                // the state predicate SANY levels it as; and it gives an operator argument level
                // 0, so that an operator that applies a temporal LAMBDA it is passed is an
                // invariant, which TLC rejects as it evaluates it.
                if crate::startup::get_level_bound(environment, body, item.scope.as_ref()) < 2 {
                    // TLC names the invariant by the operator the property asserts always holds,
                    // when it applies the operator to no arguments.
                    // SANY names a definition an INSTANCE copies by its path (`I!Inv`,
                    // `I!J!Inv`), which `getName` gives.
                    let instanced = match &body.kind {
                        ExpressionKind::Identifier { name, .. } if name.contains('!') => {
                            Some(name.clone())
                        }
                        _ => None,
                    };
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
                            |operator| instanced.unwrap_or_else(|| operator.name.clone()),
                        ),
                        expression: body.clone(),
                        scope: item.scope,
                    });
                    continue;
                }
            }
            // `getLevelBound` again, as `processConfigProps` sorts the conjunct by it.
            match crate::startup::get_level_bound(environment, conjunct, item.scope.as_ref()) {
                0 | 1 => properties.initial_predicates.push(Property {
                    name: part_name,
                    expression: item.expression,
                    scope: item.scope,
                }),
                3 => properties.liveness.push(Property {
                    name: name.clone(),
                    expression: item.expression,
                    scope: item.scope,
                }),
                _ => {
                    return Err(with_warnings(
                        FrontError::Config(get_action_property_message(&part_name, conjunct)),
                        &properties,
                    ));
                }
            }
        }
    }
    properties.is_unrolled = expansion.is_unrolled.get();
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
        // TLC generates a module that defines the predicate's check twice, whose semantic
        // analysis fails (`processConfigPossible`, `EC.TLC_PARSING_FAILED2`), after it has
        // checked every name the configuration lists, which isn't followed.
        if config.possible[..index].contains(name) {
            return Err(FrontError::NotYet(
                "a _POSSIBLE predicate listed more than once".into(),
            ));
        }
        get_config_definition("possible", name, environment, facts, evaluator, true)?;
        if get_level(&create_identifier(name), None, environment, facts, &[]) == Level::Temporal {
            return Err(FrontError::Config(format!(
                "The possible of {name} is equal to a temporal formula; only state- and action-level predicates are supported"
            )));
        }
    }
    if environment.variables.is_empty() {
        return Ok(());
    }
    if let Some(name) = &config.view {
        // `getViewSpec` rejects a name `defns` holds a value for, a constant the configuration
        // assigns or a definition TLC computed as it started, as it does an ALIAS.
        // `TLCStateMut.setTool` reads the VIEW before the SYMMETRY. No startup check follows
        // for a VIEW, so a constant definition the evaluator can't compute, which TLC computed
        // and rejects (`V == PrintT("v")`, `V == RandomElement({1, 2})`), declines.
        get_config_definition("view function", name, environment, facts, evaluator, false)?;
    }
    if let Some(name) = &config.symmetry {
        // `getSymmetryGroup` reads the definition by its name, without the substitutions.
        let definition = environment.definitions.get(name.as_str());
        if definition.is_none() && !environment.constants.contains_key(name.as_str()) {
            return Err(FrontError::Config(format!(
                "The symmetry function {name} specified in the configuration file\nis not defined in the specification."
            )));
        }
        // TLC evaluates the body of a definition with parameters without them.
        if definition.is_some_and(|definition| {
            !matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
        }) {
            return Err(FrontError::NotYet(
                "a SYMMETRY definition with parameters".to_owned(),
            ));
        }
        if definition.is_none() {
            return Err(FrontError::Evaluation(format!(
                "{}The symmetry function {name} must specify a set of permutations.",
                crate::errors::UNEXPECTED_EXCEPTION
            )));
        }
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
    conjuncts: &[Name],
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
    let conjuncts: Vec<String> = conjuncts.iter().map(|name| name.to_string()).collect();
    [
        named(PredicateForm::Predicate, "invariant", &config.invariants),
        specification,
        named(PredicateForm::Conjunct, "spec", &conjuncts),
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
        // TLC checks an invariant of its command line in each state, as it is.
        if environment.constants.contains_key(name.as_str())
            || (kind == "invariant" && is_command_line_invariant(&name))
        {
            return None;
        }
        let definition = get_definition(&name, environment)?;
        let is_evaluated = matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
            && facts.is_constant_level(definition, environment)
            && !matches!(
                definition.body.kind,
                ExpressionKind::Number { .. } | ExpressionKind::String { .. }
            )
            // `defns` keeps the operator, whose body the configuration's checks evaluate
            // (`is_computed_as_substitute`, which declines a shape it can't tell first).
            && !matches!(
                is_computed_as_substitute(&name, definition, environment),
                Ok(true)
            );
        is_evaluated.then(|| (form, kind, name, definition.clone()))
    })
    .collect()
}

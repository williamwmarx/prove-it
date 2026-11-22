//! Which definitions TLC computes as it starts (`SpecProcessor.processConstantDefns`), and what a
//! read of each then gives, as `design/startup.md` lays out. TLC attempts a 0-ary definition the
//! configuration substitutes for a declared constant whatever its level, and a 0-ary definition
//! of a module it processes where `getLevelBound` finds its body of constant level. A literal body
//! TLC holds without computing it (`processConstants`). Whether an attempt succeeds only the run
//! knows: one that fails leaves the definition an operator.

use std::cell::{OnceCell, RefCell};
use std::rc::Rc;
use std::sync::OnceLock;

use crate::ast::*;
use crate::environment::Environment;
use crate::hash::{FastMap, FastSet};
use crate::spec::get_definition;

/// TLC's Java overrides of TLA+ operators, by module: each operator with its level (`minLevel`).
const TLC_OVERRIDES: &str = include_str!("tlc_overrides.tsv");

/// The overrides as (module, operator, level), read from the table once.
static OVERRIDES: OnceLock<Vec<(&'static str, &'static str, u8)>> = OnceLock::new();

// TLC's overrides as (module, operator, level).
pub(crate) fn get_overrides() -> impl Iterator<Item = (&'static str, &'static str, u8)> {
    OVERRIDES
        .get_or_init(|| {
            TLC_OVERRIDES
                .lines()
                .filter(|line| !line.starts_with('#'))
                .filter_map(|line| {
                    let mut fields = line.split('\t');
                    Some((fields.next()?, fields.next()?, fields.next()?.parse().ok()?))
                })
                .collect()
        })
        .iter()
        .copied()
}

/// The level of the Java method TLC reads each overridden definition through instead of its
/// body, by the body's address: TLC sets the method on the body of the operator the module of
/// the class defines (`processModuleOverrides`), which a lookup finds there, and on no other
/// operator spelled the same.
fn get_overridden_bodies(environment: &Environment) -> FastMap<usize, u8> {
    let mut bodies = FastMap::default();
    for (module, operator, level) in get_overrides() {
        for linked in environment
            .modules
            .iter()
            .filter(|linked| &*linked.name == module)
        {
            for definition in &linked.definitions {
                if &*definition.name == operator {
                    bodies.insert(Rc::as_ptr(&definition.body) as usize, level);
                }
            }
        }
    }
    bodies
}

/// The level of the Java method of a builtin, an operator of a standard module the front end
/// implements, which no definition of the spec can be.
fn get_builtin_override_level(name: &str) -> Option<u8> {
    get_overrides()
        .find(|&(_, operator, _)| operator == name)
        .map(|(_, _, level)| level)
}

/// What a read of a definition gives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Read {
    /// The literal its body is, which TLC holds without evaluating it (`processConstants`).
    Literal,
    /// The value TLC computes as it starts, where that succeeds.
    Attempted,
    /// Its body, evaluated at each read.
    Operator,
}

/// Why TLC attempts a definition as it starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rule {
    /// The configuration substitutes it for a declared constant (`C <- D`).
    Substitute,
    /// `getLevelBound` finds its body of constant level.
    Constant,
}

/// TLC's startup decision for each 0-ary definition of a model.
pub struct StartupModel {
    /// The definitions TLC attempts, each with the rule it attempts it by.
    pub attempted: Vec<(Rc<Definition>, Rule)>,
    reads: FastMap<usize, Read>,
    /// The definitions whose `defns` entry TLC replaces with the value it computes, which the
    /// checks of the configuration's names read.
    held_in_defns: FastSet<usize>,
}

impl StartupModel {
    pub fn read(&self, definition: &Rc<Definition>) -> Read {
        self.reads
            .get(&key(definition))
            .copied()
            .unwrap_or(Read::Operator)
    }

    /// Whether `defns` holds the computed value of the definition, where its attempt succeeds.
    pub fn is_held_in_defns(&self, definition: &Rc<Definition>) -> bool {
        self.held_in_defns.contains(&key(definition))
    }
}

fn key(definition: &Rc<Definition>) -> usize {
    Rc::as_ptr(definition) as usize
}

fn is_nullary(definition: &Definition) -> bool {
    match &definition.kind {
        DefinitionKind::Operator { params, .. } => params.is_empty(),
        DefinitionKind::Function { .. } => true,
    }
}

fn is_literal(expression: &Expr) -> bool {
    matches!(
        expression.kind,
        ExpressionKind::Number { .. } | ExpressionKind::String { .. }
    )
}

/// `SymbolNodeValueLookupProvider.getLevelBound` of an expression read in a scope, whose
/// bindings stand for TLC's `Context`.
pub(crate) fn get_level_bound(
    environment: &Environment,
    expression: &Expr,
    scope: Option<&Rc<crate::spec::Scope>>,
) -> u8 {
    LevelBound::new(environment).get_level(expression, scope, &mut Expanding::default())
}

/// `getLevelBound` of a definition's body, and of a function definition's bounds, as
/// `processConstantDefns` asks it.
pub(crate) fn get_definition_level_bound(
    environment: &Environment,
    definition: &Rc<Definition>,
) -> u8 {
    LevelBound::new(environment).get_definition_level(definition)
}

/// TLC's startup decision for the model of `environment`.
pub fn get_startup_model(environment: &Environment) -> StartupModel {
    let bound = LevelBound::new(environment);
    let mut model = StartupModel {
        attempted: Vec::new(),
        reads: FastMap::default(),
        held_in_defns: FastSet::default(),
    };
    // The definitions the configuration substitutes for another definition's name, which TLC
    // reaches through that name's tool object and computes.
    let definition_substitutes: FastSet<usize> = environment
        .substitutions
        .iter()
        .filter(|(name, _)| {
            !environment
                .root_constants
                .iter()
                .any(|constant| constant.name == **name)
        })
        .filter(|(_, target)| !environment.constants.contains_key(*target))
        .filter_map(|(_, target)| environment.definitions.get(target).map(key))
        .collect();
    for constant in &environment.root_constants {
        // A definition the configuration gives a value substitutes that value, which TLC holds.
        let Some(target) = environment
            .substitutions
            .get(&constant.name)
            .filter(|target| !environment.constants.contains_key(*target))
        else {
            continue;
        };
        let Some(definition) = environment.definitions.get(target) else {
            continue;
        };
        // TLC checks only that the definition has no parameters, a function's too.
        if is_nullary(definition) {
            model.reads.insert(key(definition), Read::Attempted);
            model.attempted.push((definition.clone(), Rule::Substitute));
        }
    }
    for written in &environment.startup_definitions {
        if !is_nullary(written) || environment.constants.contains_key(&written.name) {
            continue;
        }
        // TLC finds the definition the configuration substitutes for the name, which holds a
        // value once TLC computed it.
        let Some(definition) = get_definition(&written.name, environment)
            .filter(|_| environment.substitutions.contains_key(&written.name))
            .or(Some(written))
        else {
            continue;
        };
        // The configuration's value for the definition it substitutes is what the name holds.
        if !Rc::ptr_eq(definition, written) && environment.constants.contains_key(&definition.name)
        {
            continue;
        }
        if !is_nullary(definition)
            || model
                .attempted
                .iter()
                .any(|(attempted, _)| Rc::ptr_eq(attempted, definition))
        {
            continue;
        }
        let is_substituted_copy = environment.is_substituted(definition);
        if is_literal(&definition.body)
            && !is_substituted_copy
            && !definition_substitutes.contains(&key(definition))
            && matches!(&definition.kind, DefinitionKind::Operator { .. })
        {
            model.reads.entry(key(definition)).or_insert(Read::Literal);
            continue;
        }
        if bound.get_definition_level(definition) == 0 {
            model.reads.insert(key(definition), Read::Attempted);
            model.held_in_defns.insert(key(definition));
            model.attempted.push((definition.clone(), Rule::Constant));
        }
    }
    model
}

fn address(expression: &Expr) -> usize {
    Rc::as_ptr(expression) as usize
}

/// The statements of the named theorems and assumptions of the spec's modules, by address. TLC
/// looks a theorem's or an assumption's name up to a `ThmOrAssumpDefNode`, whose statement
/// `getLevelBound` never enters.
fn get_fact_statements(environment: &Environment) -> FastSet<usize> {
    let mut facts = FastSet::default();
    for module in &environment.modules {
        for assumption in module.assumptions.iter().filter(|fact| fact.name.is_some()) {
            facts.insert(address(&assumption.expression));
        }
        for theorem in module.theorems.iter().filter(|fact| fact.name.is_some()) {
            if let Statement::Expression(statement) = &theorem.statement {
                facts.insert(address(statement));
            }
        }
    }
    facts
}

/// The level of the Java method of an operator of the standard module `module`, where TLC
/// overrides it.
fn get_module_override_level(module: &str, name: &str) -> Option<u8> {
    get_overrides()
        .find(|&(overridden, operator, _)| overridden == module && operator == name)
        .map(|(_, _, level)| level)
}

/// What `getLevelBound` reads of an environment once: the overridden bodies, the statements of
/// the named theorems and assumptions, and the level of each definition it walked, by key, where
/// the walk reached no definition or binding being expanded below the definition's own frame
/// (whose level TLC's walk gives as 0 only there).
#[derive(Default)]
pub struct LevelBoundCache {
    tables: OnceCell<(FastMap<usize, u8>, FastSet<usize>)>,
    definition_levels: RefCell<FastMap<usize, u8>>,
}

/// The definitions and bindings a walk is expanding, by key and depth, with the lowest depth a
/// reference reached in the frame being computed.
struct Expanding {
    depths: FastMap<usize, usize>,
    lowest_reached: usize,
}

impl Default for Expanding {
    fn default() -> Expanding {
        Expanding {
            depths: FastMap::default(),
            lowest_reached: usize::MAX,
        }
    }
}

impl Expanding {
    /// Whether the key is being expanded, which the reference then reads as level 0.
    fn reaches(&mut self, key: usize) -> bool {
        let Some(&depth) = self.depths.get(&key) else {
            return false;
        };
        self.lowest_reached = self.lowest_reached.min(depth);
        true
    }

    /// Computes a frame's level, and whether the frame reached nothing below it.
    fn frame(&mut self, key: usize, compute: impl FnOnce(&mut Expanding) -> u8) -> (u8, bool) {
        let depth = self.depths.len();
        self.depths.insert(key, depth);
        let outer = std::mem::replace(&mut self.lowest_reached, usize::MAX);
        let level = compute(self);
        self.depths.remove(&key);
        let is_closed = self.lowest_reached >= depth;
        self.lowest_reached = if is_closed {
            outer
        } else {
            outer.min(self.lowest_reached)
        };
        (level, is_closed)
    }
}

/// `SymbolNodeValueLookupProvider.getLevelBound` over the AST.
struct LevelBound<'a> {
    environment: &'a Environment,
    overridden: &'a FastMap<usize, u8>,
    facts: &'a FastSet<usize>,
    definition_levels: &'a RefCell<FastMap<usize, u8>>,
}

impl<'a> LevelBound<'a> {
    fn new(environment: &'a Environment) -> LevelBound<'a> {
        let cache = &environment.level_bounds;
        let (overridden, facts) = cache.tables.get_or_init(|| {
            (
                get_overridden_bodies(environment),
                get_fact_statements(environment),
            )
        });
        LevelBound {
            environment,
            overridden,
            facts,
            definition_levels: &cache.definition_levels,
        }
    }

    fn get_definition_level(&self, definition: &Rc<Definition>) -> u8 {
        self.expand_definition(definition, &mut Expanding::default())
    }

    /// The level of a definition's body, from the cache where the walk closed over it.
    fn expand_definition(&self, definition: &Rc<Definition>, expanding: &mut Expanding) -> u8 {
        if let Some(&level) = self.definition_levels.borrow().get(&key(definition)) {
            return level;
        }
        let (level, is_closed) = expanding.frame(key(definition), |expanding| {
            self.get_definition_level_in(definition, expanding)
        });
        if is_closed {
            self.definition_levels
                .borrow_mut()
                .insert(key(definition), level);
        }
        level
    }

    // `getLevelBoundAppl`: an action or a temporal operator bounds its level without its
    // operands; an operator TLC finds by name a variable's spelling gives level 1; an operator it
    // finds defined adds its body's level; an argument that is an operator is of level 0.
    fn get_level(
        &self,
        expression: &Expr,
        scope: Option<&Rc<crate::spec::Scope>>,
        expanding: &mut Expanding,
    ) -> u8 {
        match &expression.kind {
            ExpressionKind::Number { .. }
            | ExpressionKind::Decimal { .. }
            | ExpressionKind::String { .. }
            | ExpressionKind::ExceptAt
            | ExpressionKind::Lambda { .. }
            | ExpressionKind::OperatorReference { .. } => 0,
            ExpressionKind::Always(_)
            | ExpressionKind::Eventually(_)
            | ExpressionKind::Fairness { .. }
            | ExpressionKind::UnboundedQuantifier {
                is_temporal: true, ..
            } => 3,
            ExpressionKind::Prime(_)
            | ExpressionKind::Unchanged(_)
            | ExpressionKind::Action { .. } => 2,
            ExpressionKind::Enabled(_) => 1,
            ExpressionKind::Identifier { name, .. } => {
                self.get_name_level(expression, name, &[], scope, expanding)
            }
            ExpressionKind::Apply { operator, args, .. } => {
                if matches!(&**operator, "~>" | "-+->") {
                    return 3;
                }
                if &**operator == "\\cdot" {
                    return 2;
                }
                self.get_name_level(expression, operator, args, scope, expanding)
            }
            // A LET's definitions all count, used or not.
            _ => expression
                .children()
                .iter()
                .map(|child| self.get_level(child, scope, expanding))
                .max()
                .unwrap_or(0),
        }
    }

    fn get_name_level(
        &self,
        expression: &Expr,
        written: &Name,
        args: &[Expr],
        scope: Option<&Rc<crate::spec::Scope>>,
        expanding: &mut Expanding,
    ) -> u8 {
        // SANY makes an `OpArgNode` of an argument in the place of a parameter that takes
        // arguments, whatever its spelling, which `getLevelBound` gives level 0.
        let callee_params = (!expression.is_locally_resolved())
            .then(|| expression.reference())
            .flatten()
            .and_then(|name| get_definition(&name, self.environment))
            .and_then(|definition| match &definition.kind {
                DefinitionKind::Operator { params, .. } => Some(params.clone()),
                DefinitionKind::Function { .. } => None,
            });
        let arguments = args
            .iter()
            .enumerate()
            .map(|(position, argument)| {
                let is_operator_place = callee_params
                    .as_ref()
                    .and_then(|params| params.get(position))
                    .is_some_and(|param| param.arity > 0);
                if is_operator_place || self.is_operator_argument(argument) {
                    0
                } else {
                    self.get_level(argument, scope, expanding)
                }
            })
            .max()
            .unwrap_or(0);
        // TLC asks the name's `UniqueString`, shared by every name spelled the same, which only
        // the root module's variables give a location.
        if self.environment.variables.contains(written) {
            return 1;
        }
        if expression.is_locally_resolved() {
            // `lookup` finds the name in the context: an argument's `LazyValue` adds the level of
            // its expression, and an operator argument's definition the level of its body; a
            // value, or a name the context doesn't hold, adds none.
            use crate::spec::{Binding, lookup_scope};
            let Some((node, binding)) = expression
                .reference()
                .and_then(|name| lookup_scope(scope, &name))
            else {
                return arguments;
            };
            let (inner, inner_scope) = match binding {
                Binding::Thunk { expression, scope } => (expression, scope.resolve(node)),
                Binding::Closure {
                    params,
                    body,
                    scope,
                    ..
                } if params.len() == args.len() => (body, scope.resolve(node)),
                _ => return arguments,
            };
            let key = Rc::as_ptr(inner) as usize;
            if expanding.reaches(key) {
                return arguments;
            }
            let (level, _) = expanding.frame(key, |expanding| {
                self.get_level(inner, inner_scope.as_ref(), expanding)
            });
            return arguments.max(level);
        }
        let Some(name) = expression.reference() else {
            return arguments;
        };
        if self.environment.constants.contains_key(&name) {
            return arguments;
        }
        if let Some(definition) = get_definition(&name, self.environment) {
            if self.facts.contains(&address(&definition.body)) {
                return arguments;
            }
            // TLC reads an operator a Java method overrides through the method, of its level,
            // and never its body.
            if let Some(&level) = self
                .overridden
                .get(&(Rc::as_ptr(&definition.body) as usize))
            {
                return arguments.max(level);
            }
            if expanding.reaches(key(definition)) {
                return arguments;
            }
            return arguments.max(self.expand_definition(definition, expanding));
        }
        if self.environment.builtins.contains_key(&name) {
            let level = get_builtin_override_level(&name)
                .unwrap_or_else(|| self.get_standard_operator_level(&name));
            return arguments.max(level);
        }
        arguments
    }

    // The level of a standard module's operator TLC implements with no Java method, which it
    // finds by walking the operator's TLA+ definition in its module.
    fn get_standard_operator_level(&self, name: &str) -> u8 {
        crate::environment::get_standard_module_definition(name)
            .map(|(module, definition)| {
                let mut expanding = Expanding::default();
                expanding
                    .frame(key(&definition), |expanding| {
                        self.get_standard_level(&module, &definition.body, expanding)
                    })
                    .0
            })
            .unwrap_or(0)
    }

    // `getLevelBound` over a standard module's definition, whose names resolve in the module.
    fn get_standard_level(
        &self,
        module: &Module,
        expression: &Expr,
        expanding: &mut Expanding,
    ) -> u8 {
        let (written, args): (&Name, &[Expr]) = match &expression.kind {
            ExpressionKind::Identifier { name, .. } => (name, &[]),
            ExpressionKind::Apply { operator, args, .. } => (operator, args),
            ExpressionKind::Lambda { .. } | ExpressionKind::OperatorReference { .. } => return 0,
            ExpressionKind::Always(_)
            | ExpressionKind::Eventually(_)
            | ExpressionKind::Fairness { .. } => return 3,
            ExpressionKind::Prime(_)
            | ExpressionKind::Unchanged(_)
            | ExpressionKind::Action { .. } => return 2,
            ExpressionKind::Enabled(_) => return 1,
            _ => {
                return expression
                    .children()
                    .iter()
                    .map(|child| self.get_standard_level(module, child, expanding))
                    .max()
                    .unwrap_or(0);
            }
        };
        let defined = module
            .definitions
            .iter()
            .find(|definition| definition.name == *written);
        let arguments = args
            .iter()
            .enumerate()
            .map(|(position, argument)| {
                let is_operator_place = defined.is_some_and(|definition| {
                    matches!(
                        &definition.kind,
                        DefinitionKind::Operator { params, .. }
                            if params.get(position).is_some_and(|param| param.arity > 0)
                    )
                });
                if is_operator_place {
                    0
                } else {
                    self.get_standard_level(module, argument, expanding)
                }
            })
            .max()
            .unwrap_or(0);
        if self.environment.variables.contains(written) {
            return 1;
        }
        let Some(definition) = defined else {
            return arguments.max(get_builtin_override_level(written).unwrap_or(0));
        };
        if let Some(level) = get_module_override_level(&module.name, written) {
            return arguments.max(level);
        }
        if expanding.reaches(key(definition)) {
            return arguments;
        }
        let (level, _) = expanding.frame(key(definition), |expanding| {
            self.get_standard_level(module, &definition.body, expanding)
        });
        arguments.max(level)
    }

    fn get_definition_level_in(
        &self,
        definition: &Rc<Definition>,
        expanding: &mut Expanding,
    ) -> u8 {
        let sets: Vec<Expr> = match &definition.kind {
            DefinitionKind::Function { bounds } => {
                bounds.iter().map(|bound| bound.set.clone()).collect()
            }
            DefinitionKind::Operator { .. } => Vec::new(),
        };
        sets.iter()
            .chain([&definition.body])
            .map(|expression| self.get_level(expression, None, expanding))
            .max()
            .unwrap_or(0)
    }

    // An argument SANY makes an `OpArgNode` of: a LAMBDA, an operator symbol, or the name of an
    // operator with parameters.
    fn is_operator_argument(&self, argument: &Expr) -> bool {
        match &argument.kind {
            ExpressionKind::Lambda { .. } | ExpressionKind::OperatorReference { .. } => true,
            ExpressionKind::Identifier { .. } if !argument.is_locally_resolved() => {
                let Some(name) = argument.reference() else {
                    return false;
                };
                match get_definition(&name, self.environment) {
                    Some(definition) => matches!(
                        &definition.kind,
                        DefinitionKind::Operator { params, .. } if !params.is_empty()
                    ),
                    None => self
                        .environment
                        .builtins
                        .get(&name)
                        .is_some_and(|builtin| builtin.arity > 0),
                }
            }
            _ => false,
        }
    }
}

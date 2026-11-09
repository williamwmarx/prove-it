//! The modules of a spec linked into one environment, as `createEnvironment` in
//! `src/environment.ts` links them: each module's definitions under their keys, the builtins of
//! the standard modules it loads, and its variables, with every name resolved. This is the linking
//! that the IR reads; the model's values and the startup evaluation come later (F7, F8).

use std::cell::RefCell;
use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::*;
use crate::errors::{FrontError, SanyError, SanyReport, SyntaxError, format_range};
use crate::hash::{FastMap, FastSet};
use crate::lexer::tokenize;
use crate::ordered_map::OrderedMap;
use crate::parser::{extract_module, parse_module_tokens};
use crate::resolve::{
    ErrorList, GetInstance, KEY_SEPARATOR, MODULE_START, ModuleContext, ModuleReport, ModuleSymbol,
    Result, Selections, SymbolKind, Symbols, get_arity, get_param_arities, is_before,
    is_theorem_definition, resolve_module,
};
use crate::standard_builtins::{
    self, CORE_OPERATORS, STANDARD_DEPENDENCIES, StandardModule, USER_STANDARD_MODULES,
};
use crate::standard_modules;

/// A builtin the environment holds: its name, arity and flags (state-level, level-constant,
/// lazy), which the IR writes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Builtin {
    pub name: Name,
    pub arity: usize,
    pub flags: u32,
}

/// What linking makes of a spec.
pub struct Environment {
    /// The definitions by key, the instance copies included, and the root module's definitions
    /// also by the names it gives them.
    pub definitions: OrderedMap<Name, Rc<Definition>>,
    pub builtins: OrderedMap<Name, Builtin>,
    pub variables: Vec<Name>,
    pub variable_index: OrderedMap<Name, usize>,
    pub root_constants: Vec<Rc<Declaration>>,
    pub root_symbols: Rc<Symbols>,
    /// What linking prints: SANY's warnings.
    pub printed: Vec<String>,
}

pub struct EnvironmentOptions<'a> {
    pub source: &'a str,
    pub load_module: &'a dyn Fn(&str) -> Option<String>,
    pub version: TlcVersion,
}

struct LinkedModule {
    module: Rc<Module>,
    constants: Vec<Rc<Declaration>>,
    variables: Vec<Name>,
    variable_locations: Vec<Location>,
    visible: Rc<Symbols>,
    exported: Rc<Symbols>,
    modules: OrderedMap<Name, Rc<LinkedModule>>,
    facts: FastSet<Name>,
}

/// `errors` and `warnings` collect what SANY reports for the module.
struct ModuleScope {
    id: Name,
    symbols: Symbols,
    modules: OrderedMap<Name, Rc<LinkedModule>>,
    nested: Rc<RefCell<Vec<Rc<Module>>>>,
    errors: ErrorList,
    warnings: ErrorList,
}

/// `createSanyError`.
fn sany_error(errors: Vec<SanyError>, is_fatal: bool, warnings: Vec<SanyError>) -> FrontError {
    let mut error = SyntaxError::sany(errors);
    if let Some(report) = &mut error.sany {
        **report = SanyReport {
            is_fatal,
            warnings,
            ..(**report).clone()
        };
    }
    FrontError::Syntax(error)
}

fn missing_module_error(name: &str, importer: &str) -> FrontError {
    sany_error(
        vec![SanyError {
            location: format!("In module {importer}"),
            message: format!(
                "Cannot find source file for module {name} imported in module {importer}."
            ),
        }],
        true,
        Vec::new(),
    )
}

fn module_redefined_error(module: &Module) -> FrontError {
    FrontError::Syntax(SyntaxError::new(format!(
        "Multiply-defined module '{}' at line {}, column {}",
        module.name, module.location.line, module.location.column
    )))
}

fn get_module_redefinition(module: &Module, existing: &Module) -> Option<SanyError> {
    let (Some(range), Some(existing)) = (&module.location.range, &existing.location.range) else {
        return None;
    };
    Some(SanyError {
        location: format_range(range),
        message: format!(
            "Multiply-defined module '{}': this definition or declaration conflicts \nwith the one at {}.",
            module.name,
            format_range(existing)
        ),
    })
}

/// `Context.kindOfNode` names a definition or a parameter a definition, and any other symbol a
/// declaration.
fn get_node_word(kind: SymbolKind) -> &'static str {
    match kind {
        SymbolKind::Builtin
        | SymbolKind::Definition
        | SymbolKind::Instance
        | SymbolKind::Parameter => "definition",
        _ => "declaration",
    }
}

/// The Java class of the node SANY binds a symbol to.
fn get_node_class(kind: SymbolKind) -> &'static str {
    if kind == SymbolKind::Theorem {
        "ThmOrAssumpDefNode"
    } else {
        get_node_word(kind)
    }
}

const MAXIMUM_INTEGER: f64 = 2_147_483_647.0;
const MINIMUM_INTEGER: f64 = -2_147_483_648.0;

fn is_tlc_integer(value: f64) -> bool {
    value.fract() == 0.0 && (MINIMUM_INTEGER..=MAXIMUM_INTEGER).contains(&value)
}

/// Like TLC, rejects a decimal or a big integer anywhere in a module, even where nothing evaluates
/// it.
fn reject_literals(expressions: &[Expr]) -> Result<()> {
    for expression in expressions {
        let describe = || {
            format!(
                "line {}, column {}",
                expression.location.line, expression.location.column
            )
        };
        match &expression.kind {
            ExpressionKind::Decimal { text } => {
                return Err(FrontError::Evaluation(format!(
                    "TLC can't handle real numbers: {text} at {}",
                    describe()
                )));
            }
            ExpressionKind::Number { value, text } if !is_tlc_integer(*value) => {
                return Err(FrontError::Evaluation(format!(
                    "TLC can't handle a number this big: {text} at {}",
                    describe()
                )));
            }
            ExpressionKind::Let { instances, .. } => {
                let mut children = expression.children();
                children.extend(get_substitutions(instances.as_deref().unwrap_or(&[])));
                reject_literals(&children)?;
            }
            _ => reject_literals(&expression.children())?,
        }
    }
    Ok(())
}

fn get_substitutions(instances: &[Rc<Instance>]) -> Vec<Expr> {
    instances
        .iter()
        .flat_map(|instance| {
            instance
                .substitutions
                .iter()
                .map(|substitution| substitution.expression.clone())
        })
        .collect()
}

fn reject_module_literals(module: &Module) -> Result<()> {
    let mut expressions: Vec<Expr> = Vec::new();
    for definition in &module.definitions {
        if let DefinitionKind::Function { bounds } = &definition.kind {
            expressions.extend(bounds.iter().map(|bound| bound.set.clone()));
        }
        expressions.push(definition.body.clone());
    }
    expressions.extend(
        module
            .assumptions
            .iter()
            .map(|assumption| assumption.expression.clone()),
    );
    expressions.extend(
        module
            .theorems
            .iter()
            .filter_map(|theorem| match &theorem.statement {
                Statement::Expression(expression) => Some(expression.clone()),
                Statement::AssumeProve(_) => None,
            }),
    );
    expressions.extend(get_substitutions(&module.instances));
    reject_literals(&expressions)?;
    for nested in &module.modules {
        reject_module_literals(nested)?;
    }
    Ok(())
}

/// `containsReference`: a name that may select a subexpression.
fn contains_reference(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Subexpression { .. } => true,
        ExpressionKind::Identifier { name, .. } if name.contains('!') => true,
        ExpressionKind::Apply { operator, .. } if operator.contains('!') => true,
        _ => expression
            .children()
            .iter()
            .any(|child| contains_reference(child)),
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

fn statement_expressions(statement: &Statement) -> Vec<Expr> {
    match statement {
        Statement::Expression(expression) => vec![expression.clone()],
        Statement::AssumeProve(assume_prove) => assume_prove
            .assumptions
            .iter()
            .flat_map(|assumption| match assumption {
                Assumed::Expression(expression) => vec![expression.clone()],
                Assumed::NewSymbol(symbol) => symbol.set.iter().cloned().collect(),
                Assumed::AssumeProve(inner) => {
                    statement_expressions(&Statement::AssumeProve(inner.clone()))
                }
            })
            .chain([assume_prove.conclusion.clone()])
            .collect(),
    }
}

fn fact_expressions(facts: &[Fact]) -> Vec<Expr> {
    facts
        .iter()
        .filter_map(|fact| match fact {
            Fact::Expression(expression) => Some(expression.clone()),
            Fact::Module { .. } => None,
        })
        .collect()
}

/// The expressions of a proof that `resolveModuleSubexpressions` reads, and whether it holds an
/// INSTANCE.
fn proof_expressions(proof: Option<&Proof>, expressions: &mut Vec<Expr>) -> bool {
    match proof.map(|proof| &proof.kind) {
        Some(ProofKind::By { facts, .. }) => {
            expressions.extend(fact_expressions(facts));
            false
        }
        Some(ProofKind::Steps { steps, .. }) => steps.iter().fold(false, |has_instance, step| {
            let has_step_instance = match &step.body {
                StepBody::UseOrHide(use_or_hide) => {
                    expressions.extend(fact_expressions(&use_or_hide.facts));
                    false
                }
                StepBody::Instance(_) => true,
                StepBody::Define { definitions, .. } => {
                    definitions
                        .iter()
                        .fold(false, |has_instance, definition| match definition {
                            DefinitionUnit::Instance(_) => true,
                            DefinitionUnit::Definition(definition) => {
                                if let DefinitionKind::Function { bounds } = &definition.kind {
                                    expressions
                                        .extend(bounds.iter().map(|bound| bound.set.clone()));
                                }
                                expressions.push(definition.body.clone());
                                has_instance
                            }
                        })
                }
                StepBody::Have(expression) | StepBody::Case(expression) => {
                    expressions.push(expression.clone());
                    false
                }
                StepBody::Witness(witnessed) => {
                    expressions.extend(witnessed.iter().cloned());
                    false
                }
                StepBody::Take { bounds, .. } => {
                    expressions.extend(bounds.iter().map(|bound| bound.set.clone()));
                    false
                }
                StepBody::Pick { bounds, body, .. } => {
                    expressions.extend(bounds.iter().map(|bound| bound.set.clone()));
                    expressions.push(body.clone());
                    false
                }
                StepBody::Assert { statement, .. } => {
                    expressions.extend(statement_expressions(statement));
                    false
                }
                StepBody::Qed => false,
            };
            proof_expressions(step.proof.as_deref(), expressions)
                || has_instance
                || has_step_instance
        }),
        _ => false,
    }
}

/// What the Rust front end doesn't link yet in a module: an INSTANCE, and a name that selects a
/// subexpression, which `resolveModuleSubexpressions` rewrites.
fn get_unported(module: &Module) -> Option<&'static str> {
    if !module.instances.is_empty() {
        return Some("an INSTANCE");
    }
    let mut expressions: Vec<Expr> = Vec::new();
    for definition in &module.definitions {
        if let DefinitionKind::Function { bounds } = &definition.kind {
            expressions.extend(bounds.iter().map(|bound| bound.set.clone()));
        }
        expressions.push(definition.body.clone());
    }
    expressions.extend(
        module
            .assumptions
            .iter()
            .map(|assumption| assumption.expression.clone()),
    );
    let mut has_instance = false;
    for theorem in &module.theorems {
        expressions.extend(statement_expressions(&theorem.statement));
        has_instance |= proof_expressions(theorem.proof.as_ref(), &mut expressions);
    }
    for use_or_hide in &module.uses {
        expressions.extend(fact_expressions(&use_or_hide.facts));
    }
    if has_instance
        || expressions
            .iter()
            .any(|expression| has_let_instance(expression))
    {
        return Some("an INSTANCE");
    }
    expressions
        .iter()
        .any(|expression| contains_reference(expression))
        .then_some("a name that selects a subexpression")
}

struct Linker<'a> {
    options: &'a EnvironmentOptions<'a>,
    root: Rc<Module>,
    /// Each module text parsed once, as `createTlcOrder`'s `parseText` reads it.
    texts: RefCell<FastMap<String, Rc<Module>>>,
    definitions: RefCell<OrderedMap<Name, Rc<Definition>>>,
    builtins: RefCell<OrderedMap<Name, Builtin>>,
    standard_exports: RefCell<FastMap<Name, Rc<Symbols>>>,
    linked_modules: RefCell<FastMap<Name, Rc<LinkedModule>>>,
    nested_modules: RefCell<FastMap<Name, Rc<LinkedModule>>>,
    link_order: RefCell<Vec<Rc<LinkedModule>>>,
    dependencies: RefCell<FastMap<Name, FastSet<Name>>>,
    loading: RefCell<Vec<FastSet<Name>>>,
    /// The top-level modules being linked, to report a cycle of EXTENDS or INSTANCE.
    linking: RefCell<Vec<Name>>,
    warnings: ErrorList,
    selections: Rc<Selections>,
}

fn get_standard_modules(version: TlcVersion) -> &'static [StandardModule] {
    match version {
        TlcVersion::Master => standard_builtins::MASTER,
        TlcVersion::V1_7_4 => standard_builtins::TLC_174,
    }
}

fn get_dependencies(name: &str) -> &'static [&'static str] {
    STANDARD_DEPENDENCIES
        .iter()
        .find(|entry| entry.0 == name)
        .map_or(&[], |entry| entry.1)
}

fn is_sany_standard_module(name: &str, version: TlcVersion) -> bool {
    let modules = match version {
        TlcVersion::Master => standard_modules::MASTER,
        TlcVersion::V1_7_4 => standard_modules::TLC_174,
    };
    modules.iter().any(|module| module.0 == name)
}

impl Linker<'_> {
    fn parse_text(&self, source: &str) -> std::result::Result<Rc<Module>, SyntaxError> {
        if let Some(module) = self.texts.borrow().get(source) {
            return Ok(module.clone());
        }
        let tokens = tokenize(source)?;
        let module = Rc::new(parse_module_tokens(source, &tokens, self.options.version)?);
        self.texts
            .borrow_mut()
            .insert(source.to_owned(), module.clone());
        Ok(module)
    }

    fn use_module<'b>(&self, name: &Name, used: impl IntoIterator<Item = &'b Name> + Clone) {
        for closure in self.loading.borrow_mut().iter_mut() {
            closure.insert(name.clone());
            closure.extend(used.clone().into_iter().cloned());
        }
    }

    fn add_standard_module(&self, name: &str) -> Option<Rc<Symbols>> {
        if let Some(cached) = self.standard_exports.borrow().get(name) {
            return Some(cached.clone());
        }
        let standard = get_standard_modules(self.options.version)
            .iter()
            .find(|module| module.name == name)?;
        // TLC loads the modules a standard module instantiates too, and the Java methods of each
        // replace the operators of every module, as those of Integers replace those of Naturals.
        for dependency in get_dependencies(name) {
            self.add_standard_module(dependency);
        }
        let mut exported = Symbols::new();
        for extended in standard.extends {
            if let Some(symbols) = self.add_standard_module(extended) {
                for (symbol_name, symbol) in symbols.iter() {
                    exported.insert(symbol_name.clone(), symbol.clone());
                }
            }
        }
        for operator in standard.operators {
            let operator_name: Name = Rc::from(operator.name);
            self.builtins.borrow_mut().insert(
                operator_name.clone(),
                Builtin {
                    name: operator_name.clone(),
                    arity: operator.arity,
                    flags: operator.flags,
                },
            );
            let range = operator
                .range
                .map(
                    |[start_line, start_column, end_line, end_column]| SourceRange {
                        module: Rc::from(name),
                        start: Position {
                            line: start_line,
                            column: start_column,
                        },
                        end: Position {
                            line: end_line,
                            column: end_column,
                        },
                    },
                )
                .or_else(|| {
                    exported
                        .get(operator.name)
                        .and_then(|symbol| symbol.range.clone())
                });
            exported.insert(
                operator_name.clone(),
                ModuleSymbol {
                    key: operator_name,
                    kind: SymbolKind::Definition,
                    arity: operator.arity,
                    params: operator.params.map(Rc::from),
                    range,
                },
            );
        }
        let exported = Rc::new(exported);
        self.standard_exports
            .borrow_mut()
            .insert(Rc::from(name), exported.clone());
        Some(exported)
    }

    fn get_standard_symbols(&self, name: &Name) -> Option<Rc<Symbols>> {
        // SANY reads a module from the user's directories before its standard modules.
        if USER_STANDARD_MODULES.contains(&&**name) && (self.options.load_module)(name).is_some() {
            return None;
        }
        let symbols = self.add_standard_module(name);
        let dependencies: Vec<Name> = get_dependencies(name)
            .iter()
            .map(|dependency| Rc::from(*dependency))
            .collect();
        if symbols.is_some() {
            self.use_module(name, &dependencies);
        }
        // TLC loads the Java class of each module a standard module uses, so one that uses
        // Integers overrides the arithmetic of Naturals.
        if symbols.is_some()
            && dependencies
                .iter()
                .any(|dependency| &**dependency == "Integers")
        {
            self.add_standard_module("Integers");
        }
        symbols
    }

    fn load_module(&self, name: &Name, importer: &str) -> Result<Rc<Module>> {
        let source = (self.options.load_module)(name)
            .or_else(|| {
                standard_modules::BUNDLED
                    .iter()
                    .find(|module| module.0 == &**name)
                    .map(|module| module.1.to_owned())
            })
            .or_else(|| extract_module(self.options.source, name))
            .ok_or_else(|| missing_module_error(name, importer))?;
        // A module SANY's parser rejects fails with SANY's message, which F5 ports.
        let module = self
            .parse_text(&source)
            .map_err(|_| FrontError::NotYet(format!("SANY's parse error for module {name}")))?;
        if module.name != *name {
            return Err(sany_error(
                vec![SanyError {
                    location: "Unknown location".to_owned(),
                    message: format!(
                        "File name '{name}' does not match the name '{}' of the top level module it contains.",
                        module.name
                    ),
                }],
                true,
                Vec::new(),
            ));
        }
        reject_module_literals(&module)?;
        Ok(module)
    }

    fn link_top_level(&self, parsed: &Rc<Module>) -> Result<(Rc<LinkedModule>, FastSet<Name>)> {
        let cycle_start = self
            .linking
            .borrow()
            .iter()
            .position(|name| *name == parsed.name);
        if let Some(start) = cycle_start {
            let cycle: Vec<String> = self.linking.borrow()[start..]
                .iter()
                .chain([&parsed.name])
                .map(|name| format!("{name}.tla"))
                .collect();
            return Err(FrontError::Syntax(SyntaxError::new(format!(
                "Circular dependency among .tla files; dependency cycle is: {}",
                cycle.join(" --> ")
            ))));
        }
        let nested: Rc<RefCell<Vec<Rc<Module>>>> = Rc::default();
        let errors: ErrorList = Rc::default();
        self.linking.borrow_mut().push(parsed.name.clone());
        self.loading.borrow_mut().push(FastSet::default());
        let linked = self.link_module(
            parsed,
            ModuleScope {
                id: parsed.name.clone(),
                symbols: Symbols::new(),
                modules: OrderedMap::new(),
                nested: nested.clone(),
                errors: errors.clone(),
                warnings: self.warnings.clone(),
            },
        );
        let closure = self.loading.borrow_mut().pop().unwrap_or_default();
        self.linking.borrow_mut().pop();
        let linked = linked?;
        if !errors.borrow().is_empty() {
            return Err(sany_error(
                errors.take(),
                false,
                self.warnings.borrow().clone(),
            ));
        }
        let duplicate = nested
            .borrow()
            .iter()
            .find(|module| closure.contains(&module.name))
            .cloned();
        if let Some(duplicate) = duplicate {
            let loaded = self.linked_modules.borrow().get(&duplicate.name).cloned();
            if let Some(redefinition) =
                loaded.and_then(|loaded| get_module_redefinition(&duplicate, &loaded.module))
            {
                return Err(sany_error(
                    vec![redefinition],
                    false,
                    self.warnings.borrow().clone(),
                ));
            }
            return Err(module_redefined_error(&duplicate));
        }
        Ok((linked, closure))
    }

    fn get_linked_module(&self, name: &Name, importer: &str) -> Result<Rc<LinkedModule>> {
        let cached = self.linked_modules.borrow().get(name).cloned();
        if let Some(cached) = cached {
            let used: Vec<Name> = self
                .dependencies
                .borrow()
                .get(name)
                .map(|set| set.iter().cloned().collect())
                .unwrap_or_default();
            self.use_module(name, &used);
            return Ok(cached);
        }
        let (linked, closure) = self.link_top_level(&self.load_module(name, importer)?)?;
        // TLC replaces each definition of a module that has a standard module's name with the
        // Java method of that name, so a user's Bags.tla keeps the definitions that Bags has no
        // method for.
        if is_sany_standard_module(name, self.options.version)
            && let Some(standard) = get_standard_modules(self.options.version)
                .iter()
                .find(|module| module.name == &**name)
        {
            for operator in standard.operators {
                let Some(symbol) = linked.visible.get(operator.name) else {
                    continue;
                };
                if symbol.kind != SymbolKind::Definition || symbol.arity != operator.arity {
                    continue;
                }
                self.builtins.borrow_mut().insert(
                    symbol.key.clone(),
                    Builtin {
                        name: Rc::from(operator.name),
                        arity: operator.arity,
                        flags: operator.flags,
                    },
                );
                self.definitions.borrow_mut().remove(&symbol.key);
            }
        }
        self.linked_modules
            .borrow_mut()
            .insert(name.clone(), linked.clone());
        let used: Vec<Name> = closure.iter().cloned().collect();
        self.dependencies.borrow_mut().insert(name.clone(), closure);
        self.use_module(name, &used);
        Ok(linked)
    }

    fn link_module(&self, parsed: &Rc<Module>, scope: ModuleScope) -> Result<Rc<LinkedModule>> {
        if let Some(unported) = get_unported(parsed) {
            return Err(FrontError::NotYet(unported.to_owned()));
        }
        let mut visible: Symbols = CORE_OPERATORS
            .iter()
            .map(|(name, arity, _)| {
                let name: Name = Rc::from(*name);
                (
                    name.clone(),
                    ModuleSymbol {
                        key: name,
                        kind: SymbolKind::Builtin,
                        arity: *arity,
                        params: None,
                        range: None,
                    },
                )
            })
            .collect();
        for (name, symbol) in scope.symbols.iter() {
            visible.insert(name.clone(), symbol.clone());
        }
        let extends_report = ModuleReport {
            location: MODULE_START,
            errors: Rc::default(),
            warnings: Rc::default(),
        };
        let reports: Rc<RefCell<Vec<ModuleReport>>> =
            Rc::new(RefCell::new(vec![extends_report.clone()]));
        let mut exported = Symbols::new();
        // Context.mergeExtendContext keeps the first of the symbols the extended modules share by
        // name, and warns of two definitions or two declarations but rejects a definition and a
        // declaration.
        let merge_extended = |symbols: &Symbols, visible: &mut Symbols, exported: &mut Symbols| {
            for (name, symbol) in symbols.iter() {
                let Some(current) = exported.get(name) else {
                    visible.insert(name.clone(), symbol.clone());
                    exported.insert(name.clone(), symbol.clone());
                    continue;
                };
                let (Some(current_range), Some(range)) = (&current.range, &symbol.range) else {
                    continue;
                };
                if current_range == range {
                    continue;
                }
                let location = format_range(range);
                let existing = format_range(current_range);
                if get_node_class(current.kind) == get_node_class(symbol.kind) {
                    extends_report.warnings.borrow_mut().push(SanyError {
                        location,
                        message: format!(
                            "Warning: the {} of '{name}' conflicts with \nits {} at {existing}.",
                            get_node_word(current.kind),
                            get_node_word(current.kind)
                        ),
                    });
                    continue;
                }
                extends_report.errors.borrow_mut().push(SanyError {
                    location,
                    message: format!(
                        "The {} of '{name}' conflicts with \nits {} at {existing}.",
                        get_node_word(symbol.kind),
                        get_node_word(current.kind)
                    ),
                });
            }
        };
        let facts: Rc<RefCell<FastSet<Name>>> = Rc::default();
        let mut modules: OrderedMap<Name, Rc<LinkedModule>> = OrderedMap::new();
        let mut constants: Vec<Rc<Declaration>> = parsed.constants.clone();
        let mut variables: Vec<Name> = parsed
            .variables
            .iter()
            .map(|variable| variable.name.clone())
            .collect();
        let mut variable_locations: Vec<Location> = parsed
            .variables
            .iter()
            .map(|variable| variable.location.clone())
            .collect();
        for name in &parsed.extends {
            let nested = scope.modules.get(name).cloned();
            let standard_symbols = if nested.is_some() {
                None
            } else {
                self.get_standard_symbols(name)
            };
            if let Some(standard_symbols) = standard_symbols {
                merge_extended(&standard_symbols, &mut visible, &mut exported);
                continue;
            }
            let linked = match nested {
                Some(nested) => nested,
                None => self.get_linked_module(name, &parsed.name)?,
            };
            for constant in &linked.constants {
                if constants
                    .iter()
                    .all(|existing| existing.name != constant.name)
                {
                    constants.push(constant.clone());
                }
            }
            for (index, variable) in linked.variables.iter().enumerate() {
                if variables.contains(variable) {
                    continue;
                }
                variables.push(variable.clone());
                variable_locations.push(linked.variable_locations[index].clone());
            }
            merge_extended(&linked.exported, &mut visible, &mut exported);
            facts.borrow_mut().extend(linked.facts.iter().cloned());
            for (module_name, module) in linked.modules.iter() {
                modules.insert(module_name.clone(), module.clone());
            }
        }
        let bound = Rc::new(visible.clone());
        let declaration_symbol = |declaration: &Declaration, kind: SymbolKind| ModuleSymbol {
            key: declaration.name.clone(),
            kind,
            arity: declaration.arity,
            params: None,
            range: declaration.location.range.clone(),
        };
        let declarations: Vec<(Rc<Declaration>, SymbolKind)> = parsed
            .constants
            .iter()
            .map(|constant| (constant.clone(), SymbolKind::Constant))
            .chain(
                parsed
                    .variables
                    .iter()
                    .map(|variable| (variable.clone(), SymbolKind::Variable)),
            )
            .collect();
        for (declaration, kind) in &declarations {
            exported.insert(
                declaration.name.clone(),
                declaration_symbol(declaration, *kind),
            );
        }
        let is_root = Rc::ptr_eq(parsed, &self.root);
        let id = scope.id.clone();
        let get_key = move |definition: &Definition| -> Name {
            if is_root {
                definition.name.clone()
            } else {
                Rc::from(format!("{}{KEY_SEPARATOR}{id}", definition.name))
            }
        };
        let get_definition_symbol = |definition: &Definition| ModuleSymbol {
            key: get_key(definition),
            kind: if is_theorem_definition(parsed, definition) {
                SymbolKind::Theorem
            } else {
                SymbolKind::Definition
            },
            arity: get_arity(definition),
            params: Some(get_param_arities(definition)),
            range: definition.location.range.clone(),
        };
        // Generator.generateModule reports the errors of a nested module and goes on, and then
        // SymbolTable.addModule reports a module already defined.
        for nested in &parsed.modules {
            let mut visible_modules = scope.modules.clone();
            for (name, module) in modules.iter() {
                visible_modules.insert(name.clone(), module.clone());
            }
            let existing = visible_modules.get(&nested.name).cloned();
            let redefinition = existing
                .as_ref()
                .and_then(|existing| get_module_redefinition(nested, &existing.module));
            if existing.is_some() && redefinition.is_none() {
                return Err(module_redefined_error(nested));
            }
            scope.nested.borrow_mut().push(nested.clone());
            let report = ModuleReport {
                location: nested.location.position(),
                errors: Rc::default(),
                warnings: Rc::default(),
            };
            reports.borrow_mut().push(report.clone());
            // SANY keeps the first of two symbols of a name.
            let mut symbols = visible.clone();
            for (declaration, kind) in &declarations {
                if is_before(declaration.location.position(), nested.location.position())
                    && !symbols.contains_key(&declaration.name)
                {
                    symbols.insert(
                        declaration.name.clone(),
                        declaration_symbol(declaration, *kind),
                    );
                }
            }
            for definition in &parsed.definitions {
                if is_before(definition.location.position(), nested.location.position())
                    && !symbols.contains_key(&definition.name)
                {
                    symbols.insert(definition.name.clone(), get_definition_symbol(definition));
                }
            }
            let linked = self.link_module(
                nested,
                ModuleScope {
                    id: Rc::from(format!("{}/{}", scope.id, nested.name)),
                    symbols,
                    modules: visible_modules,
                    nested: scope.nested.clone(),
                    errors: report.errors.clone(),
                    warnings: report.warnings.clone(),
                },
            )?;
            if let Some(redefinition) = redefinition {
                report.errors.borrow_mut().push(redefinition);
            }
            if existing.is_none() {
                modules.insert(nested.name.clone(), linked.clone());
            }
            if !self.nested_modules.borrow().contains_key(&nested.name) {
                self.nested_modules
                    .borrow_mut()
                    .insert(nested.name.clone(), linked);
            }
        }
        let module = parsed.clone();
        let definitions: OrderedMap<Name, Rc<Definition>> = module
            .definitions
            .iter()
            .rev()
            .map(|definition| (definition.name.clone(), definition.clone()))
            .collect();
        let get_instance: GetInstance =
            Rc::new(|_| Err(FrontError::NotYet("an INSTANCE".to_owned())));
        let context = ModuleContext {
            imported: Rc::new(visible.clone()),
            get_instance,
            bound,
            definitions: Rc::new(definitions),
            get_key: Rc::new(get_key.clone()),
            instanced: Rc::default(),
            facts: facts.clone(),
            reports,
            warnings: scope.warnings.clone(),
            selections: self.selections.clone(),
        };
        let errors = resolve_module(&module, &context)?;
        scope.errors.borrow_mut().extend(errors);
        for definition in &module.definitions {
            let key = get_key(definition);
            self.definitions
                .borrow_mut()
                .insert(key, definition.clone());
            let symbol = get_definition_symbol(definition);
            // SANY binds the name of a fact to a fact the module imports before it.
            if symbol.kind == SymbolKind::Theorem
                && visible
                    .get(&definition.name)
                    .is_some_and(|existing| existing.kind == SymbolKind::Theorem)
            {
                continue;
            }
            visible.insert(definition.name.clone(), symbol.clone());
            if !definition.is_local {
                exported.insert(definition.name.clone(), symbol);
            }
        }
        let mut linked_facts = facts.take();
        linked_facts.extend(
            module
                .theorems
                .iter()
                .filter_map(|theorem| theorem.name.clone())
                .chain(
                    module
                        .assumptions
                        .iter()
                        .filter_map(|assumption| assumption.name.clone()),
                ),
        );
        let linked = Rc::new(LinkedModule {
            module,
            constants,
            variables,
            variable_locations,
            visible: Rc::new(visible),
            exported: Rc::new(exported),
            modules,
            facts: linked_facts,
        });
        self.link_order.borrow_mut().push(linked.clone());
        Ok(linked)
    }
}

/// `formatSanyWarnings`.
pub fn format_sany_warnings(warnings: &[SanyError]) -> String {
    format!(
        "*** Warnings: {}\n\n{}",
        warnings.len(),
        warnings
            .iter()
            .map(|warning| format!("{}\n\n{}\n\n\n", warning.location, warning.message))
            .collect::<Vec<_>>()
            .join("\n")
    )
}

/// `getEnabledVariableName`.
pub fn get_enabled_variable_name(name: &str) -> Name {
    Rc::from(format!("{name}@ENABLED"))
}

/// Links the spec's modules as `createEnvironment` does for a spec without a model
/// (`isUnconfigured`) that SANY accepted (`isSanyAccepted`), so it runs no level checks.
pub fn create_environment(options: &EnvironmentOptions) -> Result<Environment> {
    let root = Rc::new(parse_module_tokens(
        options.source,
        &tokenize(options.source)?,
        options.version,
    )?);
    let linker = Linker {
        options,
        root: root.clone(),
        texts: RefCell::new(
            [(options.source.to_owned(), root.clone())]
                .into_iter()
                .collect(),
        ),
        definitions: RefCell::default(),
        builtins: RefCell::new(
            CORE_OPERATORS
                .iter()
                .map(|(name, arity, flags)| {
                    let name: Name = Rc::from(*name);
                    (
                        name.clone(),
                        Builtin {
                            name,
                            arity: *arity,
                            flags: *flags,
                        },
                    )
                })
                .collect(),
        ),
        standard_exports: RefCell::default(),
        linked_modules: RefCell::default(),
        nested_modules: RefCell::default(),
        link_order: RefCell::default(),
        dependencies: RefCell::default(),
        loading: RefCell::default(),
        linking: RefCell::default(),
        warnings: Rc::default(),
        selections: Rc::default(),
    };
    reject_module_literals(&root)?;
    let (linked_root, _) = linker.link_top_level(&root)?;
    let warnings = linker.warnings.borrow().clone();
    let printed = if warnings.is_empty() {
        Vec::new()
    } else {
        vec![format_sany_warnings(&warnings)]
    };
    let mut definitions = linker.definitions.take();
    for (name, symbol) in linked_root.visible.iter() {
        if symbol.key == *name {
            continue;
        }
        if let Some(definition) = definitions.get(&symbol.key).cloned() {
            definitions.insert(name.clone(), definition);
        }
    }
    let variables = linked_root.variables.clone();
    let mut variable_index: OrderedMap<Name, usize> = variables
        .iter()
        .enumerate()
        .map(|(position, name)| (name.clone(), position))
        .collect();
    let mut declared: Vec<Name> = Vec::new();
    for linked in linker.link_order.borrow().iter() {
        for variable in &linked.module.variables {
            if !declared.contains(&variable.name) {
                declared.push(variable.name.clone());
            }
        }
    }
    for name in declared {
        let index = variable_index
            .get(&name)
            .copied()
            .unwrap_or(variable_index.len());
        variable_index.insert(get_enabled_variable_name(&name), index);
    }
    Ok(Environment {
        definitions,
        builtins: linker.builtins.take(),
        variables,
        variable_index,
        root_constants: linked_root.constants.clone(),
        root_symbols: linked_root.visible.clone(),
        printed,
    })
}

//! The modules of a spec linked into one environment, as `createEnvironment` in
//! `src/environment.ts` links them: each module's definitions under their keys, the builtins of
//! the standard modules it loads, and its variables, with every name resolved. This is the linking
//! that the IR reads; the model's values and the startup evaluation come later (F7, F8).

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::*;
use crate::config::{ConfigValue, ModelConfig};
use crate::errors::{FrontError, SanyError, SanyReport, SyntaxError, format_range};
use crate::eval::Evaluator;
use crate::hash::{FastMap, FastSet};
use crate::instances::{
    AddDefinition, Instantiation, Instantiator, apply, identifier, let_expression, local_arguments,
    local_identifier, operator_definition, param, rename_locals, with_let_instances,
};
use crate::levels::{
    InstanceCheck, LevelAnalyzer, LevelContext, ModuleLevelContext, Scope, check_instance,
    get_level_units,
};
use crate::lexer::tokenize;
use crate::order::TlcOrder;
use crate::ordered_map::OrderedMap;
use crate::parser::{extract_module, parse_module_for_sany, parse_module_tokens};
use crate::resolve::{
    ErrorList, GetKey, InstancedModule, KEY_SEPARATOR, MODULE_START, ModuleContext, ModuleReport,
    ModuleSymbol, Result, SemanticUnit, SymbolKind, Symbols, Tables, collect_semantic_errors,
    get_arity, get_param_arities, is_before, is_theorem_definition, resolve_module,
    resolve_substitutions,
};
use crate::spec::get_definition;
use crate::standard_builtins::{
    self, CORE_OPERATORS, STANDARD_DEPENDENCIES, StandardModule, USER_STANDARD_MODULES,
};
use crate::standard_modules;
use crate::subexpressions::{resolve_instance_subexpressions, resolve_module_subexpressions};
use crate::tlc_messages::is_eval_exception;
use crate::values::ValueOrder;

/// A builtin the environment holds: its name, arity and flags (state-level, level-constant,
/// lazy), which the IR writes.
#[derive(Clone, Debug, PartialEq)]
pub struct Builtin {
    pub name: Name,
    pub arity: usize,
    pub flags: u32,
    /// A configuration's definition of a constant operator by its values: each row's arguments
    /// and its value (`createOperatorTable`).
    pub table: Option<Rc<OperatorTable>>,
}

pub type OperatorTable = Vec<(Vec<ConfigValue>, ConfigValue)>;

/// What linking makes of a spec.
pub struct Environment {
    /// The definitions by key, the instance copies included, and the root module's definitions
    /// also by the names it gives them.
    pub definitions: OrderedMap<Name, Rc<Definition>>,
    pub builtins: OrderedMap<Name, Builtin>,
    /// The configuration's substitutions, by the key of what it substitutes for.
    pub substitutions: OrderedMap<Name, Name>,
    /// The values the configuration assigns, by key.
    pub constants: OrderedMap<Name, ConfigValue>,
    /// The values the configuration assigns operators with parameters, by key, which TLC gives
    /// any application of the operator without evaluating its arguments (`Tool.evalAppl`).
    pub operator_constants: OrderedMap<Name, ConfigValue>,
    pub variables: Vec<Name>,
    /// Where the root module declares each of its variables (`variableLocations`).
    pub variable_locations: Vec<Location>,
    pub variable_index: OrderedMap<Name, usize>,
    pub root_constants: Vec<Rc<Declaration>>,
    pub root_symbols: Rc<Symbols>,
    /// The copies an INSTANCE with substitutions makes (`substitutedDefinitions`), by address.
    pub substituted_definitions: FastMap<usize, Rc<Definition>>,
    /// The copies an INSTANCE with substitutions makes, by key, with the name and location TLC
    /// gives an action that applies one (`instanceActions`).
    pub instance_actions: OrderedMap<Name, InstanceAction>,
    /// The name TLC gives each copy a named INSTANCE makes, by key: `I!Foo` (`instanceNames`).
    pub instance_names: OrderedMap<Name, Name>,
    /// What linking prints: SANY's warnings.
    pub printed: Vec<String>,
    /// The definitions TLC computes when it starts, each module's in the order TLC computes them,
    /// the modules in the order SANY finishes them, except a module an INSTANCE gives parameters
    /// to; empty for a spec linked without a configuration.
    pub startup_definitions: Vec<Rc<Definition>>,
    /// The assumptions of the root module and the modules it extends, an extended module's first.
    pub assumptions: Vec<Rc<Assumption>>,
    /// The resolution tables SANY's level analysis reads.
    pub tables: Rc<Tables>,
    /// The methods of the Java class that overrides a module's operators, which TLC reports as it
    /// starts.
    pub java_overrides: Vec<crate::java_overrides::JavaOverride>,
}

impl Environment {
    /// `createLevelAnalyzer` over the model: its assigned constants, and its variables with the
    /// builtins of `state_builtins` the spec has.
    pub fn create_level_analyzer(&self, state_builtins: &[&str]) -> LevelAnalyzer<'_> {
        LevelAnalyzer::new(
            LevelContext {
                constants: self.constants.keys().cloned().collect(),
                variables: self
                    .variables
                    .iter()
                    .cloned()
                    .chain(
                        state_builtins
                            .iter()
                            .map(|name| Name::from(*name))
                            .filter(|name| self.builtins.contains_key(name)),
                    )
                    .collect(),
                get_definition: Box::new(|name| get_definition(name, self).cloned()),
                get_qualified_name: Box::new(|_| None),
            },
            &self.tables,
        )
    }
}

/// The name and location TLC gives an action that applies a definition an INSTANCE with
/// substitutions copies: the name the instance exports it by, at the INSTANCE.
#[derive(Clone)]
pub struct InstanceAction {
    pub name: Name,
    pub location: Location,
}

/// What reads the bytes of the Java class TLC loads for a module, if it has one.
pub type ClassLoader<'a> = dyn Fn(&str) -> Option<Vec<u8>> + 'a;

pub struct EnvironmentOptions<'a> {
    pub source: &'a str,
    pub load_module: &'a dyn Fn(&str) -> Option<String>,
    pub config: &'a ModelConfig,
    /// Links the modules without a model, as SANY does, so a declared constant needs no value.
    pub is_unconfigured: bool,
    pub version: TlcVersion,
    /// Checks the levels of each module, as `createEnvironment` does for a spec SANY hasn't
    /// accepted (`isSanyAccepted`).
    pub is_level_checked: bool,
    /// The bytes of the Java class TLC loads for a module (`loadClass`), whose public static
    /// methods override the module's operators.
    pub load_class: Option<&'a ClassLoader<'a>>,
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
    extended: Vec<Rc<LinkedModule>>,
}

/// `errors` and `warnings` collect what SANY reports for the module.
struct ModuleScope {
    id: Name,
    symbols: Symbols,
    modules: OrderedMap<Name, Rc<LinkedModule>>,
    nested: Rc<RefCell<Vec<Rc<Module>>>>,
    errors: ErrorList,
    warnings: ErrorList,
    level_checks: LevelChecks,
}

/// The modules a top-level module links, each with the instances SANY checks with it.
type ModuleLevelChecks = Vec<(Rc<LinkedModule>, Vec<InstanceCheck>)>;
type LevelChecks = Rc<RefCell<ModuleLevelChecks>>;

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
    /// The methods of the Java class that overrides a module's operators.
    java_overrides: RefCell<Vec<crate::java_overrides::JavaOverride>>,
    dependencies: RefCell<FastMap<Name, FastSet<Name>>>,
    loading: RefCell<Vec<FastSet<Name>>>,
    /// The top-level modules being linked, to report a cycle of EXTENDS or INSTANCE.
    linking: RefCell<Vec<Name>>,
    warnings: ErrorList,
    copy_count: Cell<usize>,
    /// Whether each definition's module has parameters, which an INSTANCE copies it for.
    parameterized: RefCell<FastMap<Name, bool>>,
    /// The copies an INSTANCE with substitutions makes, by address.
    substituted_definitions: RefCell<FastMap<usize, Rc<Definition>>>,
    /// The definition each instance copy came from, and the instance parameters the copy adds.
    copy_sources: RefCell<OrderedMap<Name, (Name, usize)>>,
    tables: Rc<Tables>,
    /// The instances linked so far whose substitutions SANY checks.
    instance_checks: RefCell<Vec<InstanceCheck>>,
    /// The first module linked of each name, which an instance check reads.
    checked_modules: RefCell<FastMap<Name, Rc<LinkedModule>>>,
    /// The qualified name, such as I!Foo, of each copy a named INSTANCE makes.
    qualified_names: RefCell<FastMap<Name, Name>>,
    instance_actions: RefCell<OrderedMap<Name, InstanceAction>>,
    instance_names: RefCell<OrderedMap<Name, Name>>,
    /// Whether linking goes on after a module's errors, as SANY's semantic analysis does,
    /// keeping each module's messages and level checks in `collected`.
    is_collecting: Cell<bool>,
    collected: RefCell<Collected>,
}

/// What linking collects of each top-level module for SANY's report.
#[derive(Default)]
struct Collected {
    errors: FastMap<Name, Vec<SanyError>>,
    /// The module each warning so far was reported in.
    warning_modules: Vec<Name>,
    level_checks: FastMap<Name, ModuleLevelChecks>,
}

/// SANY's messages for a module: its warnings and its errors.
#[derive(Clone, Debug, Default)]
pub struct ModuleMessages {
    pub warnings: Vec<SanyError>,
    pub errors: Vec<SanyError>,
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

impl Environment {
    pub fn is_substituted(&self, definition: &Rc<Definition>) -> bool {
        self.substituted_definitions
            .contains_key(&(Rc::as_ptr(definition) as usize))
    }
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

    /// The text of a standard module SANY reads, as the parser reads it, where no module of the
    /// user's has its name.
    fn get_standard_source(&self, name: &str) -> Option<Rc<Module>> {
        self.standard_exports.borrow().get(name)?;
        let texts = match self.options.version {
            TlcVersion::Master => standard_modules::MASTER,
            TlcVersion::V1_7_4 => standard_modules::TLC_174,
        };
        let text = texts.iter().find(|module| module.0 == name)?.1;
        self.parse_text(text).ok()
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
                    table: None,
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

    /// `overrideDefinitions` with the class TLC loads for the module, if any.
    fn override_module(&self, module: Rc<Module>, is_root: bool) -> Result<Rc<Module>> {
        let Some((load, bytes)) = self
            .options
            .load_class
            .and_then(|load| Some((load, load(&module.name)?)))
        else {
            return Ok(module);
        };
        let (module, overrides) =
            crate::java_overrides::override_definitions(&module, &bytes, is_root, load)?;
        let mut java_overrides = self.java_overrides.borrow_mut();
        // TLC reports the overrides in the order it links the modules, which matters only for
        // two of them.
        if !java_overrides.is_empty() {
            return Err(FrontError::NotYet(
                "Java classes overriding two modules".to_owned(),
            ));
        }
        *java_overrides = overrides;
        Ok(module)
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
        let module = self.override_module(module, false)?;
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
        // SANY accepts the literals TLC can't evaluate.
        if !self.is_collecting.get() {
            reject_module_literals(&module)?;
        }
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
        let level_checks: LevelChecks = Rc::default();
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
                level_checks: level_checks.clone(),
            },
        );
        let closure = self.loading.borrow_mut().pop().unwrap_or_default();
        self.linking.borrow_mut().pop();
        let linked = linked?;
        if self.is_collecting.get() {
            let mut collected = self.collected.borrow_mut();
            let count = self.warnings.borrow().len();
            let owned = collected.warning_modules.len();
            collected
                .warning_modules
                .extend((owned..count).map(|_| parsed.name.clone()));
            collected.errors.insert(parsed.name.clone(), errors.take());
        }
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
            let loaded = self
                .linked_modules
                .borrow()
                .get(&duplicate.name)
                .map(|loaded| loaded.module.clone())
                .or_else(|| self.get_standard_source(&duplicate.name));
            // SANY reports it where it meets the nested module, among the module's other errors.
            let is_reported = self
                .collected
                .borrow()
                .errors
                .get(&parsed.name)
                .is_some_and(|reported| !reported.is_empty());
            if is_reported {
                return Err(FrontError::NotYet(format!(
                    "a nested module {} of a name already defined, with other errors",
                    duplicate.name
                )));
            }
            if let Some(redefinition) =
                loaded.and_then(|loaded| get_module_redefinition(&duplicate, &loaded))
            {
                return Err(sany_error(
                    vec![redefinition],
                    false,
                    self.warnings.borrow().clone(),
                ));
            }
            return Err(module_redefined_error(&duplicate));
        }
        if self.is_collecting.get() {
            self.collected
                .borrow_mut()
                .level_checks
                .insert(parsed.name.clone(), level_checks.take());
        } else if self.options.is_level_checked {
            for (module, checks) in level_checks.take() {
                self.check_levels(&module, checks)?;
            }
        }
        Ok((linked, closure))
    }

    /// `checkModuleLevels`'s context of a linked module: its declarations, and its definitions by
    /// the names it sees them by.
    fn create_level_context(&self, linked: &Rc<LinkedModule>) -> LevelContext<'_> {
        let get_key = {
            let linked = linked.clone();
            move |symbol: &str| -> Name {
                linked
                    .visible
                    .get(symbol)
                    .map_or_else(|| Rc::from(symbol), |visible| visible.key.clone())
            }
        };
        let definition_key = get_key.clone();
        LevelContext {
            constants: linked
                .constants
                .iter()
                .map(|constant| constant.name.clone())
                .collect(),
            variables: linked.variables.iter().cloned().collect(),
            get_definition: Box::new(move |symbol| {
                self.definitions
                    .borrow()
                    .get(&definition_key(symbol))
                    .cloned()
            }),
            get_qualified_name: Box::new(move |symbol| {
                self.qualified_names.borrow().get(&get_key(symbol)).cloned()
            }),
        }
    }

    /// What an instance check reads of the module an instance names.
    fn create_module_level_context(&self, name: &Name) -> Result<ModuleLevelContext<'_>> {
        let checked = self.checked_modules.borrow().get(name).cloned();
        let linked = match checked {
            Some(linked) => linked,
            None => self.get_linked_module(name, name)?,
        };
        let mut seen: FastSet<usize> = FastSet::default();
        let definitions = linked
            .visible
            .values()
            .filter_map(|symbol| self.definitions.borrow().get(&symbol.key).cloned())
            .filter(|definition| seen.insert(Rc::as_ptr(definition) as usize))
            .collect();
        Ok(ModuleLevelContext {
            constants: linked.constants.clone(),
            variables: linked.variables.clone(),
            definitions,
            assumptions: linked
                .module
                .assumptions
                .iter()
                .map(|assumption| assumption.expression.clone())
                .collect(),
            theorems: linked.module.theorems.clone(),
            analyzer: LevelAnalyzer::new(self.create_level_context(&linked), &self.tables),
        })
    }

    /// `checkModuleLevels`: SANY's level errors in a linked module and its instances.
    fn check_levels(&self, linked: &Rc<LinkedModule>, checks: Vec<InstanceCheck>) -> Result<()> {
        let analyzer = LevelAnalyzer::new(self.create_level_context(linked), &self.tables);
        let instance_units = checks
            .iter()
            .map(|check| SemanticUnit {
                location: check.location.position(),
                check: Box::new(|_, _| {
                    let instancee = self.create_module_level_context(&check.module)?;
                    check_instance(check, &instancee, &analyzer)
                }),
            })
            .collect();
        let units = get_level_units(&linked.module, &analyzer, instance_units);
        let errors = collect_semantic_errors(units, &self.warnings)?;
        if errors.is_empty() {
            return Ok(());
        }
        Err(sany_error(errors, false, self.warnings.borrow().clone()))
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
                        table: None,
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
        let first_check = self.instance_checks.borrow().len();
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
        let mut extended = Vec::new();
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
            extended.push(linked);
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
        let get_key: GetKey = Rc::new(move |definition: &Definition| -> Name {
            if is_root {
                definition.name.clone()
            } else {
                Rc::from(format!("{}{KEY_SEPARATOR}{id}", definition.name))
            }
        });
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
        let is_parameter_free = constants.is_empty() && variables.is_empty();
        let instanced: Rc<RefCell<FastMap<usize, Symbols>>> = Rc::default();
        // Where an INSTANCE first made each name it adds visible.
        let mut imported_at: FastMap<Name, Position> = FastMap::default();
        let mut items: Vec<(Position, LinkItem)> = parsed
            .instances
            .iter()
            .map(|instance| {
                (
                    instance.location.position(),
                    LinkItem::Instance(instance.clone()),
                )
            })
            .chain(
                parsed
                    .modules
                    .iter()
                    .map(|nested| (nested.location.position(), LinkItem::Module(nested.clone()))),
            )
            .collect();
        items.sort_by(|left, right| {
            if is_before(left.0, right.0) {
                std::cmp::Ordering::Less
            } else {
                std::cmp::Ordering::Greater
            }
        });
        for (_, item) in items {
            let visible_modules = merge_modules(&scope.modules, &modules);
            match item {
                LinkItem::Instance(instance) => {
                    let context = self.create_context(
                        parsed,
                        parsed,
                        &visible,
                        &bound,
                        &get_key,
                        &instanced,
                        &facts,
                        &reports,
                        &scope.warnings,
                        &visible_modules,
                    );
                    let symbols = self.instantiate(
                        &instance,
                        parsed,
                        &context,
                        is_parameter_free,
                        visible_modules.get(&instance.module).cloned(),
                    )?;
                    for (name, symbol) in symbols.iter() {
                        if visible.contains_key(name) {
                            continue;
                        }
                        imported_at.insert(name.clone(), instance.location.position());
                        visible.insert(name.clone(), symbol.clone());
                        if !instance.is_local {
                            exported.insert(name.clone(), symbol.clone());
                        }
                    }
                    instanced
                        .borrow_mut()
                        .insert(Rc::as_ptr(&instance) as usize, symbols);
                }
                LinkItem::Module(nested) => {
                    // Generator.generateModule reports the errors of a nested module and goes
                    // on, and then SymbolTable.addModule reports a module already defined.
                    let existing = visible_modules.get(&nested.name).cloned();
                    let redefinition = existing
                        .as_ref()
                        .and_then(|existing| get_module_redefinition(&nested, &existing.module));
                    if existing.is_some() && redefinition.is_none() {
                        return Err(module_redefined_error(&nested));
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
                            symbols
                                .insert(definition.name.clone(), get_definition_symbol(definition));
                        }
                    }
                    let linked = self.link_module(
                        &nested,
                        ModuleScope {
                            id: Rc::from(format!("{}/{}", scope.id, nested.name)),
                            symbols,
                            modules: visible_modules,
                            nested: scope.nested.clone(),
                            errors: report.errors.clone(),
                            warnings: report.warnings.clone(),
                            level_checks: scope.level_checks.clone(),
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
            }
        }
        let visible_modules = merge_modules(&scope.modules, &modules);
        let expanded = with_let_instances(
            parsed,
            &mut |instance, lets| {
                let nested = get_let_module(parsed, instance, &modules, &visible_modules);
                self.instantiate_locally(instance, lets, &parsed.name, nested)
            },
            &self.tables,
        )?;
        let available: Vec<Rc<Definition>> = visible
            .iter()
            .filter_map(|(name, symbol)| {
                let definition = self.definitions.borrow().get(&symbol.key).cloned()?;
                Some(Rc::new(Definition {
                    name: name.clone(),
                    ..(*definition).clone()
                }))
            })
            .collect();
        let module = resolve_module_subexpressions(&expanded, &available, &self.tables)?;
        let context = self.create_context(
            parsed,
            &module,
            &visible,
            &bound,
            &get_key,
            &instanced,
            &facts,
            &reports,
            &scope.warnings,
            &visible_modules,
        );
        let errors = resolve_module(&module, &context)?;
        scope.errors.borrow_mut().extend(errors);
        for definition in &module.definitions {
            let key = get_key(definition);
            self.definitions
                .borrow_mut()
                .insert(key.clone(), definition.clone());
            self.parameterized
                .borrow_mut()
                .insert(key, !is_parameter_free);
            let symbol = get_definition_symbol(definition);
            // SANY binds the name of a fact to a fact the module imports before it.
            if symbol.kind == SymbolKind::Theorem
                && visible
                    .get(&definition.name)
                    .is_some_and(|existing| existing.kind == SymbolKind::Theorem)
                && imported_at
                    .get(&definition.name)
                    .is_none_or(|at| is_before(*at, definition.location.position()))
            {
                continue;
            }
            visible.insert(definition.name.clone(), symbol.clone());
            if !definition.is_hidden() {
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
            extended,
        });
        self.checked_modules
            .borrow_mut()
            .entry(linked.module.name.clone())
            .or_insert_with(|| linked.clone());
        // SANY checks the instances of a module with its definitions and theorems, so it reports
        // their errors together.
        let checks = self.instance_checks.borrow_mut().split_off(first_check);
        scope
            .level_checks
            .borrow_mut()
            .push((linked.clone(), checks));
        self.link_order.borrow_mut().push(linked.clone());
        Ok(linked)
    }

    /// `getUnit`: what resolution reads of the module and the modules it links to.
    #[allow(clippy::too_many_arguments)]
    fn create_context<'b>(
        &'b self,
        parsed: &Rc<Module>,
        module: &Module,
        visible: &Symbols,
        bound: &Rc<Symbols>,
        get_key: &GetKey,
        instanced: &Rc<RefCell<FastMap<usize, Symbols>>>,
        facts: &Rc<RefCell<FastSet<Name>>>,
        reports: &Rc<RefCell<Vec<ModuleReport>>>,
        warnings: &ErrorList,
        visible_modules: &OrderedMap<Name, Rc<LinkedModule>>,
    ) -> ModuleContext<'b> {
        let parsed_for_instances = parsed.clone();
        let modules_for_instances = visible_modules.clone();
        // SANY keeps the first of two definitions of a name.
        let definitions: OrderedMap<Name, Rc<Definition>> = module
            .definitions
            .iter()
            .rev()
            .map(|definition| (definition.name.clone(), definition.clone()))
            .collect();
        ModuleContext {
            imported: Rc::new(visible.clone()),
            get_instance: Rc::new(move |instance| {
                let parsed = &parsed_for_instances;
                let nested = get_let_module(
                    parsed,
                    instance,
                    &modules_for_instances,
                    &modules_for_instances,
                );
                let standard_symbols = if nested.is_some() {
                    None
                } else {
                    self.get_standard_symbols(&instance.module)
                };
                if let Some(standard_symbols) = standard_symbols {
                    return Ok(InstancedModule {
                        declarations: Vec::new(),
                        symbols: get_standard_instance_symbols(instance, &standard_symbols),
                        instancer: parsed.name.clone(),
                    });
                }
                let linked = match nested {
                    Some(nested) => nested,
                    None => self.get_linked_module(&instance.module, &parsed.name)?,
                };
                let declarations = get_declarations(&linked);
                Ok(InstancedModule {
                    symbols: self.get_instance_symbols(
                        instance,
                        &linked.exported,
                        &declarations,
                        &mut |key, _| Ok(key.clone()),
                    )?,
                    declarations,
                    instancer: parsed.name.clone(),
                })
            }),
            bound: bound.clone(),
            definitions: Rc::new(definitions),
            get_key: get_key.clone(),
            instanced: instanced.clone(),
            facts: facts.clone(),
            reports: reports.clone(),
            warnings: warnings.clone(),
            tables: self.tables.clone(),
        }
    }

    fn create_name(&self, name: &str) -> Name {
        let count = self.copy_count.get();
        self.copy_count.set(count + 1);
        Rc::from(format!("{name}#{count}"))
    }

    /// The names an INSTANCE adds for the definitions of the module it instantiates, each with the
    /// key that `get_key` gives it. SANY binds a copy of a definition that depends on the
    /// parameters at the INSTANCE.
    fn get_instance_symbols(
        &self,
        instance: &Instance,
        exported: &Symbols,
        declarations: &[Declaration],
        get_key: &mut dyn FnMut(&Name, &Name) -> Result<Name>,
    ) -> Result<Symbols> {
        let mut symbols = Symbols::new();
        for (name, symbol) in exported.iter() {
            if declarations
                .iter()
                .any(|declaration| declaration.name == *name)
            {
                continue;
            }
            let Some(instance_name) = &instance.name else {
                let key = get_key(&symbol.key, name)?;
                let is_parameterized = self.parameterized.borrow().get(&symbol.key) == Some(&true);
                symbols.insert(
                    name.clone(),
                    ModuleSymbol {
                        key,
                        kind: symbol.kind,
                        arity: symbol.arity,
                        params: symbol.params.clone(),
                        range: if is_parameterized {
                            instance.location.range.clone()
                        } else {
                            symbol.range.clone()
                        },
                    },
                );
                continue;
            };
            let qualified: Name = Rc::from(format!("{instance_name}!{name}"));
            symbols.insert(
                qualified.clone(),
                ModuleSymbol {
                    key: get_key(&symbol.key, &qualified)?,
                    kind: symbol.kind,
                    arity: symbol.arity + instance.params.len(),
                    params: symbol.params.as_ref().map(|params| {
                        instance
                            .params
                            .iter()
                            .map(|param| param.arity)
                            .chain(params.iter().copied())
                            .collect()
                    }),
                    range: None,
                },
            );
        }
        Ok(symbols)
    }

    fn instantiation<'b>(
        &'b self,
        params: Vec<OperatorParam>,
        substitutions: OrderedMap<Name, Expr>,
        linked: &LinkedModule,
        add_definition: AddDefinition<'b>,
    ) -> Instantiator<'b> {
        Instantiator::new(
            Instantiation {
                params,
                substitutions,
                variables: linked.variables.iter().cloned().collect(),
                get_definition: Box::new(|key| self.definitions.borrow().get(key).cloned()),
                is_parameterized: Box::new(|key| {
                    self.parameterized.borrow().get(key) == Some(&true)
                }),
                add_definition,
                create_name: Box::new(|name| self.create_name(name)),
            },
            &self.tables,
        )
    }

    /// `instantiate`: links an INSTANCE of a module, adding the copies of its definitions to the
    /// environment, and returns the names it adds.
    fn instantiate(
        &self,
        instance: &Rc<Instance>,
        module: &Module,
        context: &ModuleContext,
        is_parameter_free: bool,
        nested: Option<Rc<LinkedModule>>,
    ) -> Result<Symbols> {
        let standard_symbols = if nested.is_some() {
            None
        } else {
            self.get_standard_symbols(&instance.module)
        };
        if let Some(standard_symbols) = standard_symbols {
            return Ok(get_standard_instance_symbols(instance, &standard_symbols));
        }
        let linked = match nested {
            Some(nested) => nested,
            None => self.get_linked_module(&instance.module, &module.name)?,
        };
        for name in &linked.facts {
            context.facts.borrow_mut().insert(match &instance.name {
                None => name.clone(),
                Some(instance_name) => Rc::from(format!("{instance_name}!{name}")),
            });
        }
        let declarations = get_declarations(&linked);
        let suffix = format!("#{}", self.copy_count.get());
        self.copy_count.set(self.copy_count.get() + 1);
        let renamed: FastMap<Name, Name> = instance
            .params
            .iter()
            .map(|param| {
                (
                    param.name.clone(),
                    Rc::from(format!("{}{suffix}", param.name)),
                )
            })
            .collect();
        let substitutions = resolve_substitutions(
            &*resolve_instance_subexpressions(instance, module, &self.tables)?,
            &declarations,
            module,
            context,
        )?;
        // Generator.createSubstIn: the definitions of a module with errors have no bodies to
        // substitute in, which SANY reports once at each INSTANCE of it.
        let is_instancee_failed = self
            .collected
            .borrow()
            .errors
            .get(&instance.module)
            .is_some_and(|errors| !errors.is_empty());
        if is_instancee_failed
            && let Some(report) = context.reports.borrow().last()
            && let Some(range) = &instance.location.range
        {
            report.errors.borrow_mut().push(SanyError {
                location: format_range(range),
                message:
                    "Substitution error, probably due to error \nin module being instantiated."
                        .to_owned(),
            });
        }
        self.instance_checks.borrow_mut().push(InstanceCheck {
            module: instance.module.clone(),
            instancer: module.name.clone(),
            lets: Vec::new(),
            substitutions: substitutions.clone(),
            location: instance.location.clone(),
        });
        let has_declarations = !declarations.is_empty();
        let prefix = instance.params.len();
        let module_name = module.name.clone();
        let instance_name = instance.name.clone();
        let instantiator = self.instantiation(
            instance
                .params
                .iter()
                .map(|param| OperatorParam {
                    name: Rc::from(format!("{}{suffix}", param.name)),
                    ..param.clone()
                })
                .collect(),
            substitutions
                .iter()
                .map(|(name, expression)| {
                    (
                        name.clone(),
                        rename_locals(expression, &renamed, &FastSet::default(), &self.tables),
                    )
                })
                .collect(),
            &linked,
            Box::new(move |source, name, create| {
                let key = self.create_name(&format!("{name}{KEY_SEPARATOR}{module_name}"));
                let definition = create(&key)?;
                if has_declarations {
                    self.substituted_definitions
                        .borrow_mut()
                        .insert(Rc::as_ptr(&definition) as usize, definition.clone());
                }
                self.definitions
                    .borrow_mut()
                    .insert(key.clone(), definition);
                self.parameterized
                    .borrow_mut()
                    .insert(key.clone(), !is_parameter_free);
                self.copy_sources
                    .borrow_mut()
                    .insert(key.clone(), (source.clone(), prefix));
                if let Some(instance_name) = &instance_name {
                    let mut instance_names = self.instance_names.borrow_mut();
                    let source_name = instance_names.get(source).cloned().unwrap_or(name.clone());
                    instance_names.insert(
                        key.clone(),
                        Rc::from(format!("{instance_name}!{source_name}")),
                    );
                }
                Ok(key)
            }),
        );
        self.get_instance_symbols(
            instance,
            &linked.exported,
            &declarations,
            &mut |key, name| {
                let copy = match instance.name {
                    None => instantiator.get_key(key)?,
                    Some(_) => instantiator.get_qualified_key(key)?,
                };
                if has_declarations {
                    self.instance_actions.borrow_mut().insert(
                        copy.clone(),
                        InstanceAction {
                            name: name.clone(),
                            location: instance.location.clone(),
                        },
                    );
                }
                if instance.name.is_some() {
                    self.qualified_names
                        .borrow_mut()
                        .insert(copy.clone(), name.clone());
                }
                Ok(copy)
            },
        )
    }

    /// `instantiateLocally`: the definitions an INSTANCE in a LET adds to the LET.
    fn instantiate_locally(
        &self,
        instance: &Rc<Instance>,
        lets: &[Rc<Definition>],
        instancer: &Name,
        nested: Option<Rc<LinkedModule>>,
    ) -> Result<Vec<Rc<Definition>>> {
        let location = &instance.location;
        let standard_symbols = if nested.is_some() {
            None
        } else {
            self.get_standard_symbols(&instance.module)
        };
        if let Some(standard_symbols) = standard_symbols {
            let Some(instance_name) = &instance.name else {
                return Ok(Vec::new());
            };
            return Ok(standard_symbols
                .iter()
                .map(|(name, symbol)| {
                    let forwarded = create_argument_params(symbol.arity);
                    create_local_alias(
                        Rc::from(format!("{instance_name}!{name}")),
                        symbol.key.clone(),
                        instance.params.iter().chain(&forwarded).cloned().collect(),
                        &forwarded,
                        location,
                    )
                })
                .collect());
        }
        let linked = match nested {
            Some(nested) => nested,
            None => self.get_linked_module(&instance.module, instancer)?,
        };
        let suffix = format!("#{}", self.copy_count.get());
        self.copy_count.set(self.copy_count.get() + 1);
        let explicit: FastMap<Name, Expr> = instance
            .substitutions
            .iter()
            .map(|substitution| (substitution.name.clone(), substitution.expression.clone()))
            .collect();
        let declarations = get_declarations(&linked);
        let get_replacement = |declaration: &Declaration| {
            explicit
                .get(&declaration.name)
                .cloned()
                .unwrap_or_else(|| identifier(declaration.name.clone(), location))
        };
        self.instance_checks.borrow_mut().push(InstanceCheck {
            module: instance.module.clone(),
            instancer: instancer.clone(),
            lets: lets.to_vec(),
            substitutions: declarations
                .iter()
                .map(|declaration| (declaration.name.clone(), get_replacement(declaration)))
                .collect(),
            location: location.clone(),
        });
        let instance_param_names: FastSet<Name> = instance
            .params
            .iter()
            .map(|param| param.name.clone())
            .collect();
        let is_parameter_dependent = |declaration: &Declaration| {
            mentions_name(&get_replacement(declaration), &instance_param_names)
        };
        let substitution_definitions: Vec<Rc<Definition>> = declarations
            .iter()
            .map(|declaration| {
                let (params, body) =
                    get_substitution_body(get_replacement(declaration), declaration, location);
                let all = if is_parameter_dependent(declaration) {
                    instance.params.iter().cloned().chain(params).collect()
                } else {
                    params
                };
                Rc::new(operator_definition(
                    Rc::from(format!("{}{suffix}", declaration.name)),
                    all,
                    body,
                    true,
                    location,
                ))
            })
            .collect();
        let copies: Rc<RefCell<Vec<Rc<Definition>>>> = Rc::default();
        let instance_module = instance.module.clone();
        let copied = copies.clone();
        let local_suffix = suffix.clone();
        let instantiator = self.instantiation(
            instance.params.clone(),
            declarations
                .iter()
                .map(|declaration| {
                    let name: Name = Rc::from(format!("{}{suffix}", declaration.name));
                    let replacement = if is_parameter_dependent(declaration) {
                        let call =
                            apply(name, local_arguments(&instance.params, location), location);
                        call.resolved.is_local.set(true);
                        call
                    } else {
                        local_identifier(name, location)
                    };
                    (declaration.name.clone(), replacement)
                })
                .collect(),
            &linked,
            Box::new(move |_, name, create| {
                let key: Name = Rc::from(format!(
                    "{name}{KEY_SEPARATOR}{instance_module}{local_suffix}.{}",
                    copied.borrow().len()
                ));
                let definition = create(&key)?;
                let copy = match definition.kind {
                    DefinitionKind::Operator { .. } => Rc::new(Definition {
                        name: key.clone(),
                        ..(*definition).clone()
                    }),
                    DefinitionKind::Function { .. } => create_local_function(&definition, &key),
                };
                copied.borrow_mut().push(copy);
                Ok(key)
            }),
        );
        let mut aliases: Vec<Rc<Definition>> = Vec::new();
        for (name, symbol) in linked.exported.iter() {
            if declarations
                .iter()
                .any(|declaration| declaration.name == *name)
            {
                continue;
            }
            let key = instantiator.get_key(&symbol.key)?;
            let own_params = create_argument_params(symbol.arity);
            let params: Vec<OperatorParam> =
                instance.params.iter().chain(&own_params).cloned().collect();
            let forwarded = if key == symbol.key {
                own_params
            } else {
                params.clone()
            };
            aliases.push(create_local_alias(
                match &instance.name {
                    None => name.clone(),
                    Some(instance_name) => Rc::from(format!("{instance_name}!{name}")),
                },
                key,
                params,
                &forwarded,
                location,
            ));
        }
        drop(instantiator);
        let mut definitions = substitution_definitions;
        definitions.extend(copies.take());
        definitions.extend(aliases);
        Ok(definitions)
    }
}

/// What a module links in the order of its text: an INSTANCE, or a module nested in it.
enum LinkItem {
    Instance(Rc<Instance>),
    Module(Rc<Module>),
}

fn merge_modules(
    outer: &OrderedMap<Name, Rc<LinkedModule>>,
    own: &OrderedMap<Name, Rc<LinkedModule>>,
) -> OrderedMap<Name, Rc<LinkedModule>> {
    let mut merged = outer.clone();
    for (name, module) in own.iter() {
        merged.insert(name.clone(), module.clone());
    }
    merged
}

/// `getLetModule`: the module nested in this one that an INSTANCE in a LET or a proof
/// instantiates, which it may name only after the module.
fn get_let_module(
    parsed: &Module,
    instance: &Instance,
    modules: &OrderedMap<Name, Rc<LinkedModule>>,
    visible_modules: &OrderedMap<Name, Rc<LinkedModule>>,
) -> Option<Rc<LinkedModule>> {
    let Some(own) = parsed
        .modules
        .iter()
        .find(|nested| nested.name == instance.module)
    else {
        return visible_modules.get(&instance.module).cloned();
    };
    let is_instanced_after_definition = parsed
        .instances
        .iter()
        .find(|item| item.module == own.name)
        .is_some_and(|first| is_before(own.location.position(), first.location.position()));
    if is_instanced_after_definition {
        modules.get(&own.name).cloned()
    } else {
        None
    }
}

fn get_standard_instance_symbols(instance: &Instance, standard_symbols: &Symbols) -> Symbols {
    let Some(instance_name) = &instance.name else {
        return standard_symbols.clone();
    };
    standard_symbols
        .iter()
        .map(|(name, symbol)| {
            (
                Rc::from(format!("{instance_name}!{name}")),
                ModuleSymbol {
                    range: None,
                    ..symbol.clone()
                },
            )
        })
        .collect()
}

fn get_declarations(linked: &LinkedModule) -> Vec<Declaration> {
    linked
        .constants
        .iter()
        .map(|constant| (**constant).clone())
        .chain(linked.variables.iter().zip(&linked.variable_locations).map(
            |(variable, location)| Declaration {
                name: variable.clone(),
                arity: 0,
                location: location.clone(),
            },
        ))
        .collect()
}

fn create_argument_params(arity: usize) -> Vec<OperatorParam> {
    (0..arity)
        .map(|index| param(Rc::from(format!("argument{index}")), 0))
        .collect()
}

/// `createLocalAlias`: a definition that names another, forwarding its arguments.
fn create_local_alias(
    name: Name,
    key: Name,
    params: Vec<OperatorParam>,
    forwarded: &[OperatorParam],
    location: &Location,
) -> Rc<Definition> {
    let body = if forwarded.is_empty() {
        identifier(key, location)
    } else {
        apply(key, local_arguments(forwarded, location), location)
    };
    Rc::new(operator_definition(name, params, body, true, location))
}

/// `createLocalFunction`: an operator whose LET defines the function a LET INSTANCE copies.
fn create_local_function(definition: &Rc<Definition>, key: &Name) -> Rc<Definition> {
    let location = &definition.location;
    Rc::new(operator_definition(
        key.clone(),
        Vec::new(),
        let_expression(
            vec![definition.clone()],
            local_identifier(definition.name.clone(), location),
            location,
        ),
        true,
        location,
    ))
}

fn mentions_name(expression: &Expression, names: &FastSet<Name>) -> bool {
    match &expression.kind {
        ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. }
            if expression
                .reference()
                .is_some_and(|name| names.contains(&name)) =>
        {
            true
        }
        _ => expression
            .children()
            .iter()
            .any(|child| mentions_name(child, names)),
    }
}

/// `getSubstitutionBody`: the parameters and body of the definition a LET INSTANCE makes for a
/// declaration of the module.
fn get_substitution_body(
    replacement: Expr,
    declaration: &Declaration,
    location: &Location,
) -> (Vec<OperatorParam>, Expr) {
    if declaration.arity == 0 {
        return (Vec::new(), replacement);
    }
    if let ExpressionKind::Lambda { params, body, .. } = &replacement.kind {
        return (
            params.iter().map(|name| param(name.clone(), 0)).collect(),
            body.clone(),
        );
    }
    let params = create_argument_params(declaration.arity);
    let operator = match &replacement.kind {
        ExpressionKind::Identifier { .. } | ExpressionKind::OperatorReference { .. } => {
            replacement.reference().unwrap_or_default()
        }
        _ => declaration.name.clone(),
    };
    let body = apply(operator, local_arguments(&params, location), location);
    (params, body)
}

const BUILTIN_LAZY: u32 = 4;

/// `toValue` fails with an unexpected exception on a configuration number too big for TLC.
fn check_value(value: &ConfigValue) -> Result<()> {
    match value {
        ConfigValue::Number(number) if !is_tlc_integer(*number) => {
            let mut text = String::new();
            crate::json::write_js_number(&mut text, *number);
            Err(FrontError::Evaluation(format!(
                "Integer overflow: {text} is outside TLC's 32-bit range"
            )))
        }
        ConfigValue::Set(elements) => elements.iter().try_for_each(check_value),
        _ => Ok(()),
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

fn create_linker<'a>(options: &'a EnvironmentOptions<'a>, root: &Rc<Module>) -> Linker<'a> {
    Linker {
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
                            table: None,
                        },
                    )
                })
                .collect(),
        ),
        standard_exports: RefCell::default(),
        linked_modules: RefCell::default(),
        nested_modules: RefCell::default(),
        link_order: RefCell::default(),
        java_overrides: RefCell::default(),
        dependencies: RefCell::default(),
        loading: RefCell::default(),
        linking: RefCell::default(),
        warnings: Rc::default(),
        copy_count: Cell::new(0),
        parameterized: RefCell::default(),
        substituted_definitions: RefCell::default(),
        copy_sources: RefCell::default(),
        tables: Rc::default(),
        instance_checks: RefCell::default(),
        checked_modules: RefCell::default(),
        qualified_names: RefCell::default(),
        instance_actions: RefCell::default(),
        instance_names: RefCell::default(),
        is_collecting: Cell::new(false),
        collected: RefCell::default(),
    }
}

/// SANY's messages for each module of `order`, the order SANY analyzes the modules in. SANY goes
/// on after a module's errors, and level-checks a module, when `is_level_checked`, only while no
/// module so far has errors. A module with messages that isn't in `order` is `NotYet`.
pub fn get_sany_messages(
    options: &EnvironmentOptions,
    order: &[Name],
) -> Result<Vec<ModuleMessages>> {
    // SANY reports what the parser rejects in a BY, USE or HIDE as semantic errors of the module,
    // before the others.
    let (root, parser_errors) =
        parse_module_for_sany(options.source, &tokenize(options.source)?, options.version)?;
    let root = Rc::new(root);
    let linker = create_linker(options, &root);
    linker.is_collecting.set(true);
    linker.tables.is_collecting.set(true);
    if let Err(error) = linker.link_top_level(&root) {
        // An error of the root module that stops linking is one SANY reports with the module's
        // other messages, after the modules before it.
        let FrontError::Syntax(SyntaxError {
            sany: Some(report), ..
        }) = &error
        else {
            return Err(error);
        };
        // SANY places the arity of a substitution in the builtins' module.
        let is_in_root = |location: &str| {
            location.ends_with(&format!(" of module {}", root.name))
                || location == format!("In module {}", root.name)
                || location == "In module --TLA+ BUILTINS--"
        };
        if report.is_fatal || !report.errors.iter().all(|item| is_in_root(&item.location)) {
            return Err(error);
        }
        let mut collected = linker.collected.borrow_mut();
        collected
            .errors
            .entry(root.name.clone())
            .or_default()
            .extend(report.errors.iter().cloned());
        let count = linker.warnings.borrow().len();
        let owned = collected.warning_modules.len();
        collected
            .warning_modules
            .extend((owned..count).map(|_| root.name.clone()));
    }
    let mut collected = linker.collected.take();
    if !parser_errors.is_empty() {
        let errors = collected.errors.entry(root.name.clone()).or_default();
        if !errors.is_empty() {
            return Err(FrontError::NotYet(
                "SANY's errors in a BY, USE or HIDE with other errors".to_owned(),
            ));
        }
        *errors = parser_errors;
    }
    let warnings = linker.warnings.borrow().clone();
    let is_listed = |name: &Name| order.contains(name);
    let is_unlisted = collected
        .errors
        .iter()
        .any(|(name, errors)| !errors.is_empty() && !is_listed(name))
        || collected
            .warning_modules
            .iter()
            .any(|name| !is_listed(name));
    if is_unlisted {
        return Err(FrontError::NotYet(
            "messages of a module SANY doesn't analyze".to_owned(),
        ));
    }
    let mut level_checks = collected.level_checks;
    let mut has_errors = false;
    let mut messages = Vec::new();
    for name in order {
        let mut errors = collected.errors.get(name).cloned().unwrap_or_default();
        has_errors = has_errors || !errors.is_empty();
        if !has_errors && options.is_level_checked {
            for (module, checks) in level_checks.remove(name).unwrap_or_default() {
                match linker.check_levels(&module, checks) {
                    Ok(()) => {}
                    Err(FrontError::Syntax(SyntaxError {
                        sany: Some(report), ..
                    })) => errors.extend(report.errors),
                    Err(error) => return Err(error),
                }
            }
            has_errors = !errors.is_empty();
        }
        messages.push(ModuleMessages {
            warnings: warnings
                .iter()
                .zip(&collected.warning_modules)
                .filter(|(_, module)| *module == name)
                .map(|(warning, _)| warning.clone())
                .collect(),
            errors,
        });
    }
    if linker.warnings.borrow().len() != warnings.len() {
        return Err(FrontError::NotYet("a level check's warnings".to_owned()));
    }
    Ok(messages)
}

/// Links the spec's modules as `createEnvironment` does for a spec without a model
/// (`isUnconfigured`) that SANY accepted (`isSanyAccepted`), so it runs no level checks.
pub fn create_environment(options: &EnvironmentOptions) -> Result<Environment> {
    // TLC loads the overrides a `tlc2.overrides.TLCOverrides` index at its package's path lists
    // from any class, which the front end doesn't read. Its class loader finds no index by the
    // class's name alone (`TLAClass.loadClass`).
    if let Some(load) = options.load_class
        && load("tlc2/overrides/TLCOverrides").is_some()
    {
        return Err(FrontError::NotYet(
            "a TLCOverrides index of Java overrides".into(),
        ));
    }
    let parsed = Rc::new(parse_module_tokens(
        options.source,
        &tokenize(options.source)?,
        options.version,
    )?);
    let (root, root_overrides) = match options
        .load_class
        .and_then(|load| Some((load, load(&parsed.name)?)))
    {
        Some((load, bytes)) => {
            crate::java_overrides::override_definitions(&parsed, &bytes, true, load)?
        }
        None => (parsed, Vec::new()),
    };
    let linker = create_linker(options, &root);
    *linker.java_overrides.borrow_mut() = root_overrides;
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
    let config = options.config;
    let get_root_key = |name: &str| -> Name {
        linked_root
            .visible
            .get(name)
            .map_or_else(|| Rc::from(name), |symbol| symbol.key.clone())
    };
    let declared_constants: Vec<Name> = linked_root
        .constants
        .iter()
        .map(|constant| constant.name.clone())
        .collect();
    let variables = linked_root.variables.clone();
    let get_scoped_keys = |name: &str, module: Option<&str>| -> Vec<Name> {
        let Some(module) = module else {
            return vec![Rc::from(name), get_root_key(name)];
        };
        if module == &*root.name
            || declared_constants
                .iter()
                .any(|constant| &**constant == name)
        {
            return Vec::new();
        }
        let linked = linker
            .linked_modules
            .borrow()
            .get(module)
            .cloned()
            .or_else(|| linker.nested_modules.borrow().get(module).cloned());
        vec![
            linked
                .and_then(|linked| linked.visible.get(name).map(|symbol| symbol.key.clone()))
                .unwrap_or_else(|| Rc::from(name)),
        ]
    };
    let mut builtins = linker.builtins.take();
    let get_key_arity =
        |definitions: &OrderedMap<Name, Rc<Definition>>, key: &str| match definitions
            .get(key)
            .map(|definition| &definition.kind)
        {
            Some(DefinitionKind::Operator { params, .. }) => params.len(),
            _ => linked_root
                .constants
                .iter()
                .find(|constant| &*constant.name == key)
                .map_or(0, |constant| constant.arity),
        };
    let mut constants: OrderedMap<Name, ConfigValue> = OrderedMap::new();
    let mut operator_keys: FastSet<Name> = FastSet::default();
    let mut operator_constants: OrderedMap<Name, ConfigValue> = OrderedMap::new();
    let mut set_operator = |key: &Name,
                            builtin: Builtin,
                            definitions: &mut OrderedMap<Name, Rc<Definition>>,
                            constants: &mut OrderedMap<Name, ConfigValue>,
                            value: Option<&ConfigValue>| {
        builtins.insert(key.clone(), builtin);
        definitions.remove(key);
        constants.remove(key);
        operator_keys.insert(key.clone());
        operator_constants.remove(key);
        if let Some(value) = value {
            operator_constants.insert(key.clone(), value.clone());
        }
    };
    // `makeConstantTable` adds a row of an operator's table to the value the configuration gave
    // its name before, which it casts to a table.
    for (position, assignment) in config.constants.iter().enumerate() {
        let assigned = config.constants[..position].iter().find(|earlier| {
            earlier.name == assignment.name
                && earlier.args.is_none()
                && earlier.module.is_none()
                && assignment.module.is_none()
        });
        if let Some(earlier) = assigned.filter(|_| assignment.args.is_some()) {
            let class = match earlier.value {
                ConfigValue::Number(_) => "IntValue",
                ConfigValue::String(_) => "StringValue",
                ConfigValue::Boolean(_) => "BoolValue",
                ConfigValue::ModelValue(_) => "ModelValue",
                ConfigValue::Set(_) => "SetEnumValue",
                ConfigValue::Record(_) => "RecordValue",
            };
            return Err(FrontError::Evaluation(format!(
                "{}java.lang.ClassCastException\n: class tlc2.value.impl.{class} cannot be cast to class tlc2.value.impl.OpRcdValue (tlc2.value.impl.{class} and tlc2.value.impl.OpRcdValue are in unnamed module of loader 'app')",
                crate::errors::UNEXPECTED_HEAD
            )));
        }
    }
    for assignment in config
        .constants
        .iter()
        .filter(|assignment| assignment.args.is_none())
    {
        check_value(&assignment.value)?;
        for key in get_scoped_keys(&assignment.name, assignment.module.as_deref()) {
            let arity = get_key_arity(&definitions, &key);
            if arity == 0 {
                constants.insert(key, assignment.value.clone());
            } else {
                set_operator(
                    &key,
                    Builtin {
                        name: key.clone(),
                        arity,
                        flags: BUILTIN_LAZY,
                        table: None,
                    },
                    &mut definitions,
                    &mut constants,
                    Some(&assignment.value),
                );
            }
        }
    }
    // The rows of each operator the configuration gives by its values, as a table.
    let mut tables: OrderedMap<String, (Name, Option<String>, usize, OperatorTable)> =
        OrderedMap::new();
    for assignment in &config.constants {
        let Some(args) = &assignment.args else {
            continue;
        };
        let table_key = format!(
            "{}!{}",
            assignment.module.as_deref().unwrap_or(""),
            assignment.name
        );
        if let Some(table) = tables.get(&table_key)
            && table.2 != args.len()
        {
            return Err(FrontError::Config(format!(
                "The arity of the operator {} is inconsistent in the configuration file.",
                assignment.name
            )));
        }
        for value in args.iter().chain([&assignment.value]) {
            check_value(value)?;
        }
        if !tables.contains_key(&table_key) {
            tables.insert(
                table_key.clone(),
                (
                    Rc::from(assignment.name.as_str()),
                    assignment.module.clone(),
                    args.len(),
                    Vec::new(),
                ),
            );
        }
        if let Some(table) = tables.get_mut(&table_key) {
            table.3.push((args.clone(), assignment.value.clone()));
        }
    }
    for (name, module, row_arity, rows) in tables.values() {
        let rows = Rc::new(rows.clone());
        for key in get_scoped_keys(name, module.as_deref()) {
            let arity = match get_key_arity(&definitions, &key) {
                0 => *row_arity,
                arity => arity,
            };
            set_operator(
                &key,
                Builtin {
                    name: name.clone(),
                    arity,
                    flags: 0,
                    table: Some(rows.clone()),
                },
                &mut definitions,
                &mut constants,
                None,
            );
        }
    }
    let substitutions: OrderedMap<Name, Name> = config
        .substitutions
        .iter()
        .flat_map(|substitution| {
            get_scoped_keys(&substitution.name, substitution.module.as_deref())
                .into_iter()
                .map(|key| (key, get_root_key(&substitution.target)))
        })
        .collect();
    for substitution in config
        .substitutions
        .iter()
        .filter(|substitution| substitution.module.is_none())
    {
        let name = substitution.name.as_str();
        let target = substitution.target.as_str();
        let is_declared = |name: &str| {
            declared_constants
                .iter()
                .any(|constant| &**constant == name)
        };
        if !is_declared(name) && !linked_root.visible.contains_key(name) {
            return Err(FrontError::Config(format!(
                "In the configuration file, the identifier {name} does not appear in the specification."
            )));
        }
        if config
            .substitutions
            .iter()
            .any(|other| other.name == target)
        {
            return Err(FrontError::Config(format!(
                "In the configuration file, the identifier {target} appears\non the right-hand side of a <- after already appearing on the\nleft-hand side of one."
            )));
        }
        let target_key = get_root_key(target);
        let definition = definitions.get(&target_key).cloned();
        let is_defined = definition.is_some()
            || builtins.contains_key(&target_key)
            || constants.contains_key(&target_key)
            || is_declared(target)
            || variables.iter().any(|variable| &**variable == target);
        if !is_defined {
            return Err(FrontError::Config(format!(
                "The configuration file substitutes for {name} with the undefined identifier {target}."
            )));
        }
        if let Some(DefinitionKind::Operator { params, .. }) =
            definition.as_ref().map(|definition| &definition.kind)
        {
            let arity = linked_root
                .constants
                .iter()
                .find(|constant| &*constant.name == name)
                .map(|constant| constant.arity)
                .or_else(|| linked_root.visible.get(name).map(|symbol| symbol.arity));
            if Some(params.len()) != arity {
                return Err(FrontError::Config(format!(
                    "The configuration file substitutes for {name} with {target} of different number of arguments."
                )));
            }
        }
    }
    // TLC sets a module-scoped entry on the body of the module's definition, which every
    // instance of the module shares.
    let scoped_keys: FastSet<Name> = config
        .constants
        .iter()
        .filter_map(|item| item.module.as_deref().map(|module| (&item.name, module)))
        .chain(
            config
                .substitutions
                .iter()
                .filter_map(|item| item.module.as_deref().map(|module| (&item.name, module))),
        )
        .flat_map(|(name, module)| get_scoped_keys(name, Some(module)))
        .collect();
    let copy_sources = linker.copy_sources.take();
    let get_override = |key: &Name, prefix: usize| -> Option<(Name, usize)> {
        let mut current = (key.clone(), prefix);
        loop {
            if scoped_keys.contains(&current.0) {
                return Some(current);
            }
            let (source, added) = copy_sources.get(&current.0)?;
            current = (source.clone(), current.1 + added);
        }
    };
    for (key, (source, prefix)) in copy_sources.iter() {
        let (Some((target, skipped)), Some(definition)) =
            (get_override(source, *prefix), definitions.get(key).cloned())
        else {
            continue;
        };
        let params = match &definition.kind {
            DefinitionKind::Operator { params, .. } => params.clone(),
            DefinitionKind::Function { .. } => Vec::new(),
        };
        let alias = create_local_alias(
            key.clone(),
            target,
            params.clone(),
            params.get(skipped..).unwrap_or(&[]),
            &definition.location,
        );
        definitions.insert(key.clone(), alias.clone());
        for (name, symbol) in linked_root.visible.iter() {
            if symbol.key == *key && name != key {
                definitions.insert(name.clone(), alias.clone());
            }
        }
    }
    let unassigned: Vec<&Name> = declared_constants
        .iter()
        .filter(|name| {
            !constants.contains_key(*name)
                && !substitutions.contains_key(*name)
                && !operator_keys.contains(*name)
        })
        .collect();
    if !unassigned.is_empty() && !options.is_unconfigured {
        // TLC reports the first constant it finds unassigned in SANY's order of declarations.
        let order = TlcOrder::new(options.source, options.load_module, options.version)?
            .get_declaration_order(false)?;
        let name = order
            .iter()
            .find(|constant| unassigned.contains(constant))
            .unwrap_or(unassigned[0]);
        return Err(FrontError::Config(format!(
            "The constant parameter {name} is not assigned a value by the configuration file."
        )));
    }
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
    let startup_definitions = if options.is_unconfigured {
        Vec::new()
    } else {
        get_startup_definitions(&linker, &linked_root, &definitions, options)?
    };
    let mut assumptions = Vec::new();
    add_assumptions(&linked_root, &mut Vec::new(), &mut assumptions);
    let environment = Environment {
        startup_definitions,
        assumptions,
        tables: linker.tables.clone(),
        definitions,
        builtins,
        substitutions,
        constants,
        operator_constants,
        variables,
        variable_locations: linked_root.variable_locations.clone(),
        variable_index,
        root_constants: linked_root.constants.clone(),
        root_symbols: linked_root.visible.clone(),
        substituted_definitions: linker.substituted_definitions.take(),
        instance_actions: linker.instance_actions.take(),
        instance_names: linker.instance_names.take(),
        printed,
        java_overrides: linker.java_overrides.take(),
    };
    // TLC evaluates a substitute for a constant at startup and rejects it only when that fails and
    // the level bound it computes is above constant. The bound counts the operators that TLC's
    // Java code overrides with a minimum level as state-level, so the analyzer takes them for
    // variables.
    {
        let analyzer = environment.create_level_analyzer(&["TLCGet", "Trace", "CounterExample"]);
        let ranks = FastMap::default();
        let evaluator = Evaluator::new(
            &environment,
            ValueOrder { ranks: &ranks },
            options.version,
            false,
        );
        for (name, target) in environment.substitutions.iter() {
            let Some(definition) = environment.definitions.get(target) else {
                continue;
            };
            let is_parameterless = matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty());
            if !declared_constants.contains(name)
                || !is_parameterless
                || analyzer
                    .analyze_definition(definition, &Scope::default())?
                    .data
                    .level
                    == 0
            {
                continue;
            }
            match evaluator.evaluate(&definition.body, None) {
                // TLC's SpecProcessor adds the message of a TLCRuntimeException, not an
                // EvalException's.
                Err(FrontError::Evaluation(message)) => {
                    let addendum = if is_eval_exception(&message) {
                        String::new()
                    } else {
                        format!(" - specifically: {message}")
                    };
                    return Err(FrontError::Config(format!(
                        "The configuration file substitutes constant {name} with non-constant {target}{addendum}"
                    )));
                }
                Err(error) => return Err(error),
                Ok(_) => {}
            }
        }
    }
    Ok(environment)
}

// TLC computes the constant definitions of each module in the order SANY finishes the modules,
// except those of a module that an INSTANCE gives parameters to.
fn get_startup_definitions(
    linker: &Linker,
    linked_root: &Rc<LinkedModule>,
    definitions: &OrderedMap<Name, Rc<Definition>>,
    options: &EnvironmentOptions,
) -> Result<Vec<Rc<Definition>>> {
    let link_order = linker.link_order.borrow();
    let instantiated: FastSet<Name> = link_order
        .iter()
        .flat_map(|linked| {
            linked
                .module
                .instances
                .iter()
                .map(|instance| instance.module.clone())
        })
        .collect();
    let order = TlcOrder::new(options.source, options.load_module, options.version)?;
    let mut startup = Vec::new();
    for linked in link_order.iter().filter(|linked| {
        !instantiated.contains(&linked.module.name)
            || (linked.constants.is_empty() && linked.variables.is_empty())
    }) {
        let name = (!Rc::ptr_eq(linked, linked_root)).then_some(&*linked.module.name);
        for name in order.get_definition_order(name)? {
            let key = linked
                .visible
                .get(&name)
                .map_or(&name, |symbol| &symbol.key);
            startup.extend(definitions.get(key).cloned());
        }
    }
    Ok(startup)
}

fn add_assumptions(
    linked: &Rc<LinkedModule>,
    visited: &mut Vec<*const LinkedModule>,
    assumptions: &mut Vec<Rc<Assumption>>,
) {
    if visited.contains(&Rc::as_ptr(linked)) {
        return;
    }
    visited.push(Rc::as_ptr(linked));
    for extended in &linked.extended {
        add_assumptions(extended, visited, assumptions);
    }
    assumptions.extend(linked.module.assumptions.iter().cloned());
}

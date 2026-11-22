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
use crate::operator_tables::{PackagedMethod, TableObjects};
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
    self, CORE_OPERATORS, REPLACEABLE_TLC_MODULES, STANDARD_DEPENDENCIES, StandardModule,
    USER_STANDARD_MODULES,
};
use crate::standard_modules;
use crate::subexpressions::{resolve_instance_subexpressions, resolve_module_subexpressions};
use crate::tlc_messages::is_eval_exception;
use crate::values::ValueOrder;

/// A builtin the environment holds: its name, arity and flags (state-level, level-constant,
/// lazy), which the IR writes.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Intrinsic {
    Any,
    DefnsBuiltin,
    /// The Java method of a standard module TLC's jar holds, bound to the definition of a file
    /// of the user's that replaces the module (`processModuleOverrides`).
    StandardMethod,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Builtin {
    pub name: Name,
    pub intrinsic: Option<Intrinsic>,
    pub arity: usize,
    pub flags: u32,
    /// A configuration's definition of a constant operator by its values: each row's arguments
    /// and its value (`createOperatorTable`).
    pub table: Option<Rc<OperatorTable>>,
}

pub type OperatorTable = Vec<(Vec<ConfigValue>, ConfigValue)>;

#[derive(Clone, Copy)]
enum JsonSourceOpcode {
    Value,
    Array,
    Object,
}

impl JsonSourceOpcode {
    fn selected(method: &PackagedMethod) -> Option<Self> {
        if method.module.as_ref() != "Json" || method.builtin.arity != 1 {
            return None;
        }
        match method.builtin.name.as_ref() {
            "ToJson" => Some(Self::Value),
            "ToJsonArray" => Some(Self::Array),
            "ToJsonObject" => Some(Self::Object),
            _ => None,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Value => "ToJson",
            Self::Array => "ToJsonArray",
            Self::Object => "ToJsonObject",
        }
    }
}

/// An original configuration OpDef header whose positive arity prevents startup replacement.
pub(crate) struct ConfigOpDefHeader {
    definition: Rc<Definition>,
}

impl ConfigOpDefHeader {
    pub(crate) fn definition(&self) -> &Rc<Definition> {
        &self.definition
    }
}

/// A definition a global substitution targets that has a module-scoped value: whether the
/// linking took its body for of constant level, what it took of TLC's computation of the body as
/// it starts, and the definitions TLC computes as it starts that read the value.
#[derive(Clone, Debug)]
struct ScopedTargetCheck {
    key: Name,
    definition: Rc<Definition>,
    is_constant: bool,
    /// Whether TLC computes Y's body as it starts, through a declared constant at any level.
    is_attempted: bool,
    /// Whether the linking left the entry out, taking that computation to succeed.
    is_hidden: bool,
    cached: Vec<Rc<Definition>>,
    /// Whether each of `cached` may fail as TLC computes it, reading the entry, rather than
    /// succeed, and whether it must: TLC swallows the failure and computes the definition again
    /// at each use, after it computed Y, so that every read finds Y's computed body.
    may_fail: bool,
    must_fail: bool,
}

/// What the startup checks found of the substitutions' targets with a module-scoped value:
/// those whose body of constant level TLC fails to compute as it starts (`failed`), and those
/// whose every reader TLC computes before Y fails reading the entry, without an effect, so that
/// every read finds Y's computed body (`reread`).
#[derive(Default)]
struct TargetFacts {
    failed: FastSet<Name>,
    reread: FastSet<Name>,
}

impl TargetFacts {
    fn is_empty(&self) -> bool {
        self.failed.is_empty() && self.reread.is_empty()
    }
}

/// What linking makes of a spec.
pub struct Environment {
    /// The definitions by key, the instance copies included, and the root module's definitions
    /// also by the names it gives them.
    pub definitions: OrderedMap<Name, Rc<Definition>>,
    /// Exact pre-configuration copied headers, retained to verify later resolution identity.
    pub pre_override_headers: OrderedMap<Name, Rc<Definition>>,
    pub builtins: OrderedMap<Name, Builtin>,
    pub(crate) operator_objects: TableObjects,
    standard_shortcut_modules: Vec<Name>,
    json_source_opcodes: OrderedMap<Name, JsonSourceOpcode>,
    pub(crate) pinned_standard_sources: bool,
    /// The text each module the linker parsed was read from, by the module's name, which its
    /// nodes' ranges index; none for a name two texts define.
    pub(crate) module_texts: FastMap<Name, Option<Rc<str>>>,
    /// The configuration's substitutions, by the key of what it substitutes for.
    pub substitutions: OrderedMap<Name, Name>,
    /// Initial scalar/table values assigned to user definitions or root constants, without a
    /// competing global substitution or a selected Java method.
    pub configured_value_bindings: FastSet<Name>,
    config_opdef_headers: OrderedMap<Name, ConfigOpDefHeader>,
    /// The names of the definitions the configuration substitutes for anything but a declared
    /// constant of the root module, as written, so in any module.
    pub substitutes_for_definitions: Vec<Name>,
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
    /// The copies an INSTANCE with substitutions makes of a definition that is itself such a
    /// copy, by address: TLC's copy's body is a `SubstInNode` over the copied one's.
    pub nested_substitutions: FastSet<usize>,
    /// The copies an INSTANCE in a LET with substitutions makes of such a copy, by key.
    pub nested_let_copies: FastSet<Name>,
    /// The copies an INSTANCE with substitutions makes, by key, with the name and location TLC
    /// gives an action that applies one (`instanceActions`).
    pub instance_actions: OrderedMap<Name, InstanceAction>,
    /// The name TLC gives each copy a named INSTANCE makes, by key: `I!Foo` (`instanceNames`).
    pub instance_names: OrderedMap<Name, Name>,
    /// What linking prints: SANY's warnings.
    pub printed: Vec<String>,
    /// The definitions TLC computes when it starts, each module's in the order TLC computes them,
    /// the modules of files in the order SANY finishes them, each followed by its inner modules,
    /// except a module an INSTANCE gives parameters to; empty for a spec linked without a
    /// configuration.
    pub startup_definitions: Vec<Rc<Definition>>,
    /// The definitions `processConstantDefns` looks up again for a module whose context holds
    /// them from a module it extends (`ModuleNode.getOpDefs`), each with how many of
    /// `startup_definitions` TLC takes up before that module's: TLC evaluates one again there,
    /// with its effects, where it failed before (`lookup` finds the value of one that computed).
    pub startup_repeats: Vec<(usize, Rc<Definition>)>,
    /// For each module with two or more inner modules, the definitions TLC computes as it starts
    /// in each inner module and the modules nested in it: `processConstantDefns` takes the inner
    /// modules in the order of the module's Hashtable (`Context.getModDefs`), which the front end
    /// doesn't follow.
    pub startup_inner_siblings: Vec<Vec<Vec<Rc<Definition>>>>,
    /// The definitions of the modules an INSTANCE names whose order as TLC starts the front end
    /// doesn't follow (`get_startup_walk`): those of an inner module or of a module an INSTANCE
    /// in a LET names, and those of a module an INSTANCE gives parameters to that the front end
    /// computes as it starts.
    pub instanced_definitions: Vec<Rc<Definition>>,
    /// The assumptions of the root module and the modules it extends, an extended module's first.
    pub assumptions: Vec<Rc<Assumption>>,
    /// The resolution tables SANY's level analysis reads.
    pub tables: Rc<Tables>,
    /// The methods of the Java class that overrides a module's operators, which TLC reports as it
    /// starts.
    pub java_overrides: Vec<crate::java_overrides::JavaOverride>,
    /// An override index can replace definitions even when no class has the module's name.
    /// Actual or uncertain index origins prohibit the new literal-body certificates.
    /// This is a presence/profile witness, independent of legacy byte-based index loading.
    pub has_java_override_index: bool,
    /// The modules the spec links, in the order it links them.
    pub modules: Vec<Rc<Module>>,
    /// WITH literals whose semantic Expr object processConstants never visits.
    pub uninitialized_literals: FastSet<usize>,
    /// INSTANCE copies whose level inspection would follow a built-in's absent body.
    pub missing_operator_bodies: FastSet<usize>,
    /// The definitions a substitution targets that have a module-scoped value, with what the
    /// linking assumed of them, which the startup checks confirm.
    scoped_target_checks: Vec<ScopedTargetCheck>,
    /// The definitions a selector of the configuration names whose module-scoped value the
    /// environment leaves out (`check_selected_scoped_values`), by key, with that value.
    pub scoped_selected_values: FastMap<Name, ConfigValue>,
    /// Whether the environment keeps those values, as something else may read them
    /// (`check_selected_scoped_values`).
    pub is_scoped_selection_kept: bool,
    /// Whether it keeps them for a LET's INSTANCE, whose copies the front end checks apart.
    pub is_scoped_selection_let_instanced: bool,
}

impl Environment {
    pub(crate) fn has_json_source_opcode(&self, key: &Name, shown: &str) -> bool {
        let direct = self.json_source_opcodes.get(key).copied();
        let alias = self
            .operator_objects
            .is_admitted
            .then(|| {
                let method = self.operator_objects.method_aliases.get(key)?;
                JsonSourceOpcode::selected(method)
            })
            .flatten();
        direct
            .or(alias)
            .is_some_and(|opcode| opcode.name() == shown)
    }

    /// Source evidence for the exact successful standard shortcuts and their dependencies.
    /// Missing reads and an unmodeled parent remain unknown; this performs no resolver calls.
    pub fn has_pinned_standard_sources(
        &self,
        origin: &crate::model::ModelOrigin<'_>,
        version: TlcVersion,
    ) -> bool {
        !origin.legacy_metadata
            && origin
                .parent_runtime
                .in_profile(version, origin.java_profile)
                == crate::model::ParentRuntime::ModeledTlcMasterJdk21
            && origin.module_source_reads.is_some_and(|reads| {
                reads.canonical_or_absent(
                    self.standard_shortcut_modules.iter().map(|name| &**name),
                    version,
                )
            })
    }

    pub(crate) fn config_opdef_header(&self, name: &str) -> Option<&ConfigOpDefHeader> {
        self.config_opdef_headers.get(name)
    }

    /// `createLevelAnalyzer` over the model: its assigned constants, and its variables with the
    /// builtins of `state_builtins` the spec has.
    /// A level analyzer of the specification as SANY level-checks it, before TLC substitutes
    /// the configuration's definitions for the root module's declared constants: such a
    /// constant stays the declaration it is (`LevelNode.levelParams`).
    pub fn create_unsubstituted_level_analyzer(&self) -> LevelAnalyzer<'_> {
        LevelAnalyzer::new(
            LevelContext {
                constants: self.constants.keys().cloned().collect(),
                variables: self.variables.iter().cloned().collect(),
                get_definition: Box::new(|name| {
                    let is_declared = self.substitutions.contains_key(name)
                        && self
                            .root_constants
                            .iter()
                            .any(|declaration| &*declaration.name == name);
                    if is_declared {
                        return None;
                    }
                    crate::spec::get_definition(name, self).cloned()
                }),
                get_qualified_name: Box::new(|_| None),
            },
            &self.tables,
        )
    }

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
    pub origin: Option<&'a crate::model::ModelOrigin<'a>>,
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
    /// The modules of the command line's postconditions, which TLC adds to the root module's
    /// EXTENDS after its own (`ParameterizedSpecObj.findOrCreateParsedUnit`).
    pub linked_extendees: &'a [&'a str],
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

pub(crate) fn reject_module_literals(module: &Module) -> Result<()> {
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
    allow_native_aliases: bool,
    options: &'a EnvironmentOptions<'a>,
    root: Rc<Module>,
    /// Each module text parsed once, as `createTlcOrder`'s `parseText` reads it.
    texts: RefCell<FastMap<String, Rc<Module>>>,
    definitions: RefCell<OrderedMap<Name, Rc<Definition>>>,
    builtins: RefCell<OrderedMap<Name, Builtin>>,
    builtin_java_methods: RefCell<OrderedMap<Name, Name>>,
    /// The standard modules whose Java class TLC binds to a file of the user's that replaces the
    /// module (`REPLACEABLE_TLC_MODULES`), which the source evidence then covers too.
    user_replaced_modules: RefCell<Vec<Name>>,
    standard_exports: RefCell<FastMap<Name, Rc<Symbols>>>,
    packaged_methods: RefCell<Vec<PackagedMethod>>,
    json_source_opcodes: RefCell<OrderedMap<Name, JsonSourceOpcode>>,
    linked_modules: RefCell<FastMap<Name, Rc<LinkedModule>>>,
    nested_modules: RefCell<FastMap<Name, Rc<LinkedModule>>>,
    link_order: RefCell<Vec<Rc<LinkedModule>>>,
    external_module_order: RefCell<Vec<Name>>,
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
    /// The copies an INSTANCE with substitutions makes of such a copy, by address.
    nested_substitutions: RefCell<FastSet<usize>>,
    /// The copies an INSTANCE in a LET with substitutions makes of such a copy, by key.
    nested_let_copies: RefCell<FastSet<Name>>,
    /// The definition each instance copy came from, and the instance parameters the copy adds.
    copy_sources: RefCell<OrderedMap<Name, (Name, usize)>>,
    missing_operator_bodies: RefCell<FastSet<usize>>,
    tables: Rc<Tables>,
    /// The instances linked so far whose substitutions SANY checks.
    instance_checks: RefCell<Vec<InstanceCheck>>,
    /// The first module linked of each name, which an instance check reads.
    checked_modules: RefCell<FastMap<Name, Rc<LinkedModule>>>,
    /// The qualified name, such as I!Foo, of each copy a named INSTANCE makes.
    qualified_names: RefCell<FastMap<Name, Name>>,
    instance_actions: RefCell<OrderedMap<Name, InstanceAction>>,
    instance_names: RefCell<OrderedMap<Name, Name>>,
    /// The modules an INSTANCE in a LET, or an INSTANCE of an inner module, names, whose copies
    /// TLC computes as it starts in an order the front end doesn't follow.
    unordered_instancees: RefCell<FastSet<Name>>,
    /// The definition each copy an INSTANCE in a LET makes came from, and the instance
    /// parameters the copy adds.
    let_copy_sources: RefCell<OrderedMap<Name, (Name, usize)>>,
    /// The definitions with a module-scoped configuration entry that copies an INSTANCE in a LET
    /// makes read in place of their own bodies, as TLC's copies share the body the entry is set
    /// on (`SpecProcessor.processConstantDefns`).
    let_aliased_keys: FastSet<Name>,
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
#[derive(Clone, Debug, Default, PartialEq, Eq)]
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

/// The modules a standard module uses whose definitions its own may read: TLCExt uses only TLC,
/// whose operators are Java methods whatever the modules TLC uses (but a file of the user's
/// that replaces TLC itself), and Integers, with Naturals.
fn get_unbound_dependencies(name: &str) -> &'static [&'static str] {
    match name {
        "TLCExt" => &["TLC", "Integers", "Naturals"],
        _ => get_dependencies(name),
    }
}

/// Whether SANY reads the module from a file of the user's of its name, before its standard
/// module (`SimpleFilenameToStream.locate`), as far as the front end follows it.
pub(crate) fn is_user_replaceable(name: &str) -> bool {
    USER_STANDARD_MODULES.contains(&name) || REPLACEABLE_TLC_MODULES.contains(&name)
}

fn is_sany_standard_module(name: &str, version: TlcVersion) -> bool {
    let modules = match version {
        TlcVersion::Master => standard_modules::MASTER,
        TlcVersion::V1_7_4 => standard_modules::TLC_174,
    };
    modules.iter().any(|module| module.0 == name)
}

thread_local! {
    /// The standard modules of the pinned TLC as the parser reads them, by name, each parsed on
    /// the first read of one of its definitions; and what each name read gave.
    static PARSED_STANDARD_MODULES: RefCell<FastMap<&'static str, Option<Rc<Module>>>> =
        RefCell::new(FastMap::default());
    static STANDARD_DEFINITIONS: RefCell<FastMap<Box<str>, Option<StandardDefinition>>> =
        RefCell::new(FastMap::default());
}

/// A standard module's definition, with the module it is read in.
pub(crate) type StandardDefinition = (Rc<Module>, Rc<Definition>);

fn get_parsed_standard_module(name: &'static str, source: &'static str) -> Option<Rc<Module>> {
    PARSED_STANDARD_MODULES.with(|modules| {
        modules
            .borrow_mut()
            .entry(name)
            .or_insert_with(|| crate::parser::parse_module(source).ok().map(Rc::new))
            .clone()
    })
}

/// The definition of `name` in the standard modules of the pinned TLC, as the parser reads
/// them, with its module: the first module in order that defines it. The operator tables say
/// which modules define a name, so only those are parsed, each once.
pub(crate) fn get_standard_module_definition(name: &str) -> Option<StandardDefinition> {
    STANDARD_DEFINITIONS.with(|definitions| {
        if let Some(definition) = definitions.borrow().get(name) {
            return definition.clone();
        }
        let definition = standard_modules::MASTER
            .iter()
            .filter(|(module, _)| {
                standard_builtins::MASTER.iter().any(|table| {
                    table.name == *module
                        && table.operators.iter().any(|operator| operator.name == name)
                })
            })
            .find_map(|(module, source)| {
                let module = get_parsed_standard_module(module, source)?;
                let definition = module
                    .definitions
                    .iter()
                    .find(|definition| &*definition.name == name)?
                    .clone();
                Some((module, definition))
            });
        definitions
            .borrow_mut()
            .insert(name.into(), definition.clone());
        definition
    })
}

impl Environment {
    /// The definition of a standard module's operator the front end implements as a builtin, as
    /// SANY parses the module: SANY levels an application of the operator by it.
    pub fn get_standard_definition(&self, name: &str) -> Option<Rc<Definition>> {
        if !self.builtins.contains_key(name) {
            return None;
        }
        get_standard_module_definition(name).map(|(_, definition)| definition)
    }

    pub fn is_substituted(&self, definition: &Rc<Definition>) -> bool {
        self.substituted_definitions
            .contains_key(&(Rc::as_ptr(definition) as usize))
    }

    /// Whether the configuration substitutes a definition without parameters for a name other
    /// than a declared constant (`X <- Y`, X a definition): `processConstantDefns` computes Y
    /// again where it reaches X, with its prints and draws, where X's lookup finds Y's OpDefNode.
    pub fn is_recomputed_substitute(&self, definition: &Rc<Definition>) -> bool {
        matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
            && self.substitutions.iter().any(|(name, target)| {
                !self
                    .root_constants
                    .iter()
                    .any(|constant| constant.name == *name)
                    && self
                        .definitions
                        .get(target)
                        .is_some_and(|other| Rc::ptr_eq(other, definition))
            })
    }

    pub fn is_nested_substitution(&self, definition: &Rc<Definition>) -> bool {
        self.nested_substitutions
            .contains(&(Rc::as_ptr(definition) as usize))
            || self.nested_let_copies.contains(&definition.name)
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

    fn has_native_subset_set(&self, module: &str) -> bool {
        module == "Randomization"
            && self
                .options
                .origin
                .is_some_and(|origin| origin.is_closed_for([module]))
    }

    fn standard_builtin_flags(&self, module: &str, operator: &str, flags: u32) -> u32 {
        let is_closed = self
            .options
            .origin
            .is_some_and(|origin| origin.legacy_metadata || origin.is_closed_for([module]));
        // TestRandomSetOfSubsets is a definition of TLA+ whose level is RandomSetOfSubsets's.
        let strict_random_method = (module == "Randomization"
            && matches!(operator, "RandomSetOfSubsets" | "TestRandomSetOfSubsets"))
            || (module == "TLC" && operator == "RandomElement");
        let strict_closed = strict_random_method
            && self
                .options
                .origin
                .is_some_and(|origin| origin.is_closed_for([module]));
        // Randomization's Java RandomSubset has no minimum level (`MethodValue.get`), so
        // `processConstantDefns` computes a constant definition that draws with it as TLC starts,
        // with the generator's first draws, and keeps the value it drew.
        let is_constant_subset = module == "Randomization"
            && operator == "RandomSubset"
            && self
                .options
                .origin
                .is_some_and(|origin| origin.is_closed_for([module]));
        let flags = if strict_random_method && strict_closed || is_constant_subset {
            flags & !1
        } else {
            flags
        };
        let flags = if is_closed && (!strict_random_method || strict_closed) {
            flags
        } else {
            flags | tla_ir::Builtin::EXTERNAL_CLASS as u32
        };
        let flags = if module == "TLCExt"
            && operator == "TLCDefer"
            && self.options.version == TlcVersion::Master
            && self.options.origin.is_some_and(|origin| {
                origin.parent_runtime == crate::model::ParentRuntime::ModeledTlcMasterJdk21
                    && origin.is_closed_for([module])
            }) {
            flags | tla_ir::Builtin::PACKAGED_TLC_DEFER as u32
        } else {
            flags
        };
        // Keep the earlier byte-based legacy gate distinct from the new presence-only proof.
        if (operator == "Any" || module == "Json" && operator == "ToJson")
            && self
                .options
                .load_class
                .is_some_and(|load| load(module).is_some())
        {
            flags | tla_ir::Builtin::DECLINED as u32
        } else {
            flags
        }
    }

    fn construct_builtin(&self, key: Name, builtin: Builtin) {
        self.json_source_opcodes.borrow_mut().remove(&key);
        self.builtins.borrow_mut().insert(key, builtin);
    }

    fn record_packaged_method(&self, module: &str, key: &Name, builtin: Builtin) {
        if self.options.version == TlcVersion::Master
            && self
                .options
                .origin
                .is_some_and(|origin| origin.is_closed_for([module]))
            && let Some(method) = PackagedMethod::registered(module, builtin)
        {
            if let Some(opcode) = JsonSourceOpcode::selected(&method) {
                self.json_source_opcodes
                    .borrow_mut()
                    .insert(key.clone(), opcode);
            }
            self.packaged_methods.borrow_mut().push(method);
        }
    }

    fn mark_external_inherited_builtins(&self, module: &str) {
        if module == "Integers"
            && !self
                .options
                .origin
                .is_some_and(|origin| origin.legacy_metadata || origin.is_closed_for([module]))
        {
            // Nat is inherited, so Integers' operator list doesn't install it again.
            for builtin in self.builtins.borrow_mut().values_mut() {
                if &*builtin.name == "Nat" {
                    builtin.flags |= tla_ir::Builtin::EXTERNAL_CLASS as u32;
                }
            }
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
            if crate::startup::get_overrides()
                .any(|(module, op, _)| module == name && op == operator.name)
            {
                self.builtin_java_methods
                    .borrow_mut()
                    .insert(operator_name.clone(), Rc::from(name));
            }
            self.construct_builtin(
                operator_name.clone(),
                Builtin {
                    intrinsic: None,
                    name: operator_name.clone(),
                    arity: operator.arity,
                    flags: self.standard_builtin_flags(name, operator.name, operator.flags),
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
        self.mark_external_inherited_builtins(name);
        for (_, operator, _) in
            crate::startup::get_overrides().filter(|(module, _, _)| *module == name)
        {
            if let Some(symbol) = exported.get(operator)
                && let Some(mut builtin) = self.builtins.borrow().get(&symbol.key).cloned()
            {
                if name == "Integers" {
                    builtin.flags &=
                        !(tla_ir::Builtin::NATURALS_GEQ | tla_ir::Builtin::NATURALS_METHOD) as u32;
                }
                self.record_packaged_method(name, &symbol.key, builtin);
            }
        }
        let exported = Rc::new(exported);
        self.standard_exports
            .borrow_mut()
            .insert(Rc::from(name), exported.clone());
        self.external_module_order.borrow_mut().push(Rc::from(name));
        Some(exported)
    }

    fn get_standard_symbols(&self, name: &Name) -> Result<Option<Rc<Symbols>>> {
        // SANY reads a module from the user's directories before its standard modules.
        if is_user_replaceable(name) && (self.options.load_module)(name).is_some() {
            if REPLACEABLE_TLC_MODULES.contains(&&**name)
                && !self.user_replaced_modules.borrow().contains(name)
            {
                self.user_replaced_modules.borrow_mut().push(name.clone());
            }
            return Ok(None);
        }
        // A standard module SANY reads from TLC's jar extends a file of the user's that replaces
        // one it uses, whose definitions the operators of the standard module then use. A file
        // whose text is the jar's own module defines what the jar's does. Every operator of
        // TLC, Sequences, FiniteSets and Randomization is a Java method (`TLC.java`,
        // `TLCGetSet.java`, `TLCEval.java`, `Sequences.java`, `FiniteSets.java`,
        // `Randomization.java`), whatever the file's definitions its body would use, but
        // Randomization's TestRandomSetOfSubsets, whose body names only Java methods, which TLC
        // binds to the file's definitions by name (`processModuleOverrides`). TLC doesn't check
        // the assumptions of a module such a module's LOCAL INSTANCE alone reaches; SANY still
        // reads the file, as the front end does.
        if get_standard_modules(self.options.version)
            .iter()
            .any(|module| module.name == &**name)
            && !matches!(
                &**name,
                "TLC" | "Sequences" | "FiniteSets" | "Randomization"
            )
            && get_unbound_dependencies(name).iter().any(|dependency| {
                is_user_replaceable(dependency)
                    && (self.options.load_module)(dependency).is_some_and(|text| {
                        crate::get_standard_module(dependency, self.options.version)
                            != Some(text.as_str())
                    })
            })
        {
            return Err(FrontError::NotYet(format!(
                "a standard module that uses a module a file of the user's replaces: {name}"
            )));
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
        Ok(symbols)
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
            // TLC binds the methods of the Java class of a module its jar holds to the module's
            // definitions by name alone, without comparing arities. The front end follows the
            // binding only for the operators the standard module defines, with their arities:
            // it keys any other as a builtin of its own key, which the engine declines where it
            // evaluates it.
            if REPLACEABLE_TLC_MODULES.contains(&&**name) {
                for (_, method, _) in
                    crate::startup::get_overrides().filter(|(module, _, _)| *module == &**name)
                {
                    let spelled = match method {
                        "\\leq" => "<=",
                        "\\geq" => ">=",
                        method => method,
                    };
                    let Some(symbol) = linked
                        .visible
                        .get(method)
                        .or_else(|| linked.visible.get(spelled))
                    else {
                        continue;
                    };
                    // Integers' class holds Naturals' operators too.
                    let standard_arity = get_standard_modules(self.options.version)
                        .iter()
                        .filter(|module| {
                            module.name == &**name || get_dependencies(name).contains(&module.name)
                        })
                        .flat_map(|module| module.operators)
                        .find(|operator| operator.name == spelled || operator.name == method)
                        .map(|operator| operator.arity);
                    if symbol.kind == SymbolKind::Definition && standard_arity != Some(symbol.arity)
                    {
                        self.construct_builtin(
                            symbol.key.clone(),
                            Builtin {
                                intrinsic: None,
                                name: symbol.key.clone(),
                                arity: symbol.arity,
                                flags: tla_ir::Builtin::DECLINED as u32,
                                table: None,
                            },
                        );
                        self.definitions.borrow_mut().remove(&symbol.key);
                    }
                }
            }
            for operator in standard.operators {
                let Some(symbol) = linked.visible.get(operator.name) else {
                    continue;
                };
                if symbol.kind != SymbolKind::Definition || symbol.arity != operator.arity {
                    continue;
                }
                if crate::startup::get_overrides()
                    .any(|(module, op, _)| module == &**name && op == operator.name)
                {
                    self.builtin_java_methods
                        .borrow_mut()
                        .insert(symbol.key.clone(), name.clone());
                }
                self.construct_builtin(
                    symbol.key.clone(),
                    Builtin {
                        // The IR names the method of a module TLC's jar holds as the standard
                        // module's operator, which the engine knows.
                        intrinsic: REPLACEABLE_TLC_MODULES
                            .contains(&&**name)
                            .then_some(Intrinsic::StandardMethod),
                        name: Rc::from(operator.name),
                        arity: operator.arity,
                        flags: self.standard_builtin_flags(name, operator.name, operator.flags),
                        table: None,
                    },
                );
                if let Some(builtin) = self.builtins.borrow().get(&symbol.key).cloned() {
                    self.record_packaged_method(name, &symbol.key, builtin);
                }
                self.definitions.borrow_mut().remove(&symbol.key);
            }
        }
        if self.has_native_subset_set(name)
            && let Some(symbol) = linked.visible.get("RandomSubsetSet")
            && symbol.kind == SymbolKind::Definition
            && symbol.arity == 3
        {
            self.construct_builtin(
                symbol.key.clone(),
                Builtin {
                    name: Rc::from("RandomSubsetSet"),
                    intrinsic: None,
                    arity: 3,
                    flags: self.standard_builtin_flags(name, "RandomSubsetSet", 0),
                    table: None,
                },
            );
            self.definitions.borrow_mut().remove(&symbol.key);
        }
        if self.allow_native_aliases
            && &**name == "AnySet"
            && self
                .options
                .origin
                .is_some_and(|origin| !origin.legacy_metadata && origin.is_closed_for([&**name]))
            && self
                .options
                .load_class
                .is_none_or(|load| load(name).is_none())
            && !self
                .options
                .config
                .constants
                .iter()
                .any(|assignment| assignment.name.rsplit('!').next() == Some("ANY"))
            && !self
                .options
                .config
                .substitutions
                .iter()
                .any(|substitution| substitution.name.rsplit('!').next() == Some("ANY"))
            && linked.module.definitions.iter().any(|definition| {
                definition.name.as_ref() == "ANY"
                    && matches!(
                        definition.kind,
                        DefinitionKind::Function { .. }
                            | DefinitionKind::Operator {
                                body_range: Some(_),
                                ..
                            }
                    )
            })
            && let Some(symbol) = linked.visible.get("ANY")
            && symbol.kind == SymbolKind::Definition
            && symbol.arity == 0
        {
            self.construct_builtin(
                symbol.key.clone(),
                Builtin {
                    name: Rc::from("ANY"),
                    intrinsic: Some(Intrinsic::Any),
                    arity: 0,
                    flags: self.standard_builtin_flags(name, "ANY", 0),
                    table: None,
                },
            );
            self.definitions.borrow_mut().remove(&symbol.key);
        }
        self.mark_external_inherited_builtins(name);
        if &**name == "TransitiveClosure"
            && self
                .options
                .load_class
                .is_none_or(|load| load(name).is_none())
            && let Some(symbol) = linked.visible.get("Warshall")
            && symbol.kind == SymbolKind::Definition
            && symbol.arity == 1
        {
            self.construct_builtin(
                symbol.key.clone(),
                Builtin {
                    intrinsic: None,
                    name: Rc::from("Warshall"),
                    arity: 1,
                    flags: 0,
                    table: None,
                },
            );
            self.definitions.borrow_mut().remove(&symbol.key);
        }
        self.linked_modules
            .borrow_mut()
            .insert(name.clone(), linked.clone());
        self.external_module_order.borrow_mut().push(name.clone());
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
        let mut variables = Vec::new();
        let mut variable_locations = Vec::new();
        for variable in &parsed.variables {
            if !variables.contains(&variable.name) {
                variables.push(variable.name.clone());
                variable_locations.push(variable.location.clone());
            }
        }
        for name in &parsed.extends {
            let nested = scope.modules.get(name).cloned();
            let standard_symbols = if nested.is_some() {
                None
            } else {
                self.get_standard_symbols(name)?
            };
            if let Some(standard_symbols) = standard_symbols {
                merge_extended(&standard_symbols, &mut visible, &mut exported);
                continue;
            }
            let linked = match nested {
                Some(nested) => nested,
                None => self.get_linked_module(name, &parsed.name)?,
            };
            // A declaration an earlier extended module made of the name stays the one the root
            // module's context holds (`mergeExtendContext`), a constant or a variable alike, so
            // the later one declares nothing (`getConstantDecls`, `getVariableDecls`).
            for constant in &linked.constants {
                if constants
                    .iter()
                    .all(|existing| existing.name != constant.name)
                    && !exported.contains_key(&constant.name)
                {
                    constants.push(constant.clone());
                }
            }
            for (index, variable) in linked.variables.iter().enumerate() {
                if variables.contains(variable) || exported.contains_key(variable) {
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
        let native_subset_set = self.has_native_subset_set(&parsed.name);
        let id = scope.id.clone();
        // A file of the user's that replaces a module TLC's jar holds keys each definition TLC
        // binds to the Java method as the standard module keys its operator, so that what the
        // spec reads by the name, such as PrintT, is the builtin it is with the jar's module.
        let standard_methods: Vec<(&'static str, usize)> = if REPLACEABLE_TLC_MODULES
            .contains(&&*parsed.name)
            && is_sany_standard_module(&parsed.name, self.options.version)
        {
            get_standard_modules(self.options.version)
                .iter()
                .filter(|module| module.name == &*parsed.name)
                .flat_map(|module| module.operators)
                .map(|operator| (operator.name, operator.arity))
                .collect()
        } else {
            Vec::new()
        };
        let get_key: GetKey = Rc::new(move |definition: &Definition| -> Name {
            if is_root
                || standard_methods.contains(&(&*definition.name, get_arity(definition)))
                || (native_subset_set
                    && matches!(&*definition.name, "RandomSubsetSet" | "RandomSetOfSubsets")
                    && get_arity(definition) == 3)
            {
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
                        &imported_at,
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
                let alias = Rc::new(Definition {
                    name: name.clone(),
                    ..(*definition).clone()
                });
                self.tables
                    .set_instance_context(&alias, self.tables.instance_context(&definition));
                self.tables.set_alias_source(&alias, &definition);
                Some(alias)
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
            &imported_at,
            &facts,
            &reports,
            &scope.warnings,
            &visible_modules,
        );
        let errors = resolve_module(&module, &context)?;
        scope.errors.borrow_mut().extend(errors);
        for definition in &module.definitions {
            let key = get_key(definition);
            self.json_source_opcodes.borrow_mut().remove(&key);
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
        imported_at: &FastMap<Name, Position>,
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
                    self.get_standard_symbols(&instance.module)?
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
            imported_at: Rc::new(imported_at.clone()),
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

    /// The definition with a module-scoped entry a copy of `source` an INSTANCE in a LET makes
    /// reads, through any number of copies, and the parameters the copies add before its own.
    fn get_let_alias(&self, source: &Name, prefix: usize) -> Option<(Name, usize)> {
        if self.let_aliased_keys.is_empty() {
            return None;
        }
        get_copy_target(
            &self.copy_sources.borrow(),
            &self.let_copy_sources.borrow(),
            source,
            prefix,
            &self.let_aliased_keys,
        )
    }

    fn instantiation<'b>(
        &'b self,
        params: Vec<OperatorParam>,
        substitutions: OrderedMap<Name, Expr>,
        linked: &LinkedModule,
        add_definition: AddDefinition<'b>,
        is_named_where_used: bool,
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
                is_named_where_used,
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
            self.get_standard_symbols(&instance.module)?
        };
        if let Some(standard_symbols) = standard_symbols {
            if !instance.params.is_empty() {
                return Err(FrontError::NotYet(
                    "an INSTANCE of a standard module with parameters".to_owned(),
                ));
            }
            return Ok(get_standard_instance_symbols(instance, &standard_symbols));
        }
        if nested.is_some() {
            self.unordered_instancees
                .borrow_mut()
                .insert(instance.module.clone());
        }
        let linked = match nested {
            Some(nested) => nested,
            None => self.get_linked_module(&instance.module, &module.name)?,
        };
        // For an unnamed LOCAL INSTANCE of a module without parameters, SANY's
        // `Generator.generateInstance` makes a new OpDefNode of each definition (`if (localness)`),
        // which TLC's `processConstantDefns` computes again in the instantiating module, where an
        // unnamed INSTANCE that isn't LOCAL shares the module's own. The front end doesn't order
        // those copies, so it takes them as it takes an inner module's. `SymbolTable.addSymbol`
        // keeps a name the instantiating module already binds to a definition of the same
        // module, as an earlier EXTENDS or INSTANCE of it does, and drops the copy.
        if instance.is_local
            && instance.name.is_none()
            && linked.constants.is_empty()
            && linked.variables.is_empty()
            && linked.exported.iter().any(|(name, symbol)| {
                symbol.kind == SymbolKind::Definition && !context.imported.contains_key(name)
            })
        {
            self.unordered_instancees
                .borrow_mut()
                .insert(instance.module.clone());
        }
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
        let missing_operator_params: FastSet<Name> = substitutions
            .iter()
            .filter_map(|(name, value)| {
                let is_operator = declarations
                    .iter()
                    .any(|decl| decl.name == *name && decl.arity > 0);
                let core = value.reference().is_some_and(|target| {
                    CORE_OPERATORS
                        .iter()
                        .any(|(core, arity, _)| *arity > 0 && *core == &*target)
                });
                (is_operator && core).then(|| name.clone())
            })
            .collect();
        let has_declarations = !declarations.is_empty();
        let prefix = instance.params.len();
        let module_name = module.name.clone();
        let instance_name = instance.name.clone();
        let own_instance_context: Vec<Expr> = instance
            .substitutions
            .iter()
            .map(|s| s.expression.clone())
            .collect();
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
                // `Generator.generateInstance` gives a named INSTANCE with substitutions a
                // definition of its own for each one, with a `SubstInNode` for its body, even one
                // a module without parameters made, where the copy with no INSTANCE parameters to
                // add is the definition itself: the copy is kept apart from the definition, which
                // the module's own names reach without the `SubstInNode`.
                let definition = if has_declarations
                    && (self.definitions.borrow().get(source))
                        .is_some_and(|source| Rc::ptr_eq(source, &definition))
                {
                    Rc::new((*definition).clone())
                } else {
                    definition
                };
                let mut contexts = self
                    .definitions
                    .borrow()
                    .get(source)
                    .map(|source| self.tables.instance_context(source))
                    .unwrap_or_default();
                contexts.extend(own_instance_context.iter().cloned());
                self.tables.set_instance_context(&definition, contexts);
                if !missing_operator_params.is_empty()
                    && self.definitions.borrow().get(source).is_some_and(|source| {
                        let mut pending = vec![source.body.clone()];
                        while let Some(node) = pending.pop() {
                            if !node.resolved.is_local.get()
                                && matches!(node.kind, ExpressionKind::Apply { .. })
                                && node
                                    .reference()
                                    .is_some_and(|name| missing_operator_params.contains(&name))
                            {
                                return true;
                            }
                            // getLevelBound gives operator arguments level zero without visiting their body.
                            if !matches!(
                                node.kind,
                                ExpressionKind::Lambda { .. }
                                    | ExpressionKind::OperatorReference { .. }
                            ) {
                                pending.extend(node.children());
                            }
                        }
                        false
                    })
                {
                    self.missing_operator_bodies
                        .borrow_mut()
                        .insert(Rc::as_ptr(&definition) as usize);
                }
                if has_declarations {
                    let is_nested = (self.definitions.borrow().get(source)).is_some_and(|source| {
                        (self.substituted_definitions.borrow())
                            .contains_key(&(Rc::as_ptr(source) as usize))
                    });
                    if is_nested {
                        self.nested_substitutions
                            .borrow_mut()
                            .insert(Rc::as_ptr(&definition) as usize);
                    }
                    self.substituted_definitions
                        .borrow_mut()
                        .insert(Rc::as_ptr(&definition) as usize, definition.clone());
                }
                self.json_source_opcodes.borrow_mut().remove(&key);
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
            false,
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
        self.unordered_instancees
            .borrow_mut()
            .insert(instance.module.clone());
        let location = &instance.location;
        let standard_symbols = if nested.is_some() {
            None
        } else {
            self.get_standard_symbols(&instance.module)?
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
        let prefix = instance.params.len();
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
        // The copies that read a definition with a module-scoped entry, each with the copy of
        // the definition's own body.
        let let_aliased: Rc<RefCell<FastMap<Name, Name>>> = Rc::default();
        let aliased = let_aliased.clone();
        let instance_module = instance.module.clone();
        let copied = copies.clone();
        let local_suffix = suffix.clone();
        let instantiator = self.instantiation(
            instance.params.clone(),
            declarations
                .iter()
                .map(|declaration| {
                    let name: Name = Rc::from(format!("{}{suffix}", declaration.name));
                    // The instance's parameters the definition takes are written nowhere.
                    let unwritten = Location {
                        range: None,
                        ..location.clone()
                    };
                    let replacement = if is_parameter_dependent(declaration) {
                        let call = apply(
                            name,
                            local_arguments(&instance.params, &unwritten),
                            location,
                        );
                        call.resolved.is_local.set(true);
                        call
                    } else {
                        local_identifier(name, location)
                    };
                    (declaration.name.clone(), replacement)
                })
                .collect(),
            &linked,
            Box::new(move |source, name, create| {
                let key: Name = Rc::from(format!(
                    "{name}{KEY_SEPARATOR}{instance_module}{local_suffix}.{}",
                    copied.borrow().len()
                ));
                let definition = create(&key)?;
                let mut copy = match definition.kind {
                    DefinitionKind::Operator { .. } => Rc::new(Definition {
                        name: key.clone(),
                        ..(*definition).clone()
                    }),
                    DefinitionKind::Function { .. } => create_local_function(&definition, &key),
                };
                self.let_copy_sources
                    .borrow_mut()
                    .insert(key.clone(), (source.clone(), prefix));
                // TLC sets a module-scoped entry on the body the definition holds, which SANY's
                // copies for the LET share: the copy reads the definition the entry is set on.
                // TLC takes the entry's value from the body without a frame of its own
                // (`SymbolNodeValueLookupProvider.lookup` looks through the `SubstInNode`). The
                // copy of the body is kept for the name the INSTANCE exports where it takes no
                // arguments: `LetInNode` binds such a name to a `LazyValue` of its own body, which
                // `Context.lookup` finds first, and which reads the entry only where the body is
                // a literal (`Tool.evalImpl`'s NumeralKind, DecimalKind and StringKind).
                if let Some((target, skipped)) = self.get_let_alias(source, prefix) {
                    let is_literal =
                        (self.definitions.borrow().get(&target)).is_some_and(|target| {
                            matches!(
                                target.body.kind,
                                ExpressionKind::Number { .. }
                                    | ExpressionKind::Decimal { .. }
                                    | ExpressionKind::String { .. }
                            )
                        });
                    let own_key: Name = Rc::from(format!("{key}.own"));
                    let own = match definition.kind {
                        DefinitionKind::Operator { .. } => Rc::new(Definition {
                            name: own_key.clone(),
                            ..(*definition).clone()
                        }),
                        DefinitionKind::Function { .. } => {
                            create_local_function(&definition, &own_key)
                        }
                    };
                    if !is_literal {
                        copied.borrow_mut().push(own);
                    }
                    aliased.borrow_mut().insert(
                        key.clone(),
                        if is_literal { target.clone() } else { own_key },
                    );
                    let params = match &copy.kind {
                        DefinitionKind::Operator { params, .. } => params.clone(),
                        DefinitionKind::Function { .. } => Vec::new(),
                    };
                    copy = create_local_alias(
                        key.clone(),
                        target,
                        params.clone(),
                        params.get(skipped..).unwrap_or(&[]),
                        &Location {
                            range: None,
                            ..definition.location.clone()
                        },
                    );
                }
                // A copy of a definition an INSTANCE of the instancee with substitutions copied:
                // TLC's copy's body is that copy's `SubstInNode`, at an INSTANCE the IR doesn't
                // keep.
                if (self.definitions.borrow().get(source)).is_some_and(|source| {
                    (self.substituted_definitions.borrow())
                        .contains_key(&(Rc::as_ptr(source) as usize))
                }) {
                    let mut nested = self.nested_let_copies.borrow_mut();
                    nested.insert(key.clone());
                    if let Some(own) = aliased.borrow().get(&key) {
                        nested.insert(own.clone());
                    }
                }
                copied.borrow_mut().push(copy);
                Ok(key)
            }),
            true,
        );
        let mut aliases: Vec<Rc<Definition>> = Vec::new();
        for (name, symbol) in linked.exported.iter() {
            if declarations
                .iter()
                .any(|declaration| declaration.name == *name)
            {
                continue;
            }
            let mut key = instantiator.get_key(&symbol.key)?;
            let own_params = create_argument_params(symbol.arity);
            let own_copy = (let_aliased.borrow().get(&key).cloned())
                .filter(|_| instance.params.is_empty() && symbol.arity == 0);
            let params: Vec<OperatorParam> =
                instance.params.iter().chain(&own_params).cloned().collect();
            let is_copied = key != symbol.key;
            let forwarded = if is_copied {
                params.clone()
            } else {
                own_params
            };
            // A copy that reads a module-scoped entry's value has no `SubstInNode` TLC enters.
            let is_copied = match own_copy {
                Some(own) => {
                    key = own;
                    is_copied
                }
                None => is_copied && !let_aliased.borrow().contains_key(&key),
            };
            // `Generator.processModuleDefinition` gives the name an INSTANCE exports the body of
            // the definition it copies, in a `SubstInNode` at the INSTANCE only where the
            // INSTANCE substitutes something: `CallStackTool` puts a frame at the INSTANCE only
            // there. The name forwards to the copy with the substitutes put in, at the INSTANCE,
            // or to the definition itself, where nothing is written.
            let body_location = if is_copied {
                location.clone()
            } else {
                Location {
                    range: None,
                    ..location.clone()
                }
            };
            // The copy's parameters are the name's own, which TLC's `SubstInNode` evaluates
            // where the expression that applies the name gives them: the arguments the name
            // forwards are written nowhere, so an argument's evaluation puts no frame at the
            // INSTANCE.
            let unwritten = Location {
                range: None,
                ..location.clone()
            };
            let body = if forwarded.is_empty() {
                identifier(key, &body_location)
            } else {
                apply(key, local_arguments(&forwarded, &unwritten), &body_location)
            };
            aliases.push(Rc::new(operator_definition(
                match &instance.name {
                    None => name.clone(),
                    Some(instance_name) => Rc::from(format!("{instance_name}!{name}")),
                },
                params,
                body,
                true,
                location,
            )));
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
    create_local_alias_at(name, key, params, forwarded, location, location)
}

// `createLocalAlias` whose body is at `body_location`.
fn create_local_alias_at(
    name: Name,
    key: Name,
    params: Vec<OperatorParam>,
    forwarded: &[OperatorParam],
    location: &Location,
    body_location: &Location,
) -> Rc<Definition> {
    let body = if forwarded.is_empty() {
        identifier(key, body_location)
    } else {
        apply(
            key,
            local_arguments(forwarded, body_location),
            body_location,
        )
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
        ExpressionKind::Identifier { .. }
        | ExpressionKind::Apply { .. }
        | ExpressionKind::OperatorReference { .. }
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
    // TLC puts the operator itself in place of the declaration: what applies it is written
    // nowhere.
    let unwritten = Location {
        range: None,
        ..location.clone()
    };
    let body = apply(operator, local_arguments(&params, &unwritten), &unwritten);
    (params, body)
}

const BUILTIN_LAZY: u32 = 4;

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

fn create_linker<'a>(
    options: &'a EnvironmentOptions<'a>,
    root: &Rc<Module>,
    allow_native_aliases: bool,
) -> Linker<'a> {
    Linker {
        allow_native_aliases,
        options,
        root: root.clone(),
        texts: RefCell::new(
            [(options.source.to_owned(), root.clone())]
                .into_iter()
                .collect(),
        ),
        definitions: RefCell::default(),
        builtin_java_methods: RefCell::default(),
        builtins: RefCell::new(
            CORE_OPERATORS
                .iter()
                .map(|(name, arity, flags)| {
                    let name: Name = Rc::from(*name);
                    let flags = *flags
                        | if options.origin.is_some_and(|origin| {
                            origin.legacy_metadata || origin.is_closed_for(["Strings"])
                        }) {
                            0
                        } else {
                            tla_ir::Builtin::EXTERNAL_CLASS as u32
                        };
                    (
                        name.clone(),
                        Builtin {
                            intrinsic: None,
                            name,
                            arity: *arity,
                            flags,
                            table: None,
                        },
                    )
                })
                .collect(),
        ),
        standard_exports: RefCell::default(),
        user_replaced_modules: RefCell::default(),
        packaged_methods: RefCell::default(),
        json_source_opcodes: RefCell::default(),
        linked_modules: RefCell::default(),
        nested_modules: RefCell::default(),
        link_order: RefCell::default(),
        external_module_order: RefCell::default(),
        java_overrides: RefCell::default(),
        dependencies: RefCell::default(),
        loading: RefCell::default(),
        linking: RefCell::default(),
        warnings: Rc::default(),
        copy_count: Cell::new(0),
        parameterized: RefCell::default(),
        substituted_definitions: RefCell::default(),
        nested_substitutions: RefCell::default(),
        nested_let_copies: RefCell::default(),
        copy_sources: RefCell::default(),
        missing_operator_bodies: RefCell::default(),
        tables: Rc::default(),
        instance_checks: RefCell::default(),
        checked_modules: RefCell::default(),
        qualified_names: RefCell::default(),
        instance_actions: RefCell::default(),
        instance_names: RefCell::default(),
        unordered_instancees: RefCell::default(),
        let_copy_sources: RefCell::default(),
        let_aliased_keys: FastSet::default(),
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
    let linker = create_linker(options, &root, true);
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
    create_checked_environment(options, true)
}

pub(crate) fn create_environment_without_native_aliases(
    options: &EnvironmentOptions,
) -> Result<Environment> {
    create_checked_environment(options, false)
}

// Links the spec, and again where TLC fails to compute a substitution's target with a
// module-scoped value as it starts.
fn create_checked_environment(
    options: &EnvironmentOptions,
    allow_native_aliases: bool,
) -> Result<Environment> {
    let environment =
        link_environment_with_aliases(options, allow_native_aliases, &TargetFacts::default())?;
    let failed = check_constant_substitutes(&environment, options.version)?;
    if failed.is_empty() {
        return Ok(environment);
    }
    let environment = link_environment_with_aliases(options, allow_native_aliases, &failed)?;
    if !check_constant_substitutes(&environment, options.version)?.is_empty() {
        return Err(FrontError::NotYet(
            "a substitution whose target has a module-scoped value the spec reads otherwise"
                .to_owned(),
        ));
    }
    Ok(environment)
}

/// The modules whose Java class TLC counts as its own (`BuiltInModuleHelper.isBuiltInModule`).
const BUILT_IN_CLASSES: [&str; 15] = [
    "AnySet",
    "Bags",
    "FiniteSets",
    "Integers",
    "Naturals",
    "Sequences",
    "Strings",
    "TLC",
    "TransitiveClosure",
    "Randomization",
    "Json",
    "TLCExt",
    "TLCGetSet",
    "TLCEval",
    "_Possible",
];

/// TLC loads its own Java class named after each module of the spec, wherever the module's text
/// comes from, and runs each method of it in place of the operator of the module spelled the same,
/// whatever its arity (`processModuleOverrides`): a module of the user's named TransitiveClosure
/// computes Warshall in Java, not by its body. The front end gives an imported module named like a
/// standard module the builtins of that module of the same names and arities
/// (`get_linked_module`), and reads any other operator by its body, so a spec that names one the
/// class replaces declines.
fn reject_class_overrides(
    environment: &Environment,
    root: &Module,
    config: &ModelConfig,
    version: TlcVersion,
) -> Result<()> {
    let mut replaced: Vec<(Rc<str>, Name, Option<Position>)> = Vec::new();
    for module in &environment.modules {
        if !BUILT_IN_CLASSES.contains(&&*module.name) {
            continue;
        }
        let standard = (module.name != root.name && is_sany_standard_module(&module.name, version))
            .then(|| {
                get_standard_modules(version)
                    .iter()
                    .find(|standard| standard.name == &*module.name)
            })
            .flatten();
        for definition in &module.definitions {
            let is_replaced = crate::startup::get_overrides().any(|(class, operator, _)| {
                class == &*module.name && operator == &*definition.name
            });
            let arity = match &definition.kind {
                DefinitionKind::Operator { params, .. } => params.len(),
                DefinitionKind::Function { .. } => 0,
            };
            let is_builtin = (module.name != root.name
                && &*module.name == "Randomization"
                && &*definition.name == "RandomSubsetSet"
                && arity == 3
                && environment
                    .builtins
                    .values()
                    .any(|builtin| &*builtin.name == "RandomSubsetSet"))
                || standard.is_some_and(|standard| {
                    standard.operators.iter().any(|operator| {
                        operator.name == &*definition.name && operator.arity == arity
                    })
                });
            if is_replaced && !is_builtin {
                replaced.push((
                    module.name.clone(),
                    definition.name.clone(),
                    definition.location.range.as_ref().map(|range| range.start),
                ));
            }
        }
    }
    if replaced.is_empty() {
        return Ok(());
    }
    // The keys of the replaced definitions, and of their copies an INSTANCE makes, which keep the
    // definition's place in its module.
    let is_replaced = |definition: &Definition| {
        replaced.iter().any(|(module, name, start)| {
            definition.name == *name
                && definition
                    .location
                    .range
                    .as_ref()
                    .is_some_and(|range| range.module == *module && Some(range.start) == *start)
        })
    };
    let keys: FastSet<Name> = environment
        .definitions
        .iter()
        .filter(|(_, definition)| is_replaced(definition))
        .map(|(key, _)| key.clone())
        .collect();
    let named = get_named_definition(environment, config, &keys);
    match named.and_then(|key| environment.definitions.get(&key)) {
        Some(definition) => Err(FrontError::NotYet(format!(
            "an operator of a module of the user's that TLC's Java class replaces: {}!{}",
            definition
                .location
                .range
                .as_ref()
                .map_or("", |range| &*range.module),
            definition.name
        ))),
        None => Ok(()),
    }
}

/// The operators a `tlc2.overrides.TLCOverrides` index replaces (`decline_index_overrides`): the
/// builtins by key, and the definitions that became declined builtins, each with the name TLC
/// gives it and whether its method is quiet (`IndexTarget::is_quiet`).
#[derive(Default)]
struct IndexReplaced {
    builtins: FastMap<Name, (String, bool)>,
    definitions: FastMap<Name, (String, bool)>,
    /// The builtins a global value or a substitute replaces in the root module, which only an
    /// INSTANCE's copy reads as the method.
    global: FastMap<Name, (String, bool)>,
}

/// `processModuleOverrides` also puts the methods a `tlc2.overrides.TLCOverrides` index lists in
/// place of the bodies of the operators they name (`get_index_targets`), which the front end and
/// the engine compute by their bodies. TLC finds the operator by `ModuleNode.getOpDef`, which
/// searches every definition of the module's context: its own, its LOCAL ones, and those EXTENDS,
/// INSTANCE and LOCAL INSTANCE bring in, by the name SANY gives it, such as `\leq` for `<=`;
/// SANY gives no operator a synonym's other spelling, which replaces nothing. An EXTENDS shares
/// the definition's node, and an INSTANCE's copy shares its body, or wraps it in a `SubstInNode`
/// that `lookup` looks through, so the method replaces the definition in the module that wrote
/// it and every copy of it. A definition of that name and arity in that module, or in any copy an
/// INSTANCE makes of it, becomes a declined builtin, which declines where the model evaluates
/// it. The builtin a standard module's operator is, which the engine computes whatever its
/// flags, is returned, for a spec that may evaluate it to decline (`reject_index_builtins`). A
/// module SANY didn't load has none, and TLC skips an `@TLAPlusOperator` method whose arity
/// differs. A replacement TLC calls, or fails on, as it starts declines the spec, as does one an
/// INSTANCE names (`I!Op`), whose copies the front end doesn't resolve.
fn decline_index_overrides(
    linker: &Linker,
    config: &ModelConfig,
    definitions: &mut OrderedMap<Name, Rc<Definition>>,
    load_class: &ClassLoader,
    root: &Module,
    root_visible: &Symbols,
) -> Result<IndexReplaced> {
    let mut replaced_index = IndexReplaced::default();
    for target in crate::java_overrides::get_index_targets(load_class)? {
        let is_arity = |arity: usize| target.arity.is_none_or(|target| target == arity);
        let label = format!("{}!{}", target.module, target.identifier);
        // The spellings of the name SANY gives the operator, where the identifier is that name.
        let synonyms: Vec<&str> = match crate::tlc_data::SANY_OPERATOR_SYNONYMS
            .iter()
            .find(|group| group.contains(&target.identifier.as_str()))
        {
            Some(group) if group[0] != target.identifier => continue,
            Some(group) => group.to_vec(),
            None => vec![target.identifier.as_str()],
        };
        let module: Name = Rc::from(target.module.as_str());
        let linked = linker.linked_modules.borrow().get(&module).cloned();
        // The module's context: the root's or a user module's scope, or a standard module's
        // operators with those of the modules it extends or instantiates.
        let symbol = if *root.name == *target.module {
            synonyms
                .iter()
                .find_map(|name| root_visible.get(*name).cloned())
        } else if let Some(linked) = linked {
            synonyms
                .iter()
                .find_map(|name| linked.visible.get(*name).cloned())
        } else if linker.standard_exports.borrow().contains_key(&module) {
            [target.module.as_str()]
                .into_iter()
                .chain(get_dependencies(&target.module).iter().copied())
                .filter_map(|name| linker.standard_exports.borrow().get(name).cloned())
                .find_map(|symbols| synonyms.iter().find_map(|name| symbols.get(*name).cloned()))
        } else if linker.nested_modules.borrow().contains_key(&module) {
            return Err(FrontError::NotYet(format!(
                "an inner module's operator a TLCOverrides index's Java method replaces: {label}"
            )));
        } else {
            continue;
        };
        if target.identifier.contains('!') {
            return Err(FrontError::NotYet(format!(
                "an INSTANCE's operator a TLCOverrides index's Java method replaces: {label}"
            )));
        }
        let Some(symbol) = symbol.filter(|symbol| {
            matches!(symbol.kind, SymbolKind::Definition | SymbolKind::Builtin)
                && is_arity(symbol.arity)
        }) else {
            continue;
        };
        // The definition the name resolves to, by the module that wrote it.
        let resolved = definitions.get(&symbol.key).cloned();
        let builtin = if resolved.is_some() {
            None
        } else {
            linker.builtins.borrow().get(&symbol.key).cloned()
        };
        let builtins: Vec<Name> = match &builtin {
            // SANY's own operators, such as `\in`, aren't definitions `getOpDefs` lists.
            Some(builtin)
                if CORE_OPERATORS
                    .iter()
                    .any(|(name, _, _)| *name == &*builtin.name) =>
            {
                continue;
            }
            // Every builtin of the operator's name and arity, as Integers' `+` is Naturals'.
            Some(builtin) => linker
                .builtins
                .borrow()
                .iter()
                .filter(|(_, other)| other.name == builtin.name && other.arity == builtin.arity)
                .map(|(key, _)| key.clone())
                .collect(),
            None => Vec::new(),
        };
        let replaced: Vec<(Name, usize)> = match &resolved {
            Some(resolved) => {
                let written = resolved
                    .location
                    .range
                    .as_ref()
                    .map(|range| range.module.clone());
                definitions
                    .iter()
                    .filter_map(|(key, definition)| {
                        let arity = match &definition.kind {
                            DefinitionKind::Operator { params, .. } => params.len(),
                            DefinitionKind::Function { .. } => 0,
                        };
                        (*definition.name == *resolved.name
                            && is_arity(arity)
                            && written.is_some()
                            && definition
                                .location
                                .range
                                .as_ref()
                                .map(|range| &range.module)
                                == written.as_ref())
                        .then(|| (key.clone(), arity))
                    })
                    .collect()
            }
            None => Vec::new(),
        };
        if resolved.is_none() && builtins.is_empty() {
            return Err(FrontError::NotYet(format!(
                "an operator a TLCOverrides index's Java method replaces that the front end doesn't resolve: {label}"
            )));
        }
        // `EvaluatingValue` fails as TLC starts on an operator that isn't user-defined.
        let is_lazy = target.is_lazy && (target.arity.is_some() || builtins.is_empty());
        if !is_lazy {
            return Err(FrontError::NotYet(format!(
                "a TLCOverrides index's Java method TLC calls as it starts, or can't call: {label}"
            )));
        }
        // TLC keeps the method over a value the configuration assigns the operator in a module
        // (`Any = [TLC] {2}` reads the method's 7), where a global value or a substitute replaces
        // it. A name the configuration gives is TLC's `defns` entry, which holds the method,
        // where the front end reads the definition's body.
        let names: Vec<&str> = synonyms
            .iter()
            .copied()
            .chain([&*symbol.key])
            .chain(resolved.as_ref().map(|resolved| &*resolved.name))
            .collect();
        let is_configured = config.constants.iter().any(|assignment| {
            assignment.module.is_some() && names.contains(&assignment.name.as_str())
        }) || [
            &config.init,
            &config.next,
            &config.specification,
            &config.symmetry,
            &config.view,
            &config.alias,
            &config.periodic,
            &config.rl_reward,
        ]
        .into_iter()
        .flatten()
        .chain(
            [
                &config.invariants,
                &config.properties,
                &config.constraints,
                &config.action_constraints,
                &config.postconditions,
                &config.possible,
            ]
            .into_iter()
            .flatten(),
        )
        .chain(
            config
                .substitutions
                .iter()
                .map(|substitution| &substitution.target),
        )
        .any(|name| names.contains(&name.as_str()) || *name == target.identifier);
        if is_configured {
            return Err(FrontError::NotYet(format!(
                "an operator a TLCOverrides index's Java method replaces that the configuration names: {label}"
            )));
        }
        // A global value or a substitute of the name the root module sees replaces the method
        // of a builtin as it does a definition's (`Any = {2}` reads {2}): `processSpec` gives
        // the value to the root's OpDefNode, which `lookup` reads before the body that holds
        // the method. The front end reads the value in place of the builtin too, but for every
        // copy of it, where an INSTANCE's copy is another node, whose body still holds the
        // method (`reject_index_builtins`). Only TLC's: no standard module's copy of TLC's
        // operators reads its operators without arguments (`Any`, `JavaTime`), where another
        // standard module's copy of, say, Naturals' may read the method.
        let is_replaced = target.module == "TLC"
            && synonyms.iter().any(|name| {
                root_visible
                    .get(*name)
                    .is_some_and(|visible| visible.key == symbol.key)
                    && (config.constants.iter().any(|assignment| {
                        assignment.module.is_none()
                            && assignment.args.is_none()
                            && assignment.name == *name
                    }) || config
                        .substitutions
                        .iter()
                        .any(|substitution| substitution.name == *name))
            });
        for key in builtins {
            if is_replaced {
                replaced_index
                    .global
                    .insert(key, (label.clone(), target.is_quiet));
                continue;
            }
            replaced_index
                .builtins
                .insert(key, (label.clone(), target.is_quiet));
        }
        for (key, arity) in replaced {
            definitions.remove(&key);
            replaced_index
                .definitions
                .insert(key.clone(), (label.clone(), target.is_quiet));
            linker.construct_builtin(
                key.clone(),
                Builtin {
                    intrinsic: None,
                    name: key,
                    arity,
                    flags: (tla_ir::Builtin::DECLINED | tla_ir::Builtin::INDEX_REPLACED) as u32,
                    table: None,
                },
            );
        }
    }
    Ok(replaced_index)
}

/// Declines a spec that may evaluate a builtin a TLCOverrides index replaces
/// (`decline_index_overrides`), by the names what TLC evaluates reaches (`get_reached_key`), and
/// one where a definition TLC computes as it starts (`get_startup_model`) may call a replacement
/// that isn't quiet, whose print or exit then shows: TLC drops the value, or the exception, of
/// a definition no part of the model reads, and computes the replacement of a builtin wherever
/// the model reads it.
fn reject_index_builtins(
    environment: &Environment,
    config: &ModelConfig,
    replaced: &IndexReplaced,
) -> Result<()> {
    // An INSTANCE of TLC, of a module's or a LET's, copies a builtin the configuration replaces
    // in the root module: TLC's copy is another OpDefNode, which reads the method. An INSTANCE
    // of another module, even one that extends TLC, reads the node the root module's names
    // read, which holds the value. A module's named INSTANCE's copy is read only by a name
    // written with its prefix (`I!Any`); an unnamed one's, by any name in its module.
    let expressions: Vec<Expr> = environment
        .definitions
        .values()
        .chain(&environment.startup_definitions)
        .flat_map(get_definition_expressions)
        .chain(
            environment
                .assumptions
                .iter()
                .map(|assumption| assumption.expression.clone()),
        )
        .collect();
    let is_unnamed_instanced = environment.modules.iter().any(|module| {
        module
            .instances
            .iter()
            .any(|instance| is_tlc_instance(instance) && instance.name.is_none())
    });
    let is_named_instanced = environment.modules.iter().any(|module| {
        module
            .instances
            .iter()
            .any(|instance| is_tlc_instance(instance))
    });
    // A LET's copy, whose names the front end resolves within the LET, declines wherever it is.
    let is_instanced = is_unnamed_instanced
        || expressions.iter().any(has_any_let_instance)
        || is_named_instanced
            && expressions
                .iter()
                .any(|expression| writes_prefixed(expression, &replaced.global));
    let mut owned = IndexReplaced {
        builtins: replaced.builtins.clone(),
        definitions: replaced.definitions.clone(),
        global: FastMap::default(),
    };
    if is_instanced {
        owned.builtins.extend(replaced.global.clone());
    }
    let replaced = &owned;
    let keys: FastSet<Name> = replaced.builtins.keys().cloned().collect();
    if let Some(key) = get_reached_key(
        environment,
        Some(config),
        &keys,
        Roots::Evaluated { is_startup: false },
    ) {
        return Err(FrontError::NotYet(format!(
            "an operator a TLCOverrides index's Java class replaces: {}",
            replaced
                .builtins
                .get(&key)
                .map_or(&*key, |(label, _)| label)
        )));
    }
    let loud: FastSet<Name> = replaced
        .builtins
        .iter()
        .chain(replaced.definitions.iter())
        .filter(|(_, (_, is_quiet))| !is_quiet)
        .map(|(key, _)| key.clone())
        .collect();
    if loud.is_empty() {
        return Ok(());
    }
    let startup = crate::startup::get_startup_model(environment);
    let roots = startup
        .attempted
        .iter()
        .map(|(definition, _)| definition.body.clone())
        .collect();
    match get_reached_key(environment, None, &loud, Roots::Expressions(roots)) {
        Some(key) => Err(FrontError::NotYet(format!(
            "a TLCOverrides index's Java method that a definition TLC computes as it starts may call: {}",
            replaced
                .builtins
                .get(&key)
                .or_else(|| replaced.definitions.get(&key))
                .map_or(&*key, |(label, _)| label)
        ))),
        None => Ok(()),
    }
}

/// A name the configuration selects, or substitutes for another, whose body a module-scoped
/// substitution replaces (`body_evaluated`, with whether the body is one the front end can read
/// unsubstituted): TLC evaluates the definition's own body there (`def.getBody()`), where a
/// reference to the definition reads the substitute (`lookup`). Where nothing TLC evaluates but
/// the selection names the definition, the front end drops the substitution, so the selection
/// reads the body as TLC does, which `processConstantDefns` doesn't compute; it declines where both are read, where TLC substitutes the
/// definition for another name (whose `evalAppl` evaluates the body), and where TLC fails to
/// cast a literal body's substitute.
fn check_body_evaluated_keys(
    environment: &mut Environment,
    config: &ModelConfig,
    body_evaluated: &FastMap<Name, (bool, Name)>,
) -> Result<()> {
    if body_evaluated.is_empty() {
        return Ok(());
    }
    let root_key = |environment: &Environment, name: &str| -> Name {
        environment
            .root_symbols
            .get(name)
            .map_or_else(|| Rc::from(name), |symbol| symbol.key.clone())
    };
    let decline = |name: &str| {
        Err(FrontError::NotYet(format!(
            "a definition the configuration names whose body a module-scoped substitution replaces: {name}"
        )))
    };
    // A module-scoped substitution whose name the configuration also sets for every module
    // (`K = 7` or `K <- B`) is shadowed by that setting, as the `scoped-config-global-lhs-*`
    // startup fixtures record: TLC substitutes nothing for its name there.
    let is_shadowed =
        |substitution: &crate::config::Substitution| {
            substitution.module.is_some()
                && (config.constants.iter().any(|constant| {
                    constant.module.is_none() && constant.name == substitution.name
                }) || config
                    .substitutions
                    .iter()
                    .any(|other| other.module.is_none() && other.name == substitution.name))
        };
    for substitution in &config.substitutions {
        if !is_shadowed(substitution)
            && body_evaluated.contains_key(&root_key(environment, &substitution.target))
        {
            return decline(&substitution.target);
        }
    }
    // The names the configuration names other than as the target of a shadowed substitution.
    let mut shadowed_targets: FastMap<&str, usize> = FastMap::default();
    for substitution in config.substitutions.iter().filter(|s| is_shadowed(s)) {
        *shadowed_targets
            .entry(substitution.target.as_str())
            .or_default() += 1;
    }
    let mut selected: Vec<(&str, Name)> = Vec::new();
    for name in get_configured_names(config) {
        if let Some(count) = shadowed_targets.get_mut(name)
            && *count > 0
        {
            *count -= 1;
            continue;
        }
        let key = root_key(environment, name);
        match body_evaluated.get(&key) {
            None => {}
            Some((false, _)) => return decline(name),
            Some((true, _)) => selected.push((name, key)),
        }
    }
    if selected.is_empty() {
        return Ok(());
    }
    // What TLC evaluates but the selections: every assumption and INSTANCE substitution, the
    // bodies of what the configuration names, and every definition without parameters of
    // constant level but K, which `processConstantDefns` computes as it starts.
    let mut unselected = ModelConfig {
        substitutions: config.substitutions.clone(),
        constants: config.constants.clone(),
        ..ModelConfig::default()
    };
    unselected.check_deadlock = config.check_deadlock;
    let bodies: Vec<Expr> = get_configured_names(config)
        .flat_map(|name| {
            let key = root_key(environment, name);
            [
                environment.definitions.get(&key).cloned(),
                crate::spec::get_definition(name, environment).cloned(),
            ]
        })
        .flatten()
        .flat_map(|definition| {
            let bounds = match &definition.kind {
                DefinitionKind::Function { bounds } => bounds.as_slice(),
                DefinitionKind::Operator { .. } => &[],
            };
            bounds
                .iter()
                .map(|bound| bound.set.clone())
                .chain([definition.body.clone()])
                .collect::<Vec<Expr>>()
        })
        .collect();
    // `processModelConstraints` and `processActionConstraints`, the last steps of
    // `processConfig`, set a (ACTION_)CONSTRAINT's own node on its body (`body.setToolObject(
    // toolId, def)`) in place of the substitute, so every reference TLC evaluates after that
    // finds K's node and evaluates K's own body, as the selection does. What reads the
    // substitute before is `processConstantDefns`, through `lookup` and `getLevelBound` (a
    // definition of constant level with the substitute's level that names K, and K itself), and
    // `processConfigSpec`, which walks a SPECIFICATION's or a PROPERTY's references by `lookup`.
    // Where K is of a level above constant (which `processConstantDefns` doesn't compute as K's
    // own body), no other definition TLC computes as it starts names K, the substitute has no
    // effect TLC would show computing it there, and the configuration has no SPECIFICATION or
    // PROPERTY, every reference reads K's body. A K nothing else reads is a selection as any
    // other.
    let constrained: FastSet<Name> = {
        let analyzer = environment.create_unsubstituted_level_analyzer();
        selected
            .iter()
            .filter(|(name, _)| {
                config.constraints.iter().any(|selected| selected == name)
                    || config
                        .action_constraints
                        .iter()
                        .any(|selected| selected == name)
            })
            .filter(|(_, key)| {
                let single: FastSet<Name> = [key.clone()].into_iter().collect();
                get_reached_key(
                    environment,
                    Some(&unselected),
                    &single,
                    Roots::Evaluated { is_startup: false },
                )
                .or_else(|| {
                    get_reached_key(
                        environment,
                        None,
                        &single,
                        Roots::Expressions(bodies.clone()),
                    )
                })
                .is_some()
            })
            .filter(|(_, key)| {
                environment.definitions.get(key).is_some_and(|definition| {
                    analyzer
                        .analyze_definition(definition, &crate::levels::Scope::default())
                        .is_ok_and(|levels| levels.data.level > crate::levels::CONSTANT_LEVEL)
                })
            })
            .map(|(_, key)| key.clone())
            .collect()
    };
    let keys: FastSet<Name> = selected
        .iter()
        .map(|(_, key)| key.clone())
        .filter(|key| !constrained.contains(key))
        .collect();
    let analyzer = environment.create_unsubstituted_level_analyzer();
    let startup: Vec<(Name, Expr)> = environment
        .definitions
        .iter()
        .filter(|(key, definition)| {
            !keys.contains(*key)
                && matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && analyzer
                    .analyze_definition(definition, &crate::levels::Scope::default())
                    .map_or(true, |levels| levels.data.level == crate::levels::CONSTANT_LEVEL)
        })
        .map(|(key, definition)| (key.clone(), definition.body.clone()))
        .collect();
    // Whether a substitute is of constant level, which a definition TLC computes as it starts
    // that names K then reads at once, where the front end would read K's own body.
    let has_constant_substitute = selected.iter().any(|(_, key)| {
        body_evaluated
            .get(key)
            .and_then(|(_, target)| environment.definitions.get(target))
            .is_some_and(|definition| {
                analyzer
                    .analyze_definition(definition, &crate::levels::Scope::default())
                    .map_or(true, |levels| {
                        levels.data.level == crate::levels::CONSTANT_LEVEL
                    })
            })
    });
    drop(analyzer);
    if !constrained.is_empty() {
        let effects: FastSet<Name> = crate::lower::STARTUP_VALUE_EFFECTS
            .iter()
            .map(|name| Rc::from(*name))
            .collect();
        let substitutes: Vec<Expr> = selected
            .iter()
            .filter(|(_, key)| constrained.contains(key))
            .filter_map(|(_, key)| body_evaluated.get(key))
            .filter_map(|(_, target)| environment.definitions.get(target))
            .map(|definition| definition.body.clone())
            .collect();
        let is_walked = config.specification.is_some() || !config.properties.is_empty();
        // The definitions TLC computes as it starts that name K, each of which caches what it
        // read of the substitute: that shows where anything reads one, or where one has an
        // effect.
        let early: Vec<(Name, Expr)> = startup
            .iter()
            .filter(|(_, body)| {
                get_reached_key(
                    environment,
                    None,
                    &constrained,
                    Roots::Expressions(vec![body.clone()]),
                )
                .is_some()
            })
            .cloned()
            .collect();
        let early_keys: FastSet<Name> = early.iter().map(|(key, _)| key.clone()).collect();
        let is_early_shown = !early.is_empty()
            && (get_reached_key(
                environment,
                Some(config),
                &early_keys,
                Roots::Evaluated { is_startup: false },
            )
            .is_some()
                || get_reached_key(
                    environment,
                    None,
                    &effects,
                    Roots::Expressions(early.into_iter().map(|(_, body)| body).collect()),
                )
                .is_some());
        let is_substitute_shown =
            get_reached_key(environment, None, &effects, Roots::Expressions(substitutes)).is_some();
        let reached = (is_walked || is_early_shown || is_substitute_shown)
            .then(|| constrained.iter().next().cloned())
            .flatten();
        if let Some(key) = reached {
            let name = selected
                .iter()
                .find(|(_, selected)| *selected == key)
                .map_or(&*key, |(name, _)| *name);
            return decline(name);
        }
    }
    if let Some(key) = get_reached_key(
        environment,
        Some(&unselected),
        &keys,
        Roots::Evaluated { is_startup: false },
    )
    .or_else(|| get_reached_key(environment, None, &keys, Roots::Expressions(bodies)))
    .or_else(|| {
        // A definition TLC computes as it starts, but nothing reads, that names K computes the
        // substitute there (`getLevelBound` and `lookup` follow it), which shows only where the
        // substitute or K's own body the front end would then compute has an effect, or, where
        // the substitute is of constant level, that definition (`R == PrintT(K)`, which TLC
        // prints as it starts with the substitute's value, or doesn't where computing the
        // substitute fails, whatever K's body gives).
        let effects: FastSet<Name> = crate::lower::STARTUP_VALUE_EFFECTS
            .iter()
            .map(|name| Rc::from(*name))
            .collect();
        let early: Vec<Expr> = startup
            .into_iter()
            .map(|(_, body)| body)
            .filter(|body| {
                get_reached_key(
                    environment,
                    None,
                    &keys,
                    Roots::Expressions(vec![body.clone()]),
                )
                .is_some()
            })
            .collect();
        let mut bodies: Vec<Expr> = selected
            .iter()
            .flat_map(|(_, key)| {
                [
                    environment.definitions.get(key).cloned(),
                    body_evaluated
                        .get(key)
                        .and_then(|(_, target)| environment.definitions.get(target).cloned()),
                ]
            })
            .flatten()
            .map(|definition| definition.body.clone())
            .collect();
        if has_constant_substitute {
            bodies.extend(early.iter().cloned());
        }
        get_reached_key(environment, None, &effects, Roots::Expressions(bodies))?;
        get_reached_key(environment, None, &keys, Roots::Expressions(early))
    }) {
        let name = selected
            .iter()
            .find(|(_, selected)| *selected == key)
            .map_or(&*key, |(name, _)| *name);
        return decline(name);
    }
    // `processConstantDefns` computes the substitute in place of K (`lookup`), so `defns`
    // keeps K's node, as for a module-scoped value of a definition the configuration selects
    // (`check_scoped_selection`).
    for (_, key) in selected {
        environment.substitutions.remove(&key);
        environment.constants.remove(&key);
        environment
            .scoped_selected_values
            .entry(key)
            .or_insert(ConfigValue::Boolean(true));
    }
    Ok(())
}

/// The names the configuration selects, and those it substitutes for others.
fn get_configured_names(config: &ModelConfig) -> impl Iterator<Item = &str> {
    [
        &config.init,
        &config.next,
        &config.specification,
        &config.symmetry,
        &config.view,
        &config.alias,
        &config.periodic,
        &config.rl_reward,
    ]
    .into_iter()
    .flatten()
    .chain(
        [
            &config.invariants,
            &config.properties,
            &config.constraints,
            &config.action_constraints,
            &config.postconditions,
            &config.possible,
        ]
        .into_iter()
        .flatten(),
    )
    .chain(
        config
            .substitutions
            .iter()
            .map(|substitution| &substitution.target),
    )
    .map(String::as_str)
}

/// Whether an expression names one of the keys by a name written with an INSTANCE's prefix.
fn writes_prefixed(expression: &Expr, keys: &FastMap<Name, (String, bool)>) -> bool {
    let written = match &expression.kind {
        ExpressionKind::Identifier { name, .. } => Some(name),
        ExpressionKind::Apply { operator, .. }
        | ExpressionKind::OperatorReference { operator, .. } => Some(operator),
        _ => None,
    };
    written.is_some_and(|written| written.contains('!'))
        && !expression.is_locally_resolved()
        && expression
            .reference()
            .is_some_and(|key| keys.contains_key(&key))
        || expression
            .children()
            .iter()
            .any(|child| writes_prefixed(child, keys))
}

/// Whether an INSTANCE is of TLC.
fn is_tlc_instance(instance: &Instance) -> bool {
    &*instance.module == "TLC"
}

/// Whether an expression holds a LET with an INSTANCE of TLC.
fn has_any_let_instance(expression: &Expr) -> bool {
    matches!(
        &expression.kind,
        ExpressionKind::Let {
            instances: Some(instances),
            ..
        } if instances.iter().any(|instance| is_tlc_instance(instance))
    ) || expression.children().iter().any(has_any_let_instance)
}

/// The first of the keys that TLC may evaluate a name of, by the definition the name resolves to:
/// one named in what TLC evaluates, from every definition without parameters (which TLC may
/// compute as it starts), every assumption, every INSTANCE's substitutions and every name the
/// configuration gives, through the bodies of the definitions those name. A definition with
/// parameters that nothing reached applies is never evaluated, nor is a replaced definition's
/// own body, which is the class's method in TLC.
fn get_named_definition(
    environment: &Environment,
    config: &ModelConfig,
    keys: &FastSet<Name>,
) -> Option<Name> {
    get_reached_key(
        environment,
        Some(config),
        keys,
        Roots::Evaluated { is_startup: true },
    )
}

/// Where `get_reached_key` starts: what TLC evaluates, with or without every definition without
/// parameters, or only the given expressions.
enum Roots {
    Evaluated { is_startup: bool },
    Expressions(Vec<Expr>),
}

fn get_reached_key(
    environment: &Environment,
    config: Option<&ModelConfig>,
    keys: &FastSet<Name>,
    roots: Roots,
) -> Option<Name> {
    // The text of every name an expression writes, which a LET definition is named by.
    fn written(expression: &Expr, texts: &mut FastSet<Name>) {
        match &expression.kind {
            ExpressionKind::Identifier { name, .. } => {
                texts.insert(name.clone());
            }
            ExpressionKind::Apply { operator, .. }
            | ExpressionKind::OperatorReference { operator, .. } => {
                texts.insert(operator.clone());
            }
            _ => {}
        }
        for child in &expression.children() {
            written(child, texts);
        }
    }
    fn names(expression: &Expr, found: &mut Vec<Name>) {
        // TLC evaluates a LET definition only where what it evaluates names it.
        if let ExpressionKind::Let {
            definitions,
            instances: None,
            body,
            ..
        } = &expression.kind
        {
            let mut texts = FastSet::default();
            names(body, found);
            written(body, &mut texts);
            let mut included = vec![false; definitions.len()];
            loop {
                let mut is_grown = false;
                for (index, definition) in definitions.iter().enumerate() {
                    if !included[index] && texts.contains(&definition.name) {
                        included[index] = true;
                        is_grown = true;
                        names(&definition.body, found);
                        written(&definition.body, &mut texts);
                    }
                }
                if !is_grown {
                    return;
                }
            }
        }
        if !expression.is_locally_resolved()
            && matches!(
                expression.kind,
                ExpressionKind::Identifier { .. }
                    | ExpressionKind::Apply { .. }
                    | ExpressionKind::OperatorReference { .. }
            )
            && let Some(key) = expression.reference()
        {
            found.push(key);
        }
        for child in &expression.children() {
            names(child, found);
        }
    }
    let is_parameterless = |definition: &Definition| match &definition.kind {
        DefinitionKind::Operator { params, .. } => params.is_empty(),
        DefinitionKind::Function { .. } => true,
    };
    let is_replaced = |definition: &Definition| {
        keys.iter().any(|key| {
            environment
                .definitions
                .get(key)
                .is_some_and(|replaced| std::ptr::eq(&**replaced, definition))
        })
    };
    let (mut pending, is_startup) = match roots {
        Roots::Evaluated { is_startup } => (Vec::new(), is_startup),
        Roots::Expressions(expressions) => (expressions, false),
    };
    let is_evaluated = config.is_some();
    for module in environment.modules.iter().filter(|_| is_evaluated) {
        pending.extend(
            module
                .definitions
                .iter()
                .filter(|definition| {
                    is_startup && is_parameterless(definition) && !is_replaced(definition)
                })
                .map(|definition| definition.body.clone()),
        );
        pending.extend(
            module
                .assumptions
                .iter()
                .map(|assumption| assumption.expression.clone()),
        );
        pending.extend(module.instances.iter().flat_map(|instance| {
            instance
                .substitutions
                .iter()
                .map(|substitution| substitution.expression.clone())
        }));
    }
    let root_key = |name: &str| -> Name {
        environment
            .root_symbols
            .get(name)
            .map_or_else(|| Rc::from(name), |symbol| symbol.key.clone())
    };
    let configured: Vec<Name> = config
        .into_iter()
        .flat_map(|config| {
            [
                &config.init,
                &config.next,
                &config.specification,
                &config.symmetry,
                &config.view,
                &config.alias,
                &config.periodic,
                &config.rl_reward,
            ]
            .into_iter()
            .flatten()
            .chain(
                [
                    &config.invariants,
                    &config.properties,
                    &config.constraints,
                    &config.action_constraints,
                    &config.postconditions,
                    &config.possible,
                ]
                .into_iter()
                .flatten(),
            )
            .chain(
                config
                    .substitutions
                    .iter()
                    .map(|substitution| &substitution.target),
            )
            .map(|name| root_key(name))
            .collect::<Vec<Name>>()
        })
        .collect();
    let mut visited: FastSet<Name> = FastSet::default();
    let mut reached = |key: Name, pending: &mut Vec<Expr>| -> Option<Name> {
        if keys.contains(&key) {
            return Some(key);
        }
        if visited.insert(key.clone())
            && let Some(definition) = environment.definitions.get(&key)
        {
            pending.push(definition.body.clone());
        }
        None
    };
    // What the configuration names is evaluated whatever the spec's own expressions name.
    for key in configured {
        if let Some(found) = reached(key, &mut pending) {
            return Some(found);
        }
    }
    let mut found = Vec::new();
    while let Some(expression) = pending.pop() {
        found.clear();
        names(&expression, &mut found);
        for key in found.drain(..) {
            if let Some(key) = reached(key, &mut pending) {
                return Some(key);
            }
        }
    }
    None
}

/// `create_environment` up to the substitutes for constants, which TLC evaluates as it computes
/// the constant definitions (`processConstantDefns`), after it has rejected any other error of
/// the configuration (`processSpec`).
pub fn link_environment(options: &EnvironmentOptions) -> Result<Environment> {
    link_environment_with_aliases(options, true, &TargetFacts::default())
}

/// `failed_targets` is what the startup checks found of the substitutions' targets with a
/// module-scoped value (`TargetFacts`).
fn link_environment_with_aliases(
    options: &EnvironmentOptions,
    allow_native_aliases: bool,
    failed_targets: &TargetFacts,
) -> Result<Environment> {
    let let_aliased_keys = RefCell::new(None);
    let linked = link_environment_once(
        options,
        allow_native_aliases,
        failed_targets,
        FastSet::default(),
        &let_aliased_keys,
    );
    // The copies an INSTANCE in a LET makes of a definition with a module-scoped entry read the
    // definition, which only the configuration's processing names: the spec is linked again with
    // those definitions.
    match (linked, let_aliased_keys.take()) {
        (Err(_), Some(keys)) => link_environment_once(
            options,
            allow_native_aliases,
            failed_targets,
            keys,
            &RefCell::new(None),
        ),
        (linked, _) => linked,
    }
}

/// `let_aliased_keys` are the definitions with a module-scoped entry that copies an INSTANCE in a
/// LET makes read; the definitions such copies read where they are other ones are put in
/// `wanted_let_aliases`.
fn link_environment_once(
    options: &EnvironmentOptions,
    allow_native_aliases: bool,
    failed_targets: &TargetFacts,
    let_aliased_keys: FastSet<Name>,
    wanted_let_aliases: &RefCell<Option<FastSet<Name>>>,
) -> Result<Environment> {
    let mut parsed =
        parse_module_tokens(options.source, &tokenize(options.source)?, options.version)?;
    parsed.extends.extend(
        options
            .linked_extendees
            .iter()
            .map(|&name| Name::from(name)),
    );
    let parsed = Rc::new(parsed);
    let (root, root_overrides) = match options
        .load_class
        .and_then(|load| Some((load, load(&parsed.name)?)))
    {
        Some((load, bytes)) => {
            crate::java_overrides::override_definitions(&parsed, &bytes, true, load)?
        }
        None => (parsed, Vec::new()),
    };
    let mut linker = create_linker(options, &root, allow_native_aliases);
    linker.let_aliased_keys = let_aliased_keys;
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
    let index_builtins = match options.load_class {
        Some(load_class) => decline_index_overrides(
            &linker,
            options.config,
            &mut definitions,
            load_class,
            &root,
            &linked_root.visible,
        )?,
        None => IndexReplaced::default(),
    };
    // processConstants visits copied operator bodies before configuration rewrites their values.
    let pre_override_definitions: Vec<Rc<Definition>> = definitions.values().cloned().collect();
    let pre_override_headers = definitions.clone();
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
    let get_scoped_symbols = |module: &str| -> Option<Rc<Symbols>> {
        if module == &*root.name {
            return Some(linked_root.visible.clone());
        }
        linker
            .linked_modules
            .borrow()
            .get(module)
            .map(|linked| linked.visible.clone())
            .or_else(|| linker.standard_exports.borrow().get(module).cloned())
    };
    let get_scoped_keys = |name: &str, module: Option<&str>| -> Vec<Name> {
        let Some(module) = module else {
            return vec![Rc::from(name), get_root_key(name)];
        };
        get_scoped_symbols(module)
            .and_then(|symbols| {
                symbols
                    .get(name)
                    .filter(|symbol| symbol.kind == SymbolKind::Definition)
                    .map(|symbol| symbol.key.clone())
            })
            .into_iter()
            .collect()
    };
    let external_modules: Vec<Name> = linker
        .external_module_order
        .borrow()
        .iter()
        .cloned()
        .chain([root.name.clone()])
        .collect();
    let module_rank = |module: Option<&str>| {
        external_modules
            .iter()
            .position(|name| Some(&**name) == module)
            .unwrap_or(external_modules.len())
    };
    let global_keys: FastSet<Name> = config
        .constants
        .iter()
        .filter(|assignment| assignment.module.is_none())
        .map(|assignment| assignment.name.as_str())
        .chain(
            config
                .substitutions
                .iter()
                .filter(|substitution| substitution.module.is_none())
                .map(|substitution| substitution.name.as_str()),
        )
        .flat_map(|name| get_scoped_keys(name, None))
        .collect();
    let mut builtins = linker.builtins.take();
    let original_builtins = builtins.clone();
    let json_source_opcodes = RefCell::new(linker.json_source_opcodes.take());
    let original_json_source_opcodes = json_source_opcodes.borrow().clone();
    let builtin_java_methods = linker.builtin_java_methods.take();
    let closed_java_methods: FastSet<Name> = builtin_java_methods
        .iter()
        .filter(|(_, module)| {
            options
                .origin
                .is_some_and(|origin| origin.is_closed_for([&***module]))
        })
        .map(|(key, _)| key.clone())
        .collect();
    let original_arities: FastMap<Name, usize> = definitions
        .iter()
        .map(|(name, definition)| {
            (
                name.clone(),
                match &definition.kind {
                    DefinitionKind::Operator { params, .. } => params.len(),
                    DefinitionKind::Function { .. } => 0,
                },
            )
        })
        .chain(
            builtins
                .iter()
                .filter(|(name, _)| closed_java_methods.contains(*name))
                .map(|(name, builtin)| (name.clone(), builtin.arity)),
        )
        .collect();
    let builtin_keys: FastSet<Name> = builtins.keys().cloned().collect();
    let java_keys: FastSet<Name> = linker
        .java_overrides
        .borrow()
        .iter()
        .filter(|method| method.is_matched)
        .flat_map(|method| get_scoped_keys(&method.operator, Some(&method.module)))
        .collect();
    let substituted_keys: FastSet<Name> = config
        .substitutions
        .iter()
        .filter(|substitution| substitution.module.is_none())
        .flat_map(|substitution| get_scoped_keys(&substitution.name, None))
        .collect();
    let is_configurable_root_name = |name: &str| {
        declared_constants
            .iter()
            .any(|constant| &**constant == name)
            || linked_root
                .visible
                .get(name)
                .is_some_and(|symbol| symbol.kind == SymbolKind::Definition)
    };
    let globally_assigned_keys: FastSet<Name> = config
        .constants
        .iter()
        .filter(|assignment| assignment.module.is_none())
        .flat_map(|assignment| get_scoped_keys(&assignment.name, None))
        .collect();
    // Scoped assignments replace a body ToolObject, not the OpDef in `defns`. A positive
    // original arity also prevents processConstantDefns from replacing that name later.
    let config_opdef_headers = definitions
        .iter()
        .filter(|(key, definition)| {
            options
                .origin
                .is_some_and(|origin| origin.has_closed_override_index())
                && !globally_assigned_keys.contains(*key)
                && !substituted_keys.contains(*key)
                && !builtin_keys.contains(*key)
                && !java_keys.contains(*key)
                && matches!(&definition.kind, DefinitionKind::Operator { params, .. } if !params.is_empty())
        })
        .map(|(key, definition)| {
            (
                key.clone(),
                ConfigOpDefHeader {
                    definition: definition.clone(),
                },
            )
        })
        .collect();
    let configured_value_bindings = config
        .constants
        .iter()
        .filter(|assignment| {
            assignment.module.is_none() && is_configurable_root_name(&assignment.name)
        })
        .flat_map(|assignment| get_scoped_keys(&assignment.name, None))
        .filter(|key| {
            !substituted_keys.contains(key)
                && !builtin_keys.contains(key)
                && !java_keys.contains(key)
        })
        .collect();
    let mut operator_objects = TableObjects::new(&linked_root.visible, &definitions);
    let get_key_arity =
        |definitions: &OrderedMap<Name, Rc<Definition>>, key: &str| match definitions
            .get(key)
            .map(|definition| &definition.kind)
        {
            Some(DefinitionKind::Operator { params, .. }) => params.len(),
            _ => original_arities.get(key).copied().unwrap_or_else(|| {
                linked_root
                    .constants
                    .iter()
                    .find(|constant| &*constant.name == key)
                    .map_or(0, |constant| constant.arity)
            }),
        };
    let mut constants: OrderedMap<Name, ConfigValue> = OrderedMap::new();
    let mut operator_keys: FastSet<Name> = FastSet::default();
    let mut operator_constants: OrderedMap<Name, ConfigValue> = OrderedMap::new();
    let mut set_operator = |key: &Name,
                            builtin: Builtin,
                            definitions: &mut OrderedMap<Name, Rc<Definition>>,
                            constants: &mut OrderedMap<Name, ConfigValue>,
                            value: Option<&ConfigValue>| {
        json_source_opcodes.borrow_mut().remove(key);
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
            return Err(get_table_cast_error(&earlier.value));
        }
    }
    // `processModuleOverrides` runs after scoped constant assignments and replaces the
    // assigned body with the Java method. Scoped substitutions run later and still win.
    // The six bundled module classes install legacy public static methods by name, without an
    // arity check. TLCGet and TLCEval use @Evaluation, which also installs without that check.
    // TLCSet uses @TLAPlusOperator, whose check compares the method with the OpDefNode's own
    // arity, which a scoped entry leaves as written, so its method installs too.
    let java_replaces_scoped_assignment = |name: &str, module: Option<&str>| {
        module
            .and_then(get_scoped_symbols)
            .and_then(|symbols| symbols.get(name).cloned())
            .is_some_and(|symbol| {
                java_keys.contains(&symbol.key) || closed_java_methods.contains(&symbol.key)
            })
    };
    // A substitution `X <- Y`, global or scoped, gives X the OpDefNode of Y, whose body TLC
    // evaluates as written (`Tool.evalAppl`). A module-scoped entry for Y sets a ToolObject on
    // that body, which the evaluation reads only where the body is a literal (`Tool.evalImpl`'s
    // NumeralKind, DecimalKind and StringKind). Through the substitution, the entry on any other
    // body has no effect. Where nothing else names Y, the entry has no effect at all, so it is
    // left out. A read of Y itself finds Y's ToolObject, else the body's
    // (`SymbolNodeValueLookupProvider.lookup`), and `SpecProcessor.processConstantDefns` sets Y's
    // to the value of its body as written where Y is a nullary definition of constant level it
    // reaches through X: for a declared constant X in the root module's loop over the constants,
    // and for a definition X in the loop over the definitions. So for a global substitution:
    // - where Y's body reads a variable, TLC never computes it, and Y reads the entry
    //   everywhere;
    // - where X is a declared constant and Y a definition of the root module, the constants'
    //   loop computes Y before any definition reads it, and Y reads its body everywhere;
    // - where X is a declared constant and Y a definition of another module, the definitions of
    //   modules TLC processes before the root module that TLC computes read the entry, and
    //   everything else reads the body, which the replay follows only where every definition
    //   that names Y is such a one;
    // - where X is only a definition, what Y's references read depends on the order TLC caches
    //   the definitions in, which isn't followed, and that declines.
    // The same holds for a table, which a literal body would return as the substitution's
    // value.
    let mut body_read_targets: FastSet<Name> = FastSet::default();
    let mut scoped_target_checks: Vec<ScopedTargetCheck> = Vec::new();
    let hidden_scoped_keys: FastSet<Name> = {
        let targets: FastSet<Name> = config
            .substitutions
            .iter()
            .map(|substitution| get_root_key(&substitution.target))
            .collect();
        let scoped_targets: FastSet<Name> = config
            .substitutions
            .iter()
            .filter(|substitution| substitution.module.is_some())
            .map(|substitution| get_root_key(&substitution.target))
            .collect();
        let scoped_entries: Vec<(&crate::config::ConstantAssignment, Name)> = config
            .constants
            .iter()
            .filter(|assignment| {
                assignment.module.is_some()
                    && !java_replaces_scoped_assignment(
                        &assignment.name,
                        assignment.module.as_deref(),
                    )
            })
            .flat_map(|assignment| {
                get_scoped_keys(&assignment.name, assignment.module.as_deref())
                    .into_iter()
                    .filter(|key| targets.contains(key) && !global_keys.contains(key))
                    .map(move |key| (assignment, key))
            })
            .collect();
        // A declared constant of the root module with neither a value nor a substitution of the
        // configuration's own (a module-scoped one never gives it one) fails the model before
        // anything reads an entry, as TLC reports it (`The constant parameter K is not assigned
        // a value`), which the check below gives.
        let is_unassigned = !options.is_unconfigured
            && declared_constants.iter().any(|name| {
                !config
                    .constants
                    .iter()
                    .any(|assignment| assignment.module.is_none() && *assignment.name == **name)
                    && !config.substitutions.iter().any(|substitution| {
                        substitution.module.is_none() && *substitution.name == **name
                    })
            });
        let mut hidden = FastSet::default();
        if !scoped_entries.is_empty() && !is_unassigned {
            let mut assumptions = Vec::new();
            add_assumptions(&linked_root, &mut Vec::new(), &mut assumptions);
            let definition_roots = |definition: &Definition| -> Vec<Expr> {
                let bounds = match &definition.kind {
                    DefinitionKind::Function { bounds } => bounds.as_slice(),
                    DefinitionKind::Operator { .. } => &[],
                };
                bounds
                    .iter()
                    .map(|bound| bound.set.clone())
                    .chain([definition.body.clone()])
                    .collect()
            };
            let assumption_roots: Vec<Expr> = assumptions
                .iter()
                .map(|assumption| assumption.expression.clone())
                .collect();
            let roots: Vec<Expr> = definitions
                .values()
                .flat_map(|definition| definition_roots(definition))
                .chain(assumption_roots.iter().cloned())
                .collect();
            let variables: FastSet<Name> = linked_root.variables.iter().cloned().collect();
            let declared_targets: FastSet<Name> = config
                .substitutions
                .iter()
                .filter(|substitution| {
                    substitution.module.is_none()
                        && linked_root
                            .constants
                            .iter()
                            .any(|constant| *constant.name == *substitution.name)
                })
                .map(|substitution| get_root_key(&substitution.target))
                .collect();
            let decline = || {
                Err(FrontError::NotYet(
                    "a substitution whose target has a module-scoped value the spec reads otherwise"
                        .to_owned(),
                ))
            };
            // An operator the configuration doesn't replace, which TLC evaluates as written.
            let is_plain = |name: &Name| {
                !config.substitutions.iter().any(|substitution| {
                    get_scoped_keys(&substitution.name, substitution.module.as_deref())
                        .contains(name)
                }) && !config.constants.iter().any(|assignment| {
                    get_scoped_keys(&assignment.name, assignment.module.as_deref()).contains(name)
                }) && !builtin_keys.contains(name)
                    && !java_keys.contains(name)
                    && !closed_java_methods.contains(name)
            };
            // What TLC can evaluate: every definition, assumption and INSTANCE substitution.
            let evaluated_roots: Vec<Expr> = roots
                .iter()
                .cloned()
                .chain(
                    linker
                        .link_order
                        .borrow()
                        .iter()
                        .flat_map(|linked| linked.module.instances.clone())
                        .chain(root.instances.iter().cloned())
                        .flat_map(|instance| {
                            instance
                                .substitutions
                                .iter()
                                .map(|substitution| substitution.expression.clone())
                                .collect::<Vec<Expr>>()
                        }),
                )
                .collect();
            for (assignment, key) in &scoped_entries {
                let Some(definition) = definitions.get(key).cloned() else {
                    continue;
                };
                let is_literal = matches!(
                    definition.body.kind,
                    ExpressionKind::Number { .. }
                        | ExpressionKind::Decimal { .. }
                        | ExpressionKind::String { .. }
                );
                if is_literal && assignment.args.is_none() {
                    continue;
                }
                // A literal body returns an entry with arguments, the operator's table, as its
                // value to the substitution (`Tool.evalImpl`), and a read of Y applies it
                // (`lookup`). Where nothing TLC evaluates reads Y or a name substituted by it, or
                // reads one only as an argument of a parameter its operator never names, which
                // TLC never computes (`references_shown`), the table shows nowhere: TLC computes
                // it as it starts, without a failure, and drops it.
                if is_literal && assignment.args.is_some() {
                    let mut names: FastSet<Name> = [key.clone()].into_iter().collect();
                    names.extend(
                        config
                            .substitutions
                            .iter()
                            .filter(|substitution| get_root_key(&substitution.target) == *key)
                            .flat_map(|substitution| {
                                get_scoped_keys(&substitution.name, substitution.module.as_deref())
                            }),
                    );
                    let is_configured = crate::lower::is_read_by_config(config, &|named| {
                        *named == *definition.name
                            || config.substitutions.iter().any(|substitution| {
                                substitution.name == named
                                    && get_root_key(&substitution.target) == *key
                            })
                    });
                    let entries = scoped_entries
                        .iter()
                        .filter(|(_, other)| other == key)
                        .count();
                    // A name the substitution gives the table, read only where TLC never looks
                    // into its value (`get_uninspected_parts`), or as a whole assumption, which
                    // fails as TLC expects a boolean for the table as for the literal, shows
                    // nowhere either.
                    let opaque: FastSet<Name> =
                        names.iter().filter(|name| *name != key).cloned().collect();
                    let inspected_roots: Vec<Expr> = evaluated_roots
                        .iter()
                        .filter(|root| {
                            !(is_bare_reference(root, &opaque)
                                && assumption_roots
                                    .iter()
                                    .any(|assumption| Rc::ptr_eq(assumption, root)))
                        })
                        .cloned()
                        .collect();
                    if entries == 1
                        && !is_configured
                        && !references_shown_but(
                            &inspected_roots,
                            &names,
                            &definitions,
                            &is_plain,
                            &opaque,
                        )
                    {
                        hidden.insert(key.clone());
                        continue;
                    }
                }
                if !is_literal && !references_key(&roots, key) {
                    hidden.insert(key.clone());
                    continue;
                }
                let is_nullary = matches!(
                    &definition.kind,
                    DefinitionKind::Operator { params, .. } if params.is_empty()
                );
                // An entry with arguments for Y without parameters, as `Y(0) = [M] 7`, the only
                // entry for Y, is one TLC reads nowhere: what TLC computes as it starts and every
                // later read find Y's body alike.
                if !is_literal
                    && is_nullary
                    && assignment.args.is_some()
                    && !scoped_targets.contains(key)
                    && scoped_entries
                        .iter()
                        .filter(|(_, other)| other == key)
                        .count()
                        == 1
                {
                    hidden.insert(key.clone());
                    continue;
                }
                // A function definition `Y[x \in S] == e` is an OpDefNode of arity 0 too, which
                // the startup checks follow where S is certainly empty
                // (`certainly_computes_definition`).
                let is_empty_function = matches!(
                    &definition.kind,
                    DefinitionKind::Function { bounds }
                        if bounds.iter().all(|bound| is_certainly_empty(&bound.set))
                );
                if is_literal || !(is_nullary || is_empty_function) || assignment.args.is_some() {
                    return decline();
                }
                // A module-scoped substitution `X <- [M] Y` sets Y's node on X's body, which
                // `processConstantDefns` follows (`lookup`) to compute Y where it first reaches
                // X, as for a global one. The linking reads Y's body for X only where it leaves
                // the entry out (`hidden`); the other outcomes below decline for it.
                let is_scoped_target = scoped_targets.contains(key);
                let is_declared = declared_targets.contains(key);
                // Where TLC fails to compute Y's body of constant level as it starts, it swallows
                // the failure, and Y reads the entry everywhere.
                if failed_targets.failed.contains(key) {
                    if is_scoped_target {
                        return decline();
                    }
                    body_read_targets.insert(key.clone());
                    scoped_target_checks.push(ScopedTargetCheck {
                        key: key.clone(),
                        definition,
                        is_constant: true,
                        is_attempted: false,
                        is_hidden: false,
                        cached: Vec::new(),
                        may_fail: false,
                        must_fail: false,
                    });
                    continue;
                }
                // Where every definition TLC computes before Y that shows what it reads fails
                // reading the entry, without an effect, TLC computes each again at each use,
                // and every read finds Y's computed body: the entry has no effect but where
                // computing Y fails.
                if failed_targets.reread.contains(key) {
                    hidden.insert(key.clone());
                    scoped_target_checks.push(ScopedTargetCheck {
                        key: key.clone(),
                        definition,
                        is_constant: true,
                        is_attempted: true,
                        is_hidden: true,
                        cached: Vec::new(),
                        may_fail: false,
                        must_fail: false,
                    });
                    continue;
                }
                if reaches_variable(&definitions, &variables, &definition.body) {
                    if is_scoped_target {
                        return decline();
                    }
                    body_read_targets.insert(key.clone());
                    scoped_target_checks.push(ScopedTargetCheck {
                        key: key.clone(),
                        definition,
                        is_constant: false,
                        is_attempted: is_declared,
                        is_hidden: false,
                        cached: Vec::new(),
                        may_fail: false,
                        must_fail: false,
                    });
                    continue;
                }
                if options.is_unconfigured {
                    return decline();
                }
                let (startup, root_start) =
                    get_startup_order(&linker, &linked_root, &definitions, options)?;
                // TLC computes Y through X in the root module's loop over the constants for a
                // declared constant, and otherwise where a loop over the definitions first
                // reaches X.
                let cutoff = if is_declared {
                    root_start
                } else {
                    let substituted: FastSet<usize> = config
                        .substitutions
                        .iter()
                        .filter(|substitution| get_root_key(&substitution.target) == *key)
                        .flat_map(|substitution| {
                            get_scoped_keys(&substitution.name, substitution.module.as_deref())
                                .into_iter()
                                .filter(|name| {
                                    substitution.module.is_none() || !global_keys.contains(name)
                                })
                        })
                        .filter_map(|name| definitions.get(&name))
                        .map(|definition| Rc::as_ptr(definition) as usize)
                        .collect();
                    // A module before the root module that defines X reaches it first.
                    let Some(position) = startup.iter().position(|definition| {
                        substituted.contains(&(Rc::as_ptr(definition) as usize))
                    }) else {
                        return decline();
                    };
                    position
                };
                // The definitions whose evaluation can read Y: an argument of a parameter the
                // operator never names, a LET definition nothing names and a branch a literal
                // decides away aren't reads (`references_shown`).
                let mut readers: FastSet<Name> = FastSet::default();
                readers.insert(key.clone());
                loop {
                    let added: Vec<Name> = definitions
                        .iter()
                        .filter(|(name, reader)| {
                            !readers.contains(*name)
                                && references_shown(
                                    &definition_roots(reader),
                                    &readers,
                                    &definitions,
                                    &is_plain,
                                )
                        })
                        .map(|(name, _)| name.clone())
                        .collect();
                    if added.is_empty() {
                        break;
                    }
                    readers.extend(added);
                }
                let is_reader = |candidate: &Rc<Definition>| {
                    !Rc::ptr_eq(candidate, &definition)
                        && definitions.iter().any(|(name, other)| {
                            Rc::ptr_eq(other, candidate) && readers.contains(name)
                        })
                };
                // What TLC computes before it computes Y reads the entry; everything after, and
                // every read as the model runs, reads Y's computed body.
                let early: Vec<Rc<Definition>> = startup[..cutoff]
                    .iter()
                    .filter(|candidate| {
                        !matches!(
                            &candidate.kind,
                            DefinitionKind::Operator { params, .. } if !params.is_empty()
                        ) && is_reader(candidate)
                    })
                    .cloned()
                    .collect();
                // Of `readers`, the definitions without parameters that nothing reads but each
                // other and operators with parameters that nothing applies, of no substitution
                // and no name the configuration reads, with no effect that shows what they read
                // as TLC computes them as it starts (`is_without_effects`): which value they read
                // doesn't show. TLC computes no operator with parameters as it starts.
                let get_unread = |readers: Vec<&Rc<Definition>>| -> FastSet<usize> {
                    let is_configured = |definition: &Rc<Definition>| {
                        config.substitutions.iter().any(|substitution| {
                            get_root_key(&substitution.target) == definition.name
                                || *substitution.name == *definition.name
                        }) || crate::lower::is_read_by_config(config, &|named| {
                            *named == *definition.name
                        })
                    };
                    let has_params = |definition: &Rc<Definition>| {
                        matches!(
                            &definition.kind,
                            DefinitionKind::Operator { params, .. } if !params.is_empty()
                        )
                    };
                    let mut unread: FastSet<usize> = readers
                        .into_iter()
                        .filter(|reader| {
                            matches!(
                                &reader.kind,
                                DefinitionKind::Operator { params, .. } if params.is_empty()
                            ) && is_without_effects(&definitions, &reader.body)
                        })
                        .chain(
                            definitions
                                .values()
                                .filter(|definition| has_params(definition)),
                        )
                        .filter(|definition| !is_configured(definition))
                        .map(|definition| Rc::as_ptr(definition) as usize)
                        .collect();
                    loop {
                        let read: Vec<usize> = (definitions.iter())
                            .filter(|(_, reader)| unread.contains(&(Rc::as_ptr(reader) as usize)))
                            .filter(|(name, _)| {
                                let single: FastSet<Name> = [(*name).clone()].into_iter().collect();
                                references_shown(
                                    &assumption_roots,
                                    &single,
                                    &definitions,
                                    &is_plain,
                                ) || crate::lower::is_read_by_config(config, &|named| {
                                    *named == ***name
                                }) || definitions.values().any(|other| {
                                    !unread.contains(&(Rc::as_ptr(other) as usize))
                                        && references_shown(
                                            &definition_roots(other),
                                            &single,
                                            &definitions,
                                            &is_plain,
                                        )
                                })
                            })
                            .map(|(_, reader)| Rc::as_ptr(reader) as usize)
                            .collect();
                        if read.is_empty() {
                            return unread;
                        }
                        for reader in read {
                            unread.remove(&reader);
                        }
                    }
                };
                // Where nothing reads what TLC computes before Y, it doesn't show the entry.
                let unread_early = get_unread(early.iter().collect());
                if early
                    .iter()
                    .all(|reader| unread_early.contains(&(Rc::as_ptr(reader) as usize)))
                {
                    hidden.insert(key.clone());
                    scoped_target_checks.push(ScopedTargetCheck {
                        key: key.clone(),
                        definition,
                        is_constant: true,
                        is_attempted: true,
                        is_hidden: true,
                        cached: Vec::new(),
                        may_fail: false,
                        must_fail: false,
                    });
                    continue;
                }
                // The definitions TLC computes before Y whose value shows, which read the entry.
                // Where each fails as TLC computes it, without an effect, TLC computes it again at
                // each use, reading Y's computed body, as everything else does (`TargetFacts`).
                let shown_early: Vec<Rc<Definition>> = early
                    .iter()
                    .filter(|reader| !unread_early.contains(&(Rc::as_ptr(reader) as usize)))
                    .cloned()
                    .collect();
                let may_reread = shown_early
                    .iter()
                    .all(|reader| is_rereadable(&definitions, &reader.body));
                // A reader TLC computes before Y without reading it there, as TLC builds it
                // lazily or at once without its body (`Deferral::is_deferred`), reads Y's
                // computed body, as one that fails reading the entry does.
                let deferral = Deferral {
                    definitions: &definitions,
                    readers: &readers,
                    early: &early,
                    unread: &unread_early,
                    is_plain: &is_plain,
                    builtin_keys: &builtin_keys,
                };
                let is_deferred = |reader: &Rc<Definition>| deferral.is_deferred(reader, 0, &[]);
                // Where only definitions TLC computes before Y read it, each reads the entry, and
                // the rest read what those computed: every definition that can read Y is one
                // such, or an operator with parameters that only such ones apply.
                if references_key(&assumption_roots, key)
                    || crate::lower::is_read_by_config(config, &|named| *named == *definition.name)
                {
                    if !may_reread || is_scoped_target {
                        return decline();
                    }
                    body_read_targets.insert(key.clone());
                    scoped_target_checks.push(ScopedTargetCheck {
                        key: key.clone(),
                        definition,
                        is_constant: true,
                        is_attempted: true,
                        is_hidden: false,
                        cached: shown_early
                            .into_iter()
                            .filter(|reader| !is_deferred(reader))
                            .collect(),
                        may_fail: true,
                        must_fail: true,
                    });
                    continue;
                }
                let is_early = |reader: &Rc<Definition>| {
                    matches!(
                        &reader.kind,
                        DefinitionKind::Operator { params, .. } if params.is_empty()
                    ) && early.iter().any(|candidate| Rc::ptr_eq(candidate, reader))
                        && !reaches_variable(&definitions, &variables, &reader.body)
                };
                let substituted_targets: FastSet<Name> = config
                    .substitutions
                    .iter()
                    .map(|substitution| get_root_key(&substitution.target))
                    .filter(|target| target != key)
                    .collect();
                // The definitions that read Y other than through what one TLC computes before Y
                // computed, and those it computes there that read it.
                let mut live: FastSet<Name> = FastSet::default();
                let mut computed: FastSet<Name> = FastSet::default();
                live.insert(key.clone());
                loop {
                    let added: Vec<(Name, bool)> = definitions
                        .iter()
                        .filter(|(name, reader)| {
                            !live.contains(*name)
                                && !computed.contains(*name)
                                && definition_roots(reader)
                                    .iter()
                                    .any(|root| references_any(root, &live))
                        })
                        .map(|(name, reader)| (name.clone(), is_early(reader)))
                        .collect();
                    if added.is_empty() {
                        break;
                    }
                    for (name, is_computed) in added {
                        if is_computed {
                            computed.insert(name);
                        } else {
                            live.insert(name);
                        }
                    }
                }
                // The rest that nothing reads, which TLC computes as it starts after Y, reading
                // Y's computed body, with no effect that shows what they read.
                let unread = get_unread(
                    live.iter()
                        .filter(|name| *name != key)
                        .filter_map(|name| definitions.get(name))
                        .collect(),
                );
                let is_unread =
                    |reader: &Rc<Definition>| unread.contains(&(Rc::as_ptr(reader) as usize));
                // What else reads Y must be an operator with parameters that only those apply, or
                // a definition nothing reads.
                let is_safe = |name: &Name| {
                    let Some(reader) = definitions.get(name) else {
                        return false;
                    };
                    if substituted_targets.contains(name) {
                        return false;
                    }
                    if is_unread(reader) {
                        return true;
                    }
                    if !matches!(
                        &reader.kind,
                        DefinitionKind::Operator { params, .. } if !params.is_empty()
                    ) {
                        return false;
                    }
                    let single: FastSet<Name> = [name.clone()].into_iter().collect();
                    !references_any_of(&assumption_roots, &single)
                        && !references_any_of(&definition_roots(&definition), &single)
                };
                if is_scoped_target {
                    return decline();
                }
                // Where something else reads Y, it reads Y's computed body, which every
                // definition TLC computes before Y must then read too: each must fail reading
                // the entry, without an effect, so that TLC computes it again at each use.
                let is_read_otherwise = !live.iter().filter(|name| *name != key).all(is_safe);
                let cached: Vec<Rc<Definition>> = computed
                    .iter()
                    .filter_map(|name| definitions.get(name).cloned())
                    .collect();
                // One that defers its reads reads Y's computed body, which the others read only
                // where each fails.
                let has_deferred = cached.iter().any(is_deferred);
                let cached: Vec<Rc<Definition>> = cached
                    .into_iter()
                    .filter(|reader| !is_deferred(reader))
                    .collect();
                body_read_targets.insert(key.clone());
                scoped_target_checks.push(ScopedTargetCheck {
                    key: key.clone(),
                    definition,
                    is_constant: true,
                    is_attempted: true,
                    is_hidden: false,
                    may_fail: cached
                        .iter()
                        .all(|reader| is_rereadable(&definitions, &reader.body)),
                    cached,
                    must_fail: has_deferred || is_read_otherwise,
                });
            }
        }
        hidden
    };
    let mut assignments: Vec<_> = config
        .constants
        .iter()
        .filter(|assignment| {
            assignment.args.is_none()
                && (assignment.module.is_some() || is_configurable_root_name(&assignment.name))
                && !java_replaces_scoped_assignment(&assignment.name, assignment.module.as_deref())
        })
        .collect();
    assignments.sort_by_key(|assignment| module_rank(assignment.module.as_deref()));
    // The definitions INIT, NEXT, an INVARIANT, a PROPERTY or a (ACTION_)CONSTRAINT names, which
    // `processConfigSpec` and its siblings look up in `defns`. A scoped entry leaves `defns`
    // alone (see `check_selected_scoped_values`).
    let selected_keys: FastSet<Name> = [&config.init, &config.next]
        .into_iter()
        .flatten()
        .chain(
            [
                &config.invariants,
                &config.properties,
                &config.constraints,
                &config.action_constraints,
            ]
            .into_iter()
            .flatten(),
        )
        .filter_map(|name| linked_root.visible.get(name.as_str()))
        .map(|symbol| symbol.key.clone())
        .collect();
    // The keys only a PROPERTY selects.
    let property_keys: FastSet<Name> = config
        .properties
        .iter()
        .filter_map(|name| linked_root.visible.get(name.as_str()))
        .map(|symbol| symbol.key.clone())
        .filter(|key| {
            ![&config.init, &config.next]
                .into_iter()
                .flatten()
                .chain(
                    [
                        &config.invariants,
                        &config.constraints,
                        &config.action_constraints,
                    ]
                    .into_iter()
                    .flatten(),
                )
                .filter_map(|name| linked_root.visible.get(name.as_str()))
                .any(|symbol| symbol.key == *key)
        })
        .collect();
    let mut selected_scoped_keys: Vec<Name> = Vec::new();
    // The value of each, from the last entry, as for any other scoped entry.
    let mut scoped_selected_values: FastMap<Name, ConfigValue> = FastMap::default();
    // Whether a scoped entry gives a value to the definition an unnamed INSTANCE copies into the
    // root module under a name a selector reads: TLC's copy's body is a SubstInNode over the
    // body that holds the value, which the front end's copy doesn't share.
    let mut is_copy_scoped = false;
    // Likewise a scoped substitution of that definition: the configuration's checks evaluate the
    // copy's own body (`def.getBody()`, a SubstInNode over the body an OpApplNode ignores the
    // substitute on), where every reference to it, the copy's too, reads the substitute
    // (`lookup` follows a SubstInNode's body to its tool object).
    let is_copy_substituted = config
        .substitutions
        .iter()
        .filter(|substitution| substitution.module.is_some())
        .any(|substitution| {
            get_scoped_keys(&substitution.name, substitution.module.as_deref())
                .iter()
                .any(|key| {
                    !hidden_scoped_keys.contains(key)
                        && !global_keys.contains(key)
                        && !selected_keys.contains(key)
                })
                && linked_root
                    .visible
                    .get(substitution.name.as_str())
                    .is_some_and(|symbol| {
                        selected_keys.contains(&symbol.key) && symbol.key.contains('#')
                    })
        });
    for assignment in assignments {
        for key in get_scoped_keys(&assignment.name, assignment.module.as_deref()) {
            if assignment.module.is_some() && hidden_scoped_keys.contains(&key) {
                continue;
            }
            json_source_opcodes.borrow_mut().remove(&key);
            if assignment.module.is_some() && global_keys.contains(&key) {
                continue;
            }
            if assignment.module.is_some()
                && !selected_keys.contains(&key)
                && linked_root
                    .visible
                    .get(assignment.name.as_str())
                    .is_some_and(|symbol| {
                        selected_keys.contains(&symbol.key) && symbol.key.contains('#')
                    })
            {
                is_copy_scoped = true;
            }
            // A function definition `K[x \in S] == e` is an OpDefNode of arity 0 in TLC too.
            let is_selected_definition = selected_keys.contains(&key)
                && match definitions.get(&key).map(|definition| &definition.kind) {
                    Some(DefinitionKind::Operator { params, .. }) => params.is_empty(),
                    Some(DefinitionKind::Function { .. }) => true,
                    None => false,
                };
            if assignment.module.is_some() && is_selected_definition {
                if !selected_scoped_keys.contains(&key) {
                    selected_scoped_keys.push(key.clone());
                }
                scoped_selected_values.insert(key.clone(), assignment.value.clone());
            }
            let arity = get_key_arity(&definitions, &key);
            if arity == 0 {
                constants.insert(key, assignment.value.clone());
            } else {
                set_operator(
                    &key,
                    Builtin {
                        intrinsic: None,
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
    // `processConfigProps` takes a numeral or string body as an implied initial predicate, which
    // `Tool.eval` reads as v (`getToolObject` of the literal): a TRUE v holds as the value does.
    selected_scoped_keys.retain(|key| {
        let is_true_literal = property_keys.contains(key)
            && matches!(
                scoped_selected_values.get(key),
                Some(ConfigValue::Boolean(true))
            )
            && definitions.get(key).is_some_and(|definition| {
                matches!(
                    definition.body.kind,
                    ExpressionKind::Number { .. } | ExpressionKind::String { .. }
                )
            });
        if is_true_literal {
            scoped_selected_values.remove(key);
        }
        !is_true_literal
    });
    for assignment in config.constants.iter().filter(|item| {
        item.module.is_none() && item.args.is_none() && is_configurable_root_name(&item.name)
    }) {
        operator_objects.assign_value(&Rc::from(assignment.name.as_str()), &assignment.value);
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
    let mut scoped_tables: Vec<_> = tables.values().collect();
    scoped_tables.sort_by_key(|(_, module, _, _)| module_rank(module.as_deref()));
    for (name, module, row_arity, rows) in scoped_tables {
        if module.is_none() && !is_configurable_root_name(name) {
            continue;
        }
        if java_replaces_scoped_assignment(name, module.as_deref()) {
            continue;
        }
        let rows = Rc::new(rows.clone());
        for key in get_scoped_keys(name, module.as_deref()) {
            if module.is_some() && (global_keys.contains(&key) || hidden_scoped_keys.contains(&key))
            {
                continue;
            }
            let arity = match get_key_arity(&definitions, &key) {
                0 => *row_arity,
                arity => arity,
            };
            operator_objects.attach_table(&key, &rows, module.is_none().then_some(name));
            set_operator(
                &key,
                Builtin {
                    intrinsic: None,
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
    // Declared receivers get their configuration value before Java overrides replace global
    // Defns entries. A later alias copies those entries without following receiver attachments.
    for declaration in &linked_root.constants {
        operator_objects.register_declaration(declaration);
    }
    for method in linker.packaged_methods.borrow().iter() {
        operator_objects.install_method(&method.builtin.name, method);
    }
    // An unmodeled installation is unknown, including a Java method on a user-supplied module
    // whose signature the native linker did not recognize. Do not infer absence from no event.
    for module in &external_modules {
        let symbols = get_scoped_symbols(module);
        for operator in PackagedMethod::operators(module) {
            if symbols
                .as_ref()
                .is_some_and(|symbols| symbols.contains_key(operator))
                && !linker
                    .packaged_methods
                    .borrow()
                    .iter()
                    .any(|method| method.module == *module && &*method.builtin.name == operator)
            {
                operator_objects.is_complete = false;
                operator_objects.unknown_global(Rc::from(operator));
                operator_objects
                    .unknown_installations
                    .push((module.clone(), Rc::from(operator)));
            }
        }
    }
    let mut substitutions: OrderedMap<Name, Name> = OrderedMap::new();
    for substitution in config
        .substitutions
        .iter()
        .filter(|item| item.module.is_none())
    {
        for key in get_scoped_keys(&substitution.name, None) {
            json_source_opcodes.borrow_mut().remove(&key);
            substitutions.insert(key, get_root_key(&substitution.target));
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
    // `initializeModConstants` then builds each module's table of scoped entries as
    // `makeConstantTable` builds the global one, and casts a value given before to a table
    // alike. It visits the modules in its Hashtable's order, which isn't followed where more
    // than one fails.
    let mut cast_errors: Vec<(&str, &ConfigValue)> = Vec::new();
    for (position, assignment) in config.constants.iter().enumerate() {
        let Some(module) = assignment.module.as_deref() else {
            continue;
        };
        if assignment.args.is_none() || cast_errors.iter().any(|(failed, _)| *failed == module) {
            continue;
        }
        if let Some(earlier) = config.constants[..position].iter().find(|earlier| {
            earlier.name == assignment.name
                && earlier.args.is_none()
                && earlier.module.as_deref() == Some(module)
        }) {
            cast_errors.push((module, &earlier.value));
        }
    }
    match cast_errors.as_slice() {
        [] => {}
        [(_, value)] => return Err(get_table_cast_error(value)),
        _ => {
            return Err(FrontError::NotYet(
                "module-scoped tables of more than one module that TLC fails to build".to_owned(),
            ));
        }
    }
    // `SpecProcessor.processSpec` holds the configuration's substitutions in a Hashtable, the
    // last for each name, and checks them in its loops over the root module's declared
    // constants, then its definitions (`getConstantDecls`, `getOpDefs`), and last reports a
    // name neither holds, in the Hashtable's order. The arity of an operator put in for a
    // declared constant it checks only as it computes the constant definitions
    // (`processConstantDefns`), after the scoped substitutions.
    let is_declared = |name: &str| {
        declared_constants
            .iter()
            .any(|constant| &**constant == name)
    };
    let global: Vec<&crate::config::Substitution> = config
        .substitutions
        .iter()
        .filter(|substitution| substitution.module.is_none())
        .collect();
    let target_of = |name: &str| {
        global
            .iter()
            .rev()
            .find(|substitution| substitution.name == name)
            .map(|substitution| substitution.target.as_str())
    };
    // What TLC reports of the substitution for a name it holds, but for a declared constant's
    // arity.
    let substitution_error = |name: &str, target: &str| -> Option<FrontError> {
        if global.iter().any(|other| other.name == target) {
            return Some(FrontError::Config(format!(
                "In the configuration file, the identifier {target} appears\non the right-hand side of a <- after already appearing on the\nleft-hand side of one."
            )));
        }
        let target_key = get_root_key(target);
        let definition = definitions.get(&target_key);
        let is_defined = definition.is_some()
            || builtins.contains_key(&target_key)
            || constants.contains_key(&target_key)
            || is_declared(target)
            || variables.iter().any(|variable| &**variable == target);
        if !is_defined || linked_root.facts.contains(target) {
            return Some(FrontError::Config(format!(
                "The configuration file substitutes for {name} with the undefined identifier {target}."
            )));
        }
        if !is_declared(name)
            && let Some(DefinitionKind::Operator { params, .. }) =
                definition.map(|definition| &definition.kind)
            && Some(params.len()) != linked_root.visible.get(name).map(|symbol| symbol.arity)
        {
            return Some(FrontError::Config(format!(
                "The configuration file substitutes for {name} with {target} of different number of arguments."
            )));
        }
        None
    };
    let is_held = |name: &str| {
        is_declared(name)
            || linked_root.visible.contains_key(name) && !linked_root.facts.contains(name)
    };
    let constant_arity_error = |name: &str, target: &str| -> Option<FrontError> {
        let definition = definitions.get(&get_root_key(target))?;
        let DefinitionKind::Operator { params, .. } = &definition.kind else {
            return None;
        };
        let arity = linked_root
            .constants
            .iter()
            .find(|constant| &*constant.name == name)?
            .arity;
        (params.len() != arity).then(|| {
            FrontError::Config(format!(
                "The configuration file substitutes for {name} with {target} of different number of arguments."
            ))
        })
    };
    let has_error = global.iter().any(|substitution| {
        let (name, target) = (substitution.name.as_str(), substitution.target.as_str());
        !is_held(name)
            || substitution_error(name, target).is_some()
            || constant_arity_error(name, target).is_some()
    });
    let mut deferred_arity_error = None;
    if has_error {
        let order = TlcOrder::new(options.source, options.load_module, options.version)?;
        let mut held = FastSet::default();
        for name in order
            .get_declaration_order(false)?
            .iter()
            .filter(|name| is_declared(name))
        {
            if let Some(target) = target_of(name) {
                held.insert(name.to_string());
                if let Some(error) = substitution_error(name, target) {
                    return Err(error);
                }
            }
        }
        for name in order.get_visible_definition_order(None)? {
            if is_declared(&name) || linked_root.facts.contains(&*name) {
                continue;
            }
            if let Some(target) = target_of(&name) {
                held.insert(name.to_string());
                if let Some(error) = substitution_error(&name, target) {
                    return Err(error);
                }
            }
        }
        let keys: Vec<&str> = global
            .iter()
            .map(|substitution| substitution.name.as_str())
            .collect();
        for index in config_key_order(&keys) {
            let name = keys[index];
            if !held.contains(name) {
                if is_held(name) {
                    return Err(FrontError::NotYet(
                        "a substitution for a name TLC's tables may order otherwise".to_owned(),
                    ));
                }
                return Err(FrontError::Config(format!(
                    "In the configuration file, the identifier {name} does not appear in the specification."
                )));
            }
        }
        deferred_arity_error = linked_root
            .constants
            .iter()
            .find_map(|constant| constant_arity_error(&constant.name, target_of(&constant.name)?));
    }
    for declaration in &linked_root.constants {
        if let Some(item) = config
            .substitutions
            .iter()
            .rev()
            .find(|item| item.module.is_none() && item.name == *declaration.name)
        {
            for key in get_scoped_keys(&item.name, None) {
                operator_objects.substitute(
                    &key,
                    &Rc::from(item.name.as_str()),
                    &item.target,
                    Some(declaration),
                );
            }
        }
    }
    for item in config.substitutions.iter().filter(|item| {
        item.module.is_none() && !declared_constants.iter().any(|name| **name == item.name)
    }) {
        for key in get_scoped_keys(&item.name, None) {
            operator_objects.substitute(&key, &Rc::from(item.name.as_str()), &item.target, None);
        }
    }
    let scoped_modules: Vec<&str> = config
        .substitutions
        .iter()
        .filter_map(|substitution| substitution.module.as_deref())
        .collect();
    // The scoped substitutions whose target TLC's `defns` holds as a Java method.
    let mut method_arity_mismatches: FastSet<(Name, Name)> = FastSet::default();
    // Those whose target the configuration gives a value, which the method replaces in `defns`.
    let mut method_values: FastSet<(Name, Name)> = FastSet::default();
    if !scoped_modules.is_empty() {
        let order = TlcOrder::new(options.source, options.load_module, options.version)?;
        for module in &external_modules {
            let mut overrides: OrderedMap<&str, &str> = OrderedMap::new();
            for substitution in config
                .substitutions
                .iter()
                .filter(|item| item.module.as_deref() == Some(&**module))
            {
                overrides.insert(&substitution.name, &substitution.target);
            }
            if overrides.is_empty() {
                continue;
            }
            let symbols = get_scoped_symbols(module).expect("a scoped module");
            let mut checked = FastSet::default();
            for name in order.get_visible_definition_order(Some(module))? {
                let Some(target) = overrides.get(&*name) else {
                    continue;
                };
                if overrides.contains_key(*target) {
                    return Err(FrontError::Config(format!(
                        "In the configuration file, the identifier {target} appears\non the right-hand side of a <- after already appearing on the\nleft-hand side of one."
                    )));
                }
                let target_key = get_root_key(target);
                let definition = definitions.get(&target_key);
                let is_defined = definition.is_some()
                    || builtins.contains_key(&target_key)
                    || constants.contains_key(&target_key)
                    || declared_constants
                        .iter()
                        .any(|constant| &**constant == *target);
                if !is_defined || linked_root.facts.contains(*target) {
                    return Err(FrontError::Config(format!(
                        "The configuration file substitutes for {name} with the undefined identifier {target}."
                    )));
                }
                let is_global_value = config.constants.iter().any(|assignment| {
                    assignment.module.is_none() && get_root_key(&assignment.name) == target_key
                });
                let target_arity = linked_root
                    .visible
                    .get(*target)
                    .filter(|symbol| symbol.kind == SymbolKind::Definition)
                    .map(|symbol| symbol.arity);
                // `processSpec` checks the arity only where `defns` holds an OpDefNode for the
                // target. For an operator `processModuleOverrides` replaced with a Java method it
                // holds the MethodValue, which the LHS's body takes as it is; applying it then
                // fails in the method (EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, 2154), which
                // isn't modelled, so such an LHS declines where it is applied. A global
                // substitution for the target already put the value of its own RHS in `defns`.
                let defns_key = substitutions.get(&target_key).unwrap_or(&target_key);
                let is_method =
                    closed_java_methods.contains(defns_key) || java_keys.contains(defns_key);
                // `processModuleOverrides` puts the method in `defns` after the configuration's
                // value for the target, so the LHS takes the method then too.
                let is_method_value = is_global_value && is_method && *defns_key == target_key;
                let is_mismatch = target_arity.is_some_and(|target_arity| {
                    symbols
                        .get(&name)
                        .is_some_and(|symbol| symbol.arity != target_arity)
                });
                if is_mismatch && (is_method_value || !is_global_value) {
                    if !is_method {
                        return Err(FrontError::Config(format!(
                            "The configuration file substitutes for {name} with {target} of different number of arguments."
                        )));
                    }
                    method_arity_mismatches.insert((Rc::clone(module), name.clone()));
                } else if is_method_value {
                    if closed_java_methods.contains(&target_key) {
                        method_values.insert((Rc::clone(module), name.clone()));
                    } else {
                        method_arity_mismatches.insert((Rc::clone(module), name.clone()));
                    }
                }
                checked.insert(name);
            }
            let keys: Vec<&str> = overrides.keys().copied().collect();
            for index in config_key_order(&keys) {
                let name = keys[index];
                if !checked.contains(name) {
                    return Err(FrontError::Config(format!(
                        "In the configuration file, the identifier {name} does not appear in the specification."
                    )));
                }
            }
        }
        for index in config_key_order(&scoped_modules) {
            let module = scoped_modules[index];
            if get_scoped_symbols(module).is_none() {
                return Err(FrontError::Config(format!(
                    "In the configuration file, the module name {module} is not a module in the specification."
                )));
            }
        }
    }
    if let Some(error) = deferred_arity_error {
        return Err(error);
    }
    // `processConfig` looks each name of the configuration's other sections up in `defns`,
    // which holds no THEOREM or ASSUME name, and reports it as not defined, in an order the
    // front end doesn't follow from here.
    let names_fact = config
        .init
        .iter()
        .chain(&config.next)
        .chain(&config.specification)
        .chain(&config.invariants)
        .chain(&config.properties)
        .chain(&config.constraints)
        .chain(&config.action_constraints)
        .chain(&config.symmetry)
        .chain(&config.view)
        .chain(&config.alias)
        .chain(&config.postconditions)
        .chain(&config.possible)
        .chain(&config.periodic)
        .chain(&config.rl_reward)
        .any(|name| linked_root.facts.contains(name.as_str()));
    if names_fact {
        return Err(FrontError::NotYet(
            "a configuration entry that names a THEOREM or an ASSUME".to_owned(),
        ));
    }
    let global_assigned_keys: FastSet<Name> = config
        .constants
        .iter()
        .filter(|assignment| assignment.module.is_none())
        .flat_map(|assignment| get_scoped_keys(&assignment.name, None))
        .collect();
    let methods: Vec<_> = substitutions
        .iter()
        .filter(|(_, target)| {
            global_assigned_keys.contains(*target) && closed_java_methods.contains(*target)
        })
        .filter_map(|(name, target)| {
            original_builtins
                .get(target)
                .map(|builtin| (name.clone(), target.clone(), builtin.clone()))
        })
        .collect();
    for (name, target, mut method) in methods {
        let snapshot: Name = Rc::from(format!("\0configuration-defns:{target}"));
        method.intrinsic = Some(Intrinsic::DefnsBuiltin);
        builtins.insert(snapshot.clone(), method);
        if let Some(opcode) = original_json_source_opcodes.get(&target) {
            json_source_opcodes
                .borrow_mut()
                .insert(snapshot.clone(), *opcode);
        }
        substitutions.insert(name, snapshot);
    }
    let globals = substitutions.clone();
    let mut scoped: Vec<_> = config
        .substitutions
        .iter()
        .filter(|item| item.module.is_some())
        .collect();
    scoped.sort_by_key(|item| module_rank(item.module.as_deref()));
    let global_value_keys: FastSet<Name> = config
        .constants
        .iter()
        .filter(|item| item.module.is_none())
        .flat_map(|item| get_scoped_keys(&item.name, None))
        .collect();
    // Global entries replace operator nodes; scoped entries replace their expression bodies.
    // TLC casts an aliased body's replacement to Value, so only an operator replacement fails.
    let mut body_values: FastMap<Name, ConfigValue> = FastMap::default();
    let mut body_operators: FastMap<Name, Name> = FastMap::default();
    let mut scoped_values: Vec<_> = config
        .constants
        .iter()
        .filter(|item| {
            item.module.is_some()
                && item.args.is_none()
                && !java_replaces_scoped_assignment(&item.name, item.module.as_deref())
        })
        .collect();
    scoped_values.sort_by_key(|item| module_rank(item.module.as_deref()));
    for assignment in scoped_values {
        for key in get_scoped_keys(&assignment.name, assignment.module.as_deref()) {
            if !global_keys.contains(&key) && !hidden_scoped_keys.contains(&key) {
                body_values.insert(key, assignment.value.clone());
            }
        }
    }
    // The definitions a module-scoped entry with arguments gives a table (`A(0) = [M] 7`).
    // TLC sets the table on the body the definition holds, and an INSTANCE with substitutions
    // copies the definition into a node whose body is a `SubstInNode` over that body. A name
    // that reads the copy finds the table and applies it (`lookup`), as the front end's alias
    // does, but a substitution's `evalAppl` evaluates the copy's body: a literal returns the
    // table as its value (`Tool.evalImpl`'s NumeralKind) and another body ignores it, which the
    // alias doesn't follow.
    let scoped_table_keys: FastSet<Name> = config
        .constants
        .iter()
        .filter(|item| {
            item.module.is_some()
                && item.args.is_some()
                && !java_replaces_scoped_assignment(&item.name, item.module.as_deref())
        })
        .flat_map(|item| get_scoped_keys(&item.name, item.module.as_deref()))
        .filter(|key| !global_keys.contains(key) && !hidden_scoped_keys.contains(key))
        .collect();
    // Where nothing TLC evaluates reads the substituted name, nor the configuration, and the
    // copy's body has no effect, the value the substitution gives it shows nowhere:
    // `processConstantDefns` computes it as it starts, swallowing a failure, and drops it.
    let is_table_copy_shown = |substitution: &crate::config::Substitution, target: &Name| {
        let keys: FastSet<Name> =
            get_scoped_keys(&substitution.name, substitution.module.as_deref())
                .into_iter()
                .collect();
        let is_named =
            |named: &str| keys.iter().any(|key| **key == *named) || named == substitution.name;
        if crate::lower::is_read_by_config(config, &is_named)
            || config
                .constants
                .iter()
                .any(|assignment| is_named(&assignment.name))
            || config.substitutions.iter().any(|other| {
                is_named(&get_root_key(&other.target))
                    || (!std::ptr::eq(other, substitution) && is_named(&other.name))
            }) || !definitions.get(target).is_some_and(|definition| {
            // `:>` and `@@` build functions, with no effect.
            matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && is_without_effects_but(&definitions, &definition.body, &[":>", "@@"])
        }) {
            return true;
        }
        let is_plain = |name: &Name| {
            !config.substitutions.iter().any(|substitution| {
                get_scoped_keys(&substitution.name, substitution.module.as_deref()).contains(name)
            }) && !config.constants.iter().any(|assignment| {
                get_scoped_keys(&assignment.name, assignment.module.as_deref()).contains(name)
            }) && !builtin_keys.contains(name)
                && !java_keys.contains(name)
                && !closed_java_methods.contains(name)
        };
        let mut assumptions = Vec::new();
        add_assumptions(&linked_root, &mut Vec::new(), &mut assumptions);
        // A definition of no parameters TLC computes as it starts and drops, whose value nothing
        // else names, the configuration doesn't read, and whose body has no effect, prints no
        // warning (EXCEPT) and names no INSTANCE, shows nothing of what it reads
        // (`processConstantDefns` swallows a failure): its body is no root (`Unused == K`).
        let written = get_written_names(
            definitions
                .values()
                .flat_map(|definition| {
                    let bounds = match &definition.kind {
                        DefinitionKind::Function { bounds } => bounds.as_slice(),
                        DefinitionKind::Operator { .. } => &[],
                    };
                    bounds
                        .iter()
                        .map(|bound| bound.set.clone())
                        .chain([definition.body.clone()])
                        .collect::<Vec<Expr>>()
                })
                .chain(
                    assumptions
                        .iter()
                        .map(|assumption| assumption.expression.clone()),
                ),
        );
        // Builtins whose application shows nothing as TLC computes such a definition as it
        // starts: ToString, TLCEval, `:>` and `@@` compute a value; TLCGet has a minimum level
        // of 1, so that TLC doesn't compute the definition then; and TLCSet, which sets a
        // register through the checker or the simulator, neither of which is there yet, fails
        // (`TLCGetSet.TLCSet`), which `processConstantDefns` swallows.
        let allowed: Vec<&str> = keys
            .iter()
            .map(|key| &**key)
            .chain(["ToString", "TLCEval", "TLCGet", "TLCSet", ":>", "@@"])
            .collect();
        // A configuration's `Foo <- Unused` binds Foo to the definition, which shows nothing
        // where nothing reads Foo either, as a global substitution of a name nothing writes.
        let is_unread_substitute = |substitution: &crate::config::Substitution| {
            let name = &*substitution.name;
            substitution.module.is_none()
                && written
                    .as_ref()
                    .is_some_and(|written| written.get(name).copied().unwrap_or(0) == 0)
                && !crate::lower::is_read_by_config(config, &|named: &str| named == name)
                && !config
                    .constants
                    .iter()
                    .any(|assignment| &*assignment.name == name)
                && config.substitutions.iter().all(|other| {
                    std::ptr::eq(other, substitution)
                        || (&*other.name != name && &*get_root_key(&other.target) != name)
                })
        };
        let is_unread = |key: &Name, definition: &Rc<Definition>| {
            let names = [key.clone(), definition.name.clone()];
            let is_named_here = |named: &str| names.iter().any(|name| **name == *named);
            matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                && written.as_ref().is_some_and(|written| {
                    names.iter().all(|name| {
                        written.get(name).copied().unwrap_or(0)
                            <= usize::from(writes_name(&definition.body, name))
                    })
                })
                && !crate::lower::is_read_by_config(config, &is_named_here)
                && !config
                    .constants
                    .iter()
                    .any(|assignment| is_named_here(&assignment.name))
                && !config.substitutions.iter().any(|other| {
                    is_named_here(&other.name)
                        || (is_named_here(&get_root_key(&other.target))
                            && !is_unread_substitute(other))
                })
                && is_without_effects_but(&definitions, &definition.body, &allowed)
                && !writes_except(&definitions, &definition.body)
        };
        let roots: Vec<Expr> = definitions
            .iter()
            .filter(|(key, definition)| !is_unread(key, definition))
            .map(|(_, definition)| definition)
            .flat_map(|definition| {
                let bounds = match &definition.kind {
                    DefinitionKind::Function { bounds } => bounds.as_slice(),
                    DefinitionKind::Operator { .. } => &[],
                };
                bounds
                    .iter()
                    .map(|bound| bound.set.clone())
                    .chain([definition.body.clone()])
                    .collect::<Vec<Expr>>()
            })
            .chain(
                assumptions
                    .iter()
                    .map(|assumption| assumption.expression.clone()),
            )
            .chain(
                linker
                    .link_order
                    .borrow()
                    .iter()
                    .flat_map(|linked| linked.module.instances.clone())
                    .chain(root.instances.iter().cloned())
                    .flat_map(|instance| {
                        instance
                            .substitutions
                            .iter()
                            .map(|substitution| substitution.expression.clone())
                            .collect::<Vec<Expr>>()
                    }),
            )
            .collect();
        references_shown(&roots, &keys, &definitions, &is_plain)
    };
    let unshown_table_copies: Vec<*const crate::config::Substitution> = config
        .substitutions
        .iter()
        .filter(|substitution| {
            let target = get_root_key(&substitution.target);
            let target = match substitution.module {
                Some(_) => globals.get(&target).cloned().unwrap_or(target),
                None => target,
            };
            !is_table_copy_shown(substitution, &target)
        })
        .map(|substitution| substitution as *const _)
        .collect();
    let decline_table_copy = |substitution: &crate::config::Substitution,
                              target: &Name|
     -> Result<()> {
        if !scoped_table_keys.contains(target)
            && is_copy_of_any(&linker.copy_sources.borrow(), target, &|key| {
                scoped_table_keys.contains(key)
            })
            && !unshown_table_copies.contains(&(substitution as *const _))
        {
            return Err(FrontError::NotYet(
                "a substitution whose target is an INSTANCE's copy of a definition with a module-scoped table"
                    .to_owned(),
            ));
        }
        Ok(())
    };
    let get_scoped_entry = |substitution: &crate::config::Substitution| -> (Name, Name) {
        (
            Rc::from(substitution.module.as_deref().unwrap_or_default()),
            Rc::from(substitution.name.as_str()),
        )
    };
    for substitution in &scoped {
        let target = get_root_key(&substitution.target);
        let target = globals.get(&target).cloned().unwrap_or(target);
        let entry = get_scoped_entry(substitution);
        let value = (global_value_keys.contains(&target)
            && !method_values.contains(&entry)
            && !method_arity_mismatches.contains(&entry))
        .then(|| {
            constants
                .get(&target)
                .or_else(|| operator_constants.get(&target))
                .cloned()
        })
        .flatten();
        for key in get_scoped_keys(&substitution.name, substitution.module.as_deref()) {
            if global_keys.contains(&key) {
                continue;
            }
            if let Some(value) = &value {
                body_operators.remove(&key);
                body_values.insert(key, value.clone());
            } else {
                body_values.remove(&key);
                if global_value_keys.contains(&target) {
                    body_operators.remove(&key);
                } else {
                    body_operators.insert(key, target.clone());
                }
            }
        }
    }
    // A module-scoped substitution `T <- [M] S` sets S's node on T's body, which only a
    // reference to T reads (`lookup`). Where the configuration substitutes T for another name
    // (`J <- T`), that name's `evalAppl` evaluates T's body as written, which a numeral, a
    // decimal or a string fails to cast (`Tool.evalImpl`'s NumeralKind) and an OpApplNode
    // ignores. Where T has such a body, no parameters and no other entry, no copy, and nothing
    // TLC evaluates names T (but the configuration, whose selections take `def.getBody()`), the
    // substitution shows nowhere: `processConstantDefns` computes S through T as it starts,
    // which shows nothing where S has no effect, and every evaluation of T reads its body.
    let inert_targets: FastSet<Name> = {
        let targets: FastSet<Name> = config
            .substitutions
            .iter()
            .filter(|substitution| {
                substitution.module.is_none()
                    || get_scoped_keys(&substitution.name, substitution.module.as_deref())
                        .iter()
                        .any(|key| !global_keys.contains(key))
            })
            .map(|substitution| get_root_key(&substitution.target))
            .filter(|target| body_operators.contains_key(target))
            .collect();
        if targets.is_empty() {
            FastSet::default()
        } else {
            let mut assumptions = Vec::new();
            add_assumptions(&linked_root, &mut Vec::new(), &mut assumptions);
            let roots: Vec<Expr> = definitions
                .values()
                .flat_map(|definition| {
                    let bounds = match &definition.kind {
                        DefinitionKind::Function { bounds } => bounds.as_slice(),
                        DefinitionKind::Operator { .. } => &[],
                    };
                    bounds
                        .iter()
                        .map(|bound| bound.set.clone())
                        .chain([definition.body.clone()])
                        .collect::<Vec<Expr>>()
                })
                .chain(
                    assumptions
                        .iter()
                        .map(|assumption| assumption.expression.clone()),
                )
                .chain(
                    linker
                        .link_order
                        .borrow()
                        .iter()
                        .flat_map(|linked| linked.module.instances.clone())
                        .chain(root.instances.iter().cloned())
                        .flat_map(|instance| {
                            instance
                                .substitutions
                                .iter()
                                .map(|substitution| substitution.expression.clone())
                                .collect::<Vec<Expr>>()
                        }),
                )
                .collect();
            let copy_sources = linker.copy_sources.borrow();
            let let_copy_sources = linker.let_copy_sources.borrow();
            targets
                .into_iter()
                .filter(|target| {
                    let Some(definition) = definitions.get(target) else {
                        return false;
                    };
                    let is_plain_body = matches!(
                        &definition.kind,
                        DefinitionKind::Operator { params, .. } if params.is_empty()
                    ) && is_state_level_through(&definitions, &definition.body)
                        && !matches!(
                        definition.body.kind,
                        ExpressionKind::Number { .. }
                            | ExpressionKind::Decimal { .. }
                            | ExpressionKind::String { .. }
                    );
                    let entries = config
                        .substitutions
                        .iter()
                        .filter(|substitution| substitution.module.is_some())
                        .filter(|substitution| {
                            get_scoped_keys(&substitution.name, substitution.module.as_deref())
                                .contains(target)
                        })
                        .count();
                    let has_value = config.constants.iter().any(|assignment| {
                        get_scoped_keys(&assignment.name, assignment.module.as_deref())
                            .contains(target)
                    });
                    let is_copied = copy_sources
                        .keys()
                        .chain(let_copy_sources.keys())
                        .any(|key| {
                            get_copy_target(
                                &copy_sources,
                                &let_copy_sources,
                                key,
                                0,
                                &[target.clone()].into_iter().collect(),
                            )
                            .is_some()
                        });
                    // An S with effects shows them once, as its own definition computed as TLC
                    // starts, only where TLC computes T before the root module's loop over its
                    // definitions meets T, which otherwise follows T's body to S and computes S
                    // again where S came first (`B == PrintT(7)` before `K == x = 0` prints 7
                    // twice): T a boolean literal of the root module, which the loop of the
                    // module J's entry is in (one TLC processes before the root module) or the
                    // loop over the root's constants (J a declared constant) computes first.
                    let is_computed_first = matches!(
                        &definition.body.kind,
                        ExpressionKind::Identifier { name, .. } if matches!(&**name, "TRUE" | "FALSE")
                    ) && linked_root
                        .visible
                        .get(&**target)
                        .is_some_and(|symbol| symbol.key == *target)
                        && config
                            .substitutions
                            .iter()
                            .filter(|substitution| get_root_key(&substitution.target) == *target)
                            .all(|substitution| match &substitution.module {
                                Some(module) => **module != *linked_root.module.name,
                                None => linked_root
                                    .constants
                                    .iter()
                                    .any(|constant| *constant.name == *substitution.name),
                            });
                    let is_pure_substitute = body_operators
                        .get(target)
                        .and_then(|substitute| definitions.get(substitute))
                        .is_some_and(|substitute| {
                            is_state_level_through(&definitions, &substitute.body)
                                && (is_computed_first
                                    || is_without_effects_reading(
                                        &definitions,
                                        &substitute.body,
                                        &linked_root.variables,
                                    ))
                                && matches!(
                                    &substitute.kind,
                                    DefinitionKind::Operator { params, .. } if params.is_empty()
                                )
                        });
                    is_plain_body
                        && entries == 1
                        && !has_value
                        && !is_copied
                        && is_pure_substitute
                        && !references_key(&roots, target)
                })
                .collect()
        }
    };
    for target in &inert_targets {
        body_operators.remove(target);
    }
    for substitution in config
        .substitutions
        .iter()
        .filter(|item| item.module.is_none())
    {
        let target = get_root_key(&substitution.target);
        decline_table_copy(substitution, &target)?;
        if is_copy_of_any(&linker.copy_sources.borrow(), &target, &|key| {
            body_operators.contains_key(key)
        }) {
            return Err(FrontError::NotYet(
                "a global override whose target has a module-scoped override".to_owned(),
            ));
        }
        // Only a literal body reads the entry through the substitution (`Tool.evalImpl`).
        if let Some(value) = body_values
            .get(&target)
            .filter(|_| !body_read_targets.contains(&target))
        {
            for key in get_scoped_keys(&substitution.name, None) {
                let arity = get_key_arity(&definitions, &key);
                substitutions.remove(&key);
                if arity == 0 {
                    constants.insert(key, value.clone());
                } else {
                    builtins.insert(
                        key.clone(),
                        Builtin {
                            intrinsic: None,
                            name: key.clone(),
                            arity,
                            flags: BUILTIN_LAZY,
                            table: None,
                        },
                    );
                    definitions.remove(&key);
                    operator_keys.insert(key.clone());
                    operator_constants.insert(key, value.clone());
                }
            }
        }
    }
    // The definitions whose body TLC evaluates other than a reference to them reads.
    let mut body_evaluated_keys: FastMap<Name, (bool, Name)> = FastMap::default();
    for substitution in scoped {
        let target = get_root_key(&substitution.target);
        let target = globals.get(&target).cloned().unwrap_or(target);
        let entry = get_scoped_entry(substitution);
        let is_method_mismatch = method_arity_mismatches.contains(&entry);
        // The target's Java method, as the global entries' snapshot of `defns` holds it.
        let method = method_values
            .contains(&entry)
            .then(|| original_builtins.get(&target).cloned())
            .flatten()
            .map(|mut method| {
                let snapshot: Name = Rc::from(format!("\0configuration-defns:{target}"));
                method.intrinsic = Some(Intrinsic::DefnsBuiltin);
                builtins.insert(snapshot.clone(), method);
                if let Some(opcode) = original_json_source_opcodes.get(&target) {
                    json_source_opcodes
                        .borrow_mut()
                        .insert(snapshot.clone(), *opcode);
                }
                snapshot
            });
        for key in get_scoped_keys(&substitution.name, substitution.module.as_deref()) {
            if global_keys.contains(&key) || inert_targets.contains(&key) {
                continue;
            }
            decline_table_copy(substitution, &target)?;
            json_source_opcodes.borrow_mut().remove(&key);
            let had_entry = constants.remove(&key).is_some()
                | operator_constants.remove(&key).is_some()
                | substitutions.remove(&key).is_some();
            // TLC sets the substitute on the definition's body (`opDefs[j].getBody()
            // .setToolObject`), which a reference to the definition reads (`lookup`), but where
            // TLC evaluates the body itself, as of a name the configuration selects or
            // substitutes for another (`def.getBody()`, `evalAppl` of the OpDefNode a name
            // holds), an OpApplNode body ignores it and a numeral, a decimal or a string body
            // returns it as its value (`Tool.evalImpl`'s `NumeralKind`), which, but a Value,
            // fails with an unexpected ClassCastException.
            let is_literal = definitions.get(&key).is_some_and(|definition| {
                matches!(
                    definition.body.kind,
                    ExpressionKind::Number { .. }
                        | ExpressionKind::Decimal { .. }
                        | ExpressionKind::String { .. }
                )
            });
            // A Value `defns` holds for the substitute: an assigned one, a Java method or a
            // builtin's value.
            let gives_value = method.is_some()
                || global_value_keys.contains(&target)
                || body_values.contains_key(&target)
                || !definitions.contains_key(&target);
            if !(is_literal && gives_value) {
                // Only an OpApplNode body without another entry and without parameters, which
                // TLC evaluates as written, the front end can read unsubstituted.
                let is_plain = !is_literal
                    && !had_entry
                    && !is_method_mismatch
                    && get_key_arity(&definitions, &key) == 0;
                body_evaluated_keys.insert(key.clone(), (is_plain, target.clone()));
            }
            if is_method_mismatch {
                builtins.insert(
                    key.clone(),
                    Builtin {
                        intrinsic: None,
                        name: key.clone(),
                        arity: get_key_arity(&definitions, &key),
                        flags: tla_ir::Builtin::DECLINED as u32,
                        table: None,
                    },
                );
                definitions.remove(&key);
                operator_keys.insert(key.clone());
                continue;
            }
            if let Some(method) = &method {
                substitutions.insert(key, method.clone());
                continue;
            }
            let value = if global_value_keys.contains(&target) {
                constants
                    .get(&target)
                    .or_else(|| operator_constants.get(&target))
            } else {
                body_values.get(&target)
            };
            if let Some(value) = value.cloned() {
                let arity = get_key_arity(&definitions, &key);
                if arity == 0 {
                    constants.insert(key, value);
                } else {
                    builtins.insert(
                        key.clone(),
                        Builtin {
                            intrinsic: None,
                            name: key.clone(),
                            arity,
                            flags: BUILTIN_LAZY,
                            table: None,
                        },
                    );
                    definitions.remove(&key);
                    operator_keys.insert(key.clone());
                    operator_constants.insert(key, value);
                }
            } else {
                if is_copy_of_any(&linker.copy_sources.borrow(), &target, &|key| {
                    body_operators.contains_key(key)
                }) {
                    return Err(FrontError::NotYet(
                        "a scoped override whose target has a module-scoped override".to_owned(),
                    ));
                }
                substitutions.insert(key, target.clone());
            }
        }
    }
    // TLC sets a module-scoped entry on the body of the module's definition, which every
    // instance of the module shares.
    let scoped_keys: FastSet<Name> = config
        .constants
        .iter()
        .filter(|item| !java_replaces_scoped_assignment(&item.name, item.module.as_deref()))
        .filter_map(|item| item.module.as_deref().map(|module| (&item.name, module)))
        .chain(
            config
                .substitutions
                .iter()
                .filter_map(|item| item.module.as_deref().map(|module| (&item.name, module))),
        )
        .flat_map(|(name, module)| get_scoped_keys(name, Some(module)))
        .filter(|key| !hidden_scoped_keys.contains(key))
        .collect();
    let copy_sources = linker.copy_sources.take();
    // TLC gives a module-scoped entry's value to the body the definition holds
    // (`SpecProcessor.processConstantDefns`), which the copies an INSTANCE in a LET makes share:
    // those copies read the definition.
    {
        let let_copy_sources = linker.let_copy_sources.borrow();
        let read: FastSet<Name> = (let_copy_sources.values())
            .filter_map(|(source, prefix)| {
                get_copy_target(
                    &copy_sources,
                    &let_copy_sources,
                    source,
                    *prefix,
                    &scoped_keys,
                )
            })
            .map(|(target, _)| target)
            .collect();
        // A substitution's operator is what TLC sets on the body, which the copy reads where
        // it fails with the cast of an `OpDefNode` to a `Value`.
        if read.iter().any(|key| body_operators.contains_key(key)) {
            return Err(FrontError::NotYet(
                "a module-scoped substitution for a definition an INSTANCE in a LET copies".into(),
            ));
        }
        if read != linker.let_aliased_keys {
            *wanted_let_aliases.borrow_mut() = Some(read);
            return Err(FrontError::NotYet(
                "a module-scoped configuration entry for a module an INSTANCE in a LET copies"
                    .into(),
            ));
        }
    }
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
        // TLC sets the entry on the definition's body (`setToolObject`), which the application
        // reads in place of the body, so that its call stack holds no frame of the body: the
        // alias's application has no range.
        let unranged = Location {
            range: None,
            ..definition.location.clone()
        };
        let alias = create_local_alias_at(
            key.clone(),
            target,
            params.clone(),
            params.get(skipped..).unwrap_or(&[]),
            &definition.location,
            &unranged,
        );
        definitions.insert(key.clone(), alias.clone());
        // An INSTANCE with substitutions makes the copy's body a `SubstInNode`, which TLC's
        // `lookup` reads through to the entry, so that `getActionsAppl` splits the copy's
        // application as the application of the substitute, named after it: the copy is no
        // action of the instance's.
        linker.instance_actions.borrow_mut().remove(key);
        for (name, symbol) in linked_root.visible.iter() {
            if symbol.key == *key && name != key {
                definitions.insert(name.clone(), alias.clone());
            }
        }
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
    let instantiated: FastSet<Name> = linker
        .link_order
        .borrow()
        .iter()
        .flat_map(|linked| {
            linked
                .module
                .instances
                .iter()
                .map(|instance| instance.module.clone())
        })
        .collect();
    for linked in linker.link_order.borrow().iter().filter(|linked| {
        !instantiated.contains(&linked.module.name)
            || (linked.constants.is_empty() && linked.variables.is_empty())
    }) {
        for declaration in &linked.constants {
            if linked_root
                .constants
                .iter()
                .any(|root| Rc::ptr_eq(root, declaration))
            {
                operator_objects.initialize_declaration(declaration);
            }
        }
    }
    let (startup_definitions, startup_inner_siblings, instanced_definitions, startup_repeats) =
        if options.is_unconfigured {
            Default::default()
        } else {
            get_startup_definitions(&linker, &linked_root, &definitions, options)?
        };
    let mut assumptions = Vec::new();
    add_assumptions(&linked_root, &mut Vec::new(), &mut assumptions);
    let modules: Vec<Rc<Module>> = linker
        .link_order
        .borrow()
        .iter()
        .map(|linked| linked.module.clone())
        .collect();
    let uninitialized_literals = uninitialized_instance_literals(
        &modules,
        &definitions,
        &pre_override_definitions,
        &linker.tables,
    );
    let mut module_texts: FastMap<Name, Option<Rc<str>>> = FastMap::default();
    for (text, module) in linker.texts.borrow().iter() {
        let text: Rc<str> = Rc::from(text.as_str());
        let mut pending = vec![module.clone()];
        while let Some(module) = pending.pop() {
            pending.extend(module.modules.iter().cloned());
            module_texts
                .entry(module.name.clone())
                .and_modify(|known| {
                    if known.as_deref() != Some(&*text) {
                        *known = None;
                    }
                })
                .or_insert_with(|| Some(text.clone()));
        }
    }
    let mut environment = Environment {
        scoped_target_checks,
        module_texts,
        startup_definitions,
        startup_repeats,
        startup_inner_siblings,
        instanced_definitions,
        operator_objects,
        // A file of the user's that replaces a module whose Java class TLC binds to it holds the
        // definitions the standard shortcuts read in its place.
        standard_shortcut_modules: linker
            .standard_exports
            .borrow()
            .keys()
            .cloned()
            .chain(linker.user_replaced_modules.borrow().iter().cloned())
            .collect(),
        json_source_opcodes: json_source_opcodes.into_inner(),
        pinned_standard_sources: false,
        assumptions,
        tables: linker.tables.clone(),
        definitions,
        pre_override_headers,
        builtins,
        substitutions,
        configured_value_bindings,
        config_opdef_headers,
        substitutes_for_definitions: config
            .substitutions
            .iter()
            .filter(|substitution| {
                substitution.module.is_some()
                    || !(declared_constants.iter()).any(|constant| **constant == *substitution.name)
            })
            .map(|substitution| Rc::from(substitution.target.as_str()))
            .collect(),
        constants,
        operator_constants,
        variables,
        variable_locations: linked_root.variable_locations.clone(),
        variable_index,
        root_constants: linked_root.constants.clone(),
        root_symbols: linked_root.visible.clone(),
        substituted_definitions: linker.substituted_definitions.take(),
        nested_substitutions: linker.nested_substitutions.take(),
        nested_let_copies: linker.nested_let_copies.take(),
        instance_actions: linker.instance_actions.take(),
        instance_names: linker.instance_names.take(),
        printed,
        java_overrides: linker.java_overrides.take(),
        has_java_override_index: options
            .origin
            .is_none_or(|origin| !origin.has_closed_override_index()),
        modules,
        uninitialized_literals,
        missing_operator_bodies: linker.missing_operator_bodies.take(),
        scoped_selected_values,
        is_scoped_selection_kept: false,
        is_scoped_selection_let_instanced: false,
    };
    reject_class_overrides(&environment, &root, config, options.version)?;
    reject_index_builtins(&environment, config, &index_builtins)?;
    check_body_evaluated_keys(&mut environment, config, &body_evaluated_keys)?;
    if is_copy_scoped {
        return Err(FrontError::NotYet(
            "a module-scoped configuration value of a definition an unnamed INSTANCE copies under a name the configuration selects".to_owned(),
        ));
    }
    if is_copy_substituted {
        return Err(FrontError::NotYet(
            "a module-scoped substitution of a definition an unnamed INSTANCE copies under a name the configuration selects".to_owned(),
        ));
    }
    match check_selected_scoped_values(&environment, config, &selected_scoped_keys)? {
        ScopedSelection::Kept { is_let_instanced } => {
            environment.is_scoped_selection_kept = true;
            environment.is_scoped_selection_let_instanced = is_let_instanced;
        }
        ScopedSelection::Dropped { is_applied } => {
            let mut renamed: FastMap<Name, Name> = FastMap::default();
            for key in &selected_scoped_keys {
                let Some(value) = environment.constants.get(key).cloned() else {
                    continue;
                };
                environment.constants.remove(key);
                if is_applied {
                    let applied: Name = Rc::from(format!("{key}#scoped"));
                    environment.constants.insert(applied.clone(), value);
                    renamed.insert(key.clone(), applied);
                }
            }
            if !renamed.is_empty() {
                let mut visited = FastSet::default();
                for definition in environment
                    .definitions
                    .values()
                    .chain(&environment.startup_definitions)
                {
                    for expression in get_definition_expressions(definition) {
                        rename_applications(&expression, &renamed, &mut visited);
                    }
                }
                for assumption in &environment.assumptions {
                    rename_applications(&assumption.expression, &renamed, &mut visited);
                }
            }
        }
    }
    Ok(environment)
}

/// A scoped `K = [M] v` for a definition K without parameters that INIT, NEXT, an INVARIANT, a
/// PROPERTY or a (ACTION_)CONSTRAINT names. `SpecProcessor.processSpec` makes v the tool object
/// of K's body (`getBody().setToolObject`), not of K's node, and leaves `defns` alone. Only
/// `SymbolNodeValueLookupProvider.lookup` reads that, for an application of K (or of a copy an
/// INSTANCE makes, whose SubstInNode body it reads through), and `Tool.eval` for a body that is
/// a numeral, decimal or string literal. `processConfigSpec`, `processConfigInvariants`,
/// `processConfigProps` and `processConstraints` take K's body from `defns` and walk it as
/// written. `processConstantDefns` skips K, as `lookup` gives v rather than K's node, so TLC
/// doesn't compute a K of constant level before the search either.
///
/// The environment leaves the values out of K's keys where nothing else reads v, and gives them
/// keys of their own where an application of K reads v (`ScopedSelection::Dropped`). Where an
/// application of a copy an INSTANCE of K's module makes may read v, it keeps them
/// (`ScopedSelection::Kept`): a selector then reads a K above constant level by its definition,
/// which the front end keys apart from the name the configuration gives, and
/// `check_scoped_selection` (`spec.rs`) declines most K of constant level. It declines a K the
/// root module defines then, whose key is the name, and a K whose name another part of the
/// configuration reads.
fn check_selected_scoped_values(
    environment: &Environment,
    config: &ModelConfig,
    keys: &[Name],
) -> Result<ScopedSelection> {
    const REASON: &str = "a module-scoped configuration value of a definition the configuration also selects, where TLC may read the value";
    if keys.is_empty() {
        return Ok(ScopedSelection::Dropped { is_applied: false });
    }
    let names: FastSet<Name> = keys.iter().cloned().collect();
    // The module that defines a key: `Name@Module` for another module's definition, the root's for
    // its own and for the copies INSTANCE makes (`Name@Root#n`, `I!Name`), which no INSTANCE
    // copies again.
    let homes: FastSet<&str> = keys
        .iter()
        .filter(|key| !key.contains('#') && !key.contains('!'))
        .filter_map(|key| key.split_once('@').map(|(_, module)| module))
        .collect();
    // The modules that extend a home, which an INSTANCE of them copies too.
    let mut extending: FastSet<&str> = homes.clone();
    loop {
        let before = extending.len();
        for module in &environment.modules {
            if module
                .extends
                .iter()
                .any(|name| extending.contains(&**name))
            {
                extending.insert(&module.name);
            }
        }
        if extending.len() == before {
            break;
        }
    }
    fn has_let_instance(expression: &Expression, modules: &FastSet<&str>) -> bool {
        if let ExpressionKind::Let {
            instances: Some(instances),
            ..
        } = &expression.kind
            && instances
                .iter()
                .any(|instance| modules.contains(&*instance.module))
        {
            return true;
        }
        expression
            .children()
            .iter()
            .any(|child| has_let_instance(child, modules))
    }
    let is_instanced = !extending.is_empty()
        && environment.modules.iter().any(|module| {
            module
                .instances
                .iter()
                .any(|instance| extending.contains(&*instance.module))
        });
    // A LET's INSTANCE makes copies the definitions don't list, which the LET may apply.
    let is_let_instanced = !extending.is_empty()
        && (environment
            .definitions
            .values()
            .chain(&environment.startup_definitions)
            .flat_map(get_definition_expressions)
            .any(|expression| has_let_instance(&expression, &extending))
            || environment
                .assumptions
                .iter()
                .any(|assumption| has_let_instance(&assumption.expression, &extending)));
    let mentions = |names: &FastSet<Name>| {
        environment
            .definitions
            .values()
            .chain(&environment.startup_definitions)
            .flat_map(get_definition_expressions)
            .any(|expression| mentions_name(&expression, names))
            || environment
                .assumptions
                .iter()
                .any(|assumption| mentions_name(&assumption.expression, names))
    };
    let is_applied = mentions(&names);
    // The copies an INSTANCE may make of K (`I!K`, `K@Root#n`), whose applications read v.
    let copies: FastSet<Name> = environment
        .definitions
        .iter()
        .filter(|(key, definition)| {
            (key.contains('!') || key.contains('#'))
                && keys.iter().any(|selected| {
                    environment.definitions.get(selected).is_some_and(|scoped| {
                        let name = &*scoped.name;
                        *definition.name == *name
                            || key.ends_with(&format!("!{name}"))
                            || key.starts_with(&format!("{name}@"))
                    })
                })
        })
        .map(|(key, _)| key.clone())
        .collect();
    let is_instanced = is_let_instanced || (is_instanced && mentions(&copies));
    let is_named_elsewhere = |name: &str| {
        config
            .substitutions
            .iter()
            .any(|substitution| substitution.name == name || substitution.target == name)
            || config
                .constants
                .iter()
                .any(|assignment| assignment.name == name && assignment.args.is_some())
            || [
                &config.specification,
                &config.symmetry,
                &config.view,
                &config.alias,
                &config.periodic,
                &config.rl_reward,
            ]
            .into_iter()
            .flatten()
            .chain(config.postconditions.iter())
            .chain(config.possible.iter())
            .any(|named| named == name)
    };
    for key in keys {
        let Some(definition) = environment.definitions.get(key) else {
            return Err(FrontError::NotYet(REASON.to_owned()));
        };
        if is_named_elsewhere(&definition.name)
            || is_named_elsewhere(key)
            || (is_instanced && *key == definition.name)
        {
            return Err(FrontError::NotYet(REASON.to_owned()));
        }
    }
    Ok(if is_instanced {
        ScopedSelection::Kept { is_let_instanced }
    } else {
        ScopedSelection::Dropped { is_applied }
    })
}

/// What `check_selected_scoped_values` does with the module-scoped values of the definitions
/// the configuration selects.
enum ScopedSelection {
    /// It keeps them, for the copies an INSTANCE of their module makes, one in a LET or not.
    Kept { is_let_instanced: bool },
    /// It leaves them out of K's key. Where an application of K reads v (`is_applied`), it gives
    /// v a key of its own, which the applications then name.
    Dropped { is_applied: bool },
}

/// The expressions of a definition: its body, and a function definition's sets.
fn get_definition_expressions(definition: &Rc<Definition>) -> Vec<Expr> {
    match &definition.kind {
        DefinitionKind::Function { bounds } => bounds
            .iter()
            .map(|bound| bound.set.clone())
            .chain([definition.body.clone()])
            .collect(),
        DefinitionKind::Operator { .. } => vec![definition.body.clone()],
    }
}

/// Points each application of a key `renamed` holds at the key it maps the key to.
fn rename_applications(
    expression: &Expr,
    renamed: &FastMap<Name, Name>,
    visited: &mut FastSet<usize>,
) {
    if !visited.insert(Rc::as_ptr(expression) as usize) {
        return;
    }
    if matches!(
        expression.kind,
        ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. }
    ) && !expression.is_locally_resolved()
        && let Some(key) = expression.reference()
        && let Some(applied) = renamed.get(&key)
    {
        *expression.resolved.key.borrow_mut() = Some(applied.clone());
    }
    for child in expression.children() {
        rename_applications(&child, renamed, visited);
    }
}

fn uninitialized_instance_literals(
    modules: &[Rc<Module>],
    definitions: &OrderedMap<Name, Rc<Definition>>,
    pre_override_definitions: &[Rc<Definition>],
    tables: &Tables,
) -> FastSet<usize> {
    fn literals(expression: &Expr, into: &mut FastSet<usize>, tables: &Tables) {
        let mut pending = vec![expression.clone()];
        let mut visited = FastSet::default();
        while let Some(node) = pending.pop() {
            if !visited.insert(Rc::as_ptr(&node) as usize) {
                continue;
            }
            if matches!(
                node.kind,
                ExpressionKind::Number { .. } | ExpressionKind::String { .. }
            ) {
                into.insert(Rc::as_ptr(&node) as usize);
            }
            for origin in tables.selection_origins(&node) {
                pending.extend(tables.instance_context(&origin));
            }
            pending.extend(node.children());
        }
    }
    let mut candidates = FastSet::default();
    for module in modules {
        for instance in &module.instances {
            for substitution in &instance.substitutions {
                literals(&substitution.expression, &mut candidates, tables);
            }
        }
    }
    if candidates.is_empty() {
        return candidates;
    }
    let mut initialized = FastSet::default();
    for module in modules {
        for definition in &module.definitions {
            literals(&definition.body, &mut initialized, tables);
        }
        for assumption in &module.assumptions {
            literals(&assumption.expression, &mut initialized, tables);
        }
        for theorem in &module.theorems {
            if let Statement::Expression(body) = &theorem.statement {
                literals(body, &mut initialized, tables);
            }
        }
    }
    for definition in definitions.values() {
        // Imported facts aren't OpDefNodes: processConstants does not follow their body.
        if matches!(
            &definition.kind,
            DefinitionKind::Operator {
                body_range: None,
                ..
            }
        ) {
            continue;
        }
        literals(&definition.body, &mut initialized, tables);
    }
    for definition in pre_override_definitions {
        if matches!(
            &definition.kind,
            DefinitionKind::Operator {
                body_range: None,
                ..
            }
        ) {
            continue;
        }
        for context in tables.instance_context(definition) {
            literals(&context, &mut initialized, tables);
        }
    }
    candidates.retain(|literal| !initialized.contains(literal));
    candidates
}

/// The key enumeration of ModelConfig's Java Hashtables, including collisions and rehashing.
fn config_key_order(names: &[&str]) -> Vec<usize> {
    let mut buckets: Vec<Vec<usize>> = vec![Vec::new(); 11];
    let mut seen = FastSet::default();
    for (index, name) in names.iter().enumerate() {
        if !seen.insert(*name) {
            continue;
        }
        if seen.len() > buckets.len() * 3 / 4 {
            let mut grown: Vec<Vec<usize>> = vec![Vec::new(); buckets.len() * 2 + 1];
            for bucket in buckets.iter().rev() {
                for &entry in bucket {
                    let hash = crate::sany::nodes::get_java_hash(names[entry]) & 0x7fff_ffff;
                    let slot = hash as usize % grown.len();
                    grown[slot].insert(0, entry);
                }
            }
            buckets = grown;
        }
        let hash = crate::sany::nodes::get_java_hash(name) & 0x7fff_ffff;
        let slot = hash as usize % buckets.len();
        buckets[slot].insert(0, index);
    }
    buckets.into_iter().rev().flatten().collect()
}

/// TLC evaluates a substitute for a constant as it computes the constant definitions, and rejects
/// it only when that fails and the level bound it computes is above constant.
fn check_constant_substitutes(
    environment: &Environment,
    version: TlcVersion,
) -> Result<TargetFacts> {
    // TLC evaluates a substitute for a constant at startup and rejects it only when that fails and
    // the level bound it computes is above constant. The bound counts the operators that TLC's
    // Java code overrides with a minimum level as state-level, so the analyzer takes them for
    // variables.
    let analyzer = environment.create_level_analyzer(&["TLCGet", "Trace", "CounterExample"]);
    let ranks = FastMap::default();
    let evaluator = Evaluator::new(environment, ValueOrder { ranks: &ranks }, version, false);
    for (name, target) in environment.substitutions.iter() {
        let Some(definition) = environment.definitions.get(target) else {
            continue;
        };
        let is_parameterless = matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty());
        if !environment
            .root_constants
            .iter()
            .any(|constant| constant.name == *name)
            || !is_parameterless
            || analyzer
                .analyze_definition(definition, &Scope::default())?
                .data
                .level
                == 0
                // `getLevelBound` takes a name spelled as a variable for one (`getVarLoc`),
                // bound or defined in a LET as it may be.
                && crate::startup::get_definition_level_bound(environment, definition) == 0
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
    // What the linking assumed of a substitution's target with a module-scoped value.
    let not_yet = || {
        Err(FrontError::NotYet(
            "a substitution whose target has a module-scoped value the spec reads otherwise"
                .to_owned(),
        ))
    };
    let is_constant = |definition: &Rc<Definition>| -> Result<bool> {
        Ok(analyzer
            .analyze_definition(definition, &Scope::default())?
            .data
            .level
            == 0)
    };
    let mut facts = TargetFacts::default();
    for check in &environment.scoped_target_checks {
        if is_constant(&check.definition)? != check.is_constant {
            return not_yet();
        }
        if check.is_attempted {
            // The body of a function definition is under its bounds, which the linking takes
            // only where TLC certainly computes the function.
            if matches!(check.definition.kind, DefinitionKind::Function { .. }) {
                if !check.is_constant || !certainly_computes_definition(&check.definition) {
                    return not_yet();
                }
            } else {
                let result = evaluator.evaluate(&check.definition.body, None);
                if check.is_constant {
                    // Where computing the body fails, TLC swallows the failure and leaves Y the
                    // entry, which the linking gives Y where it doesn't leave the entry out.
                    match result {
                        Ok(_) => {}
                        Err(FrontError::Evaluation(_)) => {
                            if check.is_hidden {
                                facts.failed.insert(check.key.clone());
                            }
                        }
                        // A body the constant evaluator doesn't compute, but one built of literals
                        // TLC computes without effects (`certainly_computes`), or one whose draws
                        // decide only whether it fails (`is_drawn_alike`).
                        Err(_) => {
                            if !certainly_computes_definition(&check.definition)
                                && !(check.is_hidden
                                    && is_drawn_alike(environment, &evaluator, &check.definition))
                            {
                                return not_yet();
                            }
                        }
                    }
                } else if result.is_ok() {
                    // TLC computes the body of a declared constant's substitute at any level, and
                    // where that succeeds, Y reads it rather than the entry.
                    return not_yet();
                }
            }
        }
        // TLC computes each of these as it starts, reading the entry, and one that fails
        // stays an operator, which reads Y's computed body: where all fail, without an effect,
        // so does every read (`TargetFacts`), and otherwise the linking took each to succeed.
        let mut failures = 0;
        for cached in &check.cached {
            if !is_constant(cached)? || matches!(cached.kind, DefinitionKind::Function { .. }) {
                return not_yet();
            }
            match evaluator.evaluate(&cached.body, None) {
                Ok(_) => {}
                Err(FrontError::Evaluation(_)) if check.may_fail => failures += 1,
                Err(_)
                    if check.may_fail
                        && (fails_building(&evaluator, &cached.body)
                            || fails_without_effects(
                                &environment.definitions,
                                &evaluator,
                                strip_labels(&cached.body),
                            )) =>
                {
                    failures += 1
                }
                Err(_) => return not_yet(),
            }
        }
        if check.must_fail || failures > 0 {
            if failures != check.cached.len() {
                return not_yet();
            }
            facts.reread.insert(check.key.clone());
        }
    }
    Ok(facts)
}

/// What computing an expression whose only effects are draws gives, however they come out: a
/// failure, a value, or one of the two (`Drawn::Either`).
#[derive(Clone)]
enum Drawn {
    Fails,
    Value(ConfigValue),
    Either(ConfigValue),
}

/// The builtins that draw from TLC's generator (`RandomEnumerableValues`).
pub(crate) const DRAWS: [&str; 3] = ["RandomElement", "RandomSubset", "RandomSetOfSubsets"];

/// `Drawn` of an expression TLC computes as it starts: one without effects as the constant
/// evaluator computes it, or an IF whose condition is either without effects or a draw of a
/// boolean, `RandomElement` of a set of booleans, which never fails. Anything else is unknown.
fn get_drawn(
    definitions: &OrderedMap<Name, Rc<Definition>>,
    evaluator: &Evaluator,
    expression: &Expr,
) -> Option<Drawn> {
    let mut expression = expression;
    while let ExpressionKind::Label { body, .. } = &expression.kind {
        expression = body;
    }
    if fails_without_effects(definitions, evaluator, expression) {
        return Some(Drawn::Fails);
    }
    if is_without_effects(definitions, expression) {
        return match evaluator.evaluate(expression, None) {
            Ok(value) => Some(Drawn::Value(value)),
            Err(FrontError::Evaluation(_)) => Some(Drawn::Fails),
            Err(_) => None,
        };
    }
    // `CASE p1 -> e1 [] p2 -> e2 ... [] OTHER -> o` TLC computes as `IF p1 THEN e1 ELSE IF p2
    // THEN e2 ... ELSE o`, testing the guards in turn (OPCODE_case), and fails past the last
    // guard without OTHER.
    if let ExpressionKind::Case { arms, other } = &expression.kind {
        return get_drawn_arms(definitions, evaluator, arms, other.as_ref());
    }
    let ExpressionKind::If {
        condition,
        consequent,
        alternative,
    } = &expression.kind
    else {
        return None;
    };
    get_drawn_choice(definitions, evaluator, condition, consequent, alternative)
}

/// `Drawn` of the arms of a CASE from the first on.
fn get_drawn_arms(
    definitions: &OrderedMap<Name, Rc<Definition>>,
    evaluator: &Evaluator,
    arms: &[CaseArm],
    other: Option<&Expr>,
) -> Option<Drawn> {
    let Some((arm, rest)) = arms.split_first() else {
        return match other {
            Some(other) => get_drawn(definitions, evaluator, other),
            None => Some(Drawn::Fails),
        };
    };
    let alternative = || get_drawn_arms(definitions, evaluator, rest, other);
    get_drawn_branches(
        definitions,
        evaluator,
        &arm.condition,
        || get_drawn(definitions, evaluator, &arm.body),
        alternative,
    )
}

/// `Drawn` of `IF condition THEN consequent ELSE alternative`.
fn get_drawn_choice(
    definitions: &OrderedMap<Name, Rc<Definition>>,
    evaluator: &Evaluator,
    condition: &Expr,
    consequent: &Expr,
    alternative: &Expr,
) -> Option<Drawn> {
    get_drawn_branches(
        definitions,
        evaluator,
        condition,
        || get_drawn(definitions, evaluator, consequent),
        || get_drawn(definitions, evaluator, alternative),
    )
}

/// `Drawn` of a choice between two branches by a condition: the branch a condition without
/// effects takes, or either where it is a draw that gives a boolean whatever it draws.
fn get_drawn_branches(
    definitions: &OrderedMap<Name, Rc<Definition>>,
    evaluator: &Evaluator,
    condition: &Expr,
    consequent: impl Fn() -> Option<Drawn>,
    alternative: impl Fn() -> Option<Drawn>,
) -> Option<Drawn> {
    if is_without_effects(definitions, condition) {
        return match evaluator.evaluate(condition, None) {
            Ok(ConfigValue::Boolean(true)) => consequent(),
            Ok(ConfigValue::Boolean(false)) => alternative(),
            Err(FrontError::Evaluation(_)) => Some(Drawn::Fails),
            _ => None,
        };
    }
    let is_boolean_draw = match &condition.kind {
        ExpressionKind::Apply { operator, args, .. } => {
            &**operator == "RandomElement"
                && !condition.is_locally_resolved()
                && !definitions.contains_key(operator)
                && crate::eval::is_builtin_draw(evaluator.environment, "RandomElement", "TLC")
                && args.len() == 1
                && is_without_effects(definitions, &args[0])
                && matches!(evaluator.evaluate(&args[0], None),
                    Ok(ConfigValue::Set(elements)) if !elements.is_empty()
                        && elements.iter().all(|element| matches!(element, ConfigValue::Boolean(_))))
        }
        _ => false,
    } || is_boolean_for_every_draw(definitions, evaluator, condition);
    if !is_boolean_draw {
        return None;
    }
    let value = |drawn: &Drawn| match drawn {
        Drawn::Fails => None,
        Drawn::Value(value) | Drawn::Either(value) => Some(value.clone()),
    };
    let (first, second) = (consequent()?, alternative()?);
    match (value(&first), value(&second)) {
        (None, None) => Some(Drawn::Fails),
        (Some(left), Some(right)) if left != right => None,
        (Some(value), _) | (_, Some(value)) => {
            if matches!((&first, &second), (Drawn::Value(_), Drawn::Value(_))) {
                Some(Drawn::Value(value))
            } else {
                Some(Drawn::Either(value))
            }
        }
    }
}

/// Whether a condition whose only effects are draws of `TLC.RandomElement` written in it gives a
/// boolean, without failing, for every element each draw may take, as `RandomElement({1, 2, 3})
/// = 1`: the front end's evaluator computes it once for each combination of the elements
/// (`for_every_draw`).
fn is_boolean_for_every_draw(
    definitions: &OrderedMap<Name, Rc<Definition>>,
    evaluator: &Evaluator,
    condition: &Expr,
) -> bool {
    let environment = evaluator.environment;
    if !crate::eval::is_builtin_draw(environment, "RandomElement", "TLC")
        || !is_without_effects_but(definitions, condition, &["RandomElement"])
    {
        return false;
    }
    crate::eval::for_every_draw(environment, evaluator, condition, |value, sizes| {
        matches!(value, Ok(ConfigValue::Boolean(_))) && !sizes.is_empty()
    })
}

/// Whether TLC certainly fails computing an expression, without an effect, where the constant
/// evaluator doesn't compute it: `TLC.Assert` of a condition the evaluator finds FALSE and a
/// message without effects (Java computes both arguments, then `Assert.fail`), and a tuple of
/// parts without effects applied to a number outside its domain (`TupleValue.apply`), which fail
/// alike whatever the parts give or wherever computing one fails first.
fn fails_without_effects(
    definitions: &OrderedMap<Name, Rc<Definition>>,
    evaluator: &Evaluator,
    expression: &Expr,
) -> bool {
    match &expression.kind {
        ExpressionKind::Apply { operator, args, .. } => {
            &**operator == "Assert"
                && !expression.is_locally_resolved()
                && !definitions.contains_key(operator)
                && matches!(args.as_slice(), [condition, message]
                    if is_without_effects(definitions, condition)
                        && is_without_effects(definitions, message)
                        && matches!(evaluator.evaluate(condition, None), Ok(ConfigValue::Boolean(false))))
        }
        ExpressionKind::FunctionApplication { function, args } => {
            matches!((&function.kind, args.as_slice()),
                (ExpressionKind::Tuple(elements), [index])
                    if elements.iter().all(|element| is_without_effects(definitions, element))
                        && matches!(&index.kind, ExpressionKind::Number { value, .. }
                            if value.fract() == 0.0 && (*value < 1.0 || *value > elements.len() as f64)))
        }
        _ => false,
    }
}

/// Whether a substitution's target Y, of a body TLC computes as it starts whose draws decide only
/// whether it fails and not the value it gives where it doesn't, is computed by the engine as
/// TLC computes it. With an entry Y's lookup finds as it starts, `processConstantDefns` computes Y
/// not where it reaches Y but where it reaches each name X substituted by it, and keeps the value
/// of the last computation that didn't fail, else the entry. The engine computes Y once, where
/// it reaches Y, and declines where that fails after a draw (`Definition::NAMED_AT_STARTUP`): it
/// draws first from TLC's generator as TLC's first computation of Y does where nothing else in
/// the spec draws, which then doesn't fail either, and gives the one value every computation
/// that doesn't fail gives. Nothing may read an X, which TLC computes again at each read.
pub(crate) fn is_drawn_alike(
    environment: &Environment,
    evaluator: &Evaluator,
    definition: &Rc<Definition>,
) -> bool {
    if !matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
        || !matches!(
            get_drawn(&environment.definitions, evaluator, &definition.body),
            Some(Drawn::Value(_) | Drawn::Either(_))
        )
    {
        return false;
    }
    let draws: FastSet<Name> = DRAWS.iter().map(|name| Name::from(*name)).collect();
    let substitutes: FastSet<Name> = environment
        .substitutions
        .iter()
        .filter(|(_, target)| {
            environment
                .definitions
                .get(*target)
                .is_some_and(|other| Rc::ptr_eq(other, definition))
        })
        .map(|(name, _)| name.clone())
        .collect();
    let mut roots: Vec<Expr> = environment
        .assumptions
        .iter()
        .map(|assumption| assumption.expression.clone())
        .collect();
    for other in environment.definitions.values() {
        if Rc::ptr_eq(other, definition) {
            continue;
        }
        if let DefinitionKind::Function { bounds } = &other.kind {
            roots.extend(bounds.iter().map(|bound| bound.set.clone()));
        }
        roots.push(other.body.clone());
    }
    !roots
        .iter()
        .any(|root| references_any(root, &draws) || references_any(root, &substitutes))
}

/// Whether TLC certainly fails to build a function `[x \in S |-> e]` over set enumerations,
/// each of at least one element, which are `Reducible`: TLC builds it at once (`Tool`'s
/// OPCODE_fc, `FcnLambdaValue.toFcnRcd`), computing e at every element, and the evaluator finds
/// e failing at one. The constant evaluator holds no functions.
fn fails_building(evaluator: &Evaluator, expression: &Expr) -> bool {
    let mut body = expression;
    while let ExpressionKind::Label { body: inner, .. } = &body.kind {
        body = inner;
    }
    let ExpressionKind::FunctionConstruction { bounds, body } = &body.kind else {
        return false;
    };
    let mut scope: Option<Rc<crate::spec::Scope>> = None;
    for bound in bounds {
        let BoundPattern::Name { name, .. } = &bound.pattern else {
            return false;
        };
        if !matches!(&bound.set.kind, ExpressionKind::SetEnumeration(elements) if !elements.is_empty())
        {
            return false;
        }
        let Ok(ConfigValue::Set(elements)) = evaluator.evaluate(&bound.set, None) else {
            return false;
        };
        let Some(element) = elements.into_iter().next() else {
            return false;
        };
        scope = Some(Rc::new(crate::spec::Scope {
            name: name.clone(),
            binding: crate::spec::Binding::Value(element),
            parent: scope,
        }));
    }
    matches!(
        evaluator.evaluate(body, scope.as_ref()),
        Err(FrontError::Evaluation(_))
    )
}

/// Whether TLC certainly computes a definition's value without effects, as it starts
/// (`certainly_computes`): a function definition `Y[x \in S] == e` as a function construction.
fn certainly_computes_definition(definition: &Definition) -> bool {
    match &definition.kind {
        DefinitionKind::Operator { .. } => certainly_computes(&definition.body, &[]),
        DefinitionKind::Function { bounds } => {
            bounds.iter().all(|bound| is_certainly_empty(&bound.set))
        }
    }
}

/// Whether a definition TLC computes before a substitution's target has no effect but that
/// computing it may fail, which TLC swallows as it starts and computes it again at each use:
/// one without effects, or `TLC.Assert` of arguments without effects, which holds or throws an
/// `EvalException` and prints nothing.
fn is_rereadable(definitions: &OrderedMap<Name, Rc<Definition>>, body: &Expr) -> bool {
    if is_without_effects(definitions, body) {
        return true;
    }
    let body = strip_labels(body);
    matches!(&body.kind, ExpressionKind::Apply { operator, args, .. }
        if &**operator == "Assert"
            && !body.is_locally_resolved()
            && !definitions.contains_key(operator)
            && args.len() == 2
            && args.iter().all(|argument| is_without_effects(definitions, argument)))
}

/// Whether a filter `{x \in S : p}` ranges over a set S of few elements that TLC enumerates
/// without computing anything that may run long: `SUBSET {..}` of at most 10 elements, or
/// `[{..} -> {..}]` of at most 1,024 functions (`Deferral::tests_lazily`).
fn is_small_base(filter: &Expr) -> bool {
    let ExpressionKind::SetFilter { bound, .. } = &strip_labels(filter).kind else {
        return false;
    };
    let size = |set: &Expr| match &set.kind {
        ExpressionKind::SetEnumeration(elements)
            if elements.iter().all(|element| {
                matches!(
                    &element.kind,
                    ExpressionKind::Number { .. } | ExpressionKind::String { .. }
                )
            }) =>
        {
            Some(elements.len())
        }
        _ => None,
    };
    match &bound.set.kind {
        ExpressionKind::Apply { operator, args, .. }
            if &**operator == "SUBSET" && !bound.set.is_locally_resolved() && args.len() == 1 =>
        {
            size(&args[0]).is_some_and(|size| size <= 10)
        }
        ExpressionKind::FunctionSet { domain, range } => match (size(domain), size(range)) {
            (Some(domain), Some(range)) => (range as u64)
                .checked_pow(domain as u32)
                .is_some_and(|count| count <= 1024),
            _ => false,
        },
        _ => false,
    }
}

/// An expression without the labels around it.
fn strip_labels(expression: &Expr) -> &Expr {
    let mut expression = expression;
    while let ExpressionKind::Label { body, .. } = &expression.kind {
        expression = body;
    }
    expression
}

/// Whether a definition's body is a set filter `{x \in S : p}`, which TLC builds as a
/// `SetPredValue` where S isn't `Reducible`.
fn is_filter(body: &Expr) -> bool {
    matches!(&strip_labels(body).kind, ExpressionKind::SetFilter { .. })
}

/// What tells a reader of a substitution's target Y that TLC computes before Y apart, where it
/// reads Y only where its value is used, after TLC computed Y (`Deferral::is_deferred`).
struct Deferral<'a> {
    definitions: &'a OrderedMap<Name, Rc<Definition>>,
    readers: &'a FastSet<Name>,
    early: &'a [Rc<Definition>],
    /// Of `early`, those whose value nothing shows (`get_unread`).
    unread: &'a FastSet<usize>,
    is_plain: &'a dyn Fn(&Name) -> bool,
    builtin_keys: &'a FastSet<Name>,
}

impl Deferral<'_> {
    /// Whether a set evaluates to a value TLC doesn't reduce (only `IntervalValue` and
    /// `SetEnumValue` are `Reducible`): `SUBSET S`, `Seq(S)`, `Nat`, `Int`, `STRING`, a filter
    /// (`SetPredValue`), a set of functions, of records or of tuples, or a name without
    /// parameters, of the spec's or of a LET in `lets`, for one.
    fn is_unreduced(&self, set: &Expr, lets: &[Rc<Definition>], depth: usize) -> bool {
        if depth > 8 {
            return false;
        }
        let is_builtin =
            |name: &Name| !self.definitions.contains_key(name) && self.builtin_keys.contains(name);
        match &set.kind {
            // `{x \in S : p}` TLC keeps lazy (a `SetPredValue`) only where S isn't `Reducible`:
            // over a set enumeration or an interval, OPCODE_sso builds a `SetEnumValue` at once.
            ExpressionKind::SetFilter { bound, .. } => self.is_unreduced(&bound.set, lets, depth + 1),
            // `[S -> T]`, `[a : S]` and `S \X T` TLC builds as a `SetOfFcnsValue`,
            // `SetOfRcdsValue` and `SetOfTuplesValue` (OPCODE_sof, OPCODE_sor and OPCODE_cp).
            ExpressionKind::FunctionSet { .. }
            | ExpressionKind::Record { is_set: true, .. }
            | ExpressionKind::Product(_) => true,
            ExpressionKind::Apply { operator, args, .. } if args.len() == 1 => {
                !set.is_locally_resolved()
                    && (&**operator == "SUBSET"
                        || (&**operator == "Seq"
                            && set.reference().is_some_and(|name| is_builtin(&name))))
            }
            ExpressionKind::Identifier { name, .. } if set.is_locally_resolved() => lets
                .iter()
                .rev()
                .find(|definition| definition.name == *name)
                .is_some_and(|definition| {
                    matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                        && self.is_unreduced(&definition.body, lets, depth + 1)
                }),
            ExpressionKind::Identifier { .. } => {
                let Some(name) = set.reference() else {
                    return false;
                };
                if matches!(&*name, "Nat" | "Int" | "STRING") && is_builtin(&name) {
                    return true;
                }
                (self.is_plain)(&name)
                    && self.definitions.get(&name).is_some_and(|definition| {
                        matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                            && !definition.is_recursive
                            && self.is_unreduced(&definition.body, &[], depth + 1)
                    })
            }
            _ => false,
        }
    }

    /// The definitions of the spec's a bare name reads, by its key.
    fn get_definition(&self, expression: &Expr) -> Option<&Rc<Definition>> {
        if !matches!(&expression.kind, ExpressionKind::Identifier { .. })
            || expression.is_locally_resolved()
        {
            return None;
        }
        let name = expression.reference()?;
        (self.is_plain)(&name)
            .then(|| self.definitions.get(&name))
            .flatten()
    }

    /// Whether a set a reader ranges over reads Y as TLC computes the reader: it names none of
    /// `readers`, or is a bare name of a deferred reader, whose value TLC holds lazily.
    fn is_set_unread(&self, set: &Expr, depth: usize, assumed: &[*const Definition]) -> bool {
        !references_any(set, self.readers)
            || self
                .get_definition(set)
                .is_some_and(|definition| self.is_deferred(definition, depth + 1, assumed))
    }

    /// Whether a value holds the lazy value of a deferred reader without computing it, so that
    /// the reader's predicate or body reads Y only where the value is used: `R \cup {..}` or
    /// `{..} \cup R` with a set enumeration without effects that names no reader (a
    /// `SetEnumValue`'s `cup` of a set that isn't `Reducible` returns that set where it is empty,
    /// and a lazy `SetCupValue` otherwise, whose `deepNormalize` normalizes only its operands),
    /// `{R}` (a `SetEnumValue` of one element, whose `normalize` compares nothing), `DOMAIN R` of
    /// a function TLC keeps lazy (`FcnLambdaValue.getDomain` returns its domain, not its body), and
    /// `LET L == R IN L`, which binds R lazily and returns its value.
    fn holds_lazily(&self, body: &Expr, depth: usize, assumed: &[*const Definition]) -> bool {
        if depth > 8 {
            return false;
        }
        let deferred = |expression: &Expr| {
            self.get_definition(expression)
                .is_some_and(|definition| self.is_deferred(definition, depth + 1, assumed))
        };
        let is_plain_set = |expression: &Expr| {
            matches!(&expression.kind, ExpressionKind::SetEnumeration(_))
                && !references_any(expression, self.readers)
                && is_without_effects(self.definitions, expression)
        };
        match &body.kind {
            ExpressionKind::Apply { operator, args, .. } if !body.is_locally_resolved() => {
                match (&**operator, args.as_slice()) {
                    ("\\cup", [left, right]) => {
                        (deferred(left) && is_plain_set(right))
                            || (is_plain_set(left) && deferred(right))
                    }
                    ("DOMAIN", [function]) => {
                        self.get_definition(function).is_some_and(|definition| {
                            matches!(
                                &strip_labels(&definition.body).kind,
                                ExpressionKind::FunctionConstruction { .. }
                            ) && self.is_deferred(definition, depth + 1, assumed)
                        })
                    }
                    _ => false,
                }
            }
            ExpressionKind::SetEnumeration(elements) => {
                matches!(elements.as_slice(), [element] if deferred(element))
            }
            ExpressionKind::Let {
                definitions,
                instances: None,
                recursive,
                body: inner,
            } if recursive.is_empty() && inner.is_locally_resolved() => {
                let ExpressionKind::Identifier { name, .. } = &inner.kind else {
                    return false;
                };
                definitions.iter().all(|definition| {
                    matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
                        && (deferred(&definition.body)
                            || (!references_any(&definition.body, self.readers)
                                && is_without_effects(self.definitions, &definition.body)))
                }) && definitions
                    .iter()
                    .rev()
                    .find(|definition| definition.name == *name)
                    .is_some_and(|definition| deferred(&definition.body))
            }
            _ => false,
        }
    }

    /// Whether a definition nothing shows the value of names a filter only where TLC tests an
    /// element's membership in it (`x \in R`, `SetPredValue.member`) or its elements' in another
    /// set (`R \subseteq S`, `EnumerableValue.isSubsetEq` over its `elements`), where neither
    /// operand otherwise names it. TLC enumerates the filter's set for the latter as it starts,
    /// which ends soon only where that set is small: the power set of a set enumeration of at
    /// most 10 elements, or the functions from one set enumeration to another, at most 1,024.
    fn tests_lazily(
        &self,
        body: &Expr,
        filter: &Expr,
        is_bare: &dyn Fn(&Expr) -> bool,
        names: &FastSet<Name>,
    ) -> bool {
        let ExpressionKind::Apply { operator, args, .. } = &body.kind else {
            return false;
        };
        if body.is_locally_resolved() {
            return false;
        }
        match (&**operator, args.as_slice()) {
            ("\\in", [element, set]) => is_bare(set) && !references_any(element, names),
            ("\\subseteq", [set, other]) => {
                is_bare(set) && !references_any(other, names) && is_small_base(filter)
            }
            _ => false,
        }
    }

    /// Whether a reader TLC computes before Y reads it there only lazily: a set filter `{x \in S
    /// : p}`, or a function `[x \in S |-> e]`, over a set TLC doesn't reduce (`is_unreduced`),
    /// TLC builds lazily (`Tool`'s OPCODE_sso and OPCODE_fc), and its `deepNormalize` normalizes
    /// only S; a function over sets one of which is certainly empty TLC builds at once without
    /// computing e; and a bare name of such a reader holds its value. Under a LET without
    /// instances whose definitions read no reader, whose names S may be. Where no set it ranges
    /// over reads Y (`is_set_unread`), and no other definition TLC computes before Y reads the
    /// reader but as such a deferred reader's set or whole body (`SetPredValue.toSetEnum` and
    /// `FcnLambdaValue.toFcnRcd` keep what they compute, and a membership test computes p), its
    /// predicate or body reads Y only where its value is used, after TLC computed Y: it reads
    /// Y's computed body, as one that fails reading the entry does.
    fn is_deferred(
        &self,
        reader: &Rc<Definition>,
        depth: usize,
        assumed: &[*const Definition],
    ) -> bool {
        // A reader whose deferral the walk already assumes, holding another.
        if assumed.contains(&Rc::as_ptr(reader)) {
            return true;
        }
        let DefinitionKind::Operator { params, .. } = &reader.kind else {
            return false;
        };
        if depth > 8
            || !params.is_empty()
            || reader.is_recursive
            || !is_without_effects(self.definitions, &reader.body)
        {
            return false;
        }
        let mut body = &reader.body;
        let mut lets: Vec<Rc<Definition>> = Vec::new();
        loop {
            match &body.kind {
                ExpressionKind::Label { body: inner, .. } => body = inner,
                ExpressionKind::Let {
                    definitions,
                    instances: None,
                    recursive,
                    body: inner,
                } if recursive.is_empty()
                    && definitions.iter().all(|definition| {
                        !references_any(&definition.body, self.readers)
                            && matches!(&definition.kind, DefinitionKind::Operator { .. })
                    }) =>
                {
                    lets.extend(definitions.iter().cloned());
                    body = inner;
                }
                _ => break,
            }
        }
        let is_lazy = match &body.kind {
            ExpressionKind::SetFilter { bound, .. } => {
                self.is_unreduced(&bound.set, &lets, 0)
                    && self.is_set_unread(&bound.set, depth, assumed)
            }
            ExpressionKind::FunctionConstruction { bounds, .. } => {
                (bounds
                    .iter()
                    .any(|bound| self.is_unreduced(&bound.set, &lets, 0))
                    || bounds.iter().any(|bound| is_certainly_empty(&bound.set)))
                    && bounds
                        .iter()
                        .all(|bound| self.is_set_unread(&bound.set, depth, assumed))
            }
            _ if lets.is_empty() => {
                self.get_definition(body)
                    .is_some_and(|definition| self.is_deferred(definition, depth + 1, assumed))
                    || self.holds_lazily(body, depth, assumed)
            }
            _ => false,
        };
        if !is_lazy {
            return false;
        }
        let names: FastSet<Name> = (self.definitions.iter())
            .filter(|(_, other)| Rc::ptr_eq(other, reader))
            .map(|(name, _)| name.clone())
            .collect();
        // Another reader that holds it only as a deferred reader's set or whole body doesn't
        // compute it.
        let reads_lazily = |other: &Rc<Definition>| {
            let is_bare = |expression: &Expr| {
                self.get_definition(expression)
                    .is_some_and(|definition| Rc::ptr_eq(definition, reader))
            };
            let set_ok = |set: &Expr| is_bare(set) || !references_any(set, &names);
            let mut body = &other.body;
            while let ExpressionKind::Label { body: inner, .. } = &body.kind {
                body = inner;
            }
            // One nothing shows the value of, which tests only an element's membership in a
            // filter or the filter's elements' in another set, doesn't keep what it computes:
            // `SetPredValue.member` and its `elements` compute the predicate without
            // `convertAndCache`, which only comparing, counting or fingerprinting the set calls.
            if self.unread.contains(&(Rc::as_ptr(other) as usize))
                && is_filter(&reader.body)
                && self.tests_lazily(body, &reader.body, &is_bare, &names)
            {
                return true;
            }
            let mut within = assumed.to_vec();
            within.push(Rc::as_ptr(reader));
            let is_held = match &body.kind {
                _ if is_bare(body) => true,
                ExpressionKind::SetFilter { bound, predicate } => {
                    set_ok(&bound.set) && !references_any(predicate, &names)
                }
                ExpressionKind::FunctionConstruction { bounds, body } => {
                    bounds.iter().all(|bound| set_ok(&bound.set)) && !references_any(body, &names)
                }
                _ => self.holds_lazily(body, depth + 1, &within),
            };
            is_held && self.is_deferred(other, depth + 1, &within)
        };
        !self.early.iter().any(|other| {
            !Rc::ptr_eq(other, reader)
                && definition_roots_of(other)
                    .iter()
                    .any(|root| references_any(root, &names))
                && !reads_lazily(other)
        })
    }
}

/// The expressions TLC evaluates for a definition: a function's bounds and its body.
fn definition_roots_of(definition: &Definition) -> Vec<Expr> {
    let bounds = match &definition.kind {
        DefinitionKind::Function { bounds } => bounds.as_slice(),
        DefinitionKind::Operator { .. } => &[],
    };
    bounds
        .iter()
        .map(|bound| bound.set.clone())
        .chain([definition.body.clone()])
        .collect()
}

/// Whether a function's domain is certainly empty, as `{}` or `{x \in {} : p}`, whose value TLC
/// computes without its predicate: a function over it builds without its body (`OPCODE_fc`, at
/// once over a reducible domain, else lazily, where `deepNormalize` normalizes only the domain).
fn is_certainly_empty(set: &Expr) -> bool {
    match &set.kind {
        ExpressionKind::SetEnumeration(elements) => elements.is_empty(),
        ExpressionKind::SetFilter { bound, .. } => is_certainly_empty(&bound.set),
        _ => false,
    }
}

/// Whether TLC certainly computes an expression without effects, as it starts: a number or a
/// string, a tuple or a record of such, a set of numbers or of strings, or a function over such a
/// set whose body is such or the function's own bound name. TLC compares only numbers with
/// numbers and strings with strings as it normalizes the sets.
fn certainly_computes(expression: &Expr, bound: &[Name]) -> bool {
    let is_literal_set = |set: &Expr| match &set.kind {
        ExpressionKind::SetEnumeration(elements) => {
            elements.iter().all(|element| {
                matches!(&element.kind, ExpressionKind::Number { value, .. }
                    if value.fract() == 0.0 && value.abs() < 2_147_483_648.0)
            }) || elements
                .iter()
                .all(|element| matches!(element.kind, ExpressionKind::String { .. }))
        }
        _ => false,
    };
    match &expression.kind {
        ExpressionKind::Number { value, .. } => {
            value.fract() == 0.0 && value.abs() < 2_147_483_648.0
        }
        ExpressionKind::String { .. } => true,
        ExpressionKind::Identifier { name, .. } => {
            expression.is_locally_resolved() && bound.contains(name)
        }
        ExpressionKind::Tuple(elements) => elements
            .iter()
            .all(|element| certainly_computes(element, bound)),
        ExpressionKind::Record {
            is_set: false,
            fields,
        } => fields
            .iter()
            .all(|field| certainly_computes(&field.value, bound)),
        ExpressionKind::SetEnumeration(_) => is_literal_set(expression),
        ExpressionKind::FunctionConstruction { bounds, .. }
            if bounds.iter().all(|each| is_certainly_empty(&each.set)) =>
        {
            true
        }
        ExpressionKind::FunctionConstruction { bounds, body } => {
            let mut inner = bound.to_vec();
            for each in bounds {
                let BoundPattern::Name { name, .. } = &each.pattern else {
                    return false;
                };
                if !is_literal_set(&each.set) {
                    return false;
                }
                inner.push(name.clone());
            }
            certainly_computes(body, &inner)
        }
        _ => false,
    }
}

/// A module's own definitions TLC computes as it starts, and those it holds from the modules it
/// extends (`get_startup_walk`).
type OwnAndInherited = (Vec<Rc<Definition>>, Vec<Rc<Definition>>);
type OwnDefinitions<'a> = dyn Fn(&Rc<LinkedModule>) -> Result<OwnAndInherited> + 'a;

/// The definitions TLC computes as it starts, with the groups of them whose order the front end
/// doesn't know (`startup_inner_siblings`) and the definitions of the modules an INSTANCE names.
type StartupDefinitions = (
    Vec<Rc<Definition>>,
    Vec<Vec<Vec<Rc<Definition>>>>,
    Vec<Rc<Definition>>,
    Vec<(usize, Rc<Definition>)>,
);

// TLC computes the constant definitions of each module of its table, in the order SANY finishes
// the modules (`SpecProcessor.processConstantDefns`), except those of a module that an INSTANCE
// gives parameters to. The table holds only the modules of files: TLC computes an inner module's
// after those of the module that holds it, which it takes up after its own (`getInnerModules`).
fn get_startup_definitions(
    linker: &Linker,
    linked_root: &Rc<LinkedModule>,
    definitions: &OrderedMap<Name, Rc<Definition>>,
    options: &EnvironmentOptions,
) -> Result<StartupDefinitions> {
    Ok(get_startup_walk(linker, linked_root, definitions, options)?.0)
}

// The definitions TLC computes as it starts, and where the root module's begin. The order of
// the definitions of two inner modules of a module isn't known (`startup_inner_siblings`),
// which declines.
fn get_startup_order(
    linker: &Linker,
    linked_root: &Rc<LinkedModule>,
    definitions: &OrderedMap<Name, Rc<Definition>>,
    options: &EnvironmentOptions,
) -> Result<(Vec<Rc<Definition>>, usize)> {
    let ((startup, siblings, _, _), root_start) =
        get_startup_walk(linker, linked_root, definitions, options)?;
    if !siblings.is_empty() {
        return Err(FrontError::NotYet(
            "a substitution whose target has a module-scoped value, beside two inner modules of a module".to_owned(),
        ));
    }
    Ok((startup, root_start))
}

// `get_startup_definitions`, with where the root module's definitions begin.
fn get_startup_walk(
    linker: &Linker,
    linked_root: &Rc<LinkedModule>,
    definitions: &OrderedMap<Name, Rc<Definition>>,
    options: &EnvironmentOptions,
) -> Result<(StartupDefinitions, usize)> {
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
    let inner: FastSet<Name> = link_order
        .iter()
        .flat_map(|linked| {
            linked
                .module
                .modules
                .iter()
                .map(|nested| nested.name.clone())
        })
        .collect();
    let order = TlcOrder::new(options.source, options.load_module, options.version)?;
    // A module's own definitions, and those its context holds from the modules it extends,
    // which `ModuleNode.getOpDefs` lists first.
    let own_definitions = |linked: &Rc<LinkedModule>| -> Result<OwnAndInherited> {
        let mut own = Vec::new();
        let mut inherited = Vec::new();
        if instantiated.contains(&linked.module.name)
            && !(linked.constants.is_empty() && linked.variables.is_empty())
        {
            return Ok((own, inherited));
        }
        let name = (!Rc::ptr_eq(linked, linked_root)).then_some(&*linked.module.name);
        let get = |name: &Name| {
            let key = linked.visible.get(name).map_or(name, |symbol| &symbol.key);
            definitions.get(key).cloned()
        };
        for name in order.get_inherited_definition_order(name)? {
            inherited.extend(get(&name));
        }
        for name in order.get_definition_order(name)? {
            own.extend(get(&name));
        }
        Ok((own, inherited))
    };
    // A module's own definitions, then those of its inner modules, each with its own inner ones.
    struct Walk<'a> {
        link_order: &'a [Rc<LinkedModule>],
        visited: FastSet<usize>,
        siblings: Vec<Vec<Vec<Rc<Definition>>>>,
        // Each inherited definition, with how many definitions the walk listed before the
        // module that holds it.
        repeats: Vec<(usize, Rc<Definition>)>,
        listed: usize,
    }
    fn walk(
        state: &mut Walk,
        linked: &Rc<LinkedModule>,
        own_definitions: &OwnDefinitions,
        startup: &mut Vec<Rc<Definition>>,
    ) -> Result<()> {
        if !state.visited.insert(Rc::as_ptr(linked) as usize) {
            return Ok(());
        }
        let (own, inherited) = own_definitions(linked)?;
        state.repeats.extend(
            inherited
                .into_iter()
                .map(|definition| (state.listed, definition)),
        );
        state.listed += own.len();
        startup.extend(own);
        let mut groups = Vec::new();
        for nested in &linked.module.modules {
            let Some(nested) = state
                .link_order
                .iter()
                .find(|other| other.module.name == nested.name)
                .cloned()
            else {
                continue;
            };
            let mut group = Vec::new();
            walk(state, &nested, own_definitions, &mut group)?;
            startup.extend(group.iter().cloned());
            groups.push(group);
        }
        if groups.len() > 1 {
            state.siblings.push(groups);
        }
        Ok(())
    }
    let mut state = Walk {
        link_order: &link_order,
        visited: FastSet::default(),
        siblings: Vec::new(),
        repeats: Vec::new(),
        listed: 0,
    };
    let mut startup = Vec::new();
    let mut root_start = None;
    for linked in link_order
        .iter()
        .filter(|linked| !inner.contains(&linked.module.name))
    {
        if Rc::ptr_eq(linked, linked_root) {
            root_start.get_or_insert(startup.len());
        }
        walk(&mut state, linked, &own_definitions, &mut startup)?;
    }
    // An inner module no module of a file holds, which the front end still keeps.
    for linked in link_order.iter() {
        walk(&mut state, linked, &own_definitions, &mut startup)?;
    }
    // TLC computes the definitions of a module an INSTANCE without parameters names, a module of
    // a file SANY finishes before the module that instantiates it, with that module's, and
    // computes an unnamed INSTANCE's definitions no more: they are the same `OpDefNode`s, whose
    // values `lookup` then finds. The copy a named INSTANCE makes (`I!D`, a node of its own,
    // whose body names the module's own definitions), or any INSTANCE of a module with
    // parameters, TLC computes where the instantiating module defines it, as the front end does,
    // each copy a definition of its own; the definitions of a module with parameters TLC doesn't
    // compute (`ModuleNode.processConstantDefns`), which the front end does only where another
    // module extends it. The copies of an inner module, or those an INSTANCE in a LET makes, the
    // front end doesn't order as TLC does; but of an inner module with parameters, TLC computes
    // the copies alone, which the root module's order holds where its INSTANCE is written, and
    // none of the module's own definitions (`ModuleNode.processConstantDefns` is false for a
    // module instantiated with parameters).
    let unordered = linker.unordered_instancees.borrow();
    let in_startup: FastSet<usize> = startup
        .iter()
        .map(|definition| Rc::as_ptr(definition) as usize)
        .collect();
    let instanced = link_order
        .iter()
        .filter(|linked| {
            unordered.contains(&linked.module.name)
                || instantiated.contains(&linked.module.name)
                    && !(linked.constants.is_empty() && linked.variables.is_empty())
        })
        .flat_map(|linked| {
            let is_parameter_free = linked.constants.is_empty() && linked.variables.is_empty();
            linked
                .exported
                .values()
                .filter_map(|symbol| definitions.get(&symbol.key).cloned())
                .filter(|definition| {
                    unordered.contains(&linked.module.name) && is_parameter_free
                        || in_startup.contains(&(Rc::as_ptr(definition) as usize))
                })
                .collect::<Vec<_>>()
        })
        .collect();
    let root_start = root_start.unwrap_or(startup.len());
    Ok((
        (startup, state.siblings, instanced, state.repeats),
        root_start,
    ))
}

// Whether the expression, or a definition it names, reads a variable or primes, which makes its
// level bound above constant; the startup checks confirm it with the level analysis.
fn reaches_variable(
    definitions: &OrderedMap<Name, Rc<Definition>>,
    variables: &FastSet<Name>,
    body: &Expr,
) -> bool {
    let mut pending: Vec<Expr> = vec![body.clone()];
    let mut visited = FastSet::default();
    while let Some(node) = pending.pop() {
        if !visited.insert(Rc::as_ptr(&node) as usize) {
            continue;
        }
        if matches!(
            node.kind,
            ExpressionKind::Prime(_)
                | ExpressionKind::Unchanged(_)
                | ExpressionKind::Enabled(_)
                | ExpressionKind::Always(_)
                | ExpressionKind::Eventually(_)
                | ExpressionKind::Action { .. }
                | ExpressionKind::Fairness { .. }
        ) {
            return true;
        }
        if let Some(reference) = node.reference() {
            if variables.contains(&reference) {
                return true;
            }
            if let Some(definition) = definitions.get(&reference) {
                pending.push(definition.body.clone());
            }
        }
        pending.extend(node.children());
    }
    false
}

// Whether the expression names any of the symbols whose keys are `keys`.
fn references_any(root: &Expr, keys: &FastSet<Name>) -> bool {
    let mut pending: Vec<Expr> = vec![root.clone()];
    let mut visited = FastSet::default();
    while let Some(node) = pending.pop() {
        if !visited.insert(Rc::as_ptr(&node) as usize) {
            continue;
        }
        if node
            .reference()
            .is_some_and(|reference| keys.contains(&reference))
        {
            return true;
        }
        pending.extend(node.children());
    }
    false
}

/// How many times each name is written in the expressions, as a reference, its resolved key, or
/// a string (as TLCEvalDefinition names a definition), or none where one holds an INSTANCE in a
/// LET, which may name anything.
fn get_written_names(roots: impl Iterator<Item = Expr>) -> Option<FastMap<Name, usize>> {
    let mut written: FastMap<Name, usize> = FastMap::default();
    let mut pending: Vec<Expr> = roots.collect();
    while let Some(node) = pending.pop() {
        let mut names: Vec<Name> = Vec::new();
        match &node.kind {
            ExpressionKind::Let {
                instances: Some(_), ..
            } => return None,
            ExpressionKind::Identifier { name, .. }
            | ExpressionKind::Apply { operator: name, .. }
            | ExpressionKind::OperatorReference { operator: name, .. } => {
                names.push(name.clone());
            }
            ExpressionKind::String { value } => names.push(value.clone()),
            _ => {}
        }
        names.extend(node.reference());
        names.sort();
        names.dedup();
        for name in names {
            *written.entry(name).or_insert(0) += 1;
        }
        // A string an operator only compares, prints or evaluates as a value names nothing.
        let is_valued = matches!(&node.kind, ExpressionKind::Apply { .. })
            && !node.is_locally_resolved()
            && node.reference().is_some_and(|name| {
                matches!(
                    &*name,
                    "=" | "#" | "/=" | "TLCEval" | "Print" | "PrintT" | "ToString"
                )
            });
        pending.extend(
            node.children()
                .into_iter()
                .filter(|child| !is_valued || !matches!(child.kind, ExpressionKind::String { .. })),
        );
    }
    Some(written)
}

/// Whether an expression writes `name`, as `get_written_names` counts it, at least once.
fn writes_name(expression: &Expr, name: &Name) -> bool {
    get_written_names(std::iter::once(expression.clone()))
        .is_none_or(|written| written.contains_key(name))
}

/// Whether evaluating an expression, through the definitions it names, may reach an EXCEPT,
/// which may warn as TLC computes it.
fn writes_except(definitions: &OrderedMap<Name, Rc<Definition>>, body: &Expr) -> bool {
    let mut pending: Vec<Expr> = vec![body.clone()];
    let mut visited = FastSet::default();
    while let Some(node) = pending.pop() {
        if !visited.insert(Rc::as_ptr(&node) as usize) {
            continue;
        }
        if matches!(node.kind, ExpressionKind::Except { .. }) {
            return true;
        }
        if !node.is_locally_resolved()
            && let Some(definition) = node.reference().and_then(|name| definitions.get(&name))
        {
            if let DefinitionKind::Function { bounds } = &definition.kind {
                pending.extend(bounds.iter().map(|bound| bound.set.clone()));
            }
            pending.push(definition.body.clone());
        }
        pending.extend(node.children());
    }
    false
}

/// Whether evaluating an expression under any of `roots` can read any of the symbols whose keys
/// are `keys`: TLC binds an argument of an operator it evaluates as written to a `LazyValue`
/// (`getOpContext`), which it computes only where the operator's body reads the parameter, so
/// an argument of a parameter the body never names is never read (`Ignore(x) == TRUE`).
fn references_shown(
    roots: &[Expr],
    keys: &FastSet<Name>,
    definitions: &OrderedMap<Name, Rc<Definition>>,
    is_plain: &dyn Fn(&Name) -> bool,
) -> bool {
    references_shown_but(roots, keys, definitions, is_plain, &FastSet::default())
}

/// Whether evaluating a body may evaluate a name written in it, as an operator's parameter:
/// TLC evaluates only the branch a literal IF condition or CASE guard takes, a junction's operands
/// up to a literal that decides it, and a LET's definitions its body, or one of them it
/// computes, names (`references_shown`'s rules, by the written name, where any binding of the
/// same name inside counts as the name).
fn may_evaluate_name(body: &Expr, name: &Name) -> bool {
    let is_written = |expression: &Expr| match &expression.kind {
        ExpressionKind::Identifier { name: written, .. }
        | ExpressionKind::Apply {
            operator: written, ..
        }
        | ExpressionKind::OperatorReference {
            operator: written, ..
        } => written == name,
        _ => false,
    };
    fn names(expression: &Expr, name: &Name) -> bool {
        matches!(
            &expression.kind,
            ExpressionKind::Let {
                instances: Some(_),
                ..
            }
        ) || match &expression.kind {
            ExpressionKind::Identifier { name: written, .. }
            | ExpressionKind::Apply {
                operator: written, ..
            }
            | ExpressionKind::OperatorReference {
                operator: written, ..
            } => written == name,
            _ => false,
        } || expression.children().iter().any(|child| names(child, name))
    }
    let mut pending: Vec<Expr> = vec![body.clone()];
    while let Some(node) = pending.pop() {
        if is_written(&node) {
            return true;
        }
        match &node.kind {
            ExpressionKind::If {
                condition,
                consequent,
                alternative,
            } if get_literal_boolean(condition).is_some() => {
                let holds = get_literal_boolean(condition) == Some(true);
                pending.push(if holds { consequent } else { alternative }.clone());
            }
            ExpressionKind::Junction {
                is_and, operands, ..
            } => {
                for operand in operands {
                    pending.push(operand.clone());
                    if get_literal_boolean(operand) == Some(!*is_and) {
                        break;
                    }
                }
            }
            ExpressionKind::Let {
                definitions: lets,
                instances: None,
                recursive,
                body,
            } if recursive.is_empty() => {
                let mut reached: Vec<Expr> = vec![body.clone()];
                let mut is_taken = vec![false; lets.len()];
                loop {
                    let mut added = Vec::new();
                    for (index, definition) in lets.iter().enumerate() {
                        if !is_taken[index]
                            && reached
                                .iter()
                                .any(|expression| names(expression, &definition.name))
                        {
                            is_taken[index] = true;
                            if let DefinitionKind::Function { bounds } = &definition.kind {
                                added.extend(bounds.iter().map(|bound| bound.set.clone()));
                            }
                            added.push(definition.body.clone());
                        }
                    }
                    if added.is_empty() {
                        break;
                    }
                    reached.extend(added);
                }
                pending.extend(reached);
            }
            _ => pending.extend(node.children()),
        }
    }
    false
}

/// The value of a literal `TRUE` or `FALSE` nothing redefines.
fn get_literal_boolean(expression: &Expr) -> Option<bool> {
    if !matches!(&expression.kind, ExpressionKind::Identifier { .. })
        || expression.is_locally_resolved()
    {
        return None;
    }
    match expression.reference().as_deref() {
        Some("TRUE") => Some(true),
        Some("FALSE") => Some(false),
        _ => None,
    }
}

/// Whether an expression reads, without anything that applies or substitutes it, one of `names`.
fn is_bare_reference(expression: &Expr, names: &FastSet<Name>) -> bool {
    matches!(&expression.kind, ExpressionKind::Identifier { .. })
        && !expression.is_locally_resolved()
        && expression
            .reference()
            .is_some_and(|reference| names.contains(&reference))
}

/// Where `node` is one of the shapes below, the parts of it whose reads still count, leaving out
/// the bare reads of `opaque` that TLC computes but never looks into: the elements of a tuple
/// whose length `Len` takes (`TupleValue.size`), of a tuple or the fields of a record whose
/// DOMAIN is taken, the first element of a tuple `Tail` drops (`Sequences.Tail` copies the
/// others), and the elements of two tuples compared with `=`, `#` or `/=` that `TupleValue.equals`
/// tells apart before it compares them: by their lengths, or by their first elements, two
/// different numbers or two different strings.
fn get_uninspected_parts(
    node: &Expr,
    opaque: &FastSet<Name>,
    definitions: &OrderedMap<Name, Rc<Definition>>,
) -> Option<Vec<Expr>> {
    let ExpressionKind::Apply { operator, args, .. } = &node.kind else {
        return None;
    };
    if node.is_locally_resolved() || definitions.contains_key(operator) {
        return None;
    }
    let read = |elements: &[Expr]| -> Vec<Expr> {
        elements
            .iter()
            .filter(|element| !is_bare_reference(element, opaque))
            .cloned()
            .collect()
    };
    match (&**operator, args.as_slice()) {
        ("Len" | "DOMAIN", [operand]) => match &operand.kind {
            ExpressionKind::Tuple(elements) => Some(read(elements)),
            ExpressionKind::Record {
                is_set: false,
                fields,
            } if &**operator == "DOMAIN" => Some(read(
                &fields
                    .iter()
                    .map(|field| field.value.clone())
                    .collect::<Vec<_>>(),
            )),
            _ => None,
        },
        ("Tail", [operand]) => match &operand.kind {
            ExpressionKind::Tuple(elements)
                if elements
                    .first()
                    .is_some_and(|first| is_bare_reference(first, opaque)) =>
            {
                Some(elements[1..].to_vec())
            }
            _ => None,
        },
        ("=" | "#" | "/=", [left, right]) => {
            let (ExpressionKind::Tuple(left), ExpressionKind::Tuple(right)) =
                (&left.kind, &right.kind)
            else {
                return None;
            };
            let is_told_apart = left.len() != right.len()
                || match (
                    left.first().map(|first| &first.kind),
                    right.first().map(|first| &first.kind),
                ) {
                    (
                        Some(ExpressionKind::Number { value: a, .. }),
                        Some(ExpressionKind::Number { value: b, .. }),
                    ) => a != b,
                    (
                        Some(ExpressionKind::String { value: a }),
                        Some(ExpressionKind::String { value: b }),
                    ) => a != b,
                    _ => false,
                };
            is_told_apart.then(|| read(&left.iter().chain(right).cloned().collect::<Vec<_>>()))
        }
        _ => None,
    }
}

/// `references_shown`, where the reads of `opaque` that `get_uninspected_parts` leaves out don't
/// count.
fn references_shown_but(
    roots: &[Expr],
    keys: &FastSet<Name>,
    definitions: &OrderedMap<Name, Rc<Definition>>,
    is_plain: &dyn Fn(&Name) -> bool,
    opaque: &FastSet<Name>,
) -> bool {
    // Whether an expression may name `name`: an INSTANCE in a LET, whose substitutions aren't
    // among its children, may.
    fn writes(expression: &Expr, name: &Name) -> bool {
        if matches!(
            &expression.kind,
            ExpressionKind::Let {
                instances: Some(_),
                ..
            }
        ) {
            return true;
        }
        let written = match &expression.kind {
            ExpressionKind::Identifier { name, .. } => Some(name),
            ExpressionKind::Apply { operator, .. }
            | ExpressionKind::OperatorReference { operator, .. } => Some(operator),
            _ => None,
        };
        written == Some(name)
            || expression
                .children()
                .iter()
                .any(|child| writes(child, name))
    }
    let mut pending: Vec<Expr> = roots.to_vec();
    let mut visited = FastSet::default();
    while let Some(node) = pending.pop() {
        if !visited.insert(Rc::as_ptr(&node) as usize) {
            continue;
        }
        if !opaque.is_empty()
            && let Some(parts) = get_uninspected_parts(&node, opaque, definitions)
        {
            pending.extend(parts);
            continue;
        }
        let reference = node.reference();
        if reference
            .as_ref()
            .is_some_and(|reference| keys.contains(reference))
        {
            return true;
        }
        if let ExpressionKind::Apply { args, .. } = &node.kind
            && !node.is_locally_resolved()
            && let Some(reference) = reference.filter(|reference| is_plain(reference))
            && let Some(definition) = definitions.get(&reference)
            && let DefinitionKind::Operator { params, .. } = &definition.kind
            && params.len() == args.len()
        {
            for (param, arg) in params.iter().zip(args) {
                if param.arity != 0 || may_evaluate_name(&definition.body, &param.name) {
                    pending.push(arg.clone());
                }
            }
            continue;
        }
        match &node.kind {
            // `Tool`'s OPCODE_ite evaluates only the branch a literal condition takes.
            ExpressionKind::If {
                condition,
                consequent,
                alternative,
            } if matches!(&condition.kind, ExpressionKind::Identifier { .. })
                && !condition.is_locally_resolved()
                && condition
                    .reference()
                    .is_some_and(|name| &*name == "TRUE" || &*name == "FALSE") =>
            {
                let holds = condition.reference().is_some_and(|name| &*name == "TRUE");
                pending.push(if holds { consequent } else { alternative }.clone());
                continue;
            }
            // `Tool`'s junctions (OPCODE_cl, OPCODE_dl, OPCODE_land, OPCODE_lor) evaluate their
            // operands in order and stop at one that decides them, as a literal may.
            ExpressionKind::Junction {
                is_and, operands, ..
            } => {
                for operand in operands {
                    pending.push(operand.clone());
                    if get_literal_boolean(operand) == Some(!*is_and) {
                        break;
                    }
                }
                continue;
            }
            // OPCODE_case evaluates the guards in order and only the arm of the first that holds:
            // past a literal TRUE guard nothing is evaluated, and a literal FALSE guard's arm
            // never is.
            ExpressionKind::Case { arms, other } => {
                let mut is_decided = false;
                for (position, arm) in arms.iter().enumerate() {
                    match get_literal_boolean(&arm.condition) {
                        Some(false) => {}
                        Some(true) => {
                            pending.push(arm.body.clone());
                            is_decided = true;
                        }
                        None => {
                            for later in &arms[position..] {
                                pending.push(later.condition.clone());
                                pending.push(later.body.clone());
                            }
                            pending.extend(other.iter().cloned());
                            is_decided = true;
                        }
                    }
                    if is_decided {
                        break;
                    }
                }
                if !is_decided {
                    pending.extend(other.iter().cloned());
                }
                continue;
            }
            // TLC binds a LET's definitions lazily (`evalImplLetInKind`) and computes one only
            // where its body, or one of them it computes, names it.
            ExpressionKind::Let {
                definitions: lets,
                instances: None,
                recursive,
                body,
            } if recursive.is_empty() => {
                let mut reached: Vec<Expr> = vec![body.clone()];
                let mut is_taken = vec![false; lets.len()];
                loop {
                    let mut added = Vec::new();
                    for (index, definition) in lets.iter().enumerate() {
                        if !is_taken[index]
                            && reached
                                .iter()
                                .any(|expression| writes(expression, &definition.name))
                        {
                            is_taken[index] = true;
                            if let DefinitionKind::Function { bounds } = &definition.kind {
                                added.extend(bounds.iter().map(|bound| bound.set.clone()));
                            }
                            added.push(definition.body.clone());
                        }
                    }
                    if added.is_empty() {
                        break;
                    }
                    reached.extend(added);
                }
                pending.extend(reached);
                continue;
            }
            _ => {}
        }
        pending.extend(node.children());
    }
    false
}

// Whether an expression under any of `roots` names any of the symbols whose keys are `keys`.
fn references_any_of(roots: &[Expr], keys: &FastSet<Name>) -> bool {
    roots.iter().any(|root| references_any(root, keys))
}

/// The first of `keys` that `key` is, or a definition it was copied from through any number of
/// copies (named or in a LET), with the instance parameters the copies add.
fn get_copy_target(
    copy_sources: &OrderedMap<Name, (Name, usize)>,
    let_copy_sources: &OrderedMap<Name, (Name, usize)>,
    key: &Name,
    prefix: usize,
    keys: &FastSet<Name>,
) -> Option<(Name, usize)> {
    let mut current = (key.clone(), prefix);
    let mut seen = FastSet::default();
    loop {
        if keys.contains(&current.0) {
            return Some(current);
        }
        if !seen.insert(current.0.clone()) {
            return None;
        }
        let (source, added) = copy_sources
            .get(&current.0)
            .or_else(|| let_copy_sources.get(&current.0))?;
        current = (source.clone(), current.1 + added);
    }
}

/// Whether `key`, or a definition an INSTANCE with substitutions copied it from, through any number
/// of copies, is one of `keys`. The copy keeps the override of the definition it copies: an
/// unnamed `INSTANCE Base WITH C <- 7` beside `CONSTANT K <- A` and `A <- [Base] B` makes TLC fail
/// with the cast of an `OpDefNode` to a `Value` as it evaluates K, as the definition itself does.
/// The ClassCastException `makeConstantTable` throws where it adds a row of an operator's table
/// to the value the configuration gave its name before.
fn get_table_cast_error(value: &ConfigValue) -> FrontError {
    let class = match value {
        ConfigValue::Number(_) => "IntValue",
        ConfigValue::String(_) => "StringValue",
        ConfigValue::Boolean(_) => "BoolValue",
        ConfigValue::ModelValue(_) => "ModelValue",
        ConfigValue::Set(_) => "SetEnumValue",
        ConfigValue::Record(_) => "RecordValue",
    };
    FrontError::Evaluation(format!(
        "{}java.lang.ClassCastException\n: class tlc2.value.impl.{class} cannot be cast to class tlc2.value.impl.OpRcdValue (tlc2.value.impl.{class} and tlc2.value.impl.OpRcdValue are in unnamed module of loader 'app')",
        crate::errors::UNEXPECTED_HEAD
    ))
}

fn is_copy_of_any(
    copy_sources: &OrderedMap<Name, (Name, usize)>,
    key: &Name,
    keys: &dyn Fn(&Name) -> bool,
) -> bool {
    let mut current = key.clone();
    let mut seen = FastSet::default();
    loop {
        if keys(&current) {
            return true;
        }
        if !seen.insert(current.clone()) {
            return false;
        }
        match copy_sources.get(&current) {
            Some((source, _)) => current = source.clone(),
            None => return false,
        }
    }
}

/// The builtins a definition TLC computes as it starts may apply without an effect that shows
/// what it computed: no print, register, draw, assertion or file.
const BUILTINS_WITHOUT_EFFECTS: [&str; 44] = [
    "TRUE",
    "FALSE",
    "BOOLEAN",
    "STRING",
    "Nat",
    "Int",
    "Real",
    "=",
    "#",
    "/=",
    "\\in",
    "\\notin",
    "+",
    "-",
    "*",
    "-.",
    "\\div",
    "%",
    "^",
    "<",
    ">",
    "<=",
    ">=",
    "\\leq",
    "\\geq",
    "..",
    "\\cup",
    "\\cap",
    "\\",
    "\\subseteq",
    "SUBSET",
    "UNION",
    "DOMAIN",
    "Seq",
    "Len",
    "Head",
    "Tail",
    "Append",
    "\\o",
    "SubSeq",
    "Cardinality",
    "IsFiniteSet",
    "~",
    "=>",
];

/// Whether evaluating an expression applies, through the definitions it names, only builtins
/// without effects (`BUILTINS_WITHOUT_EFFECTS`).
fn is_without_effects(definitions: &OrderedMap<Name, Rc<Definition>>, body: &Expr) -> bool {
    is_without_effects_reading(definitions, body, &[])
}

/// `is_without_effects`, where applying the builtins `allowed` names has no effect either.
fn is_without_effects_but(
    definitions: &OrderedMap<Name, Rc<Definition>>,
    body: &Expr,
    allowed: &[&str],
) -> bool {
    is_without_effects_within(definitions, body, &[], allowed)
}

/// `is_without_effects`, where reading the variables `variables` names has no effect either, but
/// nothing above state level is: SANY's levels, which TLC's configuration checks read, never see
/// a substitute.
fn is_without_effects_reading(
    definitions: &OrderedMap<Name, Rc<Definition>>,
    body: &Expr,
    variables: &[Name],
) -> bool {
    is_without_effects_within(definitions, body, variables, &[])
}

fn is_without_effects_within(
    definitions: &OrderedMap<Name, Rc<Definition>>,
    body: &Expr,
    variables: &[Name],
    allowed: &[&str],
) -> bool {
    let mut pending: Vec<Expr> = vec![body.clone()];
    let mut visited = FastSet::default();
    while let Some(node) = pending.pop() {
        if !visited.insert(Rc::as_ptr(&node) as usize) {
            continue;
        }
        if !variables.is_empty() && !is_state_level_node(&node) {
            return false;
        }
        if !node.is_locally_resolved()
            && let Some(reference) = node.reference()
        {
            match definitions.get(&reference) {
                Some(definition) => {
                    if let DefinitionKind::Function { bounds } = &definition.kind {
                        pending.extend(bounds.iter().map(|bound| bound.set.clone()));
                    }
                    pending.push(definition.body.clone());
                }
                None if BUILTINS_WITHOUT_EFFECTS.contains(&&*reference)
                    || allowed.contains(&&*reference)
                    || variables.contains(&reference) => {}
                None => return false,
            }
        }
        pending.extend(node.children());
    }
    true
}

/// Whether an expression, through the definitions it names, is of state level at most.
fn is_state_level_through(definitions: &OrderedMap<Name, Rc<Definition>>, body: &Expr) -> bool {
    let mut pending: Vec<Expr> = vec![body.clone()];
    let mut visited = FastSet::default();
    while let Some(node) = pending.pop() {
        if !visited.insert(Rc::as_ptr(&node) as usize) {
            continue;
        }
        if !is_state_level_node(&node) {
            return false;
        }
        if !node.is_locally_resolved()
            && let Some(definition) = node.reference().and_then(|key| definitions.get(&key))
        {
            if let DefinitionKind::Function { bounds } = &definition.kind {
                pending.extend(bounds.iter().map(|bound| bound.set.clone()));
            }
            pending.push(definition.body.clone());
        }
        pending.extend(node.children());
    }
    true
}

/// Whether a node, its operands aside, is of state level at most.
fn is_state_level_node(node: &Expr) -> bool {
    match &node.kind {
        ExpressionKind::Prime(_)
        | ExpressionKind::Unchanged(_)
        | ExpressionKind::Enabled(_)
        | ExpressionKind::Always(_)
        | ExpressionKind::Eventually(_)
        | ExpressionKind::Action { .. }
        | ExpressionKind::Fairness { .. }
        | ExpressionKind::UnboundedQuantifier {
            is_temporal: true, ..
        } => false,
        ExpressionKind::Apply { operator, .. } => !matches!(&**operator, "~>" | "-+->" | "\\cdot"),
        _ => true,
    }
}

// Whether an expression under any of `roots` names the symbol whose key is `key`.
fn references_key(roots: &[Expr], key: &Name) -> bool {
    let mut pending: Vec<Expr> = roots.to_vec();
    let mut visited = FastSet::default();
    while let Some(node) = pending.pop() {
        if !visited.insert(Rc::as_ptr(&node) as usize) {
            continue;
        }
        if node.reference().is_some_and(|reference| reference == *key) {
            return true;
        }
        pending.extend(node.children());
    }
    false
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

#[cfg(test)]
mod standard_definition_tests {
    use super::*;

    /// The lookup, which parses only the modules whose text spells the name, finds what parsing
    /// every module and taking the first definition of the name would, for every builtin.
    #[test]
    fn finds_the_standard_definition_parsing_every_module_would() {
        let modules: Vec<Module> = standard_modules::MASTER
            .iter()
            .filter_map(|(_, source)| crate::parser::parse_module(source).ok())
            .collect();
        let names = CORE_OPERATORS.iter().map(|(name, _, _)| *name).chain(
            [standard_builtins::MASTER, standard_builtins::TLC_174]
                .into_iter()
                .flatten()
                .flat_map(|module| module.operators.iter().map(|operator| operator.name)),
        );
        let locate = |module: &Module, definition: &Definition| {
            (
                module.name.clone(),
                definition.name.clone(),
                definition.location.clone(),
            )
        };
        for name in names {
            let expected = modules.iter().find_map(|module| {
                let definition = module
                    .definitions
                    .iter()
                    .find(|definition| &*definition.name == name)?;
                Some(locate(module, definition))
            });
            let found = get_standard_module_definition(name)
                .map(|(module, definition)| locate(&module, &definition));
            assert_eq!(found, expected, "{name}");
        }
    }
}

#[cfg(test)]
mod deferred_origin_tests {
    use super::{EnvironmentOptions, create_environment};
    use crate::TlcVersion;
    use crate::config::parse_config;
    use crate::model::{ClassOrigin, JavaProfile, ModelOrigin, ParentRuntime};

    #[test]
    fn defer_execution_needs_the_modeled_parent_and_closed_method_selection() {
        let config = parse_config("", TlcVersion::Master).unwrap();
        for parent_runtime in [ParentRuntime::Unknown, ParentRuntime::ModeledTlcMasterJdk21] {
            for java_profile in [JavaProfile::Default, JavaProfile::Opaque] {
                for legacy_metadata in [false, true] {
                    for uncertain in [None, Some("TLCExt"), Some("tlc2.overrides.TLCOverrides")] {
                        for state in [ClassOrigin::Present, ClassOrigin::Unknown] {
                            let witness = |name: &str| {
                                if Some(name) == uncertain {
                                    state
                                } else {
                                    ClassOrigin::Absent
                                }
                            };
                            let origin = ModelOrigin {
                                parent_runtime,
                                resolved_class: None,
                                module_source_reads: None,
                                legacy_metadata,
                                java_profile,
                                class_origin: &witness,
                                closed_standard: std::cell::OnceCell::new(),
                            };
                            let environment = create_environment(&EnvironmentOptions {
                                linked_extendees: &[],
                                source: "---- MODULE M ----\nEXTENDS TLCExt\nTest == TLCDefer(TRUE)\n====\n",
                                load_module: &|_| None,
                                config: &config,
                                is_unconfigured: true,
                                version: TlcVersion::Master,
                                is_level_checked: false,
                                load_class: None,
                                origin: Some(&origin),
                            }).unwrap();
                            let flags = environment.builtins.get("TLCDefer").unwrap().flags;
                            assert_eq!(
                                flags & tla_ir::Builtin::PACKAGED_TLC_DEFER as u32 != 0,
                                parent_runtime == ParentRuntime::ModeledTlcMasterJdk21
                                    && java_profile == JavaProfile::Default
                                    && !legacy_metadata
                                    && uncertain.is_none(),
                            );
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod json_source_binding_tests {
    use super::*;
    use crate::model::{ClassOrigin, JavaProfile, ModelOrigin, ParentRuntime};

    fn with_environment(config: &str, check: impl FnOnce(&Environment)) {
        let mut origin = ModelOrigin::new(JavaProfile::Default, &|_| ClassOrigin::Absent);
        origin.parent_runtime = ParentRuntime::ModeledTlcMasterJdk21;
        let config = crate::config::parse_config(config, TlcVersion::Master).unwrap();
        let environment = link_environment(&EnvironmentOptions {
            linked_extendees: &[],
            origin: Some(&origin),
            source: "---- MODULE M ----\nEXTENDS Integers,TLC,Json\nCONSTANT F(_)\nG(x)==x\n====\n",
            load_module: &|_| None,
            config: &config,
            is_unconfigured: false,
            version: TlcVersion::Master,
            is_level_checked: false,
            load_class: None,
        })
        .unwrap();
        check(&environment);
    }

    #[test]
    fn configuration_table_and_scalar_replacements_invalidate_the_original_key() {
        for config in [
            "CONSTANT F(1)=TRUE ToJsonObject(1)=TRUE",
            "CONSTANT F(1)=TRUE ToJsonObject=TRUE",
            "CONSTANT F(1)=TRUE ToJsonObject <- G",
        ] {
            with_environment(config, |environment| {
                assert!(
                    !environment.has_json_source_opcode(&Rc::from("ToJsonObject"), "ToJsonObject")
                );
            });
        }
    }

    #[test]
    fn canonical_defns_snapshot_copies_the_actual_original_binding() {
        with_environment(
            "CONSTANT ToJsonObject(1)=TRUE F <- ToJsonObject",
            |environment| {
                assert!(
                    !environment.has_json_source_opcode(&Rc::from("ToJsonObject"), "ToJsonObject")
                );
                let target = environment.substitutions.get("F").unwrap();
                assert!(matches!(
                    environment.builtins.get(target).unwrap().intrinsic,
                    Some(Intrinsic::DefnsBuiltin)
                ));
                assert!(environment.has_json_source_opcode(target, "ToJsonObject"));
            },
        );
    }
}

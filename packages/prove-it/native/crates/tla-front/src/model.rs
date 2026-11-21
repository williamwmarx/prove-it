//! A model's IR from its spec and configuration, as the native binary reads it in place of the
//! TypeScript front end's.

use std::path::{Component, Path, PathBuf};
use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::{Name, SourceRange};
use crate::config::parse_config;
use crate::dependencies::create_definition_facts;
use crate::describe::{Description, Part, UNNAMED_ACTION, describe};
use crate::environment::{
    EnvironmentOptions, create_environment, create_environment_without_native_aliases,
    link_environment,
};
use crate::errors::{FrontError, TAUTOLOGY, format_range};
use crate::eval::Evaluator;
use crate::hash::{FastMap, FastSet};
use crate::lower::{Lowering, RankedTexts, Reach, is_startup_definition};
use crate::order::{TlcOrder, get_checker_strings, get_unique};
use crate::spec::{
    Properties, Specification, SubscriptCheck, check_invariants, check_search_config,
    create_identifier, get_properties, read_specification,
};
use crate::values::ValueOrder;

/// The module TLC adds to the root module's EXTENDS where it records the trace for its trace
/// exploration spec, for the post condition that writes it.
pub const TRACE_MODULE: &str = "_TLCTrace";

/// What the model is checked with besides its files. File-based APIs choose the supported
/// pinned Master/JDK21 parent reference model for Master; this does not inspect an ambient JVM.
pub struct ModelOptions<'a> {
    /// The directories of the modules a spec reads that aren't beside it, such as the community
    /// modules, in the order TLC searches them (`-DTLA-Library`).
    pub libraries: &'a [&'a Path],
    /// The TLC version the run asks for, or none for the default, master's.
    pub version: Option<TlcVersion>,
    /// Whether TLC prints its warnings, which `-nowarning` turns off.
    pub is_warning_enabled: bool,
    /// Whether the IR holds TLCGet("spec") where an expression reads it, which the native
    /// binary checks the model with, as it holds TLC's actions; the TypeScript front end's model
    /// lowers neither.
    pub is_spec_described: bool,
    /// The seed TLC seeds its generator with, which `-seed` gives.
    pub random_seed: u64,
    /// The modules of the post conditions TLC adds to the root module's EXTENDS, in its order
    /// (`ParameterizedSpecObj`): `-dumpTrace`'s, and `_TLCTrace` where TLC records the trace for
    /// its trace exploration spec, its default. SANY loads them with the spec, which interns their
    /// strings, and each loads Integers, whose Java methods TLC then loads over Naturals'.
    pub root_extendees: &'a [&'a str],
}

/// A module's text from the spec's directory, or else the first library's that has it.
pub fn load_module(spec_path: &Path, libraries: &[&Path], name: &str) -> Option<String> {
    let directory = spec_path.parent().unwrap_or(Path::new("."));
    let file = format!("{name}.tla");
    std::iter::once(directory)
        .chain(libraries.iter().copied())
        .find_map(|directory| std::fs::read_to_string(directory.join(&file)).ok())
}

/// A message TLC prints itself as it starts, once it has computed the constant definitions and
/// before it checks the assumptions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StartupMessage {
    pub code: u32,
    pub is_warning: bool,
    pub text: String,
    /// The position among the IR's startup predicates of the invariant TLC warns about only where
    /// the value the engine computes for it at startup is TRUE; none for a message TLC prints
    /// whatever the startup computes.
    pub predicate: Option<usize>,
}

/// A model's IR, and what TLC prints as it starts the model besides SANY's report and what the
/// startup's Print and PrintT print.
pub struct LoweredModel {
    pub ir: Vec<u8>,
    /// The messages, or why the front end doesn't know them yet.
    pub startup_messages: Result<Vec<StartupMessage>, String>,
    /// What TLC prints of the Java overrides it loads, right after `Starting...`, before it
    /// computes the constant definitions.
    pub override_messages: Vec<StartupMessage>,
    /// The names TLC's `Defns` holds: the definitions, the standard modules' operators and the
    /// declared constants.
    pub defined_names: Vec<String>,
    /// How a simulation labels an initial state, as `TLCStateInfo` labels the last of TLC's
    /// initial predicates (`initPredVec`): `Init line 4, col 9 to line 4, col 13 of module M`, or
    /// `Initial predicate` and where an unnamed one is written. None where the front end can't
    /// tell.
    pub initial_label: Option<String>,
    /// The name of that initial predicate, the module it is written in and where (begin line and
    /// column, end line and column), which TLC's simulator records as the action of an initial
    /// state (`TLCGet("action")`). None where the front end can't tell.
    pub initial_action: Option<(String, String, [i32; 4])>,
    /// SANY's warnings as the library's check prints them where its caller didn't print SANY's
    /// report (`formatSanyWarnings`), or none.
    pub sany_warnings: Vec<String>,
    /// `Lowering::is_tlcext_declined`: the engine computes fewer constant definitions as it
    /// starts than TLC, which may print.
    pub is_tlcext_declined: bool,
    /// `Lowering::alias_decline`.
    pub alias_decline: Option<String>,
}

/// The encoded IR of the model the configuration describes, without TLC's actions, which the
/// engine splits, or `NotYet` for what the front end doesn't lower yet.
pub fn lower_model(
    spec_path: &Path,
    config_text: &str,
    options: &ModelOptions,
) -> Result<Vec<u8>, FrontError> {
    lower_front(spec_path, config_text, options).map(|lowered| lowered.ir)
}

/// File-based lowering selects the supported pinned Master/JDK21 reference parent runtime
/// for Master, rather than describing an ambient JVM. To describe another execution contract,
/// use source-based lowering with an explicit `ModelOrigin` (generic origins default Unknown).
///
/// The model's IR, with what TLC prints itself as it starts: `createSearch`'s warnings about the
/// invariants and properties, then `createLivenessChecker`'s, in `printCheckProgress`'s words.
pub fn lower_front(
    spec_path: &Path,
    config_text: &str,
    options: &ModelOptions,
) -> Result<LoweredModel, FrontError> {
    with_files(spec_path, options, |sources, origin| {
        lower_ranked(sources, config_text, options, &[], Some(origin)).map(|(lowered, ..)| lowered)
    })
}

/// The Java override TLC loads for a module, by the module's name: the path TLC's resolver makes
/// for its class file, and the file's bytes.
pub type ClassLoader<'a> = dyn Fn(&str) -> Option<(PathBuf, Vec<u8>)> + 'a;

/// What a model is lowered from: the root module's text, the text of each other module by its
/// name, and the Java override TLC loads for a module, by its name (`loadClass`), with the path
/// TLC's resolver makes for its file, which TLC names the override by.
pub struct ModelSources<'a> {
    pub source: &'a str,
    pub load_module: &'a dyn Fn(&str) -> Option<String>,
    pub load_class: &'a ClassLoader<'a>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JavaProfile {
    Default,
    Opaque,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClassOrigin {
    Absent,
    Present,
    Unknown,
}

/// The reference parent runtime this execution deliberately models. This is neither an
/// ambient JVM observation nor proof that no user initialization has occurred.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ParentRuntime {
    #[default]
    Unknown,
    /// Pinned TLC master with Linux x86_64 Temurin 21.0.13+9 and no extra parent
    /// classpath, manifest companions, agents or patched modules. Consumers must
    /// separately establish their execution phase and absence of parent mutation.
    ModeledTlcMasterJdk21,
}

impl ParentRuntime {
    pub fn in_profile(self, version: TlcVersion, profile: JavaProfile) -> Self {
        if version == TlcVersion::Master && profile == JavaProfile::Default {
            self
        } else {
            Self::Unknown
        }
    }
}

pub struct ModelOrigin<'a> {
    /// Artifact/reference choice only; consumers still need their own execution-phase witness.
    pub parent_runtime: ParentRuntime,
    /// Path/byte attribution is consulted only after the active early-error boundary.
    pub resolved_class: Option<&'a ClassLoader<'a>>,
    /// Passive results of module reads already performed by the source resolver.
    pub module_source_reads: Option<&'a crate::source_reads::ModuleSourceReads>,
    /// Preserve the byte-based metadata used before class-origin tracking.
    pub(crate) legacy_metadata: bool,
    pub java_profile: JavaProfile,
    pub class_origin: &'a dyn Fn(&str) -> ClassOrigin,
    /// `is_closed_for` of no module but the standard ones, which the linker asks for each
    /// operator of each standard module.
    pub(crate) closed_standard: std::cell::OnceCell<bool>,
}

impl<'a> ModelOrigin<'a> {
    pub fn new(java_profile: JavaProfile, class_origin: &'a dyn Fn(&str) -> ClassOrigin) -> Self {
        Self {
            parent_runtime: ParentRuntime::Unknown,
            resolved_class: None,
            module_source_reads: None,
            legacy_metadata: false,
            java_profile,
            class_origin,
            closed_standard: std::cell::OnceCell::new(),
        }
    }

    /// Whether the default JVM profile and resolver namespace exclude either override index.
    /// A failed byte read cannot establish this; all four presence witnesses are required.
    pub fn has_closed_override_index(&self) -> bool {
        if self.legacy_metadata || self.java_profile != JavaProfile::Default {
            return false;
        }
        [
            "tlc2.overrides.TLCOverrides",
            "tlc2/overrides/TLCOverrides",
            "tlc2.overrides.TLCBuiltInOverrides",
            "tlc2/overrides/TLCBuiltInOverrides",
        ]
        .iter()
        .fold(true, |closed, name| {
            ((self.class_origin)(name) == ClassOrigin::Absent) & closed
        })
    }

    pub fn is_closed_for<'m>(&self, modules: impl IntoIterator<Item = &'m str>) -> bool {
        if self.legacy_metadata || self.java_profile != JavaProfile::Default {
            return false;
        }
        let is_absent = |name: &str| (self.class_origin)(name) == ClassOrigin::Absent;
        let has_class = |module: &str| {
            [
                module.to_owned(),
                format!("tlc2.module.{module}"),
                format!("tlc2/module/{module}"),
            ]
            .iter()
            .fold(false, |present, name| !is_absent(name) | present)
        };
        let mut closed = *self.closed_standard.get_or_init(|| {
            let mut closed = self.has_closed_override_index();
            closed &= !has_class("Strings");
            for (module, _) in crate::standard_modules::MASTER
                .iter()
                .chain(crate::standard_modules::TLC_174)
                .chain(crate::standard_modules::BUNDLED)
                .chain(crate::standard_modules::TLC_SOURCES)
            {
                closed &= !has_class(module);
            }
            closed
        });
        for module in modules {
            closed &= !has_class(module);
        }
        closed
    }
}

fn has_closed_java_context(
    environment: &crate::environment::Environment,
    extra_modules: &[&str],
    origin: &ModelOrigin<'_>,
) -> bool {
    let mut names = extra_modules.to_vec();
    let mut pending: Vec<_> = environment.modules.iter().collect();
    while let Some(module) = pending.pop() {
        names.push(module.name.as_ref());
        pending.extend(module.modules.iter());
    }
    origin.is_closed_for(names)
}

// The runtime linker does not establish the complete footprint of these contexts.
pub(crate) fn has_unlinked_instances(module: &crate::ast::Module) -> bool {
    use crate::ast::{
        AssumeProve, Assumed, DefinitionUnit, Expr, ExpressionKind, Fact, Proof, ProofKind,
        Statement, StepBody,
    };
    fn expression(value: &Expr) -> bool {
        let mut pending = vec![value.clone()];
        while let Some(value) = pending.pop() {
            if matches!(&value.kind, ExpressionKind::Let { instances: Some(instances), .. }
                if !instances.is_empty())
            {
                return true;
            }
            pending.extend(value.children());
        }
        false
    }
    fn assumed(assumed: &Assumed) -> bool {
        match assumed {
            Assumed::Expression(value) => expression(value),
            Assumed::NewSymbol(symbol) => symbol.set.as_ref().is_some_and(expression),
            Assumed::AssumeProve(value) | Assumed::Label { body: value, .. } => assume_prove(value),
        }
    }
    fn assume_prove(value: &AssumeProve) -> bool {
        value.assumptions.iter().any(assumed) || expression(&value.conclusion)
    }
    fn statement(value: &Statement) -> bool {
        match value {
            Statement::Expression(value) => expression(value),
            Statement::AssumeProve(value) => assume_prove(value),
        }
    }
    fn facts(values: &[Fact]) -> bool {
        values
            .iter()
            .any(|value| matches!(value, Fact::Expression(value) if expression(value)))
    }
    fn proof(value: &Proof) -> bool {
        match &value.kind {
            ProofKind::Obvious { .. } | ProofKind::Omitted { .. } => false,
            ProofKind::By {
                facts: values,
                defs,
                ..
            } => facts(values) || facts(defs),
            ProofKind::Steps { steps, .. } => steps.iter().any(|step| {
                let contains = match &step.body {
                    StepBody::Instance(_) => true,
                    StepBody::Define { definitions, .. } => {
                        definitions.iter().any(|unit| match unit {
                            DefinitionUnit::Instance(_) => true,
                            DefinitionUnit::Definition(value) => expression(&value.body),
                        })
                    }
                    StepBody::UseOrHide(value) => facts(&value.facts) || facts(&value.defs),
                    StepBody::Have(value) | StepBody::Case(value) => expression(value),
                    StepBody::Witness(values) => values.iter().any(expression),
                    StepBody::Take { bounds, .. } => {
                        bounds.iter().any(|bound| expression(&bound.set))
                    }
                    StepBody::Pick { bounds, body, .. } => {
                        bounds.iter().any(|bound| expression(&bound.set)) || expression(body)
                    }
                    StepBody::Assert {
                        statement: value, ..
                    } => statement(value),
                    StepBody::Qed => false,
                };
                contains || step.proof.as_deref().is_some_and(proof)
            }),
        }
    }
    module
        .theorems
        .iter()
        .any(|theorem| statement(&theorem.statement) || theorem.proof.as_ref().is_some_and(proof))
        || module
            .uses
            .iter()
            .any(|value| facts(&value.facts) || facts(&value.defs))
        || module
            .modules
            .iter()
            .any(|inner| has_unlinked_instances(inner))
}

/// The model's sources from the file system: the spec's file, the modules beside it or in the
/// libraries, and the classes beside it.
fn with_files<T>(
    spec_path: &Path,
    options: &ModelOptions,
    lower: impl FnOnce(&ModelSources, &ModelOrigin<'_>) -> Result<T, FrontError>,
) -> Result<T, FrontError> {
    let source = std::fs::read_to_string(spec_path)
        .map_err(|error| FrontError::Config(format!("{}: {error}", spec_path.display())))?;
    let directory = spec_path.parent().unwrap_or(Path::new("."));
    let origins = std::cell::RefCell::new(std::collections::HashMap::new());
    let class_origin = |name: &str| {
        if let Some(&known) = origins.borrow().get(name) {
            return known;
        }
        let mut found = ClassOrigin::Absent;
        // TLC keeps CWD as the resolver fallback for a relative main file
        // (TLC.java:1260; SimpleFilenameToStream.java:185). A missing dotted
        // index there still lets URLClassLoader find its slash-path class.
        let fallback = (!spec_path.is_absolute()).then_some(Path::new("."));
        for directory in fallback
            .into_iter()
            .chain(std::iter::once(directory))
            .chain(options.libraries.iter().copied())
        {
            match std::fs::symlink_metadata(directory.join(format!("{name}.class"))) {
                Ok(_) => {
                    found = ClassOrigin::Present;
                    break;
                }
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(_) => {
                    found = ClassOrigin::Unknown;
                    break;
                }
            }
        }
        origins.borrow_mut().insert(name.to_owned(), found);
        found
    };
    let load_class = |name: &str| {
        let path = directory.join(format!("{name}.class"));
        std::fs::read(&path).ok().map(|bytes| (path, bytes))
    };
    lower(
        &ModelSources {
            source: &source,
            load_module: &|name| load_module(spec_path, options.libraries, name),
            load_class: &load_class,
        },
        &ModelOrigin {
            // File APIs model this supported reference runtime; these library paths are
            // child resolver paths, not additions to its parent JVM classpath.
            parent_runtime: ParentRuntime::ModeledTlcMasterJdk21.in_profile(
                options.version.unwrap_or(TlcVersion::Master),
                JavaProfile::Default,
            ),
            resolved_class: Some(&load_class),
            module_source_reads: None,
            legacy_metadata: false,
            java_profile: JavaProfile::Default,
            class_origin: &class_origin,
            closed_standard: std::cell::OnceCell::new(),
        },
    )
}

/// What finds the texts TLC interns as it computes the constant definitions an IR holds, given
/// their indexes in TLC's order and how many of the IR's ranked texts TLC interned before.
pub type StartupTexts = dyn Fn(&tla_ir::Ir, &[tla_ir::Index], usize) -> Vec<Box<[u16]>>;

/// The model as `lower_front` lowers it, with the strings TLC makes as it computes the constant
/// definitions ranked after the spec's, as `check.ts` lowers its IR once it has computed them.
/// `get_startup_texts` finds them in the IR, given the indexes of the definitions TLC computes
/// as it starts, in its order; where it finds some, the model is lowered again with them ranked.
pub fn lower_front_ranking(
    spec_path: &Path,
    config_text: &str,
    options: &ModelOptions,
    get_startup_texts: &StartupTexts,
) -> Result<LoweredModel, FrontError> {
    with_files(spec_path, options, |sources, origin| {
        lower_front_ranking_with_origin(
            sources,
            config_text,
            options,
            get_startup_texts,
            Some(origin),
        )
    })
}

/// `lower_front_ranking` of the model's sources as the caller holds them.
pub fn lower_front_ranking_of(
    sources: &ModelSources,
    config_text: &str,
    options: &ModelOptions,
    get_startup_texts: &StartupTexts,
) -> Result<LoweredModel, FrontError> {
    lower_front_ranking_with_origin(sources, config_text, options, get_startup_texts, None)
}

pub fn lower_front_ranking_with_origin(
    sources: &ModelSources,
    config_text: &str,
    options: &ModelOptions,
    get_startup_texts: &StartupTexts,
    origin: Option<&ModelOrigin<'_>>,
) -> Result<LoweredModel, FrontError> {
    let (lowered, startup, interned) = lower_ranked(sources, config_text, options, &[], origin)?;
    let Ok(ir) = tla_ir::decode(&lowered.ir) else {
        return Ok(lowered);
    };
    let startup_texts = get_startup_texts(&ir, &startup, interned);
    if startup_texts.is_empty() {
        return Ok(lowered);
    }
    lower_ranked(sources, config_text, options, &startup_texts, origin).map(|(lowered, ..)| lowered)
}

/// Run the old metadata path solely to recover an early error; a model never escapes.
pub fn probe_legacy_error(
    sources: &ModelSources,
    config_text: &str,
    options: &ModelOptions,
    origin: &ModelOrigin<'_>,
) -> Option<FrontError> {
    let legacy = ModelOrigin {
        // An error-only legacy probe cannot establish a consumer execution phase.
        parent_runtime: ParentRuntime::Unknown,
        resolved_class: origin.resolved_class,
        module_source_reads: None,
        legacy_metadata: true,
        java_profile: origin.java_profile,
        class_origin: origin.class_origin,
        closed_standard: std::cell::OnceCell::new(),
    };
    lower_ranked(sources, config_text, options, &[], Some(&legacy)).err()
}

/// Whether TLC may print as it computes the constant definitions when it starts
/// (`processConstantDefns`), before an error lowering the model raises: where a definition it
/// computes then applies Print, PrintT or AssertEq, or a Java override may print. Not where TLC
/// stops first, at the configuration or at the rest of `processSpec`.
pub fn may_print_constant_definitions(sources: &ModelSources, config_text: &str) -> bool {
    let Ok(config) = parse_config(config_text, TlcVersion::Master) else {
        return false;
    };
    let load_class = |name: &str| (sources.load_class)(name).map(|(_, bytes)| bytes);
    let Ok(environment) = link_environment(&EnvironmentOptions {
        linked_extendees: &[],
        origin: None,
        source: sources.source,
        load_module: sources.load_module,
        config: &config,
        is_unconfigured: false,
        version: TlcVersion::Master,
        is_level_checked: false,
        load_class: Some(&load_class),
    }) else {
        return false;
    };
    let facts = create_definition_facts(&environment);
    let prints = StartupPrints::new(&environment, &facts);
    !environment.java_overrides.is_empty()
        || environment
            .startup_definitions
            .iter()
            .any(|definition| prints.may_print(definition))
}

/// Which of the definitions TLC computes as it starts (`processConstantDefns`) may print there:
/// those that apply Print, PrintT or AssertEq, of constant level to the definition facts or
/// register probes. TLCSet has no minimum level in Java (`TLCGetSet.TLCSet`), so `getLevelBound`
/// counts a definition that reaches it constant and TLC computes it, printing until TLCSet fails
/// on no checker, which it swallows: `D == PrintT(8) /\ TLCSet(1, 2)` prints `8` before a
/// configuration error. The definition facts count TLCSet of state level, so such a definition
/// isn't a startup definition to them.
pub(crate) struct StartupPrints<'a> {
    environment: &'a crate::environment::Environment,
    facts: &'a crate::dependencies::DefinitionFacts,
    reaches_print: Reach<'a>,
    reaches_register: Reach<'a>,
}

impl<'a> StartupPrints<'a> {
    pub(crate) fn new(
        environment: &'a crate::environment::Environment,
        facts: &'a crate::dependencies::DefinitionFacts,
    ) -> Self {
        Self {
            environment,
            facts,
            reaches_print: Reach::effects(
                environment,
                None,
                &["Print", "PrintT", "AssertEq"],
                false,
            ),
            reaches_register: Reach::effects(environment, None, &["TLCSet"], false),
        }
    }

    pub(crate) fn may_print(&self, definition: &Rc<crate::ast::Definition>) -> bool {
        let environment = self.environment;
        self.reaches_print.definition(definition)
            && (is_startup_definition(definition, environment, self.facts)
                || matches!(&definition.kind,
                    crate::ast::DefinitionKind::Operator { params, .. } if params.is_empty())
                    && !environment.constants.contains_key(&definition.name)
                    && !environment.substitutions.contains_key(&definition.name)
                    && self.reaches_register.definition(definition)
                    && crate::startup::get_definition_level_bound(environment, definition) == 0)
    }
}

/// Whether a root extendee is one of the trace modules TLC adds for its postconditions
/// (`_TLCTrace`, `_JsonTrace`), which reach Integers through TLCExt.
fn is_trace_module(name: &str) -> bool {
    matches!(name, "_TLCTrace" | "_JsonTrace")
}

/// The modules a trace module reads, as its text in TLC's jar instances them (`LOCAL INSTANCE`),
/// with those TLCExt's and TLC's own texts instance in turn.
fn get_trace_module_instancees(name: &str) -> &'static [&'static str] {
    const READ: [&str; 7] = [
        "TLC",
        "TLCExt",
        "Sequences",
        "Naturals",
        "Integers",
        "FiniteSets",
        "Json",
    ];
    match name {
        "_TLCTrace" => &READ[..6],
        "_JsonTrace" => &READ,
        _ => &[],
    }
}

/// The builtins whose effects show where TLC computes a constant definition again as it starts:
/// they print or draw. A register TLC sets as it starts it sets on no checker
/// (`TLCGetSet.TLCSet` fails, without a `mainChecker` or `simulator`, and `processConstantDefns`
/// swallows the failure), so `Foo == TLCSet(1, 5)` leaves `TLCGet(1)` undefined however often TLC
/// computes it, and reading a register or the clock shows nothing of itself.
const STARTUP_SHOWN_EFFECTS: [&str; 7] = [
    "Print",
    "PrintT",
    "RandomElement",
    "RandomSubset",
    "RandomSetOfSubsets",
    "RandomSubsetSet",
    "TestRandomSetOfSubsets",
];

/// The name of the first module `is_checked` picks that holds a constant definition with no
/// parameters that prints or draws, which TLC computes for each module whose definitions hold it
/// (`SpecProcessor.processConstantDefns`).
fn get_effect_module(
    environment: &crate::environment::Environment,
    is_checked: impl Fn(&crate::ast::Module) -> bool,
) -> Option<Name> {
    environment
        .modules
        .iter()
        .filter(|module| is_checked(module))
        .find(|module| {
            module.definitions.iter().any(|definition| {
                matches!(&definition.kind,
                    crate::ast::DefinitionKind::Operator { params, .. } if params.is_empty())
                    && crate::lower::reaches_effect(
                        definition,
                        environment,
                        None,
                        &STARTUP_SHOWN_EFFECTS,
                        false,
                    )
                    && crate::startup::get_definition_level_bound(environment, definition) == 0
            })
        })
        .map(|module| module.name.clone())
}

/// The modules the root module's EXTENDS names, in its order, or none where the front end's
/// lexer doesn't read the source.
pub fn get_root_extends(source: &str) -> Vec<String> {
    let Ok(tokens) = crate::lexer::tokenize(source) else {
        return Vec::new();
    };
    let Some(module) = (1..tokens.len()).find(|&index| {
        &*tokens[index].text == "MODULE"
            && tokens[index - 1].kind == crate::lexer::TokenKind::Separator
    }) else {
        return Vec::new();
    };
    let mut index = module + 2;
    while tokens
        .get(index)
        .is_some_and(|token| token.kind == crate::lexer::TokenKind::Separator)
    {
        index += 1;
    }
    if tokens
        .get(index)
        .is_none_or(|token| &*token.text != "EXTENDS")
    {
        return Vec::new();
    }
    let mut names = Vec::new();
    loop {
        index += 1;
        let Some(token) = tokens.get(index) else {
            break;
        };
        names.push(token.text.to_string());
        if tokens
            .get(index + 1)
            .is_none_or(|token| &*token.text != ",")
        {
            break;
        }
        index += 1;
    }
    names
}

/// The trace modules the root module extends where the configuration takes the postcondition
/// of one as the checker writes it (`-dumpTrace`'s): it names no postcondition of the module and
/// assigns its two constants, as the binary's command line leaves it once it moved the module's
/// postcondition to a dump. Linking gives the root module the constants the module declares, all
/// of its scope the root module may name besides the postcondition.
fn get_extended_trace_modules(source: &str, config: &crate::config::ModelConfig) -> Vec<String> {
    get_root_extends(source)
        .into_iter()
        .filter(|name| {
            is_trace_module(name)
                && !config.postconditions.contains(name)
                && ["File", "InputFile"].iter().all(|suffix| {
                    let constant = format!("{name}{suffix}");
                    config.constants.iter().any(|assignment| {
                        assignment.name == constant && assignment.module.is_none()
                    })
                })
        })
        .collect()
}

/// Why the binary can't link the modules of the command line's postconditions and invariants
/// into the root module's scope, where doing so would show. TLC only loads them beside the root
/// module (`ParameterizedSpecObj.findOrCreateParsedUnit` adds each to the root module's
/// `ModuleRelatives`, which orders the loading and SANY's analysis, while SANY's `Generator`
/// builds the root module's scope from its own EXTENDS): their CONSTANTs, VARIABLEs and ASSUMEs
/// aren't the root module's, and their definitions answer no name of the configuration. The
/// front end links them into the root module's EXTENDS, which reads as TLC does only where the
/// modules they bring declare none of those and define no name the root module's scope, the
/// configuration or another of them has.
fn get_linked_scope_leak(
    source: &str,
    load: &dyn Fn(&str) -> Option<String>,
    version: TlcVersion,
    config: &crate::config::ModelConfig,
    linked: &[&str],
) -> Option<&'static str> {
    fn find_inner(module: &crate::ast::Module, name: &str) -> Option<Rc<crate::ast::Module>> {
        module.modules.iter().find_map(|inner| {
            if &*inner.name == name {
                Some(inner.clone())
            } else {
                find_inner(inner, name)
            }
        })
    }
    let parse = |text: &str| {
        let tokens = crate::lexer::tokenize(text).ok()?;
        crate::parser::parse_module_tokens(text, &tokens, version)
            .ok()
            .map(Rc::new)
    };
    let root = parse(source)?;
    let find = |name: &str| -> Option<Rc<crate::ast::Module>> {
        if &*root.name == name {
            return Some(root.clone());
        }
        // SANY reads a standard module from TLC's jar unless a file of the user's replaces it.
        let text = crate::get_standard_module(name, version)
            .filter(|_| !(crate::environment::is_user_replaceable(name) && load(name).is_some()))
            .map(str::to_owned)
            .or_else(|| load(name))
            .or_else(|| {
                crate::standard_modules::BUNDLED
                    .iter()
                    .find(|module| module.0 == name)
                    .map(|module| module.1.to_owned())
            });
        find_inner(&root, name).or_else(|| parse(&text?))
    };
    // The modules a module brings into scope: those it extends and those it instantiates.
    let get_closure = |starts: Vec<Name>, seen: &mut FastSet<Name>| {
        let mut stack = starts;
        let mut found: Vec<Option<Rc<crate::ast::Module>>> = Vec::new();
        while let Some(name) = stack.pop() {
            if !seen.insert(name.clone()) {
                continue;
            }
            let module = find(&name);
            if let Some(module) = &module {
                stack.extend(module.extends.iter().cloned());
                stack.extend(
                    module
                        .instances
                        .iter()
                        .map(|instance| instance.module.clone()),
                );
            }
            found.push(module);
        }
        found
    };
    let mut seen = FastSet::default();
    let root_closure = get_closure(vec![root.name.clone()], &mut seen);
    let added = get_closure(
        linked.iter().map(|&name| Name::from(name)).collect(),
        &mut seen,
    );
    let get_names = |module: &crate::ast::Module| -> Vec<Name> {
        module
            .definitions
            .iter()
            .map(|definition| definition.name.clone())
            .chain(
                module
                    .instances
                    .iter()
                    .filter_map(|instance| instance.name.clone()),
            )
            .chain(
                module
                    .constants
                    .iter()
                    .map(|declaration| declaration.name.clone()),
            )
            .chain(
                module
                    .variables
                    .iter()
                    .map(|declaration| declaration.name.clone()),
            )
            .collect()
    };
    let mut taken: FastSet<Name> = root_closure
        .iter()
        .flatten()
        .flat_map(|module| get_names(module))
        .collect();
    for name in [
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
    .chain(&config.invariants)
    .chain(&config.properties)
    .chain(&config.constraints)
    .chain(&config.action_constraints)
    .chain(&config.possible)
    .chain(config.constants.iter().map(|constant| &constant.name))
    .chain(
        config
            .substitutions
            .iter()
            .flat_map(|substitution| [&substitution.name, &substitution.target]),
    ) {
        taken.insert(Name::from(name.as_str()));
    }
    for module in &added {
        let Some(module) = module else {
            return Some("a command-line module the front end can't read");
        };
        if !module.constants.is_empty()
            || !module.variables.is_empty()
            || !module.assumptions.is_empty()
        {
            return Some(
                "a command-line module that declares a CONSTANT, a VARIABLE or an ASSUME TLC keeps out of the root module",
            );
        }
        if get_names(module)
            .into_iter()
            .any(|name| !taken.insert(name))
        {
            return Some(
                "a command-line module that defines a name the root module or the configuration has",
            );
        }
    }
    None
}

fn lower_ranked(
    sources: &ModelSources,
    config_text: &str,
    options: &ModelOptions,
    startup_texts: &[Box<[u16]>],
    origin: Option<&ModelOrigin<'_>>,
) -> Result<(LoweredModel, Vec<tla_ir::Index>, usize), FrontError> {
    let version = options.version.unwrap_or(TlcVersion::Master);
    let source = sources.source;
    let load = sources.load_module;
    let load_class = |name: &str| (sources.load_class)(name).map(|(_, bytes)| bytes);
    let config = parse_config(config_text, version).map_err(|error| match error.unworded {
        Some(reason) => FrontError::NotYet(reason.to_owned()),
        None => FrontError::Config(error.message),
    })?;
    // The modules of the command line's postconditions join the root's EXTENDS; the trace
    // modules of -dumpTrace and the trace exploration spec are written by the checker itself.
    let linked_extendees: Vec<&str> = options
        .root_extendees
        .iter()
        .copied()
        .filter(|name| !is_trace_module(name))
        .collect();
    if !linked_extendees.is_empty()
        && let Some(reason) =
            get_linked_scope_leak(source, load, version, &config, &linked_extendees)
    {
        return Err(FrontError::NotYet(reason.to_owned()));
    }
    let extended_trace_modules = get_extended_trace_modules(source, &config);
    let link_load = |name: &str| {
        load(name).or_else(|| {
            extended_trace_modules
                .iter()
                .any(|module| module == name)
                .then(|| {
                    format!("---- MODULE {name} ----\nCONSTANT {name}File, {name}InputFile\n====")
                })
        })
    };
    // SANY's errors come from linking, before TLC's orders parse the modules again.
    let link = |allow_native_aliases| {
        let linking = EnvironmentOptions {
            linked_extendees: &linked_extendees,
            origin,
            source,
            load_module: &link_load,
            config: &config,
            is_unconfigured: false,
            version,
            is_level_checked: false,
            load_class: Some(&load_class),
        };
        if allow_native_aliases {
            create_environment(&linking)
        } else {
            create_environment_without_native_aliases(&linking)
        }
    };
    let mut environment = link(true)?;
    let extra_origin_modules: Vec<_> = options
        .root_extendees
        .iter()
        .copied()
        .chain(
            config
                .constants
                .iter()
                .filter_map(|assignment| assignment.module.as_deref()),
        )
        .chain(
            config
                .substitutions
                .iter()
                .filter_map(|substitution| substitution.module.as_deref()),
        )
        .collect();
    let is_java_origin_closed = origin
        .is_some_and(|origin| has_closed_java_context(&environment, &extra_origin_modules, origin));
    if is_java_origin_closed
        && origin.is_some_and(|origin| environment.has_pinned_standard_sources(origin, version))
        && environment
            .modules
            .iter()
            .all(|module| !has_unlinked_instances(module))
        && version == TlcVersion::Master
        && origin
            .is_some_and(|origin| origin.parent_runtime == ParentRuntime::ModeledTlcMasterJdk21)
    {
        for name in ["\\in", "\\notin"] {
            if let Some(builtin) = environment.builtins.get_mut(name) {
                builtin.flags |= tla_ir::Builtin::CLOSED_JAVA_CONTEXT as u32;
            }
        }
    }
    if !is_java_origin_closed
        && environment
            .builtins
            .values()
            .any(|builtin| matches!(builtin.intrinsic, Some(crate::environment::Intrinsic::Any)))
    {
        environment = link(false)?;
    }
    if !is_java_origin_closed && !origin.is_some_and(|origin| origin.legacy_metadata) {
        // Literal user definitions carry no builtin flags. Their new empty-domain
        // certificates need the same context witness as builtin-based certificates.
        environment.has_java_override_index = true;
        for builtin in environment.builtins.values_mut() {
            builtin.flags |= tla_ir::Builtin::EXTERNAL_CLASS as u32;
        }
    }
    // The trace modules TLC adds to the root module's EXTENDS (`_TLCTrace` where it writes its
    // trace exploration spec, and the -dumpTrace modules) instance TLC, TLCExt and through it
    // Integers, which the linking doesn't follow. TLC computes a constant definition again for
    // each module whose definitions hold it (`processConstantDefns`), so one a file of the user's
    // that replaces TLC, TLCExt, Integers, Naturals, Sequences or FiniteSets adds, that prints or
    // draws, has those effects again for them: the Jar prints a `Foo ==
    // PrintT("hidden")` of a user's TLC.tla three times beside `EXTENDS Integers, TLC`, once with
    // -noGenerateSpecTE.
    if !options.root_extendees.is_empty() {
        let replaced = |name: &str| {
            crate::standard_builtins::REPLACEABLE_TLC_MODULES.contains(&name) || name == "TLCExt"
        };
        if let Some(name) = get_effect_module(&environment, |module| replaced(&module.name)) {
            return Err(FrontError::NotYet(format!(
                "a definition with effects that TLC computes again for its trace modules, in a file of the user's that replaces {name}"
            )));
        }
        // The trace modules load a file of the user's whether or not the spec names it: a user's
        // TLC.tla beside `EXTENDS Naturals` alone, which the linking above never reads, has its
        // `Foo == PrintT("hidden")` printed three times (for TLC, `_TLCTrace`'s and TLCExt's
        // instances), and a user's Integers.tla twice, through TLCExt's `LOCAL INSTANCE
        // Integers`. The front end links each such file the trace modules read on its own, to
        // find such a definition in it or in a file of the user's it reads in turn.
        let mut read: Vec<&str> = Vec::new();
        for &name in options
            .root_extendees
            .iter()
            .flat_map(|name| get_trace_module_instancees(name))
        {
            if !read.contains(&name) && load(name).is_some() {
                read.push(name);
            }
        }
        for name in read {
            let text = format!("---- MODULE _TLCTrace ----\nLOCAL INSTANCE {name}\n====\n");
            let trace_config = crate::config::ModelConfig::default();
            let traced = create_environment(&EnvironmentOptions {
                linked_extendees: &[],
                origin: None,
                source: &text,
                load_module: &link_load,
                config: &trace_config,
                is_unconfigured: true,
                version,
                is_level_checked: false,
                load_class: Some(&load_class),
            });
            if let Ok(traced) = traced
                && let Some(name) = get_effect_module(&traced, |module| {
                    &*module.name != "_TLCTrace" && load(&module.name).is_some()
                })
            {
                return Err(FrontError::NotYet(format!(
                    "a definition with effects that TLC computes again for its trace modules, in a file of the user's they read, {name}"
                )));
            }
        }
    }
    // TLC loads Integers' methods over Naturals' once Integers is anywhere in the parsed closure.
    // The trace modules (`_TLCTrace` and the -dumpTrace modules) reach it through TLCExt, which
    // the linking doesn't follow; a postcondition's module is linked, which marks them itself.
    if !extended_trace_modules.is_empty()
        || options
            .root_extendees
            .iter()
            .any(|name| is_trace_module(name))
    {
        for builtin in environment.builtins.values_mut() {
            builtin.flags &=
                !(tla_ir::Builtin::NATURALS_GEQ | tla_ir::Builtin::NATURALS_METHOD) as u32;
        }
    }
    let order = TlcOrder::new(source, load, version)?.with_root_extendees(options.root_extendees);
    // TLC computes the constant definitions after SANY and before it builds its checker.
    let sany = order.get_sany_string_order(&config)?;
    let decoded: Vec<Option<String>> = startup_texts
        .iter()
        .map(|units| String::from_utf16(units).ok())
        .collect();
    // A text with a lone surrogate, which a `str` can't hold, as `Tail("😀a")` makes, ranks by a
    // name of its own and keeps its units for the IR's wide texts. The name is U+FFFF, as many
    // times as it takes to be no text the front ranks, then the units in hex.
    let taken: FastSet<&str> = sany
        .iter()
        .chain(decoded.iter().flatten())
        .map(String::as_str)
        .chain(get_checker_strings(&config))
        .collect();
    let mut wide: FastMap<Rc<str>, Box<[u16]>> = FastMap::default();
    let startup: Vec<String> = decoded
        .iter()
        .zip(startup_texts)
        .map(|(text, units)| {
            text.clone().unwrap_or_else(|| {
                let hex: String = units.iter().map(|unit| format!("{unit:04x}")).collect();
                let name = (1..)
                    .map(|count| format!("{}{hex}", "\u{FFFF}".repeat(count)))
                    .find(|name| !taken.contains(name.as_str()))
                    .expect("a name no text takes");
                wide.insert(Rc::from(name.as_str()), units.clone());
                name
            })
        })
        .collect();
    let texts: Vec<Rc<str>> = get_unique(
        sany.iter()
            .map(String::as_str)
            .chain(startup.iter().map(String::as_str))
            .chain(get_checker_strings(&config)),
    )
    .into_iter()
    .map(Rc::from)
    .collect();
    let variable_order = order.get_declaration_order(true)?;
    let ranks: FastMap<Rc<str>, u32> = texts
        .iter()
        .enumerate()
        .map(|(rank, text)| (text.clone(), rank as u32))
        .collect();
    environment.pinned_standard_sources =
        origin.is_some_and(|origin| environment.has_pinned_standard_sources(origin, version));
    let table_phase_profile = environment.pinned_standard_sources
        && is_java_origin_closed
        && environment
            .modules
            .iter()
            .all(|module| !has_unlinked_instances(module))
        && version == TlcVersion::Master
        && origin.is_some_and(|origin| {
            origin
                .parent_runtime
                .in_profile(version, origin.java_profile)
                == ParentRuntime::ModeledTlcMasterJdk21
        });
    environment
        .operator_objects
        .admit(&ValueOrder { ranks: &ranks }, table_phase_profile)?;
    if environment.operator_objects.is_admitted {
        for (key, method) in environment.operator_objects.method_aliases.iter() {
            environment.substitutions.remove(key);
            environment.definitions.remove(key);
            environment.constants.remove(key);
            environment.operator_constants.remove(key);
            environment
                .builtins
                .insert(key.clone(), method.builtin.clone());
        }
    }
    let facts = create_definition_facts(&environment);
    crate::eval::take_membership_too_deep();
    let evaluator = Evaluator::new(&environment, ValueOrder { ranks: &ranks }, version, true);
    check_constant_values(&config, &environment, &facts, &ValueOrder { ranks: &ranks })?;
    let lowered = (|| {
        let prints = StartupPrints::new(&environment, &facts);
        let may_print = !environment.java_overrides.is_empty()
            || environment
                .startup_definitions
                .iter()
                .any(|definition| prints.may_print(definition));
        // TLC computes the constant definitions, which may print, before it reads the
        // configuration's invariants, the specification and the properties (`SpecProcessor`'s
        // `processConstantDefns`, then `processConfig`). A definition whose value the constant
        // evaluator computes, which never prints, printed nothing there.
        let prints_first = may_print
            && (!environment.java_overrides.is_empty() || {
                let constant_evaluator =
                    Evaluator::new(&environment, ValueOrder { ranks: &ranks }, version, true);
                environment.startup_definitions.iter().any(|definition| {
                    prints.may_print(definition)
                        && constant_evaluator.evaluate(&definition.body, None).is_err()
                })
            });
        let printed_first = |error| match error {
            FrontError::Config(_) | FrontError::Evaluation(_) if prints_first => {
                FrontError::NotYet("what the spec prints as TLC computes its constants".to_owned())
            }
            error => error,
        };
        crate::lower::check_constant_through_tlc_set(
            &config,
            &environment,
            &facts,
            ValueOrder { ranks: &ranks },
            version,
        )?;
        let constant_invariants = check_invariants(
            &config,
            &environment,
            &facts,
            &evaluator,
            options.is_warning_enabled,
        )
        .map_err(printed_first)?;
        // TLC reads the specification after it warns about the invariants.
        let mut read_subscripts = Vec::new();
        let specification = read_specification(
            &config,
            &environment,
            &facts,
            version,
            Some(&evaluator),
            &mut read_subscripts,
        )
        .map_err(printed_first)
        .map_err(|error| {
            let invariants: Vec<(Rc<str>, Option<usize>)> = constant_invariants
                .iter()
                .flatten()
                .map(|name| (name.clone(), None))
                .collect();
            let is_unknown = read_subscripts
                .iter()
                .any(|check| matches!(check, SubscriptCheck::Unknown(_)));
            match error {
                FrontError::Config(_) | FrontError::Evaluation(_)
                    if options.is_warning_enabled && is_unknown =>
                {
                    FrontError::NotYet(
                        "an error in the specification after a subscript TLC warns of".to_owned(),
                    )
                }
                error @ FrontError::Config(_)
                    if options.is_warning_enabled
                        && !(invariants.is_empty()
                            && read_subscripts.iter().all(|check| !check.is_warned())) =>
                {
                    FrontError::Warned(
                        get_search_warnings(
                            &invariants,
                            &get_subscript_warnings(&read_subscripts, &variable_order),
                            &[],
                        ),
                        Box::new(error),
                    )
                }
                error => error,
            }
        })?;
        // TLC warns of the subscript of [][Next]_v as it reads the specification, before it
        // reads the properties.
        let property_error = |error| {
            let (property_warnings, error) = match error {
                FrontError::Warned(warnings, error) => (warnings, *error),
                error => (Vec::new(), error),
            };
            let error = printed_first(error);
            if matches!(error, FrontError::NotYet(_)) {
                return error;
            }
            if matches!(&error, FrontError::Evaluation(message) if message == TAUTOLOGY) {
                if may_print {
                    return FrontError::NotYet(
                        "what the spec prints as TLC computes its constants".to_owned(),
                    );
                }
                if !options.is_warning_enabled {
                    return error;
                }
                if specification
                    .subscripts
                    .iter()
                    .any(|check| matches!(check, SubscriptCheck::Unknown(_)))
                {
                    return FrontError::NotYet(
                        "a property TLC rejects after it warns of the subscript of [][Next]_v"
                            .to_owned(),
                    );
                }
                let invariants: Vec<_> = constant_invariants
                    .iter()
                    .flatten()
                    .map(|name| (name.clone(), None))
                    .collect();
                let mut warnings = get_search_warnings(
                    &invariants,
                    &get_subscript_warnings(&specification.subscripts, &variable_order),
                    &[],
                );
                warnings.extend(property_warnings);
                return if warnings.is_empty() {
                    error
                } else {
                    FrontError::Warned(warnings, Box::new(error))
                };
            }
            let error = if property_warnings.is_empty() {
                error
            } else {
                FrontError::Warned(property_warnings, Box::new(error))
            };
            match error {
                FrontError::Config(_) | FrontError::Evaluation(_)
                    if options.is_warning_enabled
                        && specification
                            .subscripts
                            .iter()
                            .any(SubscriptCheck::is_warned) =>
                {
                    FrontError::NotYet(
                        "a property TLC rejects after it warns of the subscript of [][Next]_v"
                            .to_owned(),
                    )
                }
                error => error,
            }
        };
        let properties = get_properties(&config, &environment, &facts, version, Some(&evaluator))
            .map_err(property_error)?;
        // TLC warns of each variable the subscript lacks in its order of the variables.
        let mut subscript_warnings = if options.is_warning_enabled {
            get_subscript_warnings(&specification.subscripts, &variable_order)
        } else {
            Vec::new()
        };
        if options.is_warning_enabled && specification.is_fairness_tautology {
            let property = &config.properties[0];
            let spec = config.specification.as_ref().unwrap();
            let range = |name: &str| {
                crate::spec::get_definition(name, &environment)
                    .and_then(|definition| definition.location.range.as_ref())
                    .map(format_range)
            };
            if let (Some(property_range), Some(spec_range)) = (range(property), range(spec)) {
                subscript_warnings.push(StartupMessage {
                    code: 2258,
                    is_warning: true,
                    predicate: None,
                    text: format!("Implied-temporal checking is a tautology.\nThe temporal formula {property} at {property_range} equals\nthe fairness constraints of the behavior specification {spec} at {spec_range}.\nTherefore, checking whether {spec} => {property} using TLC will never result in a violation of {property}."),
                });
            }
        }
        // `getTlcOrder`: the variables in TLC's order of declarations.
        let position = |index: &i32| {
            let variable = &environment.variables[*index as usize];
            variable_order
                .iter()
                .position(|name| name == variable)
                .unwrap_or(environment.variables.len())
        };
        let mut tlc_order: Vec<i32> = (0..environment.variables.len() as i32).collect();
        tlc_order.sort_by_key(position);
        let mut lowering = Lowering::new(
            &environment,
            RankedTexts {
                texts: &texts,
                ranks: ranks.clone(),
                wide: &wide,
            },
        );
        lowering.evaluator = Some(&evaluator);
        lowering.random_seed = options.random_seed;
        let version_text = options.version.map(|version| match version {
            TlcVersion::V1_7_4 => "1.7.4",
            TlcVersion::Master => "master",
        });
        // `processSpec`'s checks of the configuration, which count the invariants it keeps: not
        // those that are TRUE constants.
        let is_invariant_kept = match &constant_invariants {
            Some(constant_true) => config
                .invariants
                .iter()
                .any(|name| !constant_true.iter().any(|constant| **constant == **name)),
            None => !config.invariants.is_empty(),
        };
        let is_checking_behaviors = is_invariant_kept
            || !properties.invariants.is_empty()
            || !properties.action_properties.is_empty()
            || !properties.liveness.is_empty();
        // `processConfig` warns of the invariants, the subscripts and the properties before it
        // finds the initial or the next state predicate missing, after what the constant
        // definitions print.
        let with_config_warnings = |error: FrontError| {
            if may_print {
                return FrontError::NotYet(
                    "what the spec prints as TLC computes its constants".to_owned(),
                );
            }
            let warnings = if options.is_warning_enabled {
                get_search_warnings(
                    &constant_invariants
                        .iter()
                        .flatten()
                        .map(|name| (name.clone(), None))
                        .collect::<Vec<_>>(),
                    &subscript_warnings,
                    &properties.state_level,
                )
            } else {
                Vec::new()
            };
            if warnings.is_empty() {
                error
            } else {
                FrontError::Warned(warnings, Box::new(error))
            }
        };
        if specification.init.is_none()
            && (is_checking_behaviors
                || !properties.initial_predicates.is_empty()
                || !environment.variables.is_empty())
        {
            return Err(match version {
                TlcVersion::V1_7_4 => FrontError::NotYet("TLC 1.7.4's missing Init".to_owned()),
                TlcVersion::Master => with_config_warnings(FrontError::Config(
                    "The configuration file did not specify the initial state predicate."
                        .to_owned(),
                )),
            });
        }
        if specification.next.is_none() && is_checking_behaviors {
            return Err(with_config_warnings(FrontError::Config(
                "The configuration file did not specify the next state predicate.".to_owned(),
            )));
        }
        // TLC warns of the invariants and the properties before it reads the constraints, which it
        // reads after it computes the constant definitions, which may print first.
        check_search_config(&config, &environment, &facts, &evaluator).map_err(|error| {
            if may_print && matches!(error, FrontError::Config(_) | FrontError::Evaluation(_)) {
                return FrontError::NotYet(
                    "what the spec prints as TLC computes its constants".to_owned(),
                );
            }
            let invariants: Vec<(Rc<str>, Option<usize>)> = constant_invariants
                .iter()
                .flatten()
                .map(|name| (name.clone(), None))
                .collect();
            let properties: Vec<Rc<str>> = properties
                .state_level
                .iter()
                .map(|name| Rc::from(&**name))
                .collect();
            match error {
                error @ FrontError::Config(_)
                    if options.is_warning_enabled
                        && !(invariants.is_empty()
                            && subscript_warnings.is_empty()
                            && properties.is_empty()) =>
                {
                    FrontError::Warned(
                        get_search_warnings(&invariants, &subscript_warnings, &properties),
                        Box::new(error),
                    )
                }
                error => error,
            }
        })?;
        // `Tool.getActions` fails casting a variable's declaration to OpDefNode as TLC builds its
        // `Tool` (a ClassCastException), which the native checker doesn't report.
        if specification.has_action_variable_cast {
            return Err(FrontError::NotYet(
                "a variable or a constant TLC's splitting of the next-state relation reaches, which it fails to cast to a definition as it starts".to_owned(),
            ));
        }
        // A substituted constant's argument TLC evaluates as it splits the next-state action,
        // which may fail there, where TLC casts the constant's declaration.
        if let Some(reason) = specification.action_unknown_argument {
            return Err(FrontError::NotYet(reason.to_owned()));
        }
        if specification.has_action_parameter_cast {
            let has_effect = config
                .specification
                .as_deref()
                .and_then(|name| crate::spec::get_definition(name, &environment))
                .is_some_and(|definition| facts.is_impure_definition(definition, &environment));
            let unknown_startup = environment.startup_definitions.iter().any(|definition| {
                is_startup_definition(definition, &environment, &facts)
                    && matches!(
                        evaluator.evaluate(&definition.body, None),
                        Err(FrontError::NotYet(_))
                    )
            });
            if may_print
                || has_effect
                || unknown_startup
                || (options.is_warning_enabled
                    && specification
                        .subscripts
                        .iter()
                        .any(|check| matches!(check, SubscriptCheck::Unknown(_))))
                || environment.has_java_override_index
                || environment
                    .builtins
                    .values()
                    .any(|builtin| builtin.flags & tla_ir::Builtin::EXTERNAL_CLASS as u32 != 0)
            {
                return Err(FrontError::NotYet(
                    "what TLC evaluates before a formal next-state action's cast fails".to_owned(),
                ));
            }
            let error = FrontError::Evaluation(format!(
                "{}java.lang.ClassCastException\n: class tla2sany.semantic.FormalParamNode cannot be cast to class tla2sany.semantic.OpDefNode (tla2sany.semantic.FormalParamNode and tla2sany.semantic.OpDefNode are in unnamed module of loader 'app')",
                crate::errors::UNEXPECTED_HEAD,
            ));
            let warnings = if options.is_warning_enabled {
                get_search_warnings(
                    &constant_invariants
                        .iter()
                        .flatten()
                        .map(|name| (name.clone(), None))
                        .collect::<Vec<_>>(),
                    &subscript_warnings,
                    &properties.state_level,
                )
            } else {
                Vec::new()
            };
            return Err(if warnings.is_empty() {
                error
            } else {
                FrontError::Warned(warnings, Box::new(error))
            });
        }
        // TLC searches no states of a spec without variables, which `check.ts` lowers with FALSE for
        // Init and Next.
        let model = if environment.variables.is_empty() {
            let no_behavior = Some(create_identifier("FALSE"));
            let constant = Specification {
                has_action_parameter_cast: false,
                has_action_variable_cast: false,
                has_action_constant_cast: false,
                action_unknown_argument: None,
                init: no_behavior.clone(),
                next: no_behavior,
                scope: None,
                temporals: Vec::new(),
                is_fairness_tautology: false,
                subscripts: Vec::new(),
            };
            lowering.write_model(
                &config,
                &constant,
                &Properties::default(),
                options.is_warning_enabled,
                version_text,
                Vec::new(),
            )?
        } else {
            lowering
                .write_model(
                    &config,
                    &specification,
                    &properties,
                    options.is_warning_enabled,
                    version_text,
                    tlc_order,
                )
                // TLC warns about the invariants and the properties as it processes the spec,
                // before it starts the liveness checker.
                .map_err(|error| match error {
                    FrontError::Warned(warnings, error) if options.is_warning_enabled => {
                        FrontError::Warned(
                            get_search_warnings(
                                &constant_invariants
                                    .iter()
                                    .flatten()
                                    .map(|name| (name.clone(), None))
                                    .collect::<Vec<_>>(),
                                &subscript_warnings,
                                &properties.state_level,
                            )
                            .into_iter()
                            .chain(warnings)
                            .collect(),
                            error,
                        )
                    }
                    error => error,
                })?
        };
        let branches = lowering.branches;
        let is_tlcext_declined = lowering.is_tlcext_declined;
        let alias_decline = lowering.alias_decline.clone();
        let (ir, startup) = lowering.finish_indexing(model)?;
        // TLCGet("spec"), where an expression reads it; where the front end can't describe the
        // specification, the engine stops where TLC would read it.
        let description = describe(&config, &environment, &facts, &evaluator).ok();
        // TLC places a definition an INSTANCE with substitutions copies at the INSTANCE.
        let initial_label = description.as_ref().and_then(|description| {
            let init = description.inits.last()?;
            let location = environment
                .instance_actions
                .values()
                .find(|action| action.name == init.name)
                .map_or(&init.location, |action| &action.location);
            let range = format_range(location.range.as_ref()?);
            Some(if &*init.name == UNNAMED_ACTION {
                format!("Initial predicate {range}")
            } else {
                format!("{} {range}", init.name)
            })
        });
        let initial_action = description.as_ref().and_then(|description| {
            let init = description.inits.last()?;
            let location = environment
                .instance_actions
                .values()
                .find(|action| action.name == init.name)
                .map_or(&init.location, |action| &action.location);
            let range = location.range.as_ref()?;
            Some((
                init.name.to_string(),
                range.module.to_string(),
                [
                    range.start.line as i32,
                    range.start.column as i32,
                    range.end.line as i32,
                    range.end.column as i32,
                ],
            ))
        });
        let ir = match description {
            Some(description) if options.is_spec_described && reads_spec(&ir) => {
                tla_trace::add_spec(&ir, &to_spec_description(&ir, description)).unwrap_or(ir)
            }
            _ => ir,
        };
        // Under -nowarning TLC prints none of its warnings.
        let (constant_invariants, state_level) = if options.is_warning_enabled {
            (
                get_constant_invariants(&config, &environment, &facts),
                &properties.state_level[..],
            )
        } else {
            (Vec::new(), &[][..])
        };
        let unknown_subscript = specification
            .subscripts
            .iter()
            .find_map(|check| match check {
                SubscriptCheck::Unknown(reason) if options.is_warning_enabled => Some(reason),
                _ => None,
            });
        let startup_messages = get_startup_messages(
            &config,
            &constant_invariants,
            &subscript_warnings,
            state_level,
            branches,
            version,
            options.is_warning_enabled,
        )
        .and_then(|messages| match unknown_subscript {
            Some(reason) => Err(format!("TLC's warnings about {reason}")),
            None => Ok(messages),
        });
        let override_messages = get_override_messages(&environment, sources.load_class)
            .map(|messages| {
                // -nowarning drops a method that matches no operator.
                messages
                    .into_iter()
                    .filter(|message| options.is_warning_enabled || !message.is_warning)
                    .collect::<Vec<_>>()
            })
            .and_then(|messages| {
                // TLC lists the methods in an order that depends on the JVM.
                if messages.len() > 1 {
                    return Err("the Java overrides TLC lists in the JVM's order".to_owned());
                }
                Ok(messages)
            });
        let (startup_messages, override_messages) = match override_messages {
            Ok(messages) => (startup_messages, messages),
            Err(reason) => (Err(reason), Vec::new()),
        };
        let source_certificates = tla_ir::Builtin::PINNED_STANDARD_SOURCES
            | tla_ir::Builtin::TABLE_PHASE_KNOWN
            | tla_ir::Builtin::CLOSED_JAVA_CONTEXT;
        if environment.pinned_standard_sources
            && (environment.operator_objects.is_admitted
                || ir
                    .builtins
                    .iter()
                    .any(|builtin| builtin.flags & source_certificates != 0))
            && !origin
                .is_some_and(|origin| environment.has_pinned_standard_sources(origin, version))
        {
            return Err(FrontError::NotYet(
                "standard module source reads changed before metadata publication".to_owned(),
            ));
        }
        Ok((
            LoweredModel {
                sany_warnings: environment.printed.clone(),
                is_tlcext_declined,
                alias_decline,
                override_messages,
                ir: tla_ir::encode(&ir),
                startup_messages,
                // TLC's `Defns`: what the root module defines and declares, which a named
                // THEOREM or ASSUME isn't.
                defined_names: environment
                    .definitions
                    .keys()
                    .chain(environment.builtins.keys())
                    .chain(
                        environment
                            .root_constants
                            .iter()
                            .map(|constant| &constant.name),
                    )
                    .filter(|name| {
                        !matches!(
                            environment
                                .root_symbols
                                .get(*name)
                                .map(|symbol| &symbol.kind),
                            Some(crate::resolve::SymbolKind::Theorem)
                        )
                    })
                    .map(|name| name.to_string())
                    .collect(),
                initial_label,
                initial_action,
            },
            startup,
        ))
    })();
    // TLC stops on a constant predicate the engine checks at startup before what follows it, so
    // the front end can't report what follows.
    if lowered.is_ok() && crate::eval::take_membership_too_deep() {
        return Err(FrontError::NotYet(
            "a membership in a recursively defined filter too deep for the constant evaluator, which TLC may overflow its stack on or not finish".to_owned(),
        ));
    }
    match lowered {
        Err(error) if evaluator.is_deferring() && !matches!(error, FrontError::NotYet(_)) => Err(
            FrontError::NotYet("an error after a constant predicate the engine checks".to_owned()),
        ),
        lowered => lowered.map(|(lowered, startup)| (lowered, startup, sany.len())),
    }
}

/// `SpecProcessor.processConstantDefns` calls `initialize` on the value the configuration assigns
/// each declared constant, which normalizes its sets and fails where two of their elements can't
/// be compared, as TLC's report of an exception it didn't expect. It does so module by module, in
/// a Hashtable's order of each module's constants, among the constant definitions it computes and
/// the substitutions it checks there: the failure is reported where it is the only one and
/// nothing TLC computes there can print or fail otherwise, and a value the front end can't
/// follow or whose failure it can't word declines.
fn check_constant_values(
    config: &crate::config::ModelConfig,
    environment: &crate::environment::Environment,
    facts: &crate::dependencies::DefinitionFacts,
    order: &ValueOrder<'_>,
) -> Result<(), FrontError> {
    let mut failures = Vec::new();
    for declaration in &environment.root_constants {
        let name = &*declaration.name;
        let Some(assignment) = config.constants.iter().rev().find(|assignment| {
            assignment.module.is_none() && assignment.args.is_none() && assignment.name == name
        }) else {
            continue;
        };
        if declaration.arity != 0
            || config
                .substitutions
                .iter()
                .any(|substitution| substitution.name == name)
        {
            continue;
        }
        // A value the order can't follow, or whose failure `Values.ppr` would break, may fail
        // where the front end can't spell it out.
        if let Some(message) = order.get_initialize_failure(&assignment.value)? {
            failures.push(message);
        }
    }
    let Some(message) = failures.first() else {
        return Ok(());
    };
    let may_print = !environment.java_overrides.is_empty()
        || environment
            .startup_definitions
            .iter()
            .any(|definition| facts.is_impure_definition(definition, environment));
    if failures.len() > 1 || may_print || !config.substitutions.is_empty() {
        return Err(FrontError::NotYet(
            "a configured constant TLC fails to normalize among others it computes as it starts"
                .to_owned(),
        ));
    }
    Err(FrontError::Evaluation(format!(
        "{}{message}",
        crate::errors::UNEXPECTED_EXCEPTION
    )))
}

// `printCheckProgress`'s report of each method of a Java class that overrides a module, which
// names the class file by its URL (`Class#getResource`): the path TLC's resolver made for it, with
// `.` and `..` resolved by name, as a URL resolves them.
fn get_override_messages(
    environment: &crate::environment::Environment,
    load_class: &ClassLoader<'_>,
) -> Result<Vec<StartupMessage>, String> {
    environment
        .java_overrides
        .iter()
        .map(|java_override| {
            let class = load_class(&java_override.module).map_or_else(
                || PathBuf::from(format!("{}.class", java_override.module)),
                |(path, _)| path,
            );
            // WebAssembly has no working directory, and `is_absolute` is false there for any path,
            // so a path from the root stays as it is.
            let is_absolute =
                class.is_absolute() || cfg!(target_arch = "wasm32") && class.has_root();
            let absolute = if is_absolute {
                class
            } else {
                std::path::absolute(class).map_err(|error| error.to_string())?
            };
            let path = absolute
                .components()
                .fold(PathBuf::new(), |mut path, component| {
                    match component {
                        Component::CurDir => {}
                        Component::ParentDir => {
                            path.pop();
                        }
                        _ => path.push(component),
                    }
                    path
                });
            let path = path.to_str().unwrap_or_default();
            // `pathToFileURL` escapes what a URL can't hold, which the front end doesn't follow.
            let is_plain = !path.is_empty()
                && path.chars().all(|character| {
                    character.is_ascii_alphanumeric() || "/._-".contains(character)
                });
            let is_windows = path.contains('\\') || path.as_bytes().get(1) == Some(&b':');
            if is_windows {
                return Err("the URL TLC prints on Windows of a Java class".to_owned());
            }
            if !is_plain {
                return Err("the URL of a Java class whose path a URL escapes".to_owned());
            }
            Ok(StartupMessage {
                code: if java_override.is_matched { 2168 } else { 2400 },
                is_warning: !java_override.is_matched,
                predicate: None,
                text: format!(
                    "{} {} operator override from file:{path} with signature: <Java Method: {}>.",
                    if java_override.is_matched {
                        "Loading"
                    } else {
                        "Failed to match"
                    },
                    java_override.operator,
                    java_override.signature
                ),
            })
        })
        .collect()
}

// What TLC prints as it starts after the constant definitions: `createSearch`'s warnings, in the
// order it makes them, then `createLivenessChecker`'s (`printCheckProgress`). The printer adds
// the hint after TLC's first warning, drops a warning it printed already, and, under -nowarning,
// every warning (`createMessagePrinter`); the front end gives no warnings under -nowarning.
fn get_startup_messages(
    config: &crate::config::ModelConfig,
    constant_invariants: &[(Rc<str>, Option<usize>)],
    subscript_warnings: &[StartupMessage],
    state_level_properties: &[Rc<str>],
    branches: Option<usize>,
    version: TlcVersion,
    is_warning_enabled: bool,
) -> Result<Vec<StartupMessage>, String> {
    if version == TlcVersion::V1_7_4 {
        return Err("what TLC 1.7.4 prints as it starts".to_owned());
    }
    let mut messages = get_search_warnings(
        constant_invariants,
        subscript_warnings,
        state_level_properties,
    );
    // TLC warns about a symmetry set too small as it computes the symmetry, after these warnings,
    // which the binary prints once the configuration's predicates hold.
    if let Some(branches) = branches {
        if config.symmetry.is_some() && is_warning_enabled {
            messages.push(get_liveness_symmetry_warning());
        }
        messages.push(StartupMessage {
            code: 2212,
            is_warning: false,
            predicate: None,
            text: format!(
                "Implied-temporal checking--satisfiability problem has {branches} branches."
            ),
        });
    }
    Ok(messages)
}

// The invariants TLC may warn are constants that are TRUE (`processConfigInvariants`), in the
// configuration's order: each the configuration gives TRUE, and each the engine's startup
// computes, with its position among the IR's startup predicates.
fn get_constant_invariants(
    config: &crate::config::ModelConfig,
    environment: &crate::environment::Environment,
    facts: &crate::dependencies::DefinitionFacts,
) -> Vec<(Rc<str>, Option<usize>)> {
    // The invariants come first among the startup predicates, before the conjuncts of the
    // specification.
    let predicates = crate::spec::get_constant_predicates(config, environment, facts, &[]);
    config
        .invariants
        .iter()
        .filter(|name| !crate::spec::is_command_line_invariant(name))
        .filter_map(|name| {
            let predicate = predicates
                .iter()
                .position(|(_, kind, predicate, _)| *kind == "invariant" && predicate == name);
            let is_given = environment.constants.contains_key(name.as_str());
            // TLC holds an invariant the configuration substitutes for as the definition it names,
            // and doesn't warn of it.
            let is_substituted = environment.substitutions.contains_key(name.as_str());
            ((is_given || predicate.is_some()) && !is_substituted)
                .then(|| (Rc::from(name.as_str()), predicate))
        })
        .collect()
}

/// TLC's warnings about invariants that are TRUE constants, by name.
// `processConfigSpec`'s warnings about the subscript of each `[][Next]_v`.
fn get_subscript_warnings(
    subscripts: &[SubscriptCheck],
    variable_order: &[Rc<str>],
) -> Vec<StartupMessage> {
    let warning = |code: u32, text: String| StartupMessage {
        code,
        is_warning: true,
        text,
        predicate: None,
    };
    subscripts
        .iter()
        .flat_map(|check| match check {
            SubscriptCheck::Undetermined => vec![warning(
                2139,
                "TLC could not determine if the subscript of the next-state relation contains\nall state variables. Proceed with fingers crossed.".to_owned(),
            )],
            SubscriptCheck::Unknown(_) => Vec::new(),
            SubscriptCheck::Missing(missing) => variable_order
                .iter()
                .filter(|variable| missing.contains(*variable))
                .map(|variable| warning(
                    2140,
                    format!("The subscript of the next-state relation specified by the specification\ndoes not seem to contain the state variable {variable}"),
                ))
                .collect(),
        })
        .collect()
}

pub(crate) fn get_constant_invariant_warnings(names: &[Rc<str>]) -> Vec<StartupMessage> {
    let names: Vec<_> = names.iter().map(|name| (name.clone(), None)).collect();
    get_search_warnings(&names, &[], &[])
}

// `createSearch`'s warnings about the invariants and the properties.
pub(crate) fn get_search_warnings(
    constant_invariants: &[(Rc<str>, Option<usize>)],
    subscript_warnings: &[StartupMessage],
    state_level_properties: &[Rc<str>],
) -> Vec<StartupMessage> {
    let warning = |code: u32, text: String| StartupMessage {
        code,
        is_warning: true,
        text,
        predicate: None,
    };
    constant_invariants
        .iter()
        .map(|(name, predicate)| StartupMessage { predicate: *predicate, ..warning(2149, format!("The invariant {name} is a constant-level formula (i.e., it contains no variables, primes, or temporal operators) and evaluates to TRUE. To assert constant-level formulas in your spec, use ASSUME ConstInv. If you optionally want to give the assumption a name, write ASSUME YourAssumption == ConstInv instead. See https://explain.tlapl.us/assumptions-and-invariants for additional details.")) })
        .chain(subscript_warnings.iter().cloned())
        .chain(state_level_properties.iter().map(|name| warning(2255, format!("The formula {name} is a state-level formula, but it was used as a PROPERTY (or PROPERTIES), where a temporal formula is typically expected. State-level formulas used as PROPERTY or PROPERTIES are only checked in the initial state. To verify that the formula {name} holds in all states of every behavior, use INVARIANT {name} instead. Alternatively, applying the \"always\" temporal operator ([]) to the state-level formula {name} changes it into a temporal formula, asserting that {name} holds in all states of every behavior. See https://explain.tlapl.us/invariants-and-properties for additional details."))))
        .collect()
}

/// The warning TLC prints as it starts the liveness checker of a model with a symmetry
/// (`createLivenessChecker`).
pub fn get_liveness_symmetry_warning() -> StartupMessage {
    StartupMessage {
        code: 2279,
        is_warning: true,
        predicate: None,
        text: "Declaring symmetry during liveness checking is dangerous. It might cause TLC to miss violations of the stated liveness properties. Please check liveness without symmetry defined.".to_owned(),
    }
}

// Whether an expression of the IR applies TLC's TLCGet to "spec".
fn reads_spec(ir: &tla_ir::Ir) -> bool {
    ir.nodes.arena.iter().any(|node| match &node.kind {
        tla_ir::NodeKind::Apply { name, args } => {
            !name.is_local
                && matches!(name.resolution, tla_ir::Resolution::Builtin(index)
                    if &*ir.texts[ir.builtins[index as usize].name as usize] == "TLCGet")
                && args.first().is_some_and(|&arg| {
                    matches!(&ir.nodes.arena[arg as usize].kind,
                        tla_ir::NodeKind::String(text) if &*ir.texts[*text as usize] == "spec")
                })
        }
        _ => false,
    })
}

// The description with each part's range in the IR's texts.
fn to_spec_description(ir: &tla_ir::Ir, description: Description) -> tla_trace::SpecDescription {
    let range = |range: Option<&SourceRange>| {
        let range = range?;
        let module = ir.texts.iter().position(|text| **text == *range.module)?;
        Some(tla_ir::SourceRange {
            module: module as tla_ir::TextId,
            start_line: range.start.line as i32,
            start_column: range.start.column as i32,
            end_line: range.end.line as i32,
            end_column: range.end.column as i32,
        })
    };
    let parts = |parts: Vec<Part>| {
        parts
            .into_iter()
            .map(|part| tla_trace::Described {
                name: part.name.to_string(),
                range: range(part.location.range.as_ref()),
            })
            .collect()
    };
    tla_trace::SpecDescription {
        inits: parts(description.inits),
        temporals: parts(description.temporals),
        invariants: parts(description.invariants),
        implied_inits: parts(description.implied_inits),
        implied_actions: parts(description.implied_actions),
        implied_temporals: parts(description.implied_temporals),
        variables: parts(description.variables),
        action_constraints: parts(description.action_constraints),
        constraints: parts(description.constraints),
    }
}

#[cfg(test)]
mod origin_index_tests {
    use super::{ClassOrigin, JavaProfile, ModelOrigin, ParentRuntime};

    #[test]
    fn index_absence_needs_default_profile_and_every_presence_witness() {
        for profile in [JavaProfile::Default, JavaProfile::Opaque] {
            for state in [
                ClassOrigin::Absent,
                ClassOrigin::Present,
                ClassOrigin::Unknown,
            ] {
                let witness = |_: &str| state;
                let origin = ModelOrigin {
                    parent_runtime: ParentRuntime::Unknown,
                    legacy_metadata: false,
                    resolved_class: None,
                    module_source_reads: None,
                    java_profile: profile,
                    class_origin: &witness,
                    closed_standard: std::cell::OnceCell::new(),
                };
                assert_eq!(
                    origin.has_closed_override_index(),
                    profile == JavaProfile::Default && state == ClassOrigin::Absent
                );
            }
        }
        for uncertain in [
            "tlc2.overrides.TLCOverrides",
            "tlc2/overrides/TLCOverrides",
            "tlc2.overrides.TLCBuiltInOverrides",
            "tlc2/overrides/TLCBuiltInOverrides",
        ] {
            let witness = |name: &str| {
                if name == uncertain {
                    ClassOrigin::Unknown
                } else {
                    ClassOrigin::Absent
                }
            };
            let origin = ModelOrigin {
                parent_runtime: ParentRuntime::Unknown,
                legacy_metadata: false,
                resolved_class: None,
                module_source_reads: None,
                java_profile: JavaProfile::Default,
                class_origin: &witness,
                closed_standard: std::cell::OnceCell::new(),
            };
            assert!(!origin.has_closed_override_index());
        }
    }
    #[test]
    fn parent_runtime_is_an_explicit_choice_not_an_absence_inference() {
        let absent = |_: &str| ClassOrigin::Absent;
        let origin = ModelOrigin::new(JavaProfile::Default, &absent);
        assert_eq!(origin.parent_runtime, ParentRuntime::Unknown);
        let modeled = ParentRuntime::ModeledTlcMasterJdk21;
        assert_eq!(
            modeled.in_profile(crate::TlcVersion::Master, JavaProfile::Default),
            modeled
        );
        assert_eq!(
            modeled.in_profile(crate::TlcVersion::Master, JavaProfile::Opaque),
            ParentRuntime::Unknown
        );
        assert_eq!(
            modeled.in_profile(crate::TlcVersion::V1_7_4, JavaProfile::Default),
            ParentRuntime::Unknown
        );
    }

    #[test]
    fn file_api_parent_runtime_is_the_documented_reference_choice() {
        let path =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/report-cases/14/M.tla");
        for version in [
            None,
            Some(crate::TlcVersion::Master),
            Some(crate::TlcVersion::V1_7_4),
        ] {
            let options = super::ModelOptions {
                libraries: &[],
                version,
                is_warning_enabled: false,
                is_spec_described: false,
                random_seed: 1,
                root_extendees: &[],
            };
            let selected =
                super::with_files(&path, &options, |_, origin| Ok(origin.parent_runtime)).unwrap();
            assert_eq!(
                selected,
                if version == Some(crate::TlcVersion::V1_7_4) {
                    ParentRuntime::Unknown
                } else {
                    ParentRuntime::ModeledTlcMasterJdk21
                }
            );
        }
    }
}

#[cfg(test)]
mod configuration_table_unlinked_footprint_tests {
    use super::*;
    fn marked(proof: &str, extra: &str) -> bool {
        let source = format!(
            "---- MODULE M ----\nEXTENDS Base,TLC\nVARIABLE x\nTHEOREM T == TRUE\n{proof}\n{extra}\nG(v) == v\nASSUME G(1)\nInit == x=0\nNext == UNCHANGED x\n====\n"
        );
        let source_reads = crate::source_reads::ModuleSourceReads::default();
        let modules = |name: &str| {
            let text = (name == "Base").then(|| {
                "---- MODULE Base ----\nEXTENDS TLC\nCONSTANT N\nA == N\n====\n".to_owned()
            });
            source_reads.record(name, Ok(text.as_deref()));
            text
        };
        let report = crate::report::get_sany_text_of(
            "M",
            &source,
            &crate::report::ReportOptions {
                version: TlcVersion::Master,
                file_name: None,
                load_module: &modules,
                describe_file: &|name, _| Ok(name.to_owned()),
                root_extendees: &[],
                is_xml_export: false,
                lint_codes: Default::default(),
            },
        )
        .unwrap();
        assert!(!report.is_failed);
        let classes = |_: &str| None;
        let sources = ModelSources {
            source: &source,
            load_module: &modules,
            load_class: &classes,
        };
        let mut origin = ModelOrigin::new(JavaProfile::Default, &|_| ClassOrigin::Absent);
        origin.parent_runtime = ParentRuntime::ModeledTlcMasterJdk21;
        origin.module_source_reads = Some(&source_reads);
        let options = ModelOptions {
            libraries: &[],
            version: Some(TlcVersion::Master),
            is_warning_enabled: false,
            is_spec_described: false,
            random_seed: 0,
            root_extendees: &[],
        };
        let lowered = lower_front_ranking_with_origin(
            &sources,
            "CONSTANT N = 1 G(1) = TRUE\nINIT Init\nNEXT Next",
            &options,
            &|_, _, _| vec![],
            Some(&origin),
        )
        .unwrap();
        let ir = tla_ir::decode(&lowered.ir).unwrap();
        ir.builtins
            .iter()
            .any(|b| b.flags & tla_ir::Builtin::TABLE_PHASE_KNOWN != 0)
    }
    #[test]
    fn proof_instance_does_not_publish_table_phase_authority() {
        assert!(!marked(
            "<1>1. INSTANCE Base WITH N <- 2\n<1> QED OBVIOUS",
            ""
        ));
    }
    #[test]
    fn theorem_let_instance_does_not_publish_table_phase_authority() {
        assert!(!marked(
            "OBVIOUS\nTHEOREM U == LET I == INSTANCE Base WITH N <- 2 IN TRUE\nOBVIOUS",
            ""
        ));
    }
    #[test]
    fn ordinary_proof_and_linked_global_instance_keep_table_phase_authority() {
        assert!(marked("OBVIOUS", ""));
        assert!(marked("OBVIOUS", "I == INSTANCE Base WITH N <- 2"));
    }
}

#[cfg(test)]
mod pinned_standard_source_prefix_tests {
    use super::*;
    use crate::report::{ReportOptions, get_sany_text_of};
    use crate::source_reads::ModuleSourceReads;

    // The model lowered, or none where a custom TLC.tla beside Json declines: TLC computes the
    // file's definitions again for Json's LOCAL INSTANCE TLC (the Jar prints a definition
    // `Foo == PrintT("hidden")` the custom file adds twice), which the front end doesn't follow.
    fn lowered(
        custom: bool,
        journal: bool,
        parent: ParentRuntime,
        table: u8,
    ) -> Option<tla_ir::Ir> {
        let source = if table == 1 {
            "---- MODULE M ----\nEXTENDS Integers,TLC,Json\nG(x)==x\nASSUME G(1)=\"1\"\n====\n"
        } else if table == 2 {
            "---- MODULE M ----\nEXTENDS Integers,TLC,Json\nCONSTANT F(_)\nASSUME F([a |-> 1])=\"{\\\"a\\\":1}\"\n====\n"
        } else {
            "---- MODULE M ----\nEXTENDS Integers,TLC,Json\nASSUME ToJsonObject([a |-> TRUE])=\"{\\\"a\\\":true}\"\n====\n"
        };
        let reads = ModuleSourceReads::default();
        let modules = |name: &str| {
            let text = (name == "TLC").then(|| {
                let pinned = crate::get_standard_module(name, TlcVersion::Master).unwrap();
                if custom {
                    let at = pinned.rfind("\n====").unwrap();
                    format!(
                        "{}\nFoo == PrintT(\"hidden\"){}",
                        &pinned[..at],
                        &pinned[at..]
                    )
                } else {
                    pinned.to_owned()
                }
            });
            reads.record(name, Ok(text.as_deref()));
            text
        };
        let report = get_sany_text_of(
            "M",
            source,
            &ReportOptions {
                version: TlcVersion::Master,
                file_name: None,
                load_module: &modules,
                describe_file: &|name, _| Ok(name.to_owned()),
                root_extendees: &[],
                is_xml_export: false,
                lint_codes: Default::default(),
            },
        )
        .unwrap();
        assert!(!report.is_failed);
        let classes = |_: &str| None;
        let sources = ModelSources {
            source,
            load_module: &modules,
            load_class: &classes,
        };
        let mut origin = ModelOrigin::new(JavaProfile::Default, &|_| ClassOrigin::Absent);
        origin.parent_runtime = parent;
        origin.module_source_reads = journal.then_some(&reads);
        let options = ModelOptions {
            libraries: &[],
            version: Some(TlcVersion::Master),
            is_warning_enabled: false,
            is_spec_described: false,
            random_seed: 0,
            root_extendees: &[],
        };
        let lowered = lower_front_ranking_with_origin(
            &sources,
            match table {
                1 => "CONSTANT G(1)=\"1\" G(2)={1,\"a\"}",
                2 => "CONSTANT ToJsonObject(1)=TRUE F <- ToJsonObject",
                _ => "",
            },
            &options,
            &|_, _, _| vec![],
            Some(&origin),
        );
        match lowered {
            Ok(lowered) => Some(tla_ir::decode(&lowered.ir).unwrap()),
            Err(FrontError::NotYet(reason))
                if custom
                    && reason
                        == "a standard module that uses a module a file of the user's replaces: Json" =>
            {
                None
            }
            Err(error) => panic!("{error:?}"),
        }
    }

    #[test]
    fn existing_canonical_source_reads_publish_json_certificate() {
        let ir = lowered(false, true, ParentRuntime::ModeledTlcMasterJdk21, 0).unwrap();
        assert!(
            ir.builtins
                .iter()
                .any(|b| b.flags & tla_ir::Builtin::PINNED_STANDARD_SOURCES != 0)
        );
    }

    #[test]
    fn custom_or_missing_source_evidence_and_unknown_parent_publish_no_json_certificate() {
        for (custom, journal, parent) in [
            (true, true, ParentRuntime::ModeledTlcMasterJdk21),
            (false, false, ParentRuntime::ModeledTlcMasterJdk21),
            (false, true, ParentRuntime::Unknown),
        ] {
            let Some(ir) = lowered(custom, journal, parent, 0) else {
                assert!(custom);
                continue;
            };
            assert!(
                ir.builtins
                    .iter()
                    .all(|b| b.flags & tla_ir::Builtin::PINNED_STANDARD_SOURCES == 0)
            );
        }
    }

    #[test]
    fn generic_table_phase_needs_the_same_source_witness() {
        for (custom, journal, expected) in [
            (false, true, true),
            (true, true, false),
            (false, false, false),
        ] {
            let Some(ir) = lowered(custom, journal, ParentRuntime::ModeledTlcMasterJdk21, 1) else {
                assert!(custom && !expected);
                continue;
            };
            assert_eq!(
                ir.builtins
                    .iter()
                    .any(|b| b.flags & tla_ir::Builtin::TABLE_PHASE_KNOWN != 0),
                expected
            );
        }
    }
    #[test]
    fn actual_method_alias_keeps_json_source_certificate() {
        let ir = lowered(false, true, ParentRuntime::ModeledTlcMasterJdk21, 2).unwrap();
        assert!(ir.builtins.iter().any(|b| {
            ir.texts[b.name as usize].as_ref() == "ToJsonObject"
                && b.flags & tla_ir::Builtin::PINNED_STANDARD_SOURCES != 0
        }));
    }
}

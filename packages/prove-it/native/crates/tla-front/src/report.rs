//! What SANY prints while TLC runs it on a spec, as `getSanyReport` in `src/sany/report.ts` does:
//! the file it parses each module from, each module it analyzes and each module it lints.

use std::path::Path;
use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::{Assumed, Expr, ExpressionKind, Module, ModuleUnit, Statement};
use crate::config::parse_config;
use crate::environment::{EnvironmentOptions, get_sany_messages};
use crate::errors::{FrontError, SanyError};
use crate::get_standard_module;
use crate::hash::{FastMap, FastSet};
use crate::linter::Linter;
use crate::parser::{extract_module, parse_sany_module};
use crate::pcal::{PcalFatal, PcalSession, ValidationResult};
use crate::sany_parse_error::{get_sany_174_lexical_error, get_sany_parse_error};

type Result<T> = std::result::Result<T, Stop>;

/// Why SANY stops: a fatal error of its parsing phase, which it prints, or what the front end
/// doesn't cover yet.
enum Stop {
    Fatal {
        location: Option<Rc<str>>,
        message: String,
        /// The report of SANY's parser, which SANY prints before the fatal error.
        parse_error: Option<String>,
    },
    /// A Java exception of SANY's validation of PlusCal, which it prints with its parse
    /// messages so far.
    Pcal(String),
    Front(FrontError),
}

impl From<FrontError> for Stop {
    fn from(error: FrontError) -> Stop {
        Stop::Front(error)
    }
}

fn not_yet(reason: &str) -> Stop {
    Stop::Front(FrontError::NotYet(reason.to_owned()))
}

/// Where SANY reads a module from, as `SanyModuleOrigin`: a file of its own, the file of the root
/// module, or the files of its standard modules.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModuleOrigin {
    File,
    RootFile,
    Standard,
}

/// What SANY prints while TLC runs it on a spec, and whether SANY rejects the spec, as
/// `getSanyReport`'s `text` and `isFailed`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SanyText {
    pub text: String,
    pub is_failed: bool,
    /// The Java exception SANY's semantic analysis throws, which TLC reports as a failed parse
    /// (`Assert.fail(EC.TLC_PARSING_FAILED2, ...)`), and which `text` ends with.
    pub exception: Option<String>,
}

/// How the run reads and names the spec's modules.
pub struct ReportOptions<'a> {
    pub version: TlcVersion,
    /// The file name TLC gives SANY, which SANY prints in its fatal errors, or else the root
    /// module's name.
    pub file_name: Option<&'a str>,
    /// A module's text from a file of its own, beside the spec or in the library.
    pub load_module: &'a dyn Fn(&str) -> Option<String>,
    /// The file TLC prints that it parses a module from, as `createFileDescriber` names it.
    pub describe_file: &'a dyn Fn(&str, ModuleOrigin) -> String,
}

/// tla2sany.semantic.StandardModules: SANY lints the modules other than these.
const UNLINTED_MODULES: &[&str] = &[
    "FiniteSets",
    "Sequences",
    "Bags",
    "Naturals",
    "Integers",
    "Reals",
    "RealTime",
    "Randomization",
    "TLC",
];

/// The modules a file extends and instantiates, as SANY's ParseUnit collects them, and the module
/// of that file which first names each.
#[derive(Default)]
struct Dependencies {
    extendees: Vec<Rc<str>>,
    instancees: Vec<Rc<str>>,
    importers: FastMap<Rc<str>, Rc<str>>,
}

fn get_let_instances(expression: &Expr, found: &mut Vec<Rc<str>>) {
    if let ExpressionKind::Let {
        instances: Some(instances),
        ..
    } = &expression.kind
    {
        found.extend(instances.iter().map(|instance| instance.module.clone()));
    }
    expression
        .children()
        .iter()
        .for_each(|child| get_let_instances(child, found));
}

fn get_assumed_instances(assumed: &Assumed, found: &mut Vec<Rc<str>>) {
    match assumed {
        Assumed::Expression(expression) => get_let_instances(expression, found),
        Assumed::NewSymbol(_) => {}
        Assumed::AssumeProve(assume_prove) => {
            assume_prove
                .assumptions
                .iter()
                .for_each(|assumption| get_assumed_instances(assumption, found));
            get_let_instances(&assume_prove.conclusion, found);
        }
    }
}

/// SpecObj.instanceResolvesToInternalModule: SANY finds a module that the root module
/// instantiates among its inner modules only when its first top-level INSTANCE of the module
/// follows the inner module.
fn is_internal_instance(module: &Module, name: &str) -> bool {
    let mut seen: FastSet<&str> = FastSet::default();
    for unit in &module.units {
        match unit {
            ModuleUnit::Module(inner) => {
                seen.insert(&inner.name);
            }
            ModuleUnit::Instance(instance) if &*instance.module == name => {
                return seen.contains(name);
            }
            _ => {}
        }
    }
    false
}

/// `getDependencies`: ParseUnit.calculateContextWithinParseUnit lets a module know the inner
/// modules defined before it in the modules enclosing it and the inner modules of the modules it
/// extends, but not itself.
fn get_dependencies(module: &Rc<Module>) -> Dependencies {
    fn visit(
        current: &Rc<Module>,
        is_root: bool,
        context: &FastMap<Rc<str>, Rc<Module>>,
        dependencies: &mut Dependencies,
    ) {
        let is_external = |name: &Rc<str>| !context.contains_key(name);
        let mut add_imports = |names: Vec<Rc<str>>, is_extension: bool| {
            for name in names {
                dependencies
                    .importers
                    .entry(name.clone())
                    .or_insert_with(|| current.name.clone());
                if is_extension {
                    dependencies.extendees.push(name);
                } else {
                    dependencies.instancees.push(name);
                }
            }
        };
        add_imports(
            current
                .extends
                .iter()
                .filter(|name| is_external(name))
                .cloned()
                .collect(),
            true,
        );
        let mut instances = Vec::new();
        for unit in &current.units {
            match unit {
                ModuleUnit::Instance(instance) => instances.push(instance.module.clone()),
                ModuleUnit::Definition(definition) => {
                    get_let_instances(&definition.body, &mut instances)
                }
                ModuleUnit::Theorem(theorem) if is_root => match &theorem.statement {
                    Statement::Expression(expression) => {
                        get_let_instances(expression, &mut instances)
                    }
                    Statement::AssumeProve(assume_prove) => get_assumed_instances(
                        &Assumed::AssumeProve(assume_prove.clone()),
                        &mut instances,
                    ),
                },
                ModuleUnit::Assumption(assumption) if is_root => {
                    get_let_instances(&assumption.expression, &mut instances)
                }
                _ => {}
            }
        }
        add_imports(
            instances
                .into_iter()
                .filter(|name| is_external(name) && !is_internal_instance(current, name))
                .collect(),
            false,
        );
        let mut peers = context.clone();
        for inner in &current.modules {
            let mut inner_context = peers.clone();
            // ParseUnit.handleExtensions.
            let mut extenders: Vec<*const Module> = Vec::new();
            fn add_extended_inner_modules(
                extender: &Rc<Module>,
                extenders: &mut Vec<*const Module>,
                inner_context: &mut FastMap<Rc<str>, Rc<Module>>,
            ) {
                if extenders.contains(&Rc::as_ptr(extender)) {
                    return;
                }
                extenders.push(Rc::as_ptr(extender));
                for name in &extender.extends {
                    let Some(extendee) = inner_context.get(name).cloned() else {
                        continue;
                    };
                    for extendee_inner in &extendee.modules {
                        inner_context
                            .entry(extendee_inner.name.clone())
                            .or_insert_with(|| extendee_inner.clone());
                    }
                    add_extended_inner_modules(&extendee, extenders, inner_context);
                }
            }
            add_extended_inner_modules(inner, &mut extenders, &mut inner_context);
            visit(inner, false, &inner_context, dependencies);
            peers.insert(inner.name.clone(), inner.clone());
        }
    }
    let mut dependencies = Dependencies::default();
    visit(module, true, &FastMap::default(), &mut dependencies);
    dependencies
}

struct Loaded {
    text: String,
    module: Rc<Module>,
    dependencies: Rc<Dependencies>,
}

/// A message of SANY's parsing phase, which come from its validation of PlusCal.
struct ParseMessage {
    module: Rc<str>,
    text: String,
    is_warning: bool,
}

struct Loader<'a> {
    options: &'a ReportOptions<'a>,
    source: &'a str,
    modules: FastMap<Rc<str>, Loaded>,
    /// The modules in the order they loaded.
    loaded: Vec<Rc<str>>,
    lines: Vec<String>,
    /// The translator's state, which carries over between the modules SANY validates.
    session: PcalSession,
    parse_messages: Vec<ParseMessage>,
    /// What TLC 1.7.4's SpecObj.validateParseUnit prints after the file SANY parses next.
    validations: Vec<String>,
    is_parse_reported: bool,
    /// Whether SANY's semantic analysis found errors.
    is_failed: bool,
    exception: Option<String>,
}

/// The modules a module and its inner modules extend, other than its inner modules.
fn get_extendees(module: &Module) -> Vec<Rc<str>> {
    fn visit(module: &Module, inner_names: &mut Vec<Rc<str>>, extendees: &mut Vec<Rc<str>>) {
        inner_names.push(module.name.clone());
        extendees.extend(module.extends.iter().cloned());
        for inner in &module.modules {
            visit(inner, inner_names, extendees);
        }
    }
    let mut inner_names = Vec::new();
    let mut extendees = Vec::new();
    visit(module, &mut inner_names, &mut extendees);
    extendees.retain(|extendee| !inner_names.contains(extendee));
    extendees
}

impl Loader<'_> {
    fn get_dependencies(&self, name: &str) -> Rc<Dependencies> {
        self.modules[name].dependencies.clone()
    }

    /// `loadSource` in `getSanyReport` and in the generator: TLC prints the file of a module
    /// before SANY parses it.
    fn load(
        &mut self,
        name: &Rc<str>,
        text: Option<String>,
        origin: ModuleOrigin,
        importer: &Rc<str>,
    ) -> Result<()> {
        if self.modules.contains_key(name) {
            return Ok(());
        }
        // TLC's jar bundles the CommunityModules, which the front end doesn't have.
        if text.is_none() && COMMUNITY_MODULES.contains(&&**name) {
            return Err(not_yet(
                "a module of the CommunityModules TLC's jar bundles",
            ));
        }
        let Some(text) = text else {
            return Err(Stop::Fatal {
                location: Some(importer.clone()),
                message: format!(
                    "Cannot find source file for module {name} imported in module {importer}."
                ),
                parse_error: None,
            });
        };
        let parsed = parse_sany_module(&text, None, self.options.version);
        let parsing_line = format!(
            "Parsing file {}\n",
            (self.options.describe_file)(name, origin)
        );
        // `parseSource` in the generator: TLC 1.7.4's lexer first, then SANY's parser, whose
        // report replaces the front end's own where SANY's parser would accept the module.
        let lexical_error = (self.options.version == TlcVersion::V1_7_4)
            .then(|| get_sany_174_lexical_error(&text))
            .flatten();
        let parse_error = match (lexical_error, &parsed) {
            (Some(lexical_error), _) => Some(lexical_error),
            // SANY's parser accepts what the front end's parser doesn't.
            (None, Err(_)) => Some(
                get_sany_parse_error(&text, self.options.version)
                    .ok_or_else(|| not_yet("a module SANY's parser accepts"))?,
            ),
            (None, Ok(_)) => None,
        };
        if let Some(parse_error) = parse_error {
            self.lines.push(parsing_line);
            return Err(Stop::Fatal {
                location: Some(name.clone()),
                message: format!("Could not parse module {name} from file {name}.tla"),
                parse_error: Some(parse_error),
            });
        }
        let Ok(module) = parsed else {
            return Err(not_yet("SANY's parse errors"));
        };
        if module.name != *name {
            self.lines.push(parsing_line);
            return Err(Stop::Fatal {
                location: None,
                message: format!(
                    "File name '{name}' does not match the name '{}' of the top level module it contains.",
                    module.name
                ),
                parse_error: None,
            });
        }
        let module = Rc::new(module);
        let dependencies = Rc::new(get_dependencies(&module));
        // SANY validates the PlusCal of the root module once it parses, and of a module each
        // time it resolves another module's EXTENDS of it, as `loadValidatedModule` does.
        let extenders = self
            .loaded
            .iter()
            .filter(|loaded| get_extendees(&self.modules[*loaded].module).contains(name))
            .count();
        let extendees: Vec<Rc<str>> = get_extendees(&module)
            .into_iter()
            .filter(|extendee| extendee != name && self.modules.contains_key(extendee))
            .collect();
        self.modules.insert(
            name.clone(),
            Loaded {
                text,
                module,
                dependencies,
            },
        );
        self.loaded.push(name.clone());
        for _ in 0..extenders {
            self.validate(name)?;
        }
        for extendee in &extendees {
            self.validate(extendee)?;
        }
        self.lines.push(parsing_line);
        if *name == self.root() {
            self.validate(name)?;
        }
        self.print_validations();
        Ok(())
    }

    fn root(&self) -> Rc<str> {
        self.loaded[0].clone()
    }

    fn print_validations(&mut self) {
        for validation in self.validations.drain(..) {
            self.lines.push(format!("{validation}\n"));
        }
    }

    /// `validate` in `getSanyReport`, SpecObj.validateParseUnit: SANY's validation of the
    /// module's PlusCal, whose messages Errors.addMessage keeps once each.
    fn validate(&mut self, name: &Rc<str>) -> Result<()> {
        let loaded = &self.modules[name];
        let Some(range) = &loaded.module.location.range else {
            return Ok(());
        };
        let file_lines: Vec<&str> = loaded
            .text
            .split("\r\n")
            .flat_map(|line| line.split(['\r', '\n']))
            .collect();
        let start = (range.start.line as usize)
            .saturating_sub(1)
            .min(file_lines.len());
        let end = (range.end.line as usize).clamp(start, file_lines.len());
        let outcome = self
            .session
            .validate(&file_lines[start..end], self.options.version);
        for line in self.session.log.drain(..) {
            self.lines.push(format!("{line}\n"));
        }
        let results = match outcome {
            Ok(results) => results,
            Err(PcalFatal::Runtime(message)) => return Err(Stop::Pcal(message)),
            Err(PcalFatal::Bug(_)) => return Err(not_yet("a bug of the PlusCal translator")),
        };
        let is_tla_changed = results.contains(&ValidationResult::TlaDivergenceExists);
        let is_pcal_changed = results.contains(&ValidationResult::PcalDivergenceExists);
        let is_error = results.contains(&ValidationResult::ErrorEncountered);
        // Both versions word a change to just one of the algorithm and its translation alike.
        let one_change = (is_tla_changed != is_pcal_changed).then(|| {
            let what = if is_tla_changed {
                "TLA+ translation"
            } else {
                "PlusCal algorithm"
            };
            format!("The {what} in module {name} has changed since its last translation.")
        });
        if self.options.version == TlcVersion::V1_7_4 {
            let warning = if is_tla_changed && is_pcal_changed {
                Some(format!(
                    "The PlusCal algorithm and its TLA+ translation in module {name} filename since the last translation."
                ))
            } else {
                one_change
            };
            match warning {
                Some(warning) => self.validations.push(format!("!! WARNING: {warning}")),
                // TLC 1.7.4 prints the error to its error stream.
                None if is_error => return Err(not_yet("TLC 1.7.4's PlusCal errors")),
                None => {}
            }
            return Ok(());
        }
        let text = if is_tla_changed && is_pcal_changed {
            format!(
                "Both the PlusCal algorithm and its TLA+ translation in module {name} have changed since the last translation."
            )
        } else if let Some(one_change) = one_change {
            one_change
        } else if is_error {
            format!(
                "An unexpected problem was encountered attempting to validate the specification for {name}"
            )
        } else {
            return Ok(());
        };
        if self
            .parse_messages
            .iter()
            .any(|message| message.text == text)
        {
            return Ok(());
        }
        self.parse_messages.push(ParseMessage {
            module: name.clone(),
            text,
            is_warning: !is_error || is_tla_changed || is_pcal_changed,
        });
        Ok(())
    }

    /// SANY.frontEndParse: once SANY has loaded the spec, it prints the warnings of its parsing
    /// phase. Its errors end the run, which the front end doesn't write yet.
    fn report_parse_messages(&mut self, file_name: &str) -> Result<()> {
        self.print_validations();
        if self.is_parse_reported {
            return Ok(());
        }
        self.is_parse_reported = true;
        if self
            .parse_messages
            .iter()
            .any(|message| !message.is_warning)
        {
            return Err(not_yet("SANY's errors validating PlusCal"));
        }
        if self.parse_messages.is_empty() {
            return Ok(());
        }
        self.lines.push(format!(
            "Warnings ({}) during syntax parsing of {file_name}:\n\n\n",
            self.parse_messages.len()
        ));
        for message in &self.parse_messages {
            self.lines.push(format!(
                "In module {}\n\n{}\n\n\n\n",
                message.module, message.text
            ));
        }
        Ok(())
    }

    /// The text of a module other than the root module and where SANY reads it from.
    fn read(&self, name: &str) -> (Option<String>, ModuleOrigin) {
        if let Some(file) = (self.options.load_module)(name) {
            return (Some(file), ModuleOrigin::File);
        }
        // `SimpleFilenameToStream.locate` reads the standard modules next, and `FileUtil` takes a
        // module from the root module's file only after them.
        if let Some(standard) = get_standard_module(name, self.options.version) {
            return (Some(standard.to_owned()), ModuleOrigin::Standard);
        }
        // TLC 1.7.4's SANY reads a module only from a file of its own.
        let extracted = (self.options.version != TlcVersion::V1_7_4)
            .then(|| extract_module(self.source, name))
            .flatten();
        (extracted, ModuleOrigin::RootFile)
    }

    /// SpecObj.loadSpec: SANY resolves the first unresolved name it finds from the root, every
    /// extended module before any instantiated one, each in the context of the module that names
    /// it.
    fn find_unresolved(
        &self,
        name: &Rc<str>,
        is_extension: bool,
        visited: &mut FastSet<Rc<str>>,
        resolutions: &FastSet<(Rc<str>, Rc<str>)>,
    ) -> Option<(Rc<str>, Rc<str>, Rc<str>)> {
        if !self.modules.contains_key(name) || !visited.insert(name.clone()) {
            return None;
        }
        let dependencies = self.get_dependencies(name);
        let is_resolved =
            |dependency: &Rc<str>| resolutions.contains(&(name.clone(), dependency.clone()));
        let names = if is_extension {
            &dependencies.extendees
        } else {
            &dependencies.instancees
        };
        if let Some(unresolved) = names.iter().find(|dependency| !is_resolved(dependency)) {
            let naming_module = dependencies
                .importers
                .get(unresolved)
                .cloned()
                .unwrap_or_else(|| name.clone());
            return Some((unresolved.clone(), name.clone(), naming_module));
        }
        dependencies
            .extendees
            .iter()
            .chain(&dependencies.instancees)
            .filter(|dependency| is_resolved(dependency))
            .find_map(|dependency| {
                self.find_unresolved(dependency, is_extension, visited, resolutions)
            })
    }

    /// `calculateDependencies`: SANY analyzes each module after the modules it extends and
    /// instantiates.
    fn get_analysis_order(
        &self,
        name: &Rc<str>,
        path: &mut Vec<Rc<str>>,
        visiting: &mut FastSet<Rc<str>>,
        order: &mut Vec<Rc<str>>,
    ) -> Result<()> {
        if let Some(start) = path.iter().position(|item| item == name) {
            let cycle: Vec<String> = path[start..]
                .iter()
                .chain([name])
                .map(|item| format!("{item}.tla"))
                .collect();
            return Err(Stop::Fatal {
                location: None,
                message: format!(
                    "Circular dependency among .tla files; dependency cycle is:\n\n  {}",
                    cycle.join(" --> ")
                ),
                parse_error: None,
            });
        }
        if !visiting.insert(name.clone()) {
            return Ok(());
        }
        path.push(name.clone());
        let dependencies = self.get_dependencies(name);
        for dependency in dependencies
            .extendees
            .iter()
            .chain(&dependencies.instancees)
        {
            self.get_analysis_order(dependency, path, visiting, order)?;
        }
        path.pop();
        order.push(name.clone());
        Ok(())
    }
}

/// The modules of `lib/CommunityModules.jar`, which TLC's jar bundles and finds after the spec's
/// directory and the library path.
const COMMUNITY_MODULES: &[&str] = &[
    "BagsExt",
    "Bitwise",
    "CBOR",
    "CSV",
    "Combinatorics",
    "DifferentialEquations",
    "DyadicRationals",
    "FiniteSetsExt",
    "FiniteSetsExtTheorems",
    "FiniteSetsExtTheorems_proofs",
    "Folds",
    "FoldsTheorems",
    "FoldsTheorems_proofs",
    "FunctionTheorems",
    "FunctionTheorems_proofs",
    "Functions",
    "GraphTheorems",
    "GraphTheorems_proofs",
    "GraphViz",
    "Graphs",
    "HTML",
    "IOUtils",
    "Json",
    "Quorum",
    "QuorumTheorems",
    "QuorumTheorems_proofs",
    "Relation",
    "SVG",
    "SequencesExt",
    "SequencesExtTheorems",
    "SequencesExtTheorems_proofs",
    "ShiViz",
    "Statistics",
    "UndirectedGraphs",
    "VectorClocks",
];

/// What SANY prints for the spec at `spec_path` while TLC runs it: when SANY accepts the spec
/// without a message, or stops at a fatal error other than a parse error. `NotYet` for SANY's
/// other messages, PlusCal and what SANY's linter could warn about.
pub fn get_sany_text(
    spec_path: &Path,
    options: &ReportOptions,
) -> std::result::Result<SanyText, FrontError> {
    let root: Rc<str> = Rc::from(
        spec_path
            .file_stem()
            .and_then(|stem| stem.to_str())
            .unwrap_or_default(),
    );
    let source = std::fs::read_to_string(spec_path)
        .map_err(|_| FrontError::NotYet("a spec without a file".to_owned()))?;
    let mut loader = Loader {
        options,
        source: &source,
        modules: FastMap::default(),
        loaded: Vec::new(),
        lines: Vec::new(),
        session: PcalSession::new(),
        parse_messages: Vec::new(),
        validations: Vec::new(),
        is_parse_reported: false,
        is_failed: false,
        exception: None,
    };
    let name = options.file_name.unwrap_or(&root);
    match write_sany_text(&mut loader, &root) {
        Ok(()) => Ok(SanyText {
            text: loader.lines.concat(),
            is_failed: loader.is_failed,
            exception: loader.exception,
        }),
        Err(Stop::Front(error)) => Err(error),
        // SANY.frontEndParse turns a Java exception of its validation of PlusCal into a fatal
        // error, printing the exception and its messages so far, which are warnings here.
        Err(Stop::Pcal(_)) if !loader.parse_messages.is_empty() => Err(FrontError::NotYet(
            "SANY's parse messages with a fatal error".to_owned(),
        )),
        Err(Stop::Pcal(message)) => Ok(SanyText {
            text: format!(
                "{}\nFatal errors while parsing TLA+ spec in file {name}\n\n{message}\n\n",
                loader.lines.concat()
            ),
            is_failed: true,
            exception: None,
        }),
        // The fatal error follows the messages of the parsing phase.
        Err(Stop::Fatal { .. }) if !loader.parse_messages.is_empty() => Err(FrontError::NotYet(
            "SANY's parse messages with a fatal error".to_owned(),
        )),
        // TLC 1.7.4's SANY aborts with an AbortException instead.
        Err(Stop::Fatal { .. }) if options.version == TlcVersion::V1_7_4 => {
            Err(FrontError::NotYet("TLC 1.7.4's fatal errors".to_owned()))
        }
        Err(Stop::Fatal {
            location,
            message,
            parse_error,
        }) => {
            let fatal = format!(
                "{}\n\n{message}",
                location.map_or_else(
                    || "Unknown location".to_owned(),
                    |module| format!("In module {module}")
                )
            );
            let parse_error = parse_error.map_or_else(String::new, |text| format!("{text}\n"));
            Ok(SanyText {
                text: format!(
                    "{}{parse_error}\nFatal errors while parsing TLA+ spec in file {name}\n\n{fatal}\n*** Errors: 1\n\n{fatal}\n\n\n\n",
                    loader.lines.concat()
                ),
                is_failed: true,
                exception: None,
            })
        }
    }
}

/// `Generator`'s exception where a nested module ends the module's recursive section early: its
/// `checkForUndefinedRecursiveOps` takes the section's count off the total, so the definition of
/// an operator the section declared drives the total below zero (`endOpDefNode`). `NotYet` where
/// the count is off in a way that throws nothing, or elsewhere.
fn get_generator_exception(module: &Module) -> Result<Option<&'static str>> {
    let mut pending: Vec<Rc<str>> = Vec::new();
    let mut is_cleared = false;
    for unit in &module.units {
        match unit {
            ModuleUnit::Recursive(declared) if is_cleared => {
                return Err(not_yet(&format!(
                    "a RECURSIVE declaration of {} after a module in a recursive section",
                    declared.first().map_or("", |declaration| &declaration.name)
                )));
            }
            ModuleUnit::Recursive(declared) => {
                pending.extend(declared.iter().map(|declaration| declaration.name.clone()));
            }
            ModuleUnit::Definition(definition) => {
                let Some(index) = pending.iter().position(|name| *name == definition.name) else {
                    continue;
                };
                if is_cleared {
                    return Ok(Some(
                        "util.WrongInvocationException: Defined more recursive operators than were declared in RECURSIVE statements.",
                    ));
                }
                pending.remove(index);
            }
            ModuleUnit::Module(inner) if !pending.is_empty() => {
                let is_recursive = inner
                    .units
                    .iter()
                    .any(|unit| matches!(unit, ModuleUnit::Recursive(_) | ModuleUnit::Module(_)));
                if is_recursive {
                    return Err(not_yet(
                        "a module with modules or RECURSIVE declarations in a recursive section",
                    ));
                }
                is_cleared = true;
            }
            ModuleUnit::Instance(_) if is_cleared => {
                return Err(not_yet("an INSTANCE after a module in a recursive section"));
            }
            _ => {}
        }
    }
    if is_cleared {
        return Err(not_yet(
            "a module in a recursive section whose operators aren't defined after it",
        ));
    }
    Ok(None)
}

fn write_sany_text(loader: &mut Loader, root: &Rc<str>) -> Result<()> {
    let options = loader.options;
    let source = loader.source;
    let root = root.clone();
    loader.load(&root, Some(source.to_owned()), ModuleOrigin::File, &root)?;
    let mut resolutions: FastSet<(Rc<str>, Rc<str>)> = FastSet::default();
    loop {
        let next = [true, false].into_iter().find_map(|is_extension| {
            loader.find_unresolved(&root, is_extension, &mut FastSet::default(), &resolutions)
        });
        let Some((name, importer, naming_module)) = next else {
            break;
        };
        if !loader.modules.contains_key(&name) {
            let (text, origin) = loader.read(&name);
            loader.load(&name, text, origin, &naming_module)?;
        }
        resolutions.insert((importer, name));
    }
    let mut order = Vec::new();
    loader.get_analysis_order(&root, &mut Vec::new(), &mut FastSet::default(), &mut order)?;
    loader.report_parse_messages(options.file_name.unwrap_or(&root))?;
    // SANY's generator throws on the root module before it reports its messages, and
    // `SANY.parse` prints the exception. The standard modules before it have none.
    if let Some(exception) = get_generator_exception(&loader.modules[&root].module)? {
        let is_standard = |name: &Rc<str>| loader.read(name).1 == ModuleOrigin::Standard;
        if options.version == TlcVersion::V1_7_4
            || order.iter().any(|name| *name != root && !is_standard(name))
        {
            return Err(not_yet(
                "SANY's generator exception after a module of the user's",
            ));
        }
        for name in &order {
            loader
                .lines
                .push(format!("Semantic processing of module {name}\n"));
        }
        loader.lines.push(format!("{exception}\n"));
        loader.is_failed = true;
        loader.exception = Some(exception.to_owned());
        return Ok(());
    }
    // SANY's messages come from linking, which reports what SANY's semantic analysis does.
    let config =
        parse_config("", options.version).map_err(|error| FrontError::Config(error.message))?;
    let messages = get_sany_messages(
        &EnvironmentOptions {
            source,
            load_module: &|name| loader.read(name).0,
            config: &config,
            is_unconfigured: true,
            version: options.version,
            is_level_checked: true,
            load_class: None,
        },
        &order,
    )
    .map_err(|error| match error {
        FrontError::NotYet(_) => Stop::Front(error),
        _ => not_yet("an error that stops linking"),
    })?;
    // SANY.frontEndSemanticAnalysis: after each module, SANY prints every message so far.
    let mut warnings: Vec<SanyError> = Vec::new();
    let mut errors: Vec<SanyError> = Vec::new();
    for (name, module_messages) in order.iter().zip(messages) {
        loader
            .lines
            .push(format!("Semantic processing of module {name}\n"));
        warnings.extend(module_messages.warnings);
        errors.extend(module_messages.errors);
        if warnings.is_empty() && errors.is_empty() {
            continue;
        }
        // TLC 1.7.4's SANY prints the errors and warnings together.
        if options.version == TlcVersion::V1_7_4 {
            return Err(not_yet("TLC 1.7.4's semantic errors"));
        }
        let format_message =
            |message: &SanyError| format!("{}\n\n{}", message.location, message.message);
        if !warnings.is_empty() {
            loader
                .lines
                .push(format!("*** Warnings: {}\n\n", warnings.len()));
            for warning in &warnings {
                loader
                    .lines
                    .push(format!("{}\n\n\n\n", format_message(warning)));
            }
        }
        if !errors.is_empty() {
            loader.lines.push(format!(
                "Semantic errors:\n\n*** Errors: {}\n\n",
                errors.len()
            ));
            for error in &errors {
                loader
                    .lines
                    .push(format!("{}\n\n\n", format_message(error)));
            }
        }
    }
    loader.is_failed = !errors.is_empty();
    // SANY.frontEndLinting: when SANY accepts the spec, it lints the modules. TLC 1.7.4's SANY
    // has no linter.
    if errors.is_empty() && options.version != TlcVersion::V1_7_4 {
        let linted: Vec<&Rc<str>> = order
            .iter()
            .filter(|name| !UNLINTED_MODULES.contains(&&***name))
            .collect();
        let modules: FastMap<Rc<str>, Rc<Module>> = loader
            .modules
            .iter()
            .map(|(name, loaded)| (name.clone(), loaded.module.clone()))
            .collect();
        let linter = Linter::new(&modules);
        let mut warnings = Vec::new();
        for name in &linted {
            warnings.extend(linter.lint_module(name)?);
        }
        for name in linted {
            loader.lines.push(format!("Linting of module {name}\n"));
        }
        for warning in warnings {
            loader.lines.push(format!(
                "{}\n\n{}\n\n\n\n",
                warning.location, warning.message
            ));
        }
    }
    Ok(())
}

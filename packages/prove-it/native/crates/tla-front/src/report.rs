//! What SANY prints while TLC runs it on a spec, as `getSanyReport` in `src/sany/report.ts` does:
//! the file it parses each module from, each module it analyzes and each module it lints.

use std::path::Path;
use std::rc::Rc;

use crate::TlcVersion;
use crate::ast::{Declaration, DefinitionKind, Module, ModuleUnit};
use crate::config::parse_config;
use crate::environment::{
    EnvironmentOptions, ModuleMessages, get_sany_messages, reject_module_literals,
};
use crate::errors::{FrontError, SanyError, SanyReport};
use crate::get_standard_module;
use crate::hash::{FastMap, FastSet};
use crate::lexer::{TokenKind, tokenize};
use crate::linter::Linter;
use crate::parser::{extract_module, parse_sany_module};
use crate::pcal::{PcalFatal, PcalSession, ValidationResult};
use crate::recursive::check_recursive;
use crate::sany::GENERATOR_EXCEPTION;
use crate::sany::UNLINTED_MODULES;
use crate::sany::generator::{
    DependencyScope, ModuleDependencies, get_dependencies, get_proof_instances,
};
use crate::sany::messages::{Generated, get_generator_messages};
use crate::sany::source::get_unboxed_source;
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
    /// SANY's report ends with the errors of its parsing phase, which it has printed.
    Rejected,
    Front(FrontError),
}

impl From<FrontError> for Stop {
    fn from(error: FrontError) -> Stop {
        Stop::Front(error)
    }
}

/// Where the loader that doesn't bind names to inner modules declines.
const NESTED_IN_EXTENDEE: &str = "a module nested in a module its extender extends";

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
    /// The errors that make SANY reject the spec, other than an exception, and the warnings
    /// before them, as the TypeScript check throws them.
    pub report: Option<SanyReport>,
    /// Whether SANY printed a warning, of its semantic analysis or of its linter.
    pub is_warned: bool,
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
    /// The modules TLC adds to the root module's EXTENDS for its post conditions, which SANY
    /// loads after the ones the root module extends: `-dumpTrace`'s, then `_TLCTrace` where TLC
    /// records the trace for its trace exploration spec (`ModelOptions::root_extendees`).
    pub root_extendees: &'a [&'a str],
    /// tla2sany.xml.XMLExporter runs SANY with its validAstSettings: SANY prints only its errors,
    /// with no progress lines and no warnings, and neither validates PlusCal nor lints.
    pub is_xml_export: bool,
}

/// The deepest nesting the report writes, where a square bracket counts twice: SANY's recursive
/// descent overflows Java's default stack between 1,500 and 1,600 parentheses, braces or angle
/// brackets, and between 800 and 1,000 function constructors.
const MAX_NESTING_DEPTH: usize = 1100;

/// The deepest nesting of parentheses, brackets, braces and angle brackets in a module's text, a
/// square bracket counting twice.
fn get_nesting_depth(text: &str) -> usize {
    let Ok(tokens) = tokenize(text) else {
        return 0;
    };
    let mut depth = 0usize;
    let mut deepest = 0;
    for token in tokens
        .iter()
        .filter(|token| token.kind != TokenKind::String)
    {
        match &*token.text {
            "(" | "{" | "<<" => depth += 1,
            "[" => depth += 2,
            ")" | "}" | ">>" | ">>_" => depth = depth.saturating_sub(1),
            "]" | "]_" => depth = depth.saturating_sub(2),
            _ => {}
        }
        deepest = deepest.max(depth);
    }
    deepest
}

/// SANY's character stream ends a line at a carriage return alone too, which the front end reads
/// as the line feed it stands for, keeping each offset.
fn end_lines_at_carriage_returns(text: &str) -> std::borrow::Cow<'_, str> {
    let bytes = text.as_bytes();
    let is_lone = |index: usize| bytes[index] == b'\r' && bytes.get(index + 1) != Some(&b'\n');
    if !(0..bytes.len()).any(is_lone) {
        return std::borrow::Cow::Borrowed(text);
    }
    let ended: Vec<u8> = (0..bytes.len())
        .map(|index| if is_lone(index) { b'\n' } else { bytes[index] })
        .collect();
    std::borrow::Cow::Owned(String::from_utf8(ended).expect("ASCII replaced by ASCII"))
}

struct Loaded {
    text: String,
    module: Rc<Module>,
    dependencies: Rc<ModuleDependencies>,
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
    /// Whether the loader binds names to the inner modules of the files their modules extend.
    is_binding: bool,
    report: Option<SanyReport>,
    is_warned: bool,
    /// The names a module of a file names that SANY binds to an inner module of a file the module
    /// extends, which SANY doesn't read a file for (`resolveNamesBetweenSpecAndExtention`).
    inner_bindings: FastSet<(Rc<str>, Rc<str>)>,
    /// Where SANY reads the root module from: its file, or its standard modules where no file
    /// holds it.
    root_origin: ModuleOrigin,
}

/// The inner modules of `module`, at any depth.
fn get_inner_modules(module: &Module) -> Vec<Rc<Module>> {
    module
        .modules
        .iter()
        .flat_map(|inner| {
            let mut modules = vec![inner.clone()];
            modules.extend(get_inner_modules(inner));
            modules
        })
        .collect()
}

/// The names of `names` that only the inner modules of `module`, at any depth, extending
/// `extendee` directly or through one another name.
fn get_inner_bindings(module: &Module, extendee: &str, names: &[Rc<str>]) -> Vec<Rc<str>> {
    fn split(module: &Module, extended: &mut Vec<Rc<str>>, inner: &mut Vec<Rc<Module>>) -> Module {
        let mut outer = module.clone();
        outer.modules = Vec::new();
        for nested in &module.modules {
            if nested.extends.iter().any(|name| extended.contains(name)) {
                extended.push(nested.name.clone());
                inner.push(nested.clone());
            } else {
                outer.modules.push(Rc::new(split(nested, extended, inner)));
            }
        }
        outer
    }
    let get_names = |module: &Rc<Module>| {
        let dependencies = get_dependencies(module);
        dependencies
            .extendees
            .iter()
            .chain(&dependencies.instancees)
            .filter(|name| names.contains(name))
            .cloned()
            .collect::<Vec<_>>()
    };
    let mut inner = Vec::new();
    let outer = Rc::new(split(module, &mut vec![Rc::from(extendee)], &mut inner));
    if inner.is_empty() {
        return Vec::new();
    }
    let removed: Vec<&Rc<str>> = inner.iter().map(|module| &module.name).collect();
    let outer_names: Vec<Rc<str>> = get_names(&outer)
        .into_iter()
        .filter(|name| !removed.contains(&name))
        .collect();
    inner
        .iter()
        .flat_map(get_names)
        .filter(|name| !outer_names.contains(name))
        .collect()
}
impl Loader<'_> {
    fn get_dependencies(&self, name: &str) -> Rc<ModuleDependencies> {
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
            // TLC 1.7.4's SANY gives the error no location.
            return Err(Stop::Fatal {
                location: (self.options.version == TlcVersion::Master).then(|| importer.clone()),
                message: format!(
                    "Cannot find source file for module {name} imported in module {importer}."
                ),
                parse_error: None,
            });
        };
        let raw = text;
        let text = end_lines_at_carriage_returns(&raw).into_owned();
        if get_nesting_depth(&text) > MAX_NESTING_DEPTH {
            return Err(not_yet(
                "brackets nested more deeply than SANY's parser can on Java's default stack",
            ));
        }
        // SANY's parser takes []ASSUME and []PROVE, which the front end's reads unboxed.
        let parsed = get_unboxed_source(&text)
            .and_then(|unboxed| parse_sany_module(&unboxed, None, self.options.version));
        let parsing_line = format!(
            "Parsing file {}\n",
            (self.options.describe_file)(name, origin)
        );
        // `parseSource` in the generator: TLC 1.7.4's lexer first, then SANY's parser, whose
        // report replaces the front end's own where SANY's parser would accept the module.
        let lexical_error = (self.options.version == TlcVersion::V1_7_4)
            .then(|| get_sany_174_lexical_error(&raw))
            .flatten();
        let parse_error = match (lexical_error, &parsed) {
            (Some(lexical_error), _) => Some(lexical_error),
            // SANY's parser accepts what the front end's parser doesn't.
            (None, Err(_)) => Some(
                get_sany_parse_error(&raw, self.options.version)
                    .ok_or_else(|| not_yet("a module SANY's parser accepts"))?,
            ),
            (None, Ok(_)) => None,
        };
        if let Some(parse_error) = parse_error {
            self.push_progress(parsing_line);
            // TLC and XMLExporter give SANY the file they are asked for, which SANY names for the
            // root.
            let file = match self.options.file_name {
                Some(file_name) if self.loaded.is_empty() => {
                    format!(
                        "{}.tla",
                        file_name.strip_suffix(".tla").unwrap_or(file_name)
                    )
                }
                _ => format!("{name}.tla"),
            };
            return Err(Stop::Fatal {
                location: Some(name.clone()),
                message: format!("Could not parse module {name} from file {file}"),
                parse_error: Some(parse_error),
            });
        }
        let Ok(module) = parsed else {
            return Err(not_yet("SANY's parse errors"));
        };
        if module.name != *name {
            self.push_progress(parsing_line);
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
        let mut dependencies = get_dependencies(&module);
        // SANY loads the modules a proof instantiates, which the front end doesn't yet, unless
        // the module depends on them otherwise.
        let mut inner_names = Vec::new();
        get_inner_names(&module, &mut inner_names);
        if get_proof_instances(&module).iter().any(|name| {
            !dependencies.extendees.contains(name)
                && !dependencies.instancees.contains(name)
                && !inner_names.contains(name)
        }) {
            return Err(not_yet("a proof's INSTANCE of a module SANY loads"));
        }
        // The root module extends the modules of TLC's post conditions after its own.
        if self.loaded.is_empty() {
            for (offset, &extendee) in self.options.root_extendees.iter().enumerate() {
                let extendee: Rc<str> = Rc::from(extendee);
                dependencies
                    .importers
                    .entry(extendee.clone())
                    .or_insert_with(|| name.clone());
                dependencies
                    .extendees
                    .insert(module.extends.len() + offset, extendee.clone());
                dependencies.scope.extendees.push(extendee);
            }
        }
        let dependencies = Rc::new(dependencies);
        self.modules.insert(
            name.clone(),
            Loaded {
                text,
                module,
                dependencies,
            },
        );
        self.loaded.push(name.clone());
        self.push_progress(parsing_line);
        Ok(())
    }

    /// `SpecObj.validateParseUnit`, which `loadSpec` calls on the root module once it parses, and
    /// on a module each time it resolves an EXTENDS of it, after it finds or parses it.
    fn validate_parse_unit(&mut self, name: &Rc<str>) -> Result<()> {
        self.validate(name)?;
        self.print_validations();
        Ok(())
    }

    /// A line of SANY's progress, which XMLExporter's SANY doesn't print.
    fn push_progress(&mut self, line: String) {
        if !self.options.is_xml_export {
            self.lines.push(line);
        }
    }
    fn print_validations(&mut self) {
        for validation in self.validations.drain(..) {
            self.lines.push(format!("{validation}\n"));
        }
    }

    /// `validate` in `getSanyReport`, SpecObj.validateParseUnit: SANY's validation of the
    /// module's PlusCal, whose messages Errors.addMessage keeps once each.
    fn validate(&mut self, name: &Rc<str>) -> Result<()> {
        if self.options.is_xml_export {
            return Ok(());
        }
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
    /// phase, and then any errors, as `Errors.toString` writes them with the warnings again, which
    /// end the run.
    fn report_parse_messages(&mut self, file_name: &str) -> Result<()> {
        self.print_validations();
        if self.is_parse_reported {
            return Ok(());
        }
        self.is_parse_reported = true;
        let (warnings, errors): (Vec<_>, Vec<_>) = self
            .parse_messages
            .iter()
            .partition(|message| message.is_warning);
        let format_messages = |messages: &[&ParseMessage]| {
            messages
                .iter()
                .map(|message| format!("In module {}\n\n{}\n\n\n", message.module, message.text))
                .collect::<String>()
        };
        let mut text = String::new();
        if !warnings.is_empty() {
            text.push_str(&format!(
                "Warnings ({}) during syntax parsing of {file_name}:\n\n\n",
                warnings.len()
            ));
            for warning in &warnings {
                text.push_str(&format_messages(&[warning]));
                text.push('\n');
            }
        }
        let is_rejected = !errors.is_empty();
        if is_rejected {
            text.push_str(&format!(
                "*** Errors: {}\n\n{}",
                errors.len(),
                format_messages(&errors)
            ));
            if !warnings.is_empty() {
                text.push_str(&format!(
                    "*** Warnings: {}\n\n{}",
                    warnings.len(),
                    format_messages(&warnings)
                ));
            }
            text.push('\n');
        }
        self.lines.push(text);
        if is_rejected {
            return Err(Stop::Rejected);
        }
        Ok(())
    }

    /// Whether a module the file of `extender` extends, through others, has an inner module
    /// `name` at its top level.
    fn is_nested_in_extendee(
        &self,
        extender: &Rc<str>,
        name: &str,
        visited: &mut FastSet<Rc<str>>,
    ) -> bool {
        fn nests(module: &Module, name: &str) -> bool {
            module.modules.iter().any(|inner| &*inner.name == name)
        }
        if !visited.insert(extender.clone()) || !self.modules.contains_key(extender) {
            return false;
        }
        self.get_dependencies(extender)
            .extendees
            .iter()
            .filter(|extendee| self.modules.contains_key(*extendee))
            .any(|extendee| {
                nests(&self.modules[extendee].module, name)
                    || self.is_nested_in_extendee(extendee, name, visited)
            })
    }

    /// The text of a module other than the root module as the front end reads it
    /// (`end_lines_at_carriage_returns`).
    fn read_text(&self, name: &str) -> Option<String> {
        self.read(name)
            .0
            .map(|text| end_lines_at_carriage_returns(&text).into_owned())
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
        self.find_unresolved_in(
            name,
            &dependencies.scope,
            is_extension,
            visited,
            resolutions,
        )
    }

    /// `findNextUnresolvedExtentionBody` and `findNextUnresolvedInstantiationBody` for a module of
    /// the file of `name` or one of its inner modules: the module's own unresolved names first,
    /// then those of the modules it extends and instantiates, then its inner modules'.
    fn find_unresolved_in(
        &self,
        name: &Rc<str>,
        scope: &DependencyScope,
        is_extension: bool,
        visited: &mut FastSet<Rc<str>>,
        resolutions: &FastSet<(Rc<str>, Rc<str>)>,
    ) -> Option<(Rc<str>, Rc<str>, Rc<str>)> {
        let is_resolved =
            |dependency: &Rc<str>| resolutions.contains(&(name.clone(), dependency.clone()));
        let names = if is_extension {
            &scope.extendees
        } else {
            &scope.instancees
        };
        if let Some(unresolved) = names.iter().find(|dependency| !is_resolved(dependency)) {
            return Some((unresolved.clone(), name.clone(), scope.name.clone()));
        }
        scope
            .extendees
            .iter()
            .chain(&scope.instancees)
            .filter(|dependency| {
                is_resolved(dependency)
                    && !self
                        .inner_bindings
                        .contains(&(name.clone(), (*dependency).clone()))
            })
            .find_map(|dependency| {
                self.find_unresolved(dependency, is_extension, visited, resolutions)
            })
            .or_else(|| {
                scope.inners.iter().find_map(|inner| {
                    self.find_unresolved_in(name, inner, is_extension, visited, resolutions)
                })
            })
    }

    /// `resolveNamesBetweenSpecAndExtention`: once SANY reads the file `extendee` that a module
    /// of the file `extender` extends, it binds the as yet unbound names that module, its inner
    /// modules and the modules extending it name to the inner modules of `extendee` of the same
    /// names, which SANY reads no file for. Where an inner module extends it alone, SANY reads a
    /// file for a name the file's other modules name.
    fn bind_inner_modules(
        &mut self,
        extender: &Rc<str>,
        extendee: &Rc<str>,
        resolutions: &mut FastSet<(Rc<str>, Rc<str>)>,
    ) -> Result<()> {
        // A file that extends a module bound to an inner module that extends another: SANY's
        // modules extending the extender may reach it through that inner module.
        let is_inner_extender = |name: &Rc<str>| {
            self.modules.values().any(|loaded| {
                get_inner_modules(&loaded.module)
                    .iter()
                    .any(|inner| inner.name == *name && !inner.extends.is_empty())
            })
        };
        if self.inner_bindings.iter().any(|binding| {
            self.get_dependencies(&binding.0)
                .extendees
                .contains(&binding.1)
                && is_inner_extender(&binding.1)
        }) {
            return Err(not_yet(
                "a file extending an inner module that extends another",
            ));
        }
        let inner_names: Vec<Rc<str>> = self.modules[extendee]
            .module
            .modules
            .iter()
            .map(|inner| inner.name.clone())
            .collect();
        let module = &self.modules[extender].module;
        // Where only an inner module of the file extends `extendee`, SANY binds the names of that
        // module and of the inner modules extending it, and no file extends that module.
        if !module.extends.contains(extendee) {
            let bindings = get_inner_bindings(module, extendee, &inner_names)
                .into_iter()
                .map(|bound| (extender.clone(), bound))
                .collect();
            return self.bind(bindings, resolutions);
        }
        let mut extenders = vec![extender.clone()];
        let mut bindings = Vec::new();
        let mut index = 0;
        while let Some(current) = extenders.get(index).cloned() {
            index += 1;
            // `getModulesIndirectlyExtending`: SANY counts a module that extends `current` once it
            // has resolved its EXTENDS of it.
            for (name, loaded) in &self.modules {
                if extenders.contains(name)
                    || !resolutions.contains(&(name.clone(), current.clone()))
                {
                    continue;
                }
                if loaded.module.extends.contains(&current) {
                    extenders.push(name.clone());
                } else {
                    bindings.extend(
                        get_inner_bindings(&loaded.module, &current, &inner_names)
                            .into_iter()
                            .map(|bound| (name.clone(), bound)),
                    );
                }
            }
        }
        for unit in &extenders {
            let dependencies = self.get_dependencies(unit);
            bindings.extend(
                dependencies
                    .extendees
                    .iter()
                    .chain(&dependencies.instancees)
                    .filter(|name| inner_names.contains(name))
                    .map(|name| (unit.clone(), name.clone())),
            );
        }
        self.bind(bindings, resolutions)
    }

    /// Binds each name of a file to an inner module, as `bind_inner_modules` finds them, where
    /// SANY hasn't bound it before (`bindIfNotBound`).
    fn bind(
        &mut self,
        bindings: Vec<(Rc<str>, Rc<str>)>,
        resolutions: &mut FastSet<(Rc<str>, Rc<str>)>,
    ) -> Result<()> {
        for binding in bindings {
            if resolutions.insert(binding.clone()) {
                self.inner_bindings.insert(binding);
            }
        }
        Ok(())
    }

    /// Whether the loader bound a name to an inner module where every module it read, at any
    /// depth, has a name of its own, and no bound name names a file or a standard module.
    fn is_unambiguous(&self) -> bool {
        let mut names: FastSet<Rc<str>> = FastSet::default();
        let is_distinct = self.modules.iter().all(|(name, loaded)| {
            names.insert(name.clone())
                && get_inner_modules(&loaded.module)
                    .iter()
                    .all(|inner| names.insert(inner.name.clone()))
        });
        !self.inner_bindings.is_empty()
            && is_distinct
            && self
                .inner_bindings
                .iter()
                .all(|binding| self.read(&binding.1).0.is_none())
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
            .filter(|dependency| {
                !self
                    .inner_bindings
                    .contains(&(name.clone(), (*dependency).clone()))
            })
        {
            self.get_analysis_order(dependency, path, visiting, order)?;
        }
        path.pop();
        order.push(name.clone());
        Ok(())
    }
}

/// The modules of `lib/CommunityModules.jar`, which TLC's jar bundles and finds after the spec's
/// directory and the library path, and `_CBORTrace`, a module of TLC's that extends one of them.
const COMMUNITY_MODULES: &[&str] = &[
    "_CBORTrace",
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

/// The stack a thread needs to write SANY's report: the front end recurses as deep as TLC's
/// translation of a formula does, up to the nesting it declines, which a thread's default stack
/// doesn't hold.
pub const REPORT_STACK_BYTES: usize = 64 * 1024 * 1024;

/// What SANY prints for the spec at `spec_path` while TLC runs it: when SANY accepts the spec
/// without a message, or stops at a fatal error other than a parse error. `NotYet` for SANY's
/// other messages, PlusCal and what SANY's linter could warn about.
pub fn get_sany_text(
    spec_path: &Path,
    options: &ReportOptions,
) -> std::result::Result<SanyText, FrontError> {
    let root = spec_path
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or_default();
    let source = std::fs::read_to_string(spec_path)
        .map_err(|_| FrontError::NotYet("a spec without a file".to_owned()))?;
    get_sany_text_of(root, &source, options)
}

/// What SANY prints for the root module `root` of the text `source`, which `options` read the
/// other modules for, as for a spec of that file.
pub fn get_sany_text_of(
    root: &str,
    source: &str,
    options: &ReportOptions,
) -> std::result::Result<SanyText, FrontError> {
    get_root_text(root, source, ModuleOrigin::File, options)
}

/// What SANY prints for a spec whose root module no file holds but SANY's standard modules do, or
/// `None` where they don't hold it.
pub fn get_standard_root_text(
    root: &str,
    options: &ReportOptions,
) -> Option<std::result::Result<SanyText, FrontError>> {
    let source = get_standard_module(root, options.version)?;
    Some(get_root_text(root, source, ModuleOrigin::Standard, options))
}

fn get_root_text(
    root: &str,
    source: &str,
    root_origin: ModuleOrigin,
    options: &ReportOptions,
) -> std::result::Result<SanyText, FrontError> {
    let root: Rc<str> = Rc::from(root);
    let (mut loader, mut written) = load_spec(&root, source, root_origin, options, false);
    // SANY binds a name to an inner module of a file its module extends, where the loader reads a
    // file for it, and finds none. The loader binds it only where every module of the spec has a
    // name of its own, where binding by name is SANY's binding by scope, and the name names no
    // file or standard module; elsewhere it reports what it found without binding.
    // The loader that doesn't bind declines a name of a module nested in a module its extender
    // extends; the loader that binds reads a file for it where it binds nothing, as SANY does.
    let is_nested = matches!(&written, Err(Stop::Front(FrontError::NotYet(reason)))
        if reason == NESTED_IN_EXTENDEE);
    let is_missing = is_nested
        || matches!(&written, Err(Stop::Fatal { message, .. })
            if message.starts_with("Cannot find source file for module "));
    if is_missing {
        let (bound, bound_written) = load_spec(&root, source, root_origin, options, true);
        if !matches!(bound_written, Err(Stop::Front(_)))
            && (bound.is_unambiguous() || is_nested && bound.inner_bindings.is_empty())
        {
            (loader, written) = (bound, bound_written);
        }
    }
    let name = options.file_name.unwrap_or(&root);
    match written {
        Ok(()) => Ok(SanyText {
            text: loader.lines.concat(),
            is_failed: loader.is_failed,
            exception: loader.exception,
            report: loader.report,
            is_warned: loader.is_warned,
        }),
        Err(Stop::Front(error)) => Err(error),
        Err(Stop::Rejected) => Ok(SanyText {
            text: loader.lines.concat(),
            is_failed: true,
            exception: None,
            report: None,
            is_warned: false,
        }),
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
            report: None,
            is_warned: false,
        }),
        // The fatal error follows the messages of the parsing phase.
        Err(Stop::Fatal { .. })
            if options.version == TlcVersion::V1_7_4 && !loader.parse_messages.is_empty() =>
        {
            Err(FrontError::NotYet(
                "TLC 1.7.4's parse messages with a fatal error".to_owned(),
            ))
        }
        Err(Stop::Fatal {
            location,
            message,
            parse_error,
        }) => {
            let location = location.map_or_else(
                || "Unknown location".to_owned(),
                |module| format!("In module {module}"),
            );
            let fatal = format!("{location}\n\n{message}");
            let is_tlc_174 = options.version == TlcVersion::V1_7_4;
            // The TypeScript check throws the fatal error alone, after the report of the module
            // SANY's parser rejects.
            let report = (!is_tlc_174 && loader.parse_messages.is_empty()).then(|| SanyReport {
                errors: vec![SanyError {
                    location,
                    message: message.clone(),
                }],
                warnings: Vec::new(),
                is_fatal: true,
                parse_error: parse_error.clone(),
            });
            // TLC 1.7.4's ParseException.getShortMessage fails on an error at the first token,
            // which has no image.
            let is_imageless = is_tlc_174
                && parse_error
                    .as_deref()
                    .is_some_and(|text| text.contains(" and token \"\" "));
            let parse_error = parse_error
                .filter(|_| !is_imageless)
                .map_or_else(String::new, |text| format!("{text}\n"));
            // TLC 1.7.4's SANY aborts with an AbortException, and keeps the message as an abort.
            let ending = if is_imageless {
                "java.lang.NullPointerException: Cannot invoke \"String.length()\" because \"str\" is null\n".to_owned()
            } else if is_tlc_174 {
                format!("tla2sany.semantic.AbortException\n*** Abort messages: 1\n\n{fatal}\n\n\n")
            } else {
                // `Errors.toString`: the errors of the parsing phase so far, then the fatal error,
                // then the warnings.
                let format_messages = |messages: &mut dyn Iterator<Item = String>| {
                    messages
                        .map(|text| format!("{text}\n\n\n"))
                        .collect::<String>()
                };
                let (warnings, errors): (Vec<_>, Vec<_>) = loader
                    .parse_messages
                    .iter()
                    .partition(|message| message.is_warning);
                let mut errors = errors
                    .iter()
                    .map(|error| format!("In module {}\n\n{}", error.module, error.text))
                    .chain([fatal.clone()]);
                let error_count = loader
                    .parse_messages
                    .iter()
                    .filter(|message| !message.is_warning)
                    .count()
                    + 1;
                let mut text = format!(
                    "{fatal}\n*** Errors: {error_count}\n\n{}",
                    format_messages(&mut errors)
                );
                if !warnings.is_empty() {
                    text.push_str(&format!(
                        "*** Warnings: {}\n\n{}",
                        warnings.len(),
                        format_messages(&mut warnings.iter().map(|warning| {
                            format!("In module {}\n\n{}", warning.module, warning.text)
                        }))
                    ));
                }
                text.push('\n');
                text
            };
            Ok(SanyText {
                text: format!(
                    "{}{parse_error}\nFatal errors while parsing TLA+ spec in file {name}\n\n{ending}",
                    loader.lines.concat()
                ),
                is_failed: true,
                exception: None,
                report,
                is_warned: false,
            })
        }
    }
}

/// The loader of the root module `root` of the text `source`, and how SANY's report of it ends,
/// binding names to the inner modules of extended files where `is_binding`.
fn load_spec<'a>(
    root: &Rc<str>,
    source: &'a str,
    root_origin: ModuleOrigin,
    options: &'a ReportOptions<'a>,
    is_binding: bool,
) -> (Loader<'a>, Result<()>) {
    let mut loader = Loader {
        options,
        source,
        modules: FastMap::default(),
        loaded: Vec::new(),
        lines: Vec::new(),
        session: PcalSession::new(),
        parse_messages: Vec::new(),
        validations: Vec::new(),
        is_parse_reported: false,
        is_failed: false,
        exception: None,
        report: None,
        is_warned: false,
        is_binding,
        inner_bindings: FastSet::default(),
        root_origin,
    };
    let written = write_sany_text(&mut loader, root);
    (loader, written)
}

/// What SANY prints where no file holds the root module `root`, which TLC gives SANY as `name`:
/// `SANY.frontEndParse`'s fatal error.
pub fn get_missing_root_text(name: &str, root: &str) -> SanyText {
    let fatal = format!("Unknown location\n\nCannot find source file for module {root}");
    SanyText {
        text: format!(
            "\nFatal errors while parsing TLA+ spec in file {name}\n\n{fatal}\n*** Errors: 1\n\n{fatal}\n\n\n\n"
        ),
        is_failed: true,
        exception: None,
        report: None,
        is_warned: false,
    }
}

/// What SANY prints where its generator throws on the root module, which `SANY.parse` prints
/// after the "Semantic processing" lines: the standard modules before it have no messages, and
/// a module of the user's before it is `NotYet`.
fn push_generator_exception(
    loader: &mut Loader,
    order: &[Rc<str>],
    root: &Rc<str>,
    exception: &str,
) -> Result<()> {
    let is_standard = |name: &Rc<str>| loader.read(name).1 == ModuleOrigin::Standard;
    if loader.options.version == TlcVersion::V1_7_4
        || order.iter().any(|name| name != root && !is_standard(name))
    {
        return Err(not_yet(
            "SANY's generator exception after a module of the user's",
        ));
    }
    for name in order {
        loader.push_progress(format!("Semantic processing of module {name}\n"));
    }
    loader.lines.push(format!("{exception}\n"));
    loader.is_failed = true;
    loader.exception = Some(exception.to_owned());
    Ok(())
}

/// `Generator`'s exception where a nested module ends the module's recursive section early: its
/// `checkForUndefinedRecursiveOps` takes the section's count off the total, so the definition of
/// an operator the section declared drives the total below zero (`endOpDefNode`). `NotYet` where
/// the count is off in a way that throws nothing, or elsewhere.
fn get_generator_exception(module: &Module) -> Result<Option<&'static str>> {
    check_recursive(module)?;
    let mut pending: Vec<Rc<Declaration>> = Vec::new();
    let mut declared: Vec<Rc<Declaration>> = Vec::new();
    let mut is_cleared = false;
    for unit in &module.units {
        match unit {
            ModuleUnit::Recursive(declared) if is_cleared => {
                return Err(not_yet(&format!(
                    "a RECURSIVE declaration of {} after a module in a recursive section",
                    declared.first().map_or("", |declaration| &declaration.name)
                )));
            }
            ModuleUnit::Recursive(recursive) => {
                pending.extend(recursive.iter().cloned());
                declared.extend(recursive.iter().cloned());
            }
            ModuleUnit::Definition(definition) => {
                let Some(index) = pending
                    .iter()
                    .position(|declaration| declaration.name == definition.name)
                else {
                    continue;
                };
                // `processFunction` leaves a function whose declaration takes operator arguments
                // undefined, so it doesn't count down.
                if pending[index].arity != 0
                    && matches!(definition.kind, DefinitionKind::Function { .. })
                {
                    if is_cleared {
                        return Err(not_yet(
                            "a function declared RECURSIVE with operator arguments in a recursive section",
                        ));
                    }
                    continue;
                }
                // `check_recursive` leaves no other binding of a declared name in the module, but
                // one from an EXTENDS or an INSTANCE that `SymbolTable.addSymbol` would reject the
                // declaration over, which only the resolver finds.
                let is_conflicting = !module.extends.is_empty() || !module.instances.is_empty();
                if is_cleared && is_conflicting {
                    return Err(not_yet(
                        "a recursive section after a module, whose declarations SANY may reject",
                    ));
                }
                if is_cleared {
                    return Ok(Some(GENERATOR_EXCEPTION));
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

/// SANY's messages as linking derives them, or why it doesn't.
fn link_messages(
    loader: &Loader,
    order: &[Rc<str>],
    undecided: Option<FrontError>,
    is_user_module_added: bool,
) -> Result<Vec<ModuleMessages>> {
    // Linking takes the standard modules as TLC ships them, so their messages are none, which a
    // module of the user's named like one they read may not keep.
    let is_standard_replaced = order.iter().any(|name| {
        let dependencies = loader.get_dependencies(name);
        loader.read(name).1 == ModuleOrigin::Standard
            && dependencies
                .extendees
                .iter()
                .chain(&dependencies.instancees)
                .any(|dependency| loader.read(dependency).1 != ModuleOrigin::Standard)
    });
    if is_standard_replaced {
        return Err(not_yet(
            "SANY's messages of the standard modules with one of them replaced",
        ));
    }
    // SANY analyzes the modules TLC adds for its post conditions with the spec's, but linking
    // takes only those the spec uses: one of the user's among them may fail SANY's analysis, which
    // linking wouldn't report.
    if is_user_module_added {
        return Err(not_yet(
            "a module of the user's that the trace exploration spec uses",
        ));
    }
    let options = loader.options;
    let config =
        parse_config("", options.version).map_err(|error| FrontError::Config(error.message))?;
    let linked = match undecided {
        Some(error) => Err(error),
        None => get_sany_messages(
            &EnvironmentOptions {
                source: &end_lines_at_carriage_returns(loader.source),
                load_module: &|name| loader.read_text(name),
                config: &config,
                is_unconfigured: true,
                version: options.version,
                is_level_checked: true,
                load_class: None,
            },
            order,
        ),
    };
    match linked {
        Ok(linked) => Ok(linked),
        Err(linking @ FrontError::NotYet(_)) => Err(Stop::Front(linking)),
        Err(_) => Err(not_yet("an error that stops linking")),
    }
}

/// The names of the modules within a module, at any depth.
fn get_inner_names(module: &Module, names: &mut Vec<Rc<str>>) {
    for inner in &module.modules {
        names.push(inner.name.clone());
        get_inner_names(inner, names);
    }
}

/// The modules each parse unit extends and those it instantiates, as SANY has resolved them so far.
type Referencees = FastMap<Rc<str>, (Vec<Rc<str>>, Vec<Rc<str>>)>;

/// `SpecObj.nonCircularityTest`: once SANY resolves a module's name, it aborts where the module
/// reaches itself through the modules each parse unit extends or instantiates so far, its
/// extendees first.
fn check_circularity(referencees: &Referencees, unit: &Rc<str>) -> Result<()> {
    fn visit(
        referencees: &Referencees,
        unit: &Rc<str>,
        candidate: &Rc<str>,
        visited: &mut FastSet<Rc<str>>,
        path: &mut Vec<Rc<str>>,
    ) -> Result<()> {
        if !visited.insert(candidate.clone()) {
            return Ok(());
        }
        let (extendees, instancees) = referencees.get(candidate).cloned().unwrap_or_default();
        let instancees = instancees
            .into_iter()
            .filter(|instancee| !extendees.contains(instancee));
        for referencee in extendees
            .iter()
            .cloned()
            .chain(instancees)
            .collect::<Vec<_>>()
        {
            let referencee = &referencee;
            if referencee == unit {
                let cycle: Vec<String> = path
                    .iter()
                    .chain([unit])
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
            path.push(referencee.clone());
            visit(referencees, unit, referencee, visited, path)?;
            path.pop();
        }
        Ok(())
    }
    visit(
        referencees,
        unit,
        unit,
        &mut FastSet::default(),
        &mut vec![unit.clone()],
    )
}

fn write_sany_text(loader: &mut Loader, root: &Rc<str>) -> Result<()> {
    let options = loader.options;
    let source = loader.source;
    let root = root.clone();
    loader.load(&root, Some(source.to_owned()), loader.root_origin, &root)?;
    loader.validate_parse_unit(&root)?;
    let mut resolutions: FastSet<(Rc<str>, Rc<str>)> = FastSet::default();
    let mut referencees: Referencees = FastMap::default();
    loop {
        let next = [true, false].into_iter().find_map(|is_extension| {
            loader
                .find_unresolved(&root, is_extension, &mut FastSet::default(), &resolutions)
                .map(|found| (found, is_extension))
        });
        let Some(((name, importer, naming_module), is_extension)) = next else {
            break;
        };
        // ParseUnit.handleExtensions lets a module name the modules nested in the modules it
        // extends, which the front end looks for in files.
        if !loader.is_binding
            && loader.is_nested_in_extendee(&importer, &name, &mut FastSet::default())
        {
            return Err(not_yet(NESTED_IN_EXTENDEE));
        }
        if !loader.modules.contains_key(&name) {
            let (text, origin) = loader.read(&name);
            loader.load(&name, text, origin, &naming_module)?;
        }
        if is_extension {
            loader.validate_parse_unit(&name)?;
        }
        let unit_referencees = referencees.entry(importer.clone()).or_default();
        if is_extension {
            unit_referencees.0.push(name.clone());
        } else {
            unit_referencees.1.push(name.clone());
        }
        check_circularity(&referencees, &name)?;
        resolutions.insert((importer.clone(), name.clone()));
        if is_extension && loader.is_binding {
            loader.bind_inner_modules(&importer, &name, &mut resolutions)?;
        }
    }
    let mut order = Vec::new();
    loader.get_analysis_order(&root, &mut Vec::new(), &mut FastSet::default(), &mut order)?;
    let mut added = Vec::new();
    for extendee in options.root_extendees {
        let extendee: Rc<str> = Rc::from(*extendee);
        loader.get_analysis_order(
            &extendee,
            &mut Vec::new(),
            &mut FastSet::default(),
            &mut added,
        )?;
    }
    let is_user_module_added = added
        .iter()
        .any(|name| loader.read(name).1 != ModuleOrigin::Standard);
    loader.report_parse_messages(options.file_name.unwrap_or(&root))?;
    // SANY's generator throws on the root module before it reports its messages, and
    // `SANY.parse` prints the exception. The standard modules before it have none.
    // Where the shapes `get_generator_exception` reads don't decide whether SANY's generator
    // throws, the generator below does, declining where it would throw.
    let known_exception = get_generator_exception(&loader.modules[&root].module);
    let undecided = known_exception.as_ref().err().and_then(|stop| match stop {
        Stop::Front(error @ FrontError::NotYet(_)) => Some(error.clone()),
        _ => None,
    });
    if let Some(exception) = match known_exception {
        Ok(exception) => exception,
        Err(_) if undecided.is_some() => None,
        Err(stop) => return Err(stop),
    } {
        return push_generator_exception(loader, &order, &root, exception);
    }
    // SANY's messages come from the port of SANY's generator and levelCheck, which declines the
    // shapes of messages no recording has shown, and else from linking, which reports what SANY's
    // semantic analysis does.
    let generated = match options.version {
        TlcVersion::Master => get_generator_messages(
            &root,
            &end_lines_at_carriage_returns(source),
            &|name| loader.read_text(name),
            options.root_extendees,
            &order,
        ),
        TlcVersion::V1_7_4 => Err(FrontError::NotYet(
            "SANY's generator of TLC 1.7.4".to_owned(),
        )),
    };
    // Where a message of the generator has a shape no recording shows, linking's messages are
    // printed only if they are the generator's. Where linking can't give them, the generator's
    // are, as the TypeScript report, its port, printed them.
    let (generated, unproven) = match generated {
        Ok(Generated::Unproven(messages, lints, message)) => {
            (None, Some((messages, lints, message)))
        }
        Ok(generated) => (Some(generated), None),
        Err(_) => (None, None),
    };
    let undecided_link = undecided.clone();
    // Where linking gives the messages, the linter of its modules gives the warnings of SANY's.
    let messages = match generated {
        Some(generated) => generated,
        None => match (
            link_messages(loader, &order, undecided, is_user_module_added),
            unproven,
        ) {
            (Ok(linked), Some((generated, _, message))) if generated != linked => {
                return Err(not_yet(&format!(
                    "SANY's messages, which linking gives apart from SANY's generator, one of whose messages no recording shows: {message}"
                )));
            }
            (Ok(_), Some((generated, lints, _))) | (Err(_), Some((generated, lints, _))) => {
                Generated::Messages(generated, lints)
            }
            (Ok(linked), None) => Generated::Messages(linked, None),
            (Err(stop), None) => return Err(stop),
        },
    };
    let (messages, lints) = match messages {
        Generated::Messages(messages, lints) | Generated::Unproven(messages, lints, _) => {
            (messages, lints)
        }
        Generated::Declined(reason) => return Err(not_yet(&reason)),
        // SANY's generator throws on the root module, the last SANY analyzes.
        Generated::Exception(index) if index + 1 == order.len() => {
            return push_generator_exception(loader, &order, &root, GENERATOR_EXCEPTION);
        }
        Generated::Exception(_) => {
            return Err(not_yet("SANY's generator exception before the root module"));
        }
    };
    // The TypeScript check throws the errors linking gives, which the library throws only where
    // they are SANY's.
    let is_linked = messages.iter().all(|module| module.errors.is_empty())
        || link_messages(loader, &order, undecided_link, is_user_module_added)
            .is_ok_and(|linked| linked == messages);
    // SANY.frontEndSemanticAnalysis: after each module, SANY prints every message so far.
    let mut warnings: Vec<SanyError> = Vec::new();
    let mut errors: Vec<SanyError> = Vec::new();
    for (name, module_messages) in order.iter().zip(messages) {
        loader.push_progress(format!("Semantic processing of module {name}\n"));
        let was_failed = !errors.is_empty();
        warnings.extend(module_messages.warnings);
        errors.extend(module_messages.errors);
        if warnings.is_empty() && errors.is_empty() {
            continue;
        }
        let format_message =
            |message: &SanyError| format!("{}\n\n{}", message.location, message.message);
        // TLC 1.7.4's SANY prints its warnings with its semantic errors, whose messages differ
        // from master's in ways linking doesn't follow.
        if options.version == TlcVersion::V1_7_4 {
            if !errors.is_empty() {
                return Err(not_yet("TLC 1.7.4's semantic errors"));
            }
            let mut text = format!("Semantic errors:\n\n*** Warnings: {}\n\n", warnings.len());
            for message in &warnings {
                text.push_str(&format!("{}\n\n\n", format_message(message)));
            }
            text.push('\n');
            loader.lines.push(text);
            continue;
        }
        if !warnings.is_empty() && !options.is_xml_export {
            loader.is_warned = true;
            loader
                .lines
                .push(format!("*** Warnings: {}\n\n", warnings.len()));
            for warning in &warnings {
                loader
                    .lines
                    .push(format!("{}\n\n\n\n", format_message(warning)));
            }
        }
        // The TypeScript check throws at the first module with errors, with the warnings so far,
        // unless a module holds a literal TLC can't hold, which it rejects as it loads it.
        let has_rejected_literal = || {
            loader
                .modules
                .values()
                .any(|loaded| reject_module_literals(&loaded.module).is_err())
        };
        if is_linked && !was_failed && !errors.is_empty() && !has_rejected_literal() {
            loader.report = Some(SanyReport {
                errors: errors.clone(),
                warnings: warnings.clone(),
                is_fatal: false,
                parse_error: None,
            });
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
    if !loader.is_failed && options.version != TlcVersion::V1_7_4 && !options.is_xml_export {
        let linted: Vec<&Rc<str>> = order
            .iter()
            .filter(|name| !UNLINTED_MODULES.contains(&&***name))
            .collect();
        let warnings = match lints {
            Some(lints) => lints,
            None => {
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
                warnings
            }
        };
        for name in linted {
            loader.lines.push(format!("Linting of module {name}\n"));
        }
        for warning in warnings {
            loader.is_warned = true;
            loader.lines.push(format!(
                "{}\n\n{}\n\n\n\n",
                warning.location, warning.message
            ));
        }
    }
    Ok(())
}

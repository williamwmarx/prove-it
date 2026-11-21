//! The front end's part of a run, which `tla-front` computes (native/DESIGN.md 13.2): the engine
//! IR and what TLC prints before the search, SANY's report and the messages TLC prints as it
//! starts, or where TLC stops before it searches.

use std::cell::Cell;
use std::path::Path;

use tla_front::TlcVersion;
use tla_front::errors::FrontError;
use tla_front::model::{
    JavaProfile, LoweredModel, ModelOptions, ModelOrigin, ModelSources, StartupMessage,
    lower_front_ranking_with_origin, may_print_constant_definitions, probe_legacy_error,
};
use tla_front::report::{ModuleOrigin, ReportOptions, SanyText, get_sany_text_of};
use tla_front::tlc_messages::{CodedError, get_rejected_literal};

use crate::host::{Files, Host};
use crate::host_path::{Platform, get_stem};
use crate::outcome::Thrown;
use crate::stack::on_search_stack;

/// What the front end gives a run: the model to check, or where TLC stops before it searches.
pub enum Read {
    Model(Front),
    Failed(Failure),
    /// The position of the first command-line invariant (`-inv`) whose definition names an
    /// operator SANY doesn't know, where the root module links without them.
    UnknownInInvariant(usize),
}

/// A spec TLC stops at before the search: SANY's report, then SANY's rejection of the spec, or
/// else the warnings TLC prints before the error it reports with its code, or the exception SANY
/// threw, which ends the report.
pub struct Failure {
    pub sany: String,
    pub warnings: Vec<StartupMessage>,
    pub error: Option<CodedError>,
    pub exception: Option<String>,
    /// The error the library throws for it.
    pub thrown: Option<Thrown>,
}

/// The model to check, and what TLC prints after the banner and before it computes the initial
/// states: SANY's report as tla-front writes it, then `Starting...`. The rest, what TLC prints as
/// it starts, comes from the engine's startup.
pub struct Front {
    pub ir: Vec<u8>,
    /// The names TLC's `Defns` holds, which the trace exploration spec reads.
    pub defined_names: Vec<String>,
    /// None for the IR a test names, which has no source to report on.
    pub sany: Option<String>,
    /// Whether SANY printed a warning, which the TypeScript check prints before an error it throws.
    pub is_sany_warned: bool,
    /// What TLC prints of the Java overrides it loads, right after `Starting...`.
    pub override_messages: Vec<StartupMessage>,
    /// What TLC prints itself after the constant definitions and before the assumptions (the
    /// engine's `startup_done`).
    pub startup_messages: Vec<StartupMessage>,
    /// How a simulation labels an initial state, where the front end knows.
    pub initial_label: Option<String>,
    /// The name and place TLC's simulator records as an initial state's action
    /// (`LoweredModel::initial_action`).
    pub initial_action: Option<(String, String, [i32; 4])>,
    /// SANY's warnings as the library's check prints them (`LoweredModel::sany_warnings`).
    pub sany_warnings: Vec<String>,
    /// `LoweredModel::is_tlcext_declined`.
    pub is_tlcext_declined: bool,
    /// `LoweredModel::alias_decline`.
    pub alias_decline: Option<String>,
}

/// The position of the command-line invariant whose definition SANY's generator rejects for an
/// unknown operator, where every error the front end raises is that and is in the definitions of
/// the command line's invariants, each a line of its own from `first_line` on in the root module.
/// TLC parses each invariant in a module of its own that extends the root module
/// (`TLCDebuggerExpression.process`), where the generator's error fails it as a whole.
fn get_unknown_in_invariant(error: &FrontError, main_file: &str, first_line: u32) -> Option<usize> {
    let FrontError::Syntax(syntax) = error else {
        return None;
    };
    let report = syntax.sany.as_ref()?;
    if report.is_fatal || report.parse_error.is_some() || report.errors.is_empty() {
        return None;
    }
    let root = main_file.rsplit('/').next().unwrap_or(main_file);
    report
        .errors
        .iter()
        .map(|error| {
            if !error.message.starts_with("Unknown operator: `") {
                return None;
            }
            let rest = error.location.strip_prefix("line ")?;
            let (line, rest) = rest.split_once(", col ")?;
            let (_, rest) = rest.split_once(" to line ")?;
            let (end_line, rest) = rest.split_once(", col ")?;
            let (_, module) = rest.split_once(" of module ")?;
            let line: u32 = line.parse().ok()?;
            (module == root && end_line == line.to_string() && line >= first_line)
                .then(|| (line - first_line) as usize)
        })
        .collect::<Option<Vec<_>>>()?
        .into_iter()
        .min()
}

/// The root module's text with lines inserted at the start of the line of its end, `====`, which
/// must start its line, and the number of that line, which the first inserted line takes.
pub fn insert_before_module_end(source: &str, lines: &str) -> Option<(String, u32)> {
    use tla_front::lexer::TokenKind;
    let tokens = tla_front::lexer::tokenize(source).ok()?;
    let mut depth = 0u32;
    let mut end = None;
    for (index, token) in tokens.iter().enumerate() {
        if token.kind == TokenKind::Separator
            && tokens
                .get(index + 1)
                .is_some_and(|next| &*next.text == "MODULE")
        {
            depth += 1;
        } else if token.kind == TokenKind::ModuleEnd && depth > 0 {
            depth -= 1;
            if depth == 0 {
                end = Some((token.line, token.column));
                break;
            }
        }
    }
    let (line, column) = end?;
    if column != 1 || line == 0 {
        return None;
    }
    let mut offset = 0;
    for _ in 1..line {
        offset += source[offset..].find('\n')? + 1;
    }
    let mut text = String::with_capacity(source.len() + lines.len());
    text.push_str(&source[..offset]);
    text.push_str(lines);
    text.push_str(&source[offset..]);
    Some((text, line))
}

/// The front as tla-front finds it: the model it lowers, or where TLC stops before the search, as
/// SANY rejects the spec or lowering the model raises an error TLC reports with a code. Otherwise
/// why tla-front doesn't find either.
pub fn read_front(
    spec_path: &str,
    config_text: &str,
    is_warning_enabled: bool,
    files: &Files,
    host: &dyn Host,
    is_tool: bool,
    seed: i64,
) -> Result<Read, String> {
    // SANY prints that it can't read a module's file it finds, and goes on as if it found none.
    let unreadable = Cell::new(false);
    let read = (|| {
        let spec = Path::new(spec_path);
        let directories: Vec<&Path> = files.directories.iter().map(Path::new).collect();
        let module_source_reads = tla_front::source_reads::ModuleSourceReads::default();
        let load_module = |name: &str| {
            let result = host.load_module(&directories, name);
            module_source_reads.record(
                name,
                result.as_ref().map(|text| text.as_deref()).map_err(|_| ()),
            );
            result.unwrap_or_else(|_| {
                unreadable.set(true);
                None
            })
        };
        let load_class = |name: &str| host.load_class(&directories, name);
        let source = host.read_text(spec);
        let sources = source.as_deref().map(|source| ModelSources {
            source,
            load_module: &load_module,
            load_class: &load_class,
        });
        // SANY's lexer ends a line at a carriage return that no line feed follows, as its report
        // reads the modules; the model reads them so too.
        let mut model_text = source
            .as_deref()
            .map(|source| tla_front::report::end_lines_at_carriage_returns(source).into_owned());
        // The line the definitions of the command line's invariants start at.
        let mut appended_line = None;
        if !files.appended.is_empty() {
            model_text = match model_text.as_deref() {
                Some(text) => {
                    let (text, line) = insert_before_module_end(text, files.appended)
                        .ok_or("-inv in a module whose end the binary doesn't place")?;
                    appended_line = Some(line);
                    Some(text)
                }
                None => None,
            };
        }
        let load_model_module = |name: &str| {
            load_module(name)
                .map(|text| tla_front::report::end_lines_at_carriage_returns(&text).into_owned())
        };
        let model_sources = model_text.as_deref().map(|source| ModelSources {
            source,
            load_module: &load_model_module,
            load_class: &load_class,
        });
        // The tests check engine IRs of models whose sources they don't hold: PROVE_IT_TEST_IR names
        // the IR to check in place of the one tla-front lowers, with nothing printed before the search
        // but what the engine's startup prints.
        if let Some(path) = host.get_variable("PROVE_IT_TEST_IR") {
            let ir = std::fs::read(&path)
                .map_err(|error| format!("the IR PROVE_IT_TEST_IR names: {error}"))?;
            return Ok(Read::Model(Front {
                ir,
                defined_names: Vec::new(),
                sany: None,
                is_sany_warned: false,
                override_messages: Vec::new(),
                startup_messages: Vec::new(),
                initial_label: None,
                initial_action: None,
                sany_warnings: Vec::new(),
                is_tlcext_declined: false,
                alias_decline: None,
            }));
        }
        let describe = host.get_file_describer(files);
        let sany = native_sany(
            host.platform(),
            spec_path,
            files.main_file,
            sources.as_ref(),
            &*describe,
            files.root_extendees,
            files.lint_codes,
        )
        .map_err(|error| match error {
            FrontError::NotYet(reason) => format!("SANY's report of {reason}"),
            _ => "SANY's report, which tla-front doesn't write".to_owned(),
        })?;
        if sany.is_failed {
            return Ok(Read::Failed(Failure {
                sany: sany.text,
                warnings: Vec::new(),
                error: None,
                exception: sany.exception,
                thrown: sany.report.map(Thrown::Syntax),
            }));
        }
        let origins = std::cell::RefCell::new(std::collections::HashMap::new());
        let class_origin = |name: &str| {
            if let Some(&known) = origins.borrow().get(name) {
                return known;
            }
            let found = host.class_origin(&directories, name);
            origins.borrow_mut().insert(name.to_owned(), found);
            found
        };
        let mut origin = ModelOrigin::new(
            java_profile(files.java_profile, host, files.jar.is_some()),
            &class_origin,
        );
        origin.parent_runtime = files.parent_runtime.in_profile(
            if files.is_174 {
                TlcVersion::V1_7_4
            } else {
                TlcVersion::Master
            },
            origin.java_profile,
        );
        origin.resolved_class = Some(&load_class);
        origin.module_source_reads = Some(&module_source_reads);
        // Batch pure presence requests before either early-error branch or class-byte loading.
        // The complete linked module graph, rather than this demand batch, proves final closure.
        let requested_modules: Vec<_> = sany
            .text
            .lines()
            .filter_map(|line| line.strip_prefix("Semantic processing of module "))
            .collect();
        let _ = origin.is_closed_for(requested_modules);
        let default_strings_origin = has_default_strings_origin(&origin);
        if !host.is_complete() {
            return Err("class origin metadata is not available yet".to_owned());
        }
        // With the packaged Strings class, root constants precede module override loading.
        // Class-free linking proves only this early error, not the origins of a successful run.
        let missing_constant = model_sources.as_ref().and_then(|sources| {
            let config = tla_front::config::parse_config(config_text, TlcVersion::Master).ok()?;
            let error = tla_front::environment::link_environment(
                &tla_front::environment::EnvironmentOptions {
                    linked_extendees: &[],
                    origin: None,
                    source: sources.source,
                    load_module: sources.load_module,
                    config: &config,
                    is_unconfigured: false,
                    version: TlcVersion::Master,
                    is_level_checked: false,
                    load_class: None,
                },
            )
            .err()?;
            let coded = error.get_coded(is_tool)?;
            (coded.code == 2222).then_some((error, coded))
        });
        if let Some((error, coded)) = missing_constant.as_ref().filter(|_| default_strings_origin) {
            let error = error.clone();
            let coded = coded.clone();
            let thrown = if !sany.is_warned && host.is_plain() {
                match error {
                    FrontError::Config(message) => Some(Thrown::Config(message)),
                    _ => None,
                }
            } else {
                None
            };
            return Ok(Read::Failed(Failure {
                sany: sany.text,
                warnings: Vec::new(),
                error: Some(coded),
                exception: None,
                thrown,
            }));
        }
        // A class-free candidate is only a hint.  With an uncertain Strings origin,
        // run the old lowering path first; a failure precedes standard-class reporting.
        let legacy_result = missing_constant.is_some().then(|| {
            lower(
                model_sources.as_ref(),
                config_text,
                is_warning_enabled,
                files.directories,
                seed as u64,
                files.root_extendees,
                (&origin, true),
            )
        });
        let legacy_error = legacy_result.and_then(Result::err);
        let legacy_early_error = legacy_error.is_some();
        // TLC loads external classes of every module SANY processed, including dependencies of
        // standard modules, after checking root constants and before processing the specification.
        let bytes_for = |name: &str| host.load_class(&directories, name).map(|(_, bytes)| bytes);
        let standard_classes: Vec<(&str, Vec<u8>)> = sany
            .text
            .lines()
            .filter_map(|line| line.strip_prefix("Semantic processing of module "))
            .filter(|name| {
                tla_front::standard_builtins::MASTER
                    .iter()
                    .any(|module| module.name == *name)
            })
            .filter_map(|name| {
                (!legacy_early_error)
                    .then(|| bytes_for(name))
                    .flatten()
                    .map(|bytes| (name, bytes))
            })
            .collect();
        let visibility = if !is_warning_enabled && !standard_classes.is_empty() {
            model_sources.as_ref().and_then(|sources| {
                let config =
                    tla_front::config::parse_config(config_text, TlcVersion::Master).ok()?;
                tla_front::environment::link_environment(
                    &tla_front::environment::EnvironmentOptions {
                        linked_extendees: &[],
                        origin: None,
                        source: sources.source,
                        load_module: sources.load_module,
                        config: &config,
                        is_unconfigured: true,
                        version: TlcVersion::Master,
                        is_level_checked: false,
                        load_class: None,
                    },
                )
                .ok()
            })
        } else {
            None
        };
        let visible = |module: &str, name: &str, arity: usize| {
            visibility.as_ref().is_none_or(|environment| {
                environment.root_symbols.get(name).is_some_and(|symbol| {
                    symbol.arity == arity
                        && symbol
                            .range
                            .as_ref()
                            .is_none_or(|range| &*range.module == module)
                })
            })
        };
        let has_standard_reports = standard_classes.iter().any(|(name, bytes)| {
            tla_front::java_overrides::standard_class_may_report(
                bytes,
                name,
                is_warning_enabled,
                &visible,
            )
        });
        // TLC's seed as the generator's 64 bits.
        let (warnings, error) = match legacy_error.map_or_else(
            || {
                lower(
                    model_sources.as_ref(),
                    config_text,
                    is_warning_enabled,
                    files.directories,
                    seed as u64,
                    files.root_extendees,
                    (&origin, false),
                )
            },
            Err,
        ) {
            Ok(Some(lowered)) => {
                if has_standard_reports {
                    return Err(
                        "the reports of a user class overriding a standard module".to_owned()
                    );
                }
                return Ok(Read::Model(Front {
                    ir: lowered.ir,
                    defined_names: lowered.defined_names,
                    is_sany_warned: sany.is_warned,
                    sany: Some(sany.text),
                    startup_messages: lowered.startup_messages?,
                    override_messages: lowered.override_messages,
                    initial_label: lowered.initial_label,
                    initial_action: lowered.initial_action,
                    sany_warnings: lowered.sany_warnings,
                    is_tlcext_declined: lowered.is_tlcext_declined,
                    alias_decline: lowered.alias_decline,
                }));
            }
            Ok(None) => unreachable!("normal lowering returns a model"),
            Err(FrontError::NotYet(reason)) => return Err(reason),
            Err(FrontError::Warned(warnings, error)) => (warnings, *error),
            Err(error) => (Vec::new(), error),
        };
        if let Some(first_line) = appended_line
            && !sany.is_failed
            && let Some(position) = get_unknown_in_invariant(&error, files.main_file, first_line)
        {
            return Ok(Read::UnknownInInvariant(position));
        }
        let coded = error
            .get_coded(is_tool)
            .ok_or("an error tla-front raises that TLC reports without a code")?;
        if has_standard_reports && coded.code != 2222 {
            return Err("the reports of a user class overriding a standard module".to_owned());
        }
        // The library prints SANY's warnings before it throws, which it doesn't know here. The
        // front end raises the error without computing the constant definitions, which TLC
        // computes first where the error comes after them, and which may print.
        let thrown = match error {
            _ if sany.is_warned || !host.is_plain() => None,
            // TLC reports a configuration number too big for it as a NumberFormatException, which
            // the front end words otherwise, and doesn't reject a decimal an INSTANCE substitutes,
            // which the front end does (fallback.md, "Known wrong outputs").
            FrontError::Evaluation(message) if message.starts_with("Integer overflow: ") => None,
            _ if get_rejected_literal(&error).is_some() => None,
            _ if model_sources
                .as_ref()
                .is_some_and(|sources| may_print_constant_definitions(sources, config_text)) =>
            {
                Some(Thrown::NotNative(
                    "what the spec prints as TLC computes its constants",
                ))
            }
            FrontError::Config(message) => Some(Thrown::Config(message)),
            FrontError::Evaluation(message) => Some(Thrown::Evaluation(message)),
            FrontError::StackOverflow => Some(Thrown::StackOverflow),
            _ => None,
        };
        Ok(Read::Failed(Failure {
            sany: sany.text,
            warnings,
            error: Some(coded),
            exception: None,
            thrown,
        }))
    })();
    if unreadable.get() {
        return Err(
            "a module's file the front end can't read, such as a directory or text not in UTF-8"
                .to_owned(),
        );
    }
    read
}

/// The variables the JVM reads more options from.
pub const JVM_OPTION_VARIABLES: [&str; 3] =
    ["JAVA_TOOL_OPTIONS", "JDK_JAVA_OPTIONS", "_JAVA_OPTIONS"];

/// The variables the JVM that TLC's command line starts reads: its options, and its class path.
pub const JVM_VARIABLES: [&str; 4] = [
    JVM_OPTION_VARIABLES[0],
    JVM_OPTION_VARIABLES[1],
    JVM_OPTION_VARIABLES[2],
    "CLASSPATH",
];

// The JVM reads more options from these variables, and the class path from CLASSPATH where the
// command line names none (`-cp`, `-jar`). Options it reads there are opaque as on the command
// line: an `-X` option that adds to the boot class path, a system property of the JVM's, and any
// other but those that open a module's packages to others, which change no class TLC loads: a
// class path, an agent or a module patch. A system property of TLC's, or one the command line
// models, declines as the launch is read.
fn java_profile(supplied: JavaProfile, host: &dyn Host, has_class_path: bool) -> JavaProfile {
    let is_opaque_options = |options: String| {
        let mut options = options.split_whitespace();
        while let Some(option) = options.next() {
            let is_opaque = if option.starts_with("-X") {
                crate::args::is_class_vm_option(option)
            } else if let Some(property) = option.strip_prefix("-D") {
                crate::args::is_class_property(
                    property.split_once('=').map_or(property, |(name, _)| name),
                )
            } else if ["--add-opens", "--add-exports", "--add-reads"].contains(&option) {
                options.next().is_none()
            } else {
                !["--add-opens=", "--add-exports=", "--add-reads="]
                    .iter()
                    .any(|prefix| option.starts_with(prefix))
            };
            if is_opaque {
                return true;
            }
        }
        false
    };
    if supplied == JavaProfile::Opaque
        || JVM_OPTION_VARIABLES
            .iter()
            .any(|name| host.get_variable(name).is_some_and(is_opaque_options))
        || !has_class_path && host.get_variable("CLASSPATH").is_some()
    {
        JavaProfile::Opaque
    } else {
        JavaProfile::Default
    }
}

fn has_default_strings_origin(origin: &ModelOrigin<'_>) -> bool {
    origin.java_profile == JavaProfile::Default
        && ["Strings", "tlc2.module.Strings", "tlc2/module/Strings"]
            .iter()
            .all(|name| (origin.class_origin)(name) == tla_front::model::ClassOrigin::Absent)
}

// The model as tla-front lowers it.
fn lower(
    sources: Option<&ModelSources>,
    config_text: &str,
    is_warning_enabled: bool,
    directories: &[String],
    random_seed: u64,
    root_extendees: &[&str],
    (origin, legacy_metadata): (&ModelOrigin<'_>, bool),
) -> Result<Option<LoweredModel>, FrontError> {
    let sources = sources.ok_or_else(|| FrontError::Config("the spec can't be read".into()))?;
    let directories: Vec<&Path> = directories.iter().map(Path::new).collect();
    let options = ModelOptions {
        libraries: &directories,
        version: None,
        is_warning_enabled,
        is_spec_described: true,
        random_seed,
        root_extendees,
    };
    // The evaluator recurses, so it runs with the search's stack.
    let get_startup_texts = |ir: &tla_ir::Ir, definitions: &[tla_ir::Index], interned: usize| {
        on_search_stack(|| tla_trace::get_startup_texts(ir, definitions, interned))
    };
    if legacy_metadata {
        match probe_legacy_error(sources, config_text, &options, origin) {
            Some(error) => Err(error),
            None => Ok(None),
        }
    } else {
        lower_front_ranking_with_origin(
            sources,
            config_text,
            &options,
            &get_startup_texts,
            Some(origin),
        )
        .map(Some)
    }
}

fn native_sany(
    platform: Platform,
    spec_path: &str,
    main_file: &str,
    sources: Option<&ModelSources>,
    describe_file: &dyn Fn(&str, ModuleOrigin) -> Result<String, String>,
    root_extendees: &[&str],
    lint_codes: tla_front::report::LintCodes,
) -> Result<SanyText, FrontError> {
    let root = get_stem(platform.file_name(spec_path));
    // TLC gives SANY the spec as the command line names it, without .tla, unless it's absolute.
    let file_name = if platform.is_absolute(main_file) {
        Some(root)
    } else {
        Some(main_file)
    };
    let sources = sources.ok_or_else(|| FrontError::NotYet("a spec without a file".to_owned()))?;
    let options = ReportOptions {
        version: TlcVersion::Master,
        file_name,
        load_module: sources.load_module,
        describe_file,
        root_extendees,
        is_xml_export: false,
        lint_codes,
    };
    get_sany_text_of(root, sources.source, &options)
}

#[cfg(test)]
mod class_read_order_tests {
    use super::*;
    use crate::host::{FileDescription, FileKind, Machine};
    use crate::zone::Zone;
    use std::path::PathBuf;
    use std::time::SystemTime;

    struct ReadCounter {
        source: &'static str,
        reads: Cell<usize>,
    }

    impl Host for ReadCounter {
        fn kind(&self, path: &Path) -> FileKind {
            if path == Path::new("M.tla") {
                FileKind::File
            } else {
                FileKind::Absent
            }
        }
        fn real_path(&self, path: &Path) -> Option<PathBuf> {
            Some(path.to_path_buf())
        }
        fn current_dir(&self) -> PathBuf {
            PathBuf::from("/tmp")
        }
        fn temp_dir(&self) -> PathBuf {
            PathBuf::from("/tmp")
        }
        fn read_text(&self, _: &Path) -> Option<String> {
            Some(self.source.to_owned())
        }
        fn read_bytes(&self, _: &Path) -> Option<Vec<u8>> {
            None
        }
        fn load_module(&self, _: &[&Path], _: &str) -> Result<Option<String>, PathBuf> {
            Ok(None)
        }
        fn load_class(&self, _: &[&Path], _: &str) -> Option<(PathBuf, Vec<u8>)> {
            self.reads.set(self.reads.get() + 1);
            None
        }
        fn class_origin(&self, _: &[&Path], name: &str) -> tla_front::model::ClassOrigin {
            if ["Strings", "tlc2.module.Strings", "tlc2/module/Strings"].contains(&name) {
                tla_front::model::ClassOrigin::Absent
            } else {
                tla_front::model::ClassOrigin::Unknown
            }
        }
        fn get_file_describer<'h>(&'h self, _: &Files) -> FileDescription<'h> {
            Box::new(|name, _| Ok(format!("/tmp/{name}.tla")))
        }
        fn get_variable(&self, _: &str) -> Option<String> {
            None
        }
        fn now(&self) -> SystemTime {
            SystemTime::UNIX_EPOCH
        }
        fn zone(&self) -> &Zone {
            unreachable!()
        }
        fn machine(&self) -> &Machine {
            unreachable!()
        }
    }

    #[test]
    fn missing_root_constant_precedes_every_class_byte_read() {
        let host = ReadCounter {
            source: "---- MODULE M ----\nEXTENDS TLC\nCONSTANT C\nVARIABLE x\nInit == x = 0\nNext == x' = x\n====\n",
            reads: Cell::new(0),
        };
        let files = Files {
            parent_runtime: tla_front::model::ParentRuntime::Unknown,
            java_profile: JavaProfile::Default,
            spec: Path::new("M.tla"),
            main_file: "M",
            directories: &[],
            temporary: None,
            metadir: None,
            jar: None,
            is_174: false,
            root_extendees: &[],
            appended: "",
            lint_codes: Default::default(),
        };
        let result = read_front(
            "M.tla",
            "INIT Init\nNEXT Next\n",
            true,
            &files,
            &host,
            false,
            4,
        )
        .expect("the front end completes");
        assert!(matches!(
            result,
            Read::Failed(Failure {
                error: Some(CodedError { code: 2222, .. }),
                ..
            })
        ));
        assert_eq!(host.reads.get(), 0);
        let _ = read_front(
            "M.tla",
            "CONSTANT C = 1\nINIT Init\nNEXT Next\n",
            true,
            &files,
            &host,
            false,
            4,
        );
        assert!(host.reads.get() > 0);
    }
}

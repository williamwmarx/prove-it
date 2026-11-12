//! The front end's part of a run, which `tla-front` computes (native/DESIGN.md 13.2): the engine
//! IR and what TLC prints before the search, SANY's report and the messages TLC prints as it
//! starts, or where TLC stops before it searches.

use std::cell::Cell;
use std::path::Path;

use tla_front::TlcVersion;
use tla_front::errors::FrontError;
use tla_front::model::{
    LoweredModel, ModelOptions, ModelSources, StartupMessage, lower_front_ranking_of,
    may_print_constant_definitions,
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
    /// SANY's warnings as the library's check prints them (`LoweredModel::sany_warnings`).
    pub sany_warnings: Vec<String>,
    /// `LoweredModel::is_tlcext_declined`.
    pub is_tlcext_declined: bool,
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
        let load_module = |name: &str| {
            host.load_module(&directories, name).unwrap_or_else(|_| {
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
                sany_warnings: Vec::new(),
                is_tlcext_declined: false,
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
        // TLC's seed as the generator's 64 bits.
        let (warnings, error) = match lower(
            sources.as_ref(),
            config_text,
            is_warning_enabled,
            files.directories,
            seed as u64,
            files.root_extendees,
        ) {
            Ok(lowered) => {
                return Ok(Read::Model(Front {
                    ir: lowered.ir,
                    defined_names: lowered.defined_names,
                    is_sany_warned: sany.is_warned,
                    sany: Some(sany.text),
                    startup_messages: lowered.startup_messages?,
                    override_messages: lowered.override_messages,
                    initial_label: lowered.initial_label,
                    sany_warnings: lowered.sany_warnings,
                    is_tlcext_declined: lowered.is_tlcext_declined,
                }));
            }
            Err(FrontError::NotYet(reason)) => return Err(reason),
            Err(FrontError::Warned(warnings, error)) => (warnings, *error),
            Err(error) => (Vec::new(), error),
        };
        let coded = error
            .get_coded(is_tool)
            .ok_or("an error tla-front raises that TLC reports without a code")?;
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
            _ if sources
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

// The model as tla-front lowers it.
fn lower(
    sources: Option<&ModelSources>,
    config_text: &str,
    is_warning_enabled: bool,
    directories: &[String],
    random_seed: u64,
    root_extendees: &[&str],
) -> Result<LoweredModel, FrontError> {
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
    lower_front_ranking_of(sources, config_text, &options, &get_startup_texts)
}

fn native_sany(
    platform: Platform,
    spec_path: &str,
    main_file: &str,
    sources: Option<&ModelSources>,
    describe_file: &dyn Fn(&str, ModuleOrigin) -> Result<String, String>,
    root_extendees: &[&str],
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
    };
    get_sany_text_of(root, sources.source, &options)
}

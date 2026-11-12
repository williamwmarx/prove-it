//! The front end's part of a run, which `tla-front` computes (native/DESIGN.md 13.2): the engine
//! IR and what TLC prints before the search, SANY's report and the messages TLC prints as it
//! starts, or where TLC stops before it searches.

use std::cell::Cell;
use std::path::Path;

use tla_front::errors::FrontError;
use tla_front::model::{
    LoweredModel, ModelOptions, ModelSources, StartupMessage, lower_front_ranking_of,
};
use tla_front::report::{
    ModuleOrigin, ReportOptions, SanyText, get_missing_root_text, get_sany_text_of,
};
use tla_front::tlc_messages::CodedError;
use tla_front::{TlcVersion, get_standard_module};

use crate::host::{FileKind, Files, Host};
use crate::host_path::{Platform, get_stem};
use crate::resolve::get_missing_spec_message;
use crate::stack::on_search_stack;

/// What the front end gives a run: the model to check, or where TLC stops before it searches.
pub enum Read {
    Model(Front),
    Failed(Failure),
}

/// A spec TLC stops at before the search: SANY's report, then SANY's rejection of the spec, or
/// else the warnings TLC prints before the error it reports with its code, or the exception SANY
/// threw, which ends the report. SANY's resolver says on standard error where it looked for a spec
/// no file holds.
pub struct Failure {
    pub missing_spec: Option<String>,
    pub sany: String,
    pub warnings: Vec<StartupMessage>,
    pub error: Option<CodedError>,
    pub exception: Option<String>,
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
    /// What TLC prints of the Java overrides it loads, right after `Starting...`.
    pub override_messages: Vec<StartupMessage>,
    /// What TLC prints itself after the constant definitions and before the assumptions (the
    /// engine's `startup_done`).
    pub startup_messages: Vec<StartupMessage>,
    /// How a simulation labels an initial state, where the front end knows.
    pub initial_label: Option<String>,
    /// SANY's warnings as the library's check prints them (`LoweredModel::sany_warnings`).
    pub sany_warnings: Vec<String>,
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
                override_messages: Vec::new(),
                startup_messages: Vec::new(),
                initial_label: None,
                sany_warnings: Vec::new(),
            }));
        }
        let describe = host.get_file_describer(files);
        let sany = native_sany(
            host.platform(),
            host.kind(spec) == FileKind::Absent,
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
                missing_spec: sources.is_none().then(|| {
                    get_missing_spec_message(host, files.main_file, &files.directories[1..])
                }),
                sany: sany.text,
                warnings: Vec::new(),
                error: None,
                exception: sany.exception,
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
                    sany: Some(sany.text),
                    startup_messages: lowered.startup_messages?,
                    override_messages: lowered.override_messages,
                    initial_label: lowered.initial_label,
                    sany_warnings: lowered.sany_warnings,
                }));
            }
            Err(FrontError::NotYet(reason)) => return Err(reason),
            Err(FrontError::Warned(warnings, error)) => (warnings, *error),
            Err(error) => (Vec::new(), error),
        };
        let coded = error
            .get_coded(is_tool)
            .ok_or("an error tla-front raises that TLC reports without a code")?;
        Ok(Read::Failed(Failure {
            missing_spec: None,
            sany: sany.text,
            warnings,
            error: Some(coded),
            exception: None,
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

/// SANY's report, or its fatal error where no file holds the spec and the jar no standard module
/// of its name.
fn native_sany(
    platform: Platform,
    is_spec_absent: bool,
    spec_path: &str,
    main_file: &str,
    sources: Option<&ModelSources>,
    describe_file: &dyn Fn(&str, ModuleOrigin) -> String,
    root_extendees: &[&str],
) -> Result<SanyText, FrontError> {
    let root = get_stem(platform.file_name(spec_path));
    // TLC gives SANY the spec as the command line names it, without .tla, unless it's absolute.
    let name = if platform.is_absolute(main_file) {
        root
    } else {
        main_file
    };
    let Some(sources) = sources else {
        return if is_spec_absent && get_standard_module(root, TlcVersion::Master).is_none() {
            Ok(SanyText {
                text: get_missing_root_text(name, name),
                is_failed: true,
                exception: None,
            })
        } else {
            Err(FrontError::NotYet("a spec without a file".to_owned()))
        };
    };
    let options = ReportOptions {
        version: TlcVersion::Master,
        file_name: Some(name),
        load_module: sources.load_module,
        describe_file,
        root_extendees,
        is_xml_export: false,
    };
    get_sany_text_of(root, sources.source, &options)
}

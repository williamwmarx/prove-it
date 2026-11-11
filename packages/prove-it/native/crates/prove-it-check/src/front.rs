//! The front end's part of a run, which `tla-front` computes (native/DESIGN.md 13.2): the engine
//! IR and what TLC prints before the search, SANY's report and the messages TLC prints as it
//! starts, or where TLC stops before it searches.

use std::path::Path;

use tla_front::TlcVersion;
use tla_front::errors::FrontError;
use tla_front::model::{
    LoweredModel, ModelOptions, ModelSources, StartupMessage, TRACE_MODULE, lower_front_ranking_of,
};
use tla_front::report::{ModuleOrigin, ReportOptions, SanyText, get_sany_text_of};
use tla_front::tlc_messages::CodedError;

use crate::host::{Files, Host};
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
}

/// The model to check, and what TLC prints after the banner and before it computes the initial
/// states: SANY's report as tla-front writes it, then `Starting...`. The rest, what TLC prints as
/// it starts, comes from the engine's startup.
pub struct Front {
    pub ir: Vec<u8>,
    /// None for the IR a test names, which has no source to report on.
    pub sany: Option<String>,
    /// What TLC prints of the Java overrides it loads, right after `Starting...`.
    pub override_messages: Vec<StartupMessage>,
    /// What TLC prints itself after the constant definitions and before the assumptions (the
    /// engine's `startup_done`).
    pub startup_messages: Vec<StartupMessage>,
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
    let spec = Path::new(spec_path);
    let directory = spec.parent().unwrap_or(Path::new("."));
    let directories: Vec<&Path> = std::iter::once(directory)
        .chain(files.libraries.iter().map(Path::new))
        .collect();
    let load_module = |name: &str| host.load_module(&directories, name);
    let load_class = |name: &str| host.load_class(directory, name);
    let source = host.read_text(spec);
    let sources = source.as_deref().map(|source| ModelSources {
        source,
        directory,
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
            sany: None,
            override_messages: Vec::new(),
            startup_messages: Vec::new(),
        }));
    }
    let describe = host.get_file_describer(files);
    let sany = native_sany(
        spec_path,
        sources.as_ref(),
        &*describe,
        files.is_trace_recorded,
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
        }));
    }
    // TLC's seed as the generator's 64 bits.
    let (warnings, error) = match lower(
        sources.as_ref(),
        config_text,
        is_warning_enabled,
        files.libraries,
        seed as u64,
        files.is_trace_recorded,
    ) {
        Ok(lowered) => {
            return Ok(Read::Model(Front {
                ir: lowered.ir,
                sany: Some(sany.text),
                startup_messages: lowered.startup_messages?,
                override_messages: lowered.override_messages,
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
        sany: sany.text,
        warnings,
        error: Some(coded),
        exception: None,
    }))
}

// The model as tla-front lowers it.
fn lower(
    sources: Option<&ModelSources>,
    config_text: &str,
    is_warning_enabled: bool,
    libraries: &[String],
    random_seed: u64,
    is_trace_recorded: bool,
) -> Result<LoweredModel, FrontError> {
    let sources = sources.ok_or_else(|| FrontError::Config("the spec can't be read".into()))?;
    let libraries: Vec<&Path> = libraries.iter().map(Path::new).collect();
    let options = ModelOptions {
        libraries: &libraries,
        version: None,
        is_warning_enabled,
        is_spec_described: true,
        random_seed,
        is_trace_recorded,
    };
    // The evaluator recurses, so it runs with the search's stack.
    let get_startup_texts = |ir: &tla_ir::Ir, definitions: &[tla_ir::Index], interned: usize| {
        on_search_stack(|| tla_trace::get_startup_texts(ir, definitions, interned))
    };
    lower_front_ranking_of(sources, config_text, &options, &get_startup_texts)
}

fn native_sany(
    spec_path: &str,
    sources: Option<&ModelSources>,
    describe_file: &dyn Fn(&str, ModuleOrigin) -> String,
    is_trace_recorded: bool,
) -> Result<SanyText, FrontError> {
    let spec = Path::new(spec_path);
    // TLC gives SANY the spec as the command line names it, without .tla, unless it's absolute.
    let file_name = if spec.is_absolute() {
        spec.file_stem().and_then(|stem| stem.to_str())
    } else {
        Some(spec_path.strip_suffix(".tla").unwrap_or(spec_path))
    };
    let root = spec
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or_default();
    let sources = sources.ok_or_else(|| FrontError::NotYet("a spec without a file".to_owned()))?;
    let options = ReportOptions {
        version: TlcVersion::Master,
        file_name,
        load_module: sources.load_module,
        describe_file,
        root_extendees: if is_trace_recorded {
            &[TRACE_MODULE]
        } else {
            &[]
        },
        is_xml_export: false,
    };
    get_sany_text_of(root, sources.source, &options)
}

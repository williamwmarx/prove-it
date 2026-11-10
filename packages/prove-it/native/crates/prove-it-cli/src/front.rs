//! The front end's part of a run, which `tla-front` computes (native/DESIGN.md 13.2): the engine
//! IR and what TLC prints before the search, SANY's report and the messages TLC prints as it
//! starts, or where TLC stops before it searches.

use std::path::Path;

use tla_front::TlcVersion;
use tla_front::errors::FrontError;
use tla_front::model::{LoweredModel, ModelOptions, StartupMessage, lower_front_ranking};
use tla_front::report::{ReportOptions, SanyText, get_sany_text};
use tla_front::tlc_messages::CodedError;

use crate::check::SEARCH_STACK_BYTES;
use crate::files::FileDescriber;

/// What the front end gives a run: the model to check, or where TLC stops before it searches.
pub enum Read {
    Model(Front),
    Failed(Failure),
}

/// A spec TLC stops at before the search: SANY's report, then SANY's rejection of the spec, or
/// else the error TLC reports with its code.
pub struct Failure {
    pub sany: String,
    pub error: Option<CodedError>,
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
    describer: &FileDescriber,
    libraries: &[String],
    is_tool: bool,
    seed: i64,
) -> Result<Read, String> {
    // The tests check engine IRs of models whose sources they don't hold: PROVE_IT_TEST_IR names
    // the IR to check in place of the one tla-front lowers, with nothing printed before the search
    // but what the engine's startup prints.
    if let Some(path) = std::env::var_os("PROVE_IT_TEST_IR") {
        let ir = std::fs::read(&path)
            .map_err(|error| format!("the IR PROVE_IT_TEST_IR names: {error}"))?;
        return Ok(Read::Model(Front {
            ir,
            sany: None,
            override_messages: Vec::new(),
            startup_messages: Vec::new(),
        }));
    }
    let sany = native_sany(spec_path, describer, libraries)
        .ok_or("SANY's report, which tla-front doesn't write")?;
    if sany.is_failed {
        return Ok(Read::Failed(Failure {
            sany: sany.text,
            error: None,
        }));
    }
    // TLC's seed as the generator's 64 bits.
    let error = match lower(
        spec_path,
        config_text,
        is_warning_enabled,
        libraries,
        seed as u64,
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
        Err(error) => error,
    };
    let coded = error
        .get_coded(is_tool)
        .ok_or("an error tla-front raises that TLC reports without a code")?;
    Ok(Read::Failed(Failure {
        sany: sany.text,
        error: Some(coded),
    }))
}

// The model as tla-front lowers it.
fn lower(
    spec_path: &str,
    config_text: &str,
    is_warning_enabled: bool,
    libraries: &[String],
    random_seed: u64,
) -> Result<LoweredModel, FrontError> {
    let path = if spec_path.ends_with(".tla") {
        spec_path.to_string()
    } else {
        format!("{spec_path}.tla")
    };
    let libraries: Vec<&Path> = libraries.iter().map(Path::new).collect();
    let options = ModelOptions {
        libraries: &libraries,
        version: None,
        is_warning_enabled,
        is_spec_described: true,
        random_seed,
    };
    // The evaluator recurses, so it runs with the search's stack.
    let get_startup_texts = |ir: &tla_ir::Ir, definitions: &[tla_ir::Index]| {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(SEARCH_STACK_BYTES)
                .spawn_scoped(scope, || tla_trace::get_startup_texts(ir, definitions))
                .expect("a thread to compute the startup")
                .join()
                .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
        })
    };
    lower_front_ranking(Path::new(&path), config_text, &options, &get_startup_texts)
}

fn native_sany(
    spec_path: &str,
    describer: &FileDescriber,
    libraries: &[String],
) -> Option<SanyText> {
    let spec = Path::new(spec_path);
    let directory = spec.parent().unwrap_or(Path::new("."));
    let load_module = |name: &str| {
        std::iter::once(directory)
            .chain(libraries.iter().map(Path::new))
            .find_map(|directory| {
                std::fs::read_to_string(directory.join(format!("{name}.tla"))).ok()
            })
    };
    // TLC gives SANY the spec as the command line names it, without .tla, unless it's absolute.
    let file_name = if spec.is_absolute() {
        spec.file_stem().and_then(|stem| stem.to_str())
    } else {
        Some(spec_path.strip_suffix(".tla").unwrap_or(spec_path))
    };
    let options = ReportOptions {
        version: TlcVersion::Master,
        file_name,
        load_module: &load_module,
        describe_file: &|name, origin| describer.describe(name, origin),
    };
    get_sany_text(spec, &options).ok()
}

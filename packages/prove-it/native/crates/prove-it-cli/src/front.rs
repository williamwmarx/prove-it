//! The front end's part of a run: the engine IR and what TLC prints before the search, SANY's
//! output and the warnings. The binary reads a recorded front, which the differential makes with
//! the TypeScript CLI, from the directory `PROVE_IT_FRONT` names: `<Spec>.front`, and `<Spec>.ir`
//! when the TypeScript CLI lowered the model. Without a recorded IR, `tla-front` lowers the model
//! itself (native/DESIGN.md 13.2); the text it prints will come from `tla-front` too.

use std::path::Path;

use tla_front::TlcVersion;
use tla_front::errors::FrontError;
use tla_front::model::{ModelOptions, StartupMessage, lower_front};
use tla_front::report::{ReportOptions, SanyText, get_sany_text};
use tla_front::tlc_messages::CodedError;

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

pub struct Front {
    pub ir: Vec<u8>,
    /// What TLC prints after the banner and before it computes the initial states.
    pub text: FrontText,
}

/// What TLC prints of the front: recorded by the differential, or written by tla-front.
pub enum FrontText {
    /// What TLC printed from the banner to "Computing initial states...", as the TypeScript CLI
    /// printed it; the engine's startup hooks stay silent, since it holds what they report.
    Recorded(Vec<u8>),
    /// What tla-front writes, printed as TLC prints it: SANY's report, framed by 2220
    /// "Starting SANY..." and 2219 "SANY finished." under -tool, then 2185 `Starting... (…)`, then
    /// the search's startup, whose Print and PrintT output and symmetry warnings the engine's
    /// hooks report, with `startup_messages` printed at `startup_done`, before the assumptions.
    // HACK: read once the CLI wires the engine's startup hooks; until then check.rs declines it.
    #[allow(dead_code)]
    Native {
        sany: String,
        startup_messages: Vec<StartupMessage>,
    },
}

pub fn read_front(
    spec_path: &str,
    config_text: &str,
    is_warning_enabled: bool,
    describer: &FileDescriber,
    libraries: &[String],
    is_tool: bool,
    seed: i64,
) -> Result<Read, String> {
    let lowering = Lowering {
        spec_path,
        config_text,
        is_warning_enabled,
        is_tool,
        // TLC's seed as the generator's 64 bits.
        random_seed: seed as u64,
    };
    let name = Path::new(spec_path)
        .file_stem()
        .map_or_else(String::new, |stem| stem.to_string_lossy().into_owned());
    let directory = std::env::var_os("PROVE_IT_FRONT");
    let directory = directory.as_deref().map(Path::new);
    let read = |extension: &str| match directory {
        Some(directory) => std::fs::read(directory.join(format!("{name}.{extension}"))),
        None => Err(std::io::ErrorKind::NotFound.into()),
    };
    let no_front = || match directory {
        Some(directory) => format!("no recorded front of {name} in {}", directory.display()),
        None => "the front a search prints, which tla-front doesn't write".to_owned(),
    };
    // Without a recorded front, as where TLC prints nothing past its startup for the differential
    // to record, tla-front writes the front, or finds that SANY rejects the spec or TLC reports an
    // error before the search.
    let Ok(recorded) = read("front") else {
        return native_front(&lowering, describer, libraries)
            .map_err(|reason| format!("{}: {reason}", no_front()));
    };
    // PROVE_IT_NATIVE_FRONT=1 prints SANY's report as tla-front writes it in place of the recorded
    // one, which the rest of the front still follows until tla-front writes it too.
    let output = match std::env::var_os("PROVE_IT_NATIVE_FRONT") {
        Some(_) => native_sany(spec_path, describer, libraries)
            .and_then(|sany| splice_sany(&recorded, &sany.text))
            .unwrap_or(recorded),
        None => recorded,
    };
    let ir = match read("ir") {
        Ok(ir) => ir,
        Err(_) => {
            lower(&lowering, libraries)
                .map_err(|error| match error {
                    FrontError::NotYet(reason) => format!("{}: {reason}", no_front()),
                    _ => no_front(),
                })?
                .ir
        }
    };
    Ok(Read::Model(Front {
        ir,
        text: FrontText::Recorded(output),
    }))
}

// The model as tla-front lowers it.
fn lower(
    lowering: &Lowering<'_>,
    libraries: &[String],
) -> Result<tla_front::model::LoweredModel, FrontError> {
    let spec_path = lowering.spec_path;
    let path = if spec_path.ends_with(".tla") {
        spec_path.to_string()
    } else {
        format!("{spec_path}.tla")
    };
    let libraries: Vec<&Path> = libraries.iter().map(Path::new).collect();
    let options = ModelOptions {
        libraries: &libraries,
        version: None,
        is_warning_enabled: lowering.is_warning_enabled,
        is_spec_described: true,
        random_seed: lowering.random_seed,
    };
    lower_front(Path::new(&path), lowering.config_text, &options)
}

/// What tla-front lowers a run's model from.
struct Lowering<'a> {
    spec_path: &'a str,
    config_text: &'a str,
    is_warning_enabled: bool,
    is_tool: bool,
    random_seed: u64,
}

// The front as tla-front writes it: the model with what TLC prints as it starts, or where TLC
// stops before the search, as SANY rejects the spec or lowering the model raises an error TLC
// reports with a code. Otherwise why tla-front doesn't write it.
fn native_front(
    lowering: &Lowering<'_>,
    describer: &FileDescriber,
    libraries: &[String],
) -> Result<Read, String> {
    let sany = native_sany(lowering.spec_path, describer, libraries)
        .ok_or("SANY's report, which tla-front doesn't write")?;
    if sany.is_failed {
        return Ok(Read::Failed(Failure {
            sany: sany.text,
            error: None,
        }));
    }
    let error = match lower(lowering, libraries) {
        Ok(lowered) => {
            return Ok(Read::Model(Front {
                ir: lowered.ir,
                text: FrontText::Native {
                    sany: sany.text,
                    startup_messages: lowered.startup_messages?,
                },
            }));
        }
        Err(FrontError::NotYet(reason)) => return Err(reason),
        Err(error) => error,
    };
    let coded = error
        .get_coded(lowering.is_tool)
        .ok_or("an error tla-front raises that TLC reports without a code")?;
    Ok(Read::Failed(Failure {
        sany: sany.text,
        error: Some(coded),
    }))
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

// The recorded front with SANY's report in it replaced: under -tool between "Starting SANY..."
// (2220) and "SANY finished." (2219), and otherwise before "Starting...".
fn splice_sany(recorded: &[u8], sany: &str) -> Option<Vec<u8>> {
    let text = std::str::from_utf8(recorded).ok()?;
    let (before, after) = if text.starts_with("@!@!@STARTMSG") {
        let started = "@!@!@ENDMSG 2220 @!@!@\n";
        (
            text.find(started)? + started.len(),
            text.find("@!@!@STARTMSG 2219:")?,
        )
    } else {
        (0, text.find("Starting... (")?)
    };
    Some([&recorded[..before], sany.as_bytes(), &recorded[after..]].concat())
}

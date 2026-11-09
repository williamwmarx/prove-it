//! The front end's part of a run: the engine IR and what TLC prints before the search, SANY's
//! output and the warnings. The binary reads a recorded front, which the differential makes with
//! the TypeScript CLI, from the directory `PROVE_IT_FRONT` names: `<Spec>.front`, and `<Spec>.ir`
//! when the TypeScript CLI lowered the model. Without a recorded IR, `tla-front` lowers the model
//! itself (native/DESIGN.md 13.2); the text it prints will come from `tla-front` too.

use std::path::Path;

use tla_front::TlcVersion;
use tla_front::errors::FrontError;
use tla_front::model::{ModelOptions, lower_model};
use tla_front::report::{ReportOptions, get_sany_text};

use crate::files::FileDescriber;

pub struct Front {
    pub ir: Vec<u8>,
    /// What TLC prints after the banner and before it computes the initial states.
    pub output: Vec<u8>,
}

pub fn read_front(
    spec_path: &str,
    config_text: &str,
    is_warning_enabled: bool,
    describer: &FileDescriber,
    libraries: &[String],
) -> Result<Front, String> {
    let name = Path::new(spec_path)
        .file_stem()
        .map_or_else(String::new, |stem| stem.to_string_lossy().into_owned());
    let Some(directory) = std::env::var_os("PROVE_IT_FRONT") else {
        return Err(format!("the front end, to parse {spec_path}"));
    };
    let directory = Path::new(&directory);
    let read = |extension: &str| std::fs::read(directory.join(format!("{name}.{extension}")));
    let no_front = || format!("no recorded front of {name} in {}", directory.display());
    let recorded = read("front").map_err(|_| no_front())?;
    // PROVE_IT_NATIVE_FRONT=1 prints SANY's report as tla-front writes it in place of the recorded
    // one, which the rest of the front still follows until tla-front writes it too.
    let output = match std::env::var_os("PROVE_IT_NATIVE_FRONT") {
        Some(_) => native_sany(spec_path, describer, libraries)
            .and_then(|sany| Some([sany.into_bytes(), after_sany(&recorded)?.to_vec()].concat()))
            .unwrap_or(recorded),
        None => recorded,
    };
    let ir = match read("ir") {
        Ok(ir) => ir,
        Err(_) => {
            let path = if spec_path.ends_with(".tla") {
                spec_path.to_string()
            } else {
                format!("{spec_path}.tla")
            };
            let options = ModelOptions {
                library: None,
                version: None,
                is_warning_enabled,
            };
            lower_model(Path::new(&path), config_text, &options).map_err(|error| match error {
                FrontError::NotYet(reason) => format!("{}: {reason}", no_front()),
                _ => no_front(),
            })?
        }
    };
    Ok(Front { ir, output })
}

// SANY's report of the spec's modules, or nothing where tla-front doesn't write it yet.
fn native_sany(spec_path: &str, describer: &FileDescriber, libraries: &[String]) -> Option<String> {
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

// The recorded front from where SANY's report ends: Starting..., which follows it without -tool;
// -tool prints none of it.
fn after_sany(recorded: &[u8]) -> Option<&[u8]> {
    let text = std::str::from_utf8(recorded).ok()?;
    let at = (!text.starts_with("@!@!@STARTMSG"))
        .then(|| text.find("Starting... ("))
        .flatten()?;
    Some(&recorded[at..])
}

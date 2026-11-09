//! The front end's part of a run: the engine IR and what TLC prints before the search, SANY's
//! output and the warnings. The binary reads a recorded front, which the differential makes with
//! the TypeScript CLI, from the directory `PROVE_IT_FRONT` names: `<Spec>.front`, and `<Spec>.ir`
//! when the TypeScript CLI lowered the model. Without a recorded IR, `tla-front` lowers the model
//! itself (native/DESIGN.md 13.2); the text it prints will come from `tla-front` too.

use std::path::Path;

use tla_front::errors::FrontError;
use tla_front::model::{ModelOptions, lower_model};

pub struct Front {
    pub ir: Vec<u8>,
    /// What TLC prints after the banner and before it computes the initial states.
    pub output: Vec<u8>,
}

pub fn read_front(
    spec_path: &str,
    config_text: &str,
    is_warning_enabled: bool,
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
    let output = read("front").map_err(|_| no_front())?;
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

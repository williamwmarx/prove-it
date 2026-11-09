//! The front end's part of a run: the engine IR and what TLC prints before the search, SANY's
//! output and the warnings. `tla-front` will compute it (native/DESIGN.md 12.2); until then the
//! binary reads a recorded front, which the differential makes with the TypeScript CLI, from the
//! directory `PROVE_IT_FRONT` names: `<Spec>.ir` and `<Spec>.front`.

use std::path::Path;

pub struct Front {
    pub ir: Vec<u8>,
    /// What TLC prints after the banner and before it computes the initial states.
    pub output: Vec<u8>,
}

pub fn read_front(spec_path: &str) -> Result<Front, String> {
    let name = Path::new(spec_path)
        .file_stem()
        .map_or_else(String::new, |stem| stem.to_string_lossy().into_owned());
    let Some(directory) = std::env::var_os("PROVE_IT_FRONT") else {
        return Err(format!("the front end, to parse {spec_path}"));
    };
    let directory = Path::new(&directory);
    let read = |extension: &str| std::fs::read(directory.join(format!("{name}.{extension}")));
    match (read("ir"), read("front")) {
        (Ok(ir), Ok(output)) => Ok(Front { ir, output }),
        _ => Err(format!(
            "no recorded front of {name} in {}",
            directory.display()
        )),
    }
}

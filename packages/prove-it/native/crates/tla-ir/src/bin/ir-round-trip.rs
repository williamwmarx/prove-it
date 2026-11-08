//! Decodes each engine IR file it is given, and each `.ir` file under each directory, encodes it
//! again, and reports any whose bytes differ: `ir-round-trip [--dump] <path>...`. With `--dump` it
//! prints each decoded IR instead.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let is_dumped = arguments.iter().any(|argument| argument == "--dump");
    let mut files = Vec::new();
    for argument in arguments.iter().filter(|argument| *argument != "--dump") {
        if let Err(error) = find_files(Path::new(argument), &mut files) {
            eprintln!("{argument}: {error}");
            return ExitCode::FAILURE;
        }
    }
    let failures = files
        .iter()
        .filter(|file| {
            let failure = match std::fs::read(file) {
                Err(error) => Some(format!("can't read it: {error}")),
                Ok(bytes) => match tla_ir::decode(&bytes) {
                    Err(error) => Some(format!("doesn't decode: {error}")),
                    Ok(ir) if is_dumped => {
                        println!("{}: {ir:#?}", file.display());
                        None
                    }
                    Ok(ir) => first_difference(&bytes, &tla_ir::encode(&ir))
                        .map(|at| format!("encodes differently from byte {at}")),
                },
            };
            if let Some(failure) = &failure {
                eprintln!("{}: {failure}", file.display());
            }
            failure.is_some()
        })
        .count();
    println!(
        "{} of {} IR files round-trip byte for byte",
        files.len() - failures,
        files.len()
    );
    if failures == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

// The file at `path`, or the `.ir` files in it and its subdirectories, in order.
fn find_files(path: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
    if !path.is_dir() {
        files.push(path.to_path_buf());
        return Ok(());
    }
    let mut entries = std::fs::read_dir(path)?
        .map(|entry| entry.map(|entry| entry.path()))
        .collect::<std::io::Result<Vec<_>>>()?;
    entries.sort();
    for entry in entries {
        if entry.is_dir() || entry.extension().is_some_and(|extension| extension == "ir") {
            find_files(&entry, files)?;
        }
    }
    Ok(())
}

fn first_difference(left: &[u8], right: &[u8]) -> Option<usize> {
    let shared = left
        .iter()
        .zip(right)
        .position(|(left, right)| left != right);
    shared.or((left.len() != right.len()).then(|| left.len().min(right.len())))
}

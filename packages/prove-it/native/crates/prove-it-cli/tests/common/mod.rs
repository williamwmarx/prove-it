//! Helpers the binary's integration tests share.

use std::path::PathBuf;
use std::process::{Command, Output};

pub fn run(directory: &PathBuf, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(args)
        .current_dir(directory)
        .output()
        .expect("the binary runs")
}

pub fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// Writes the spec and its configuration as `<name>.tla` and `<name>.cfg` into a directory of the
/// test's own, and runs the binary there with the arguments.
pub fn run_named(
    test: &str,
    name: &str,
    (spec, config): (&str, &str),
    args: &[&str],
) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join(format!("{name}.tla")), spec).expect("a spec");
    std::fs::write(directory.join(format!("{name}.cfg")), config).expect("a configuration");
    (run(&directory, args), directory)
}

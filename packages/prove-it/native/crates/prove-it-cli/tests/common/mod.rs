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

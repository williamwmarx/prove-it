//! What the binary's test files share: running it on a spec of the test's own, and reading what
//! it printed.
#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

pub fn run(directory: &PathBuf, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(args)
        .current_dir(directory)
        .output()
        .expect("the binary runs")
}

// Runs the binary on a spec of the test's own, written as Stop.tla with its configuration.
pub fn run_spec(test: &str, spec: &str, config: &str) -> (Output, PathBuf) {
    run_spec_with(test, spec, config, &[])
}

pub fn run_spec_with(test: &str, spec: &str, config: &str, args: &[&str]) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("Stop.tla"), spec).expect("a spec");
    std::fs::write(directory.join("Stop.cfg"), config).expect("a configuration");
    (
        run(&directory, &[args, &["-noTE", "Stop"]].concat()),
        directory,
    )
}

pub fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

pub fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
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

/// The path the binary and TLC know `directory` by once it is their working directory: `getcwd`,
/// which the JVM's `user.dir` is, names it with every symbolic link resolved, as macOS's temporary
/// directory under `/var`, a link to `/private/var`.
pub fn get_working_path(directory: &Path) -> PathBuf {
    let real = std::fs::canonicalize(directory).expect("the directory's real path");
    // Windows's canonical path is a verbatim one, `\\?\C:\…`, where `getcwd` gives `C:\…`.
    match real.to_str().and_then(|text| text.strip_prefix(r"\\?\")) {
        Some(plain) if cfg!(windows) && plain.as_bytes().get(1) == Some(&b':') => {
            PathBuf::from(plain)
        }
        _ => real,
    }
}

/// Makes `link` a symbolic link to `target`, which, where relative, is read from the link's
/// directory, as the system reads it.
pub fn link(target: &Path, link: &Path) {
    #[cfg(unix)]
    let made = std::os::unix::fs::symlink(target, link);
    // Windows links a directory and a file differently, and creates either only with the
    // privilege to (an elevated process, as on GitHub's runners, or Developer Mode).
    #[cfg(windows)]
    let made = {
        let parent = link.parent().expect("the link's directory");
        if parent.join(target).is_dir() {
            std::os::windows::fs::symlink_dir(target, link)
        } else {
            std::os::windows::fs::symlink_file(target, link)
        }
    };
    if let Err(error) = made {
        panic!(
            "cannot make {} a symbolic link to {}: {error}{}",
            link.display(),
            target.display(),
            if cfg!(windows) {
                " (Windows makes symbolic links only for an elevated process or in Developer Mode)"
            } else {
                ""
            }
        );
    }
}

/// Sets when the directory was last modified.
pub fn set_modified(directory: &Path, time: std::time::SystemTime) {
    let mut options = std::fs::OpenOptions::new();
    #[cfg(unix)]
    options.read(true);
    // Windows opens a directory only with FILE_FLAG_BACKUP_SEMANTICS, and sets its times only with
    // FILE_WRITE_ATTRIBUTES.
    #[cfg(windows)]
    {
        use std::os::windows::fs::OpenOptionsExt;
        options.access_mode(0x100).custom_flags(0x0200_0000);
    }
    options
        .open(directory)
        .expect("the directory")
        .set_modified(time)
        .expect("its time");
}

/// What the binary does on Windows with a spec TLC ran on Unix, by the lines TLC printed there: no
/// run of TLC on Windows has recorded how it prints a path, so the binary prints the forms whose
/// rendering TLC's source settles and declines the others, the first in the order it prints them.
pub enum OnWindows {
    Declined(&'static str),
    /// The lines, each `Parsing file` path with Windows's separator.
    Printed(Vec<String>),
}

/// The reasons the binary gives on Windows, each up to where it names a path.
pub const DECLINED_FILE_URL: &str =
    "SANY's report of the URL TLC prints on Windows of a module whose path isn't its real one";
pub const DECLINED_ROOT_FILE: &str =
    "SANY's report of the path TLC prints on Windows of a module in the root module's file";
pub const DECLINED_JAR: &str =
    "SANY's report of the URL TLC prints on Windows of a standard module in its jar";
pub const DECLINED_CLASS_URL: &str = "the URL TLC prints on Windows of a Java class";
pub const DECLINED_TRACE_SPEC: &str =
    "the path TLC prints on Windows of the trace exploration spec";

pub fn get_windows_expectation<S: AsRef<str>>(lines: &[S]) -> OnWindows {
    let mut printed = Vec::new();
    for line in lines {
        let line = line.as_ref();
        if let Some(file) = line.strip_prefix("Parsing file ") {
            if file.contains(" (file:") {
                return OnWindows::Declined(DECLINED_FILE_URL);
            }
            // A standard module's copy in the temporary directory, which TLC recorded with its
            // jar's URL, stays as it was: the tests name it by its file alone.
            if file.contains("/tlc-") {
                printed.push(line.to_owned());
            } else {
                printed.push(format!("Parsing file {}", file.replace('/', "\\")));
            }
        } else if line.contains("operator override from file:") {
            return OnWindows::Declined(DECLINED_CLASS_URL);
        } else if line.starts_with("Trace exploration spec path: ") {
            return OnWindows::Declined(DECLINED_TRACE_SPEC);
        } else {
            printed.push(line.to_owned());
        }
    }
    OnWindows::Printed(printed)
}

/// Asserts the binary declined, for the reason that starts as `reason` does.
pub fn assert_declined(output: &Output, reason: &str, label: &str) {
    let stderr = stderr(output);
    assert!(
        stderr.starts_with(&format!("prove-it: not native yet: {reason}")),
        "{label}: declined with {stderr:?}, not {reason:?}; printed {}",
        stdout(output)
    );
    assert_eq!(output.status.code(), Some(1), "{label}");
}

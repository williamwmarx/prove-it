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

/// The lines of a run whose text depends on the time, the machine or where TLC keeps its files.
const VARYING: &[&str] = &[
    "TLC2 Version",
    "Running ",
    "Parsing file",
    "Semantic processing",
    "Linting of module",
    "Starting...",
    "Computing initial states",
    "Finished computing initial states",
    "Finished in",
    "Picked up JAVA_TOOL_OPTIONS",
];

fn fixed(text: &str) -> String {
    text.lines()
        .filter(|line| !VARYING.iter().any(|prefix| line.starts_with(prefix)))
        .collect::<Vec<_>>()
        .join("\n")
        .trim_end()
        .to_owned()
}

/// Checks each case of `tests/<fixtures>`, a directory holding `M.tla` and `M.cfg` with what the
/// pinned jar printed on them (`tlc.txt`) and its exit code (`tlc.exit`), recorded with `args`:
/// the binary prints the same apart from the varying lines and exits the same, or, where
/// `declined.txt` holds what it says, declines so with exit 1.
pub fn check_recorded(fixtures: &str, count: usize, args: &[&str]) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join(fixtures);
    let mut cases: Vec<_> = std::fs::read_dir(&root)
        .expect("the fixtures")
        .map(|entry| entry.expect("an entry").path())
        .collect();
    cases.sort();
    assert_eq!(cases.len(), count);
    for fixture in cases {
        let name = fixture
            .file_name()
            .expect("a name")
            .to_string_lossy()
            .into_owned();
        let directory =
            std::env::temp_dir().join(format!("prove-it-{fixtures}-{name}-{}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("a fixture directory");
        for file in ["M.tla", "M.cfg"] {
            std::fs::copy(fixture.join(file), directory.join(file)).expect("a fixture file");
        }
        let output = run(&directory, &[args, &["-config", "M.cfg", "M.tla"]].concat());
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        if let Ok(declined) = std::fs::read_to_string(fixture.join("declined.txt")) {
            assert_eq!(output.status.code(), Some(1), "{name}");
            assert_eq!(stderr, declined, "{name}");
        } else {
            let reference = std::fs::read_to_string(fixture.join("tlc.txt"))
                .expect("the pinned Jar's complete output");
            let reference_exit: i32 = std::fs::read_to_string(fixture.join("tlc.exit"))
                .expect("the pinned Jar's exit code")
                .trim()
                .parse()
                .expect("an exit code");
            assert_eq!(output.status.code(), Some(reference_exit), "{name}");
            assert_eq!(
                fixed(&format!("{stdout}{stderr}")),
                fixed(&reference),
                "{name}"
            );
        }
        std::fs::remove_dir_all(directory).expect("removed fixtures");
    }
}

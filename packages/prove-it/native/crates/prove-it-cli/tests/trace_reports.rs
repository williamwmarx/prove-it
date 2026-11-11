//! What TLC reports as it prints a trace through the configuration's ALIAS, and of assumptions and
//! postconditions: each spec of `tests/trace_reports` with its configuration, and with the command
//! line's arguments in its `.args`, run through the binary as TLC's command line runs it. The
//! binary prints what TLC built at d8fb231 prints (`<spec>.out`, the exit code then the output
//! but the lines that hold times, versions, paths and seeds), or, where it doesn't follow TLC
//! yet, declines with the reason in `<spec>.declined`.

use std::path::Path;
use std::process::Command;

// The lines TLC prints with the time, its version, the machine, the paths or the seed.
const UNTIMED: [&str; 10] = [
    "TLC2 Version",
    "Running breadth-first search",
    "Starting...",
    "Finished in",
    "Parsing file",
    "Finished computing initial states",
    "Progress(",
    "Checking temporal properties",
    "Finished checking temporal properties",
    "Running Random Simulation",
];

#[test]
fn reports_as_tlc() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/trace_reports");
    let mut names: Vec<String> = std::fs::read_dir(&fixtures)
        .expect("the fixtures")
        .filter_map(|entry| {
            let path = entry.expect("an entry").path();
            (path.extension()? == "tla").then(|| path.file_stem()?.to_str().map(String::from))?
        })
        .collect();
    names.sort();
    assert!(!names.is_empty());
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-trace-reports-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let mut differences = Vec::new();
    for name in &names {
        for extension in ["tla", "cfg"] {
            std::fs::copy(
                fixtures.join(format!("{name}.{extension}")),
                directory.join(format!("{name}.{extension}")),
            )
            .expect("a copy");
        }
        let args =
            std::fs::read_to_string(fixtures.join(format!("{name}.args"))).unwrap_or_default();
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args([
                "-workers",
                "1",
                "-fp",
                "0",
                "-nowarning",
                "-noGenerateSpecTE",
            ])
            .args(args.split_whitespace())
            .arg(name)
            .current_dir(&directory)
            .output()
            .expect("the binary runs");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let (actual, expected) = match std::fs::read_to_string(fixtures.join(format!("{name}.out")))
        {
            Ok(expected) => (
                format!(
                    "exit {}\n{}",
                    output.status.code().unwrap_or(-1),
                    stdout
                        .lines()
                        .filter(|line| !UNTIMED.iter().any(|timed| line.contains(timed)))
                        .map(|line| format!("{line}\n"))
                        .collect::<String>()
                ),
                expected,
            ),
            Err(_) => (
                format!("exit {}\n{stderr}", output.status.code().unwrap_or(-1)),
                format!(
                    "exit 1\nprove-it: not native yet: {}",
                    std::fs::read_to_string(fixtures.join(format!("{name}.declined")))
                        .expect("TLC's output or the reason the binary declines")
                ),
            ),
        };
        if actual != expected {
            differences.push(format!("{name}: {stderr}\n{actual}"));
        }
    }
    std::fs::remove_dir_all(directory).expect("removed");
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

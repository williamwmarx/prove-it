//! TLCExt's operators that TLC evaluates as their TLA+ definitions or as Java methods, against TLC
//! built at d8fb231.

use std::path::Path;
use std::process::{Command, Stdio};

// What a run printed, without the lines whose text depends on the time, the machine or where TLC
// keeps the standard modules.
fn get_untimed_lines(text: &str) -> String {
    text.lines()
        .filter(|line| {
            ![
                "TLC2 Version",
                "Running breadth-first search",
                "Starting...",
                "Finished in",
                "Parsing file",
                "Progress(",
                "Finished computing initial states",
            ]
            .iter()
            .any(|timed| line.starts_with(timed))
        })
        .map(|line| format!("{line}\n"))
        .collect()
}

// Each spec of `tests/tlcext_builtins` prints what TLC built at d8fb231 prints for it
// (`<Name>.out`, with -fp 0 -workers 1 and the exit code first), on one thread and with every
// level shared between four, or, where `<Name>.declined` holds what the binary says, declines as
// it says.
#[test]
fn checks_tlcext_operators_as_tlc() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/tlcext_builtins");
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
        std::env::temp_dir().join(format!("prove-it-cli-tlcext-{}", std::process::id()));
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
        let declined = std::fs::read_to_string(fixtures.join(format!("{name}.declined"))).ok();
        let expected =
            std::fs::read_to_string(fixtures.join(format!("{name}.out"))).expect("TLC's output");
        for threads in ["1", "4"] {
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args(["-fp", "0", "-noGenerateSpecTE", "-workers", "1"])
                .args(["-config", &format!("{name}.cfg"), name])
                .current_dir(&directory)
                .env("PROVE_IT_WORKERS", threads)
                .env("PROVE_IT_SHARED_LEVEL", "1")
                .stdin(Stdio::null())
                .output()
                .expect("the binary runs");
            let stderr = String::from_utf8_lossy(&output.stderr);
            let actual = format!(
                "exit {}\n{}",
                output.status.code().unwrap_or(-1),
                get_untimed_lines(&String::from_utf8_lossy(&output.stdout))
            );
            let is_expected = match &declined {
                Some(declined) => output.status.code() == Some(1) && stderr == *declined,
                None => actual == expected,
            };
            if !is_expected {
                differences.push(format!("{name} on {threads}: {stderr}\n{actual}"));
            }
        }
    }
    std::fs::remove_dir_all(directory).expect("removed");
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

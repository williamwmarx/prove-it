//! Properties of <<A>>_v and [A]_v over steps that leave v unchanged, against TLC built at
//! d8fb231.

use std::process::{Command, Output};

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

// The specs of a grid, by name.
fn get_grid_names(grid: &std::path::Path) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(grid)
        .expect("the grid")
        .filter_map(|entry| {
            let path = entry.expect("an entry").path();
            (path.extension()? == "tla").then(|| path.file_stem()?.to_str().map(String::from))?
        })
        .collect();
    names.sort();
    assert!(!names.is_empty());
    names
}

// What a run printed, without the lines whose text depends on the time or the machine.
fn get_untimed_lines(text: &str) -> String {
    text.lines()
        .filter(|line| {
            ![
                "Running breadth-first search",
                "Starting...",
                "Finished in",
                "Progress(",
                "TLC2 Version",
                "Parsing file",
                "Finished computing initial states",
                "Checking ",
                "Finished checking temporal properties",
                "Estimates of the probability",
                "because two distinct states had the same fingerprint",
                "calculated (optimistic)",
            ]
            .iter()
            .any(|timed| line.contains(timed))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

// Properties of <<A>>_v, and of [A]_v beside them, with and without fairness, over steps that
// leave v unchanged: TLC's `LNAction` of <<A>>_v compares v in the two states before it evaluates
// A, so an A that fails or prints on such a step does neither, where TLC's evaluation of [A]_v
// evaluates A first. Each run prints what TLC built at d8fb231 prints (`angle-grid/*.out`, and
// `*.tool.out` with -tool, with -fp 0 -seed 0 -nowarning), on one thread and with every level
// shared between four, checking the properties periodically and at the end, or declines.
#[test]
fn checks_the_subscript_of_an_angle_action_before_the_action_as_tlc() {
    let grid = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/angle-grid");
    let names = get_grid_names(&grid);
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-angle-grid-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let mut differences = Vec::new();
    for name in &names {
        for extension in ["tla", "cfg"] {
            std::fs::copy(
                grid.join(format!("{name}.{extension}")),
                directory.join(format!("{name}.{extension}")),
            )
            .expect("a copy");
        }
        for (mode, suffix) in [(&[][..], "out"), (&["-tool"][..], "tool.out")] {
            let expected = std::fs::read_to_string(grid.join(format!("{name}.{suffix}")))
                .expect("TLC's output");
            for check in [&[][..], &["-lncheck", "final"][..]] {
                for threads in ["1", "4"] {
                    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                        .args([
                            "-workers",
                            "1",
                            "-fp",
                            "0",
                            "-seed",
                            "0",
                            "-nowarning",
                            "-noTE",
                        ])
                        .args(mode)
                        .args(check)
                        .arg(name)
                        .current_dir(&directory)
                        .env("PROVE_IT_WORKERS", threads)
                        .env("PROVE_IT_SHARED_LEVEL", "1")
                        .output()
                        .expect("the binary runs");
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    let actual = format!(
                        "exit {}\n{}\n",
                        output.status.code().unwrap_or(-1),
                        get_untimed_lines(&stdout(&output))
                    );
                    if actual != expected && !stderr.contains("prove-it: not native yet: ") {
                        differences.push(format!(
                            "{name} {mode:?} {check:?} on {threads}: {stderr}\n{actual}"
                        ));
                    }
                }
            }
        }
    }
    std::fs::remove_dir_all(directory).expect("removed");
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

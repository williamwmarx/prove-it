//! The errors TLC raises as it builds the liveness checker from the temporal properties, against
//! TLC built at d8fb231.

mod common;

use std::process::Command;

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

// Properties TLC finds a tautology, as `SpecProcessor.processConfigProps` does a property's \A
// over the empty set and `ModelChecker.modelCheckImpl` a formula whose negation has no solution,
// and properties with a constant part that isn't a boolean, which `Liveness.astToLive` names by a
// numeral's image or else by its location (`EC.TLC_EXPECTED_VALUE`), beside contradictions and
// constant parts that are booleans. Each run prints what TLC built at d8fb231 prints
// (`live-startup-grid/*.out`, and `*.tool.out` with -tool, with -fp 0 -seed 0 -nowarning), on one
// thread and with every level shared between four, checking the properties periodically and at
// the end, or declines.
#[test]
fn reports_the_temporal_properties_tlc_fails_to_start_on_as_tlc() {
    let grid = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/live-startup-grid");
    let names = get_grid_names(&grid);
    let directory = std::env::temp_dir().join(format!(
        "prove-it-cli-live-startup-grid-{}",
        std::process::id()
    ));
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
                    let stderr = common::stderr(&output);
                    let actual = format!(
                        "exit {}\n{}\n",
                        output.status.code().unwrap_or(-1),
                        get_untimed_lines(&common::stdout(&output))
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

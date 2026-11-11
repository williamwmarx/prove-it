//! Runs the binary on the cells `startup-texts.txt` records TLC's output for: models whose
//! constant definitions TLC computes as it starts, one a CHOOSE over every function of a set of
//! nodes that makes no string, as tlaplus/Examples' EWD998ChanID ranks its nodes, beside ones
//! that make strings TLC orders by when it made them. Each cell must print what TLC printed, byte
//! for byte, with TLC's exit code, at -workers 1 and 4.
//!
//! TLC's output is recorded by `scripts/record-startup-texts.ts` from TLC at the commit the
//! recordings pin; to check it, run that script with TLA2TOOLS_JAR set and diff the file.

use std::process::Command;

const RECORDED: &str = include_str!("startup-texts.txt");

// The lines that differ from run to run or between TLC and the binary, as the script drops them.
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

struct Cell<'r> {
    name: &'r str,
    spec: &'r str,
    config: &'r str,
    // By workers: TLC's exit code and output.
    expected: Vec<(u32, i32, &'r str)>,
}

fn parse(recorded: &str) -> Vec<Cell<'_>> {
    let mut cells = Vec::new();
    for block in recorded.split("### ").skip(1) {
        let (name, body) = block.split_once('\n').expect("a cell's name");
        if name == "end" {
            break;
        }
        // A spec's own lines start with ----, so a section starts after a line break.
        let body = body.strip_prefix("--- ").expect("a cell's sections");
        let mut sections = body.split("\n--- ");
        let spec = sections
            .next()
            .expect("a spec")
            .trim_start_matches("spec\n");
        let config = sections
            .next()
            .expect("a config")
            .trim_start_matches("config\n");
        let expected = sections
            .map(|section| {
                let (header, output) = section.split_once('\n').unwrap_or((section, ""));
                let words: Vec<&str> = header.split_whitespace().collect();
                let workers = words[1].parse().expect("a number of workers");
                let exit = words[3].parse().expect("an exit code");
                (workers, exit, output.trim_end())
            })
            .collect();
        cells.push(Cell {
            name,
            spec: spec.trim_end(),
            config: config.trim_end(),
            expected,
        });
    }
    cells
}

#[test]
fn startup_texts() {
    let cells = parse(RECORDED);
    assert_eq!(cells.len(), 2, "the recorded cells");
    for (index, cell) in cells.iter().enumerate() {
        let directory =
            std::env::temp_dir().join(format!("prove-it-startup-{}-{index}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("a directory");
        std::fs::write(directory.join("M.tla"), format!("{}\n", cell.spec)).expect("the spec");
        std::fs::write(directory.join("M.cfg"), format!("{}\n", cell.config)).expect("the config");
        for &(workers, exit, expected) in &cell.expected {
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args([
                    "-workers",
                    &workers.to_string(),
                    "-nowarning",
                    "-fp",
                    "0",
                    "-lncheck",
                    "final",
                    "-noGenerateSpecTE",
                    "-config",
                    "M.cfg",
                    "M.tla",
                ])
                .current_dir(&directory)
                .output()
                .expect("the binary runs");
            let printed = format!(
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            let printed = printed
                .lines()
                .filter(|line| !VARYING.iter().any(|prefix| line.starts_with(prefix)))
                .collect::<Vec<_>>()
                .join("\n");
            assert_eq!(
                printed.trim_end(),
                expected,
                "{} at {workers} workers",
                cell.name
            );
            assert_eq!(
                output.status.code(),
                Some(exit),
                "{} at {workers} workers",
                cell.name
            );
        }
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

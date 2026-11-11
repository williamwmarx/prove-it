//! Runs the binary on the cells `fingerprint-exceptions.txt` records TLC's output for: invariants
//! that fail on an initial state in a value's method, functions, applications and comparisons that
//! fail in the initial or next states, which TLC reports with the FingerprintException of its
//! replay, initial states that hold values TLC fails to fingerprint, temporal properties whose atoms
//! fail on the initial state, function definitions that fail as TLC builds them, memberships whose
//! comparison fails in a set nested in the one tested, and constant definitions TLC can't normalize
//! at startup. Each cell must print what TLC printed, byte for
//! byte, with TLC's exit code, at -workers 1 and 4, or be one the binary declines and that
//! `DECLINED` lists.
//!
//! TLC's output is recorded by `scripts/record-fingerprint-exceptions.ts` from TLC at the commit
//! the recordings pin; to check it, run that script with TLA2TOOLS_JAR set and diff the file.

use std::path::PathBuf;
use std::process::Command;

const RECORDED: &str = include_str!("fingerprint-exceptions.txt");

// The cells the binary declines, by name.
const DECLINED: &[&str] = &[
    // TLC compares a record with a function with the record's compareTo, but the engine's store,
    // which can't tell a record from a function over strings, stops there at a limit of its own.
    "S == {[i \\in 0..1 |-> 5]}: [a |-> x] \\notin S",
    // TLC's messages for the `equals` of a function, a tuple or a record with a value of another
    // kind, which the evaluator doesn't word yet.
    "({<<1>>} \\cup {2}) = {}",
    "2 \\in {<<1>>}",
    "Init == x = [a |-> 1]: x = {}",
    "Init == x = \"a\" :> 1: x = {}",
    "Init == x = \"a b\" :> 1: x = {}",
];

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
    spec: String,
    config: String,
    // By workers: TLC's exit code and output.
    expected: Vec<(u32, i32, String)>,
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
                (workers, exit, output.trim_end().to_owned())
            })
            .collect();
        cells.push(Cell {
            name,
            spec: spec.trim_end().to_owned(),
            config: config.trim_end().to_owned(),
            expected,
        });
    }
    cells
}

fn directory(index: usize, cell: &Cell) -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "prove-it-fingerprint-{}-{index}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("M.tla"), format!("{}\n", cell.spec)).expect("the spec");
    std::fs::write(directory.join("M.cfg"), format!("{}\n", cell.config)).expect("the config");
    directory
}

#[test]
fn fingerprint_exceptions() {
    let cells = parse(RECORDED);
    assert_eq!(cells.len(), 134, "the recorded cells");
    for (index, cell) in cells.iter().enumerate() {
        let directory = directory(index, cell);
        for (workers, exit, expected) in &cell.expected {
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
            let stderr = String::from_utf8_lossy(&output.stderr);
            if DECLINED.contains(&cell.name) {
                assert!(
                    stderr.contains("not native yet"),
                    "{} at {workers} workers, which DECLINED lists, ran natively",
                    cell.name
                );
                continue;
            }
            let printed = String::from_utf8_lossy(&output.stdout);
            let printed: Vec<&str> = printed
                .lines()
                .filter(|line| !VARYING.iter().any(|prefix| line.starts_with(prefix)))
                .collect();
            assert_eq!(
                (output.status.code(), printed.join("\n").trim_end()),
                (Some(*exit), expected.as_str()),
                "{} at {workers} workers: {stderr}",
                cell.name
            );
        }
        std::fs::remove_dir_all(&directory).expect("the directory removed");
    }
}

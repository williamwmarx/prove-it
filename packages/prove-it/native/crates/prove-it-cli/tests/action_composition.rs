//! Action splitting and evaluation order recorded from TLC at d8fb231.

use std::path::Path;
use std::process::Command;

fn fixed(text: &str) -> String {
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
        "Progress(",
    ];
    text.lines()
        .filter(|line| !VARYING.iter().any(|prefix| line.starts_with(prefix)))
        .collect::<Vec<_>>()
        .join("\n")
        .trim_end()
        .to_owned()
}

#[test]
fn keeps_composition_whole_and_rejects_it_before_evaluating_its_operands() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/action-composition");
    for entry in std::fs::read_dir(fixtures).unwrap() {
        let source = entry.unwrap().path();
        let name = source.file_name().unwrap().to_str().unwrap();
        let target = std::env::temp_dir().join(format!(
            "prove-it-action-composition-{name}-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&target).unwrap();
        for file in ["M.tla", "M.cfg"] {
            std::fs::copy(source.join(file), target.join(file)).unwrap();
        }
        for workers in ["1", "4"] {
            let expected: i32 = std::fs::read_to_string(source.join("exit"))
                .unwrap()
                .trim()
                .parse()
                .unwrap();
            let reference =
                std::fs::read_to_string(source.join(format!("tlc-{workers}.txt"))).unwrap();
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args([
                    "-workers",
                    workers,
                    "-fp",
                    "0",
                    "-seed",
                    "4",
                    "-lncheck",
                    "final",
                    "-noGenerateSpecTE",
                    "-config",
                    "M.cfg",
                    "M.tla",
                ])
                .current_dir(&target)
                .output()
                .unwrap();
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert_eq!(output.status.code(), Some(expected), "{name}, {workers}");
            assert!(stderr.is_empty(), "{name}, {workers}: {stderr}");
            assert_eq!(fixed(&stdout), reference.trim_end(), "{name}, {workers}");
            assert!(!stdout.contains("OPERAND"), "{name}, {workers}");
        }
        std::fs::remove_dir_all(target).unwrap();
    }
}

//! Full pinned-Jar witnesses for Any origin and configuration capability boundaries.

use std::path::Path;
use std::process::Command;

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

fn copy_tree(source: &Path, target: &Path) {
    std::fs::create_dir_all(target).unwrap();
    for entry in std::fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let target = target.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_tree(&entry.path(), &target);
        } else {
            std::fs::copy(entry.path(), target).unwrap();
        }
    }
}

#[test]
fn any_origin_and_scoped_binding_keep_the_old_graph_when_unproved() {
    for (name, decline) in [
        (
            "scoped-packaged",
            Some(
                "an operator of a module of the user's that TLC's Java class replaces: AnySet!ANY",
            ),
        ),
        (
            "indexed-scoped",
            Some(
                "an operator a TLCOverrides index's Java method replaces that the configuration names: AnySet!ANY",
            ),
        ),
        (
            "opaque-print",
            Some("a Java override class with a static initializer"),
        ),
        (
            "opaque-plain-print",
            Some(
                "an operator of a module of the user's that TLC's Java class replaces: AnySet!ANY",
            ),
        ),
        ("unused-literal", None),
    ] {
        let source = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/any-origin")
            .join(name);
        let target =
            std::env::temp_dir().join(format!("prove-it-any-origin-{name}-{}", std::process::id()));
        copy_tree(&source, &target);
        for workers in [1, 4] {
            let reference =
                std::fs::read_to_string(source.join(format!("tlc-{workers}.txt"))).unwrap();
            let expected: i32 = std::fs::read_to_string(source.join("exit"))
                .unwrap()
                .trim()
                .parse()
                .unwrap();
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args([
                    "-workers",
                    &workers.to_string(),
                    "-nowarning",
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
            if let Some(reason) = decline {
                assert!(!reference.trim().is_empty(), "the complete Jar witness");
                assert_eq!(output.status.code(), Some(1), "{name}, {workers}");
                assert_eq!(stderr, format!("prove-it: not native yet: {reason}\n"));
                assert_eq!(fixed(&stdout), "", "no first-graph startup effects");
            } else {
                assert_eq!(output.status.code(), Some(expected), "{name}, {workers}");
                assert_eq!(fixed(&format!("{stdout}{stderr}")), reference.trim_end());
            }
            assert!(!stdout.contains("SHOULD_NOT_RUN"));
        }
        std::fs::remove_dir_all(target).unwrap();
    }
}

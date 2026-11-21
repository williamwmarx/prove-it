//! TLC d8fb231's AnySet lifecycle, with full pinned-Jar startup output.
//! The fixtures retain TLC's complete output after startup.rs's varying-line filter.

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

#[test]
fn any_membership_and_value_consumers() {
    for name in [
        "membership",
        "print",
        "finite",
        "empty-domain",
        "duplicate-finite",
        "value",
        "empty",
        "equality",
        "not-enumerable",
        "function-domain",
        "duplicate-next",
        "fingerprint-tuple",
        "permutations",
        "random-element",
    ] {
        let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/any-set");
        let directory =
            std::env::temp_dir().join(format!("prove-it-any-{name}-{}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("a fixture directory");
        for extension in ["tla", "cfg"] {
            std::fs::copy(
                fixtures.join(format!("{name}.{extension}")),
                directory.join(format!("M.{extension}")),
            )
            .expect("a fixture");
        }
        for workers in [1, 4] {
            let reference =
                std::fs::read_to_string(fixtures.join(format!("{name}.tlc-{workers}.txt")))
                    .expect("the pinned Jar's full output");
            let reference_exit: i32 =
                std::fs::read_to_string(fixtures.join(format!("{name}.exit")))
                    .expect("the pinned Jar's exit code")
                    .trim()
                    .parse()
                    .expect("an exit code");
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
                .current_dir(&directory)
                .output()
                .expect("the binary runs");
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert_eq!(
                output.status.code(),
                Some(reference_exit),
                "{name}, {workers}"
            );
            assert_eq!(
                fixed(&format!("{stdout}{stderr}")),
                reference.trim_end(),
                "{name}, {workers}"
            );
        }
        std::fs::remove_dir_all(directory).expect("removed fixtures");
    }
}

//! A real external class precedes packaged tlc2.module.TLC (TLAClass.loadClass).
//! Full outputs were recorded with TLC d8fb231 and JDK 21.0.13+9.

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
fn any_requires_the_packaged_class_but_an_unused_any_does_not_decline() {
    for name in ["with-any", "without-any", "unused"] {
        let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/any-class")
            .join(name);
        let directory =
            std::env::temp_dir().join(format!("prove-it-any-class-{name}-{}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("a fixture directory");
        for file in ["M.tla", "M.cfg", "TLC.class"] {
            std::fs::copy(fixture.join(file), directory.join(file)).expect("a fixture file");
        }
        for workers in [1, 4] {
            let reference = std::fs::read_to_string(fixture.join(format!("tlc-{workers}.txt")))
                .expect("the pinned Jar's complete output");
            let reference_exit: i32 = std::fs::read_to_string(fixture.join("tlc.exit"))
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
            if name == "unused" {
                assert_eq!(output.status.code(), Some(reference_exit));
                assert_eq!(fixed(&format!("{stdout}{stderr}")), reference.trim_end());
            } else {
                assert_eq!(reference_exit, 75);
                assert!(!reference.trim().is_empty(), "the Jar's full diagnostic");
                assert_eq!(output.status.code(), Some(1), "{name}, {workers}");
                assert_eq!(
                    stderr,
                    if name == "with-any" {
                        "prove-it: not native yet: the reports of a user class overriding a standard module\n"
                    } else {
                        "prove-it: not native yet: the engine declined: unsupported: Any\n"
                    }
                );
                assert_eq!(fixed(&stdout), "", "{name}, {workers}");
            }
        }
        std::fs::remove_dir_all(directory).expect("removed fixtures");
    }
}

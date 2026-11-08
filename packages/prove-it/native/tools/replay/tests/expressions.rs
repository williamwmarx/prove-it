//! The fixtures of tests/conformance/expressions, which `scripts/native-expressions.ts --record`
//! writes with the TypeScript engine's compiler: `replay expressions` must compile every root
//! and give every state the value, or the reason to stop, the TypeScript side gave it, with the
//! caches on, off (PROVE_IT_MEMO=off), and with each epoch cache hit checked
//! (PROVE_IT_EPOCH_CHECK=1).

use std::path::{Path, PathBuf};
use std::process::Command;

fn fixtures() -> Vec<PathBuf> {
    let directory =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../tests/conformance/expressions");
    let mut found: Vec<PathBuf> = std::fs::read_dir(directory)
        .expect("the fixture directory")
        .map(|entry| entry.expect("an entry").path())
        .filter(|path| path.is_dir())
        .collect();
    found.sort();
    found
}

fn evaluate(fixture: &Path, setting: Option<(&str, &str)>) -> String {
    let mut command = Command::new(env!("CARGO_BIN_EXE_replay"));
    command
        .arg("expressions")
        .arg(fixture.join("model.ir"))
        .arg(fixture.join("states.jsonl"))
        .env_remove("PROVE_IT_MEMO")
        .env_remove("PROVE_IT_EPOCH_CHECK");
    if let Some((name, value)) = setting {
        command.env(name, value);
    }
    let output = command.output().expect("replay runs");
    assert!(
        output.status.success(),
        "{}: {}",
        fixture.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("UTF-8 lines")
}

fn check(setting: Option<(&str, &str)>) {
    let fixtures = fixtures();
    assert!(fixtures.len() >= 5, "the fixtures are missing");
    for fixture in fixtures {
        let expected = std::fs::read_to_string(fixture.join("expected.txt")).expect("expected.txt");
        let actual = evaluate(&fixture, setting);
        for (index, (expected, actual)) in expected.lines().zip(actual.lines()).enumerate() {
            assert_eq!(
                actual,
                expected,
                "{} line {} with {setting:?}",
                fixture.display(),
                index + 1
            );
        }
        assert_eq!(
            actual.lines().count(),
            expected.lines().count(),
            "{} with {setting:?}",
            fixture.display()
        );
    }
}

#[test]
fn evaluates_as_the_typescript_compiler() {
    check(None);
}

#[test]
fn evaluates_alike_without_caches() {
    check(Some(("PROVE_IT_MEMO", "off")));
}

#[test]
fn every_epoch_cache_hit_holds() {
    check(Some(("PROVE_IT_EPOCH_CHECK", "1")));
}

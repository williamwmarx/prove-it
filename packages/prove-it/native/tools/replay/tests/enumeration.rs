//! The cases of tests/conformance/enumeration, which `scripts/enumeration-oracle.ts --record`
//! froze with TLC's answers: `replay enumerate` must list each set's elements in the order TLC
//! does, where a quantifier binds them and where x' \in S assigns them, and fail where TLC fails.

use std::path::Path;
use std::process::Command;

#[test]
fn enumerates_lazy_sets_as_tlc_does() {
    let directory =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../tests/conformance/enumeration");
    let output = Command::new(env!("CARGO_BIN_EXE_replay"))
        .arg("enumerate")
        .arg(directory.join("requests.txt"))
        .output()
        .expect("replay runs");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).expect("UTF-8 lines");
    let answers: Vec<&str> = stdout
        .lines()
        .skip(1)
        .enumerate()
        .filter(|(index, _)| index % 3 != 0)
        .map(|(_, line)| line)
        .collect();
    let expected = std::fs::read_to_string(directory.join("answers.txt")).expect("TLC's answers");
    let expected: Vec<&str> = expected.lines().collect();
    assert_eq!(answers.len(), expected.len());
    assert!(expected.len() >= 400, "the frozen cases");
    for (index, (answer, tlc)) in answers.iter().zip(&expected).enumerate() {
        let is_same = answer == tlc || (answer.starts_with('!') && tlc.starts_with('!'));
        assert!(is_same, "case {}: TLC {tlc}, native {answer}", index / 2);
    }
}

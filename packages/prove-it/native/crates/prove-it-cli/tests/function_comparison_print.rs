//! TLC d8fb231 deep-normalizes a lazy difference's operands before PrintT enumerates it.
use std::process::Command;

#[test]
fn prints_function_and_record_difference_comparison_failures() {
    let cases = [
        (
            "[{1} -> {2, 3}]",
            "Attempted to compare the function <<2>> with the value:\n1",
        ),
        (
            "[a : {1, 2}]",
            "Attempted to compare record:\n[a |-> 1]\nwith non-record\n1",
        ),
    ];
    for (index, (left, expected)) in cases.iter().enumerate() {
        let dir = std::env::temp_dir().join(format!(
            "function-comparison-print-{}-{index}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("M.tla"), format!("---- MODULE M ----\nEXTENDS Integers, FiniteSets, TLC\nASSUME PrintT({left} \\ {{1}})\n====\n")).unwrap();
        std::fs::write(dir.join("M.cfg"), "").unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args([
                "-workers",
                "1",
                "-noGenerateSpecTE",
                "-config",
                "M.cfg",
                "M.tla",
            ])
            .current_dir(&dir)
            .output()
            .unwrap();
        std::fs::remove_dir_all(dir).unwrap();
        assert_eq!(output.status.code(), Some(10));
        assert!(
            output.stderr.is_empty(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            String::from_utf8_lossy(&output.stdout).contains(expected),
            "{}",
            String::from_utf8_lossy(&output.stdout)
        );
    }
}

#[test]
fn preserves_existing_record_tuple_comparison_failure() {
    let dir =
        std::env::temp_dir().join(format!("function-comparison-union-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("M.tla"), "---- MODULE M ----\nEXTENDS Integers, FiniteSets, Sequences, TLC\nVARIABLE x\nASSUME PrintT(Cardinality(UNION {{<<1, 2>>}, [a : {1}, b : {1}]})) \\/ TRUE\nInit == x = 0\nNext == x' = x\n====\n").unwrap();
    std::fs::write(dir.join("M.cfg"), "INIT Init\nNEXT Next\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args([
            "-workers",
            "1",
            "-noGenerateSpecTE",
            "-config",
            "M.cfg",
            "M.tla",
        ])
        .current_dir(&dir)
        .output()
        .unwrap();
    std::fs::remove_dir_all(dir).unwrap();
    assert_eq!(output.status.code(), Some(10));
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains(
            "Attempted to compare record:\n[a |-> 1, b |-> 1]\nwith non-record\n<<1, 2>>"
        )
    );
}

#[test]
fn streams_a_lazy_union_into_subset_as_tlc() {
    // TLC prints FALSE: `isSubsetEq` streams the union's elements and stops at the first `{}`
    // lacks, before any comparison of a record with an integer.
    let dir =
        std::env::temp_dir().join(format!("function-comparison-subset-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("M.tla"), "---- MODULE M ----\nEXTENDS Integers, FiniteSets, Sequences, TLC\nVARIABLE x\nASSUME PrintT((([a : {1}, b : {1}] \\cup {1}) \\subseteq {})) \\/ TRUE\nInit == x = 0\nNext == x' = x\n====\n").unwrap();
    std::fs::write(dir.join("M.cfg"), "INIT Init\nNEXT Next\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args([
            "-workers",
            "1",
            "-noGenerateSpecTE",
            "-config",
            "M.cfg",
            "M.tla",
        ])
        .current_dir(&dir)
        .output()
        .unwrap();
    std::fs::remove_dir_all(dir).unwrap();
    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty(), "{:?}", output.stderr);
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("\nFALSE\n"),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
}

#[test]
fn cached_difference_keeps_the_shared_rhs_usable_after_print() {
    // TLC d8fb231 prints the empty set and completes. R and D are operator arguments, so both
    // references to R and both references to D use the same argument values.
    let dir =
        std::env::temp_dir().join(format!("function-comparison-cache-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("M.tla"), "---- MODULE M ----\nEXTENDS Integers, Sequences, FiniteSets, TLC\nG(R, D) == Cardinality(D) >= 0 /\\ PrintT(D) /\\ (1 \\in R)\nF(R) == LET S == [{1} -> {}] IN G(R, S \\ R)\nASSUME F({1})\n====\n").unwrap();
    std::fs::write(dir.join("M.cfg"), "").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args([
            "-workers",
            "1",
            "-noGenerateSpecTE",
            "-config",
            "M.cfg",
            "M.tla",
        ])
        .current_dir(&dir)
        .output()
        .unwrap();
    std::fs::remove_dir_all(dir).unwrap();
    assert_eq!(output.status.code(), Some(0));
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .any(|line| line == "{}")
    );
}

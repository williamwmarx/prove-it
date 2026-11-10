//! Runs the binary on values TLC keeps lazy: what Print, PrintT and ToString print of a value as
//! TLC built it, and a UNION of sets TLC streams without normalizing.

use std::path::PathBuf;
use std::process::{Command, Output};

fn run(directory: &PathBuf, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(args)
        .current_dir(directory)
        .output()
        .expect("the binary runs")
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

#[test]
fn prints_a_value_as_tlc_built_it_where_the_spec_writes_it() {
    // TLC prints an interval, a SUBSET and a set of functions as written, a record's fields in
    // the order written unless it has normalized the record, as PrintT does, and a function over
    // strings that aren't field names with :>, which the store forgets and the expression says.
    // The texts are those TLC prints for this spec.
    let lines = [
        ("PrintT(1..3)", "1..3"),
        ("PrintT({2})", "{2}"),
        ("PrintT({1..2})", "{1..2}"),
        ("PrintT(<<3..2, {}>>)", "<<{}, {}>>"),
        ("PrintT([z \\in {\"a b\"} |-> 1])", "(\"a b\" :> 1)"),
        ("PrintT([yy |-> 1, zz |-> 2])", "[yy |-> 1, zz |-> 2]"),
        (
            "PrintT(ToString([zz |-> 1, yy |-> 2]))",
            "\"[zz |-> 1, yy |-> 2]\"",
        ),
        (
            "PrintT(ToString({<<1, [yy |-> 1, zz |-> 2]>>}))",
            "\"{<<1, [yy |-> 1, zz |-> 2]>>}\"",
        ),
        (
            "PrintT(ToString([i \\in {\"p q\", \"r\"} |-> i]))",
            "\"(\\\"p q\\\" :> \\\"p q\\\" @@ \\\"r\\\" :> \\\"r\\\")\"",
        ),
        ("PrintT(ToString(SUBSET (1..7)))", "\"SUBSET (1..7)\""),
        (
            "PrintT(ToString(SUBSET {1..2, 3..3}))",
            "\"{{}, {3..3}, {1..2}, {3..3, 1..2}}\"",
        ),
        (
            "PrintT(ToString(SUBSET {\"a\", \"b\", \"c\", \"d\", \"e\", \"f\", \"g\"}))",
            "\"SUBSET {\\\"d\\\", \\\"e\\\", \\\"f\\\", \\\"g\\\", \\\"a\\\", \\\"b\\\", \\\"c\\\"}\"",
        ),
        ("PrintT(ToString([{} -> {1}]))", "\"{<<>>}\""),
        (
            "PrintT(ToString([{\"a\", \"b\"} -> 1..2]))",
            "\"{[a |-> 1, b |-> 1], [a |-> 1, b |-> 2], [a |-> 2, b |-> 1], [a |-> 2, b |-> 2]}\"",
        ),
        ("PrintT(ToString([1..3 -> 1..17]))", "\"[1..3 -> 1..17]\""),
        ("PrintT([2..12 -> 0..1])", "[2..12 -> 0..1]"),
        (
            "PrintT(ToString([i \\in 0..1 |-> {i}]))",
            "\"(0 :> {0} @@ 1 :> {1})\"",
        ),
        ("Print(<<1..2, {1..2}>>, TRUE)", "<<1..2, {1..2}>>  TRUE"),
    ];
    let next = lines
        .iter()
        .map(|(print, _)| format!("  /\\ {print}\n"))
        .collect::<String>();
    let spec = format!(
        "---- MODULE Constructed ----\nEXTENDS TLC, Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 1\n{next}  /\\ x' = x + 1\n====\n"
    );
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-constructed-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("Constructed.tla"), spec).expect("the spec");
    std::fs::write(
        directory.join("Constructed.cfg"),
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
    )
    .expect("the configuration");
    let output = run(&directory, &["-noGenerateSpecTE", "Constructed"]);
    let text = stdout(&output);
    assert_eq!(
        output.status.code(),
        Some(0),
        "{text}{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let printed = lines
        .iter()
        .map(|(_, text)| format!("{text}\n"))
        .collect::<String>();
    assert!(text.contains(&printed), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn streams_a_union_of_sets_tlc_keeps_lazy_as_tlc_does() {
    // TLC sorts a set enumeration as it first enumerates it, which caches each element after the
    // first as its normalized set (`ValueVec.sort`), and UNION streams the first as built,
    // duplicates and all. The counts are TLC's for these models.
    let models = [
        (
            "y = 0",
            "y' \\in UNION {UNION {0..2, {1}}, {7}}",
            "21 states generated, 4 distinct states found",
        ),
        (
            "y = 0",
            "\\E e \\in UNION {UNION {0..2, {1}}, {7}} : y' = e",
            "17 states generated, 4 distinct states found",
        ),
        (
            "y = 0",
            "y' \\in {1} \\X UNION {UNION {0..2, {1}}, {1, 2}}",
            "25 states generated, 4 distinct states found",
        ),
        (
            "y \\in UNION {UNION (SUBSET {{1}, {1, 2}}), {1}}",
            "UNCHANGED y",
            "8 states generated, 3 distinct states found",
        ),
        (
            "y \\in UNION {{1}, UNION (SUBSET {{1}, {1, 2}})}",
            "UNCHANGED y",
            "6 states generated, 3 distinct states found",
        ),
        (
            "y \\in UNION {(SUBSET {1}) \\cup SUBSET {2}}",
            "UNCHANGED y",
            "7 states generated, 3 distinct states found",
        ),
        (
            "y \\in UNION UNION (SUBSET {{}, {{}}})",
            "UNCHANGED y",
            "3 states generated, 1 distinct states found",
        ),
    ];
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-unions-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(
        directory.join("Unions.cfg"),
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
    )
    .expect("the configuration");
    for (init, next, counts) in models {
        let spec = format!(
            "---- MODULE Unions ----\nEXTENDS Naturals\nVARIABLE y\nInit == {init}\nNext == {next}\n====\n"
        );
        std::fs::write(directory.join("Unions.tla"), spec).expect("the spec");
        let output = run(&directory, &["-noGenerateSpecTE", "Unions"]);
        let text = stdout(&output);
        assert_eq!(
            output.status.code(),
            Some(0),
            "{next}: {text}{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(text.contains(counts), "{next}: {text}");
    }
    // TLC keeps an operator's argument for its later uses, and Cardinality sorted it here, so it
    // streams as its normalized set (17 states generated), which the engine leaves.
    let spec = "---- MODULE Unions ----\nEXTENDS Naturals, FiniteSets\nVARIABLE y\nOp(u) == Cardinality(u) > 0 /\\ y' \\in u\nInit == y = 0\nNext == Op(UNION {UNION {0..2, {1}}, {7}})\n====\n";
    std::fs::write(directory.join("Unions.tla"), spec).expect("the spec");
    let output = run(&directory, &["-noGenerateSpecTE", "Unions"]);
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "prove-it: not native yet: the engine stopped: unsupported: streaming a set enumeration TLC may have sorted at an earlier use\n",
        "{}",
        stdout(&output)
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

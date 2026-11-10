//! The binary's Bags operators against TLC built at d8fb231.

use std::path::PathBuf;
use std::process::{Command, Output};

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

// Writes the spec and its configuration to a directory of their own and checks them with TLC's
// command line, without the trace exploration spec TLC would parse.
fn run_spec(test: &str, spec: &str, config: &str) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-bags-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let name = spec
        .split_whitespace()
        .nth(2)
        .expect("the module's name")
        .to_string();
    std::fs::write(directory.join(format!("{name}.tla")), spec).expect("the spec");
    std::fs::write(directory.join(format!("{name}.cfg")), config).expect("the configuration");
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-noTE", &name])
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    (output, directory)
}

// The Bags module's Java overrides (`tlc2.module.Bags`) and SubBag's TLA+ definition, as
// tests/unit/bags.test.ts has TLC fail them, and as TLC at d8fb231 fails them where a comparison,
// a cast or a lazy function fails inside a method, which TLC reports as the method's failure.
// (+) requires both arguments be bags, so a count of 0 fails it.
#[test]
fn reports_failures_of_the_bags_operators_as_tlc() {
    let java = |method: &str, error: &str| {
        let arguments = if method.contains("BagUnion")
            || method.contains("SetToBag")
            || method.contains("BagToSet")
            || method.contains("IsABag")
            || method.contains("BagCardinality")
        {
            "tlc2.value.impl.Value"
        } else {
            "tlc2.value.impl.Value,tlc2.value.impl.Value"
        };
        format!(
            "Attempted to apply the operator overridden by the Java method\npublic static {method}({arguments}),\nbut it produced the following error:\n{error}"
        )
    };
    let class_cast = |class: &str| {
        format!(
            "class tlc2.value.impl.{class} cannot be cast to class tlc2.value.impl.IntValue (tlc2.value.impl.{class} and tlc2.value.impl.IntValue are in unnamed module of loader 'app')"
        )
    };
    let cast = |method: &str| java(method, &class_cast("StringValue"));
    let string_with_integer = "Attempted to check equality of string \"a\" with non-string:\n1";
    let lazy_nat = "Attempted to compute the number of elements in the overridden value Nat.";
    const BAG_CUP: &str = "tlc2.value.impl.Value tlc2.module.Bags.BagCup";
    const BAG_DIFF: &str = "tlc2.value.impl.Value tlc2.module.Bags.BagDiff";
    const SQ_SUBSETEQ: &str = "tlc2.value.IBoolValue tlc2.module.Bags.SqSubseteq";
    const BAG_UNION: &str = "tlc2.value.impl.Value tlc2.module.Bags.BagUnion";
    let operator = |literal: &str| {
        format!(
            "The first argument of BagOfAll should be an operator, but instead it is:\n{literal}"
        )
    };
    for (index, (extends, assumption, message)) in [
        (
            "Integers",
            "BagCardinality(<<0>>)",
            "Applying BagCardinality to the following value,\nwhich is not a bag:\n<<0>>".to_string(),
        ),
        (
            "Integers",
            "<<0>> (+) EmptyBag",
            "The first argument of (+) should be a bag, but instead it is:\n<<0>>".to_string(),
        ),
        (
            "Integers",
            "EmptyBag (-) 1",
            "The second argument of (-) should be a bag, but instead it is:\n1".to_string(),
        ),
        (
            "Integers",
            "BagIn(1, <<\"a\">>)",
            "The second argument of BagIn should be a bag, but instead it is:\n<<\"a\">>".to_string(),
        ),
        (
            "Integers",
            "CopiesIn(1, <<\"a\">>)",
            "The second argument of CopiesIn should be a bag, but instead it is:\n<<\"a\">>"
                .to_string(),
        ),
        (
            "Integers",
            "BagUnion({1, 2})",
            "Attempted to apply BagUnion to the following set, whose\nelement is not a bag:\n{1, 2}"
                .to_string(),
        ),
        (
            "Integers",
            "BagUnion(Nat)",
            "Applying BagUnion to the following value,\nwhich is not a finite enumerable set:\nNat"
                .to_string(),
        ),
        (
            "Integers",
            "SetToBag(Nat)",
            "Applying BagToSet to the following value,\nwhich is not a function with a finite domain:\nNat"
                .to_string(),
        ),
        (
            "Integers",
            "BagToSet(1)",
            "Applying BagToSet to the following value,\nwhich is not a function with a finite domain:\n1"
                .to_string(),
        ),
        (
            "Integers",
            "1 \\sqsubseteq EmptyBag",
            "Applying \\sqsubseteq to the following value,\nwhich is not a function with a finite domain:\n1"
                .to_string(),
        ),
        (
            "Integers",
            "BagOfAll(LAMBDA n : n, 1)",
            "The second argument of BagOfAll should be a function with a finite domain, but instead it is:\n1"
                .to_string(),
        ),
        (
            "Integers",
            "<<2147483647>> (+) <<1>>",
            "Overflow when computing 2147483647+1".to_string(),
        ),
        (
            "Integers",
            "BagUnion({<<2147483647>>, <<1>>})",
            "Overflow when computing 1+2147483647".to_string(),
        ),
        (
            "Integers",
            "<<\"a\">> (-) EmptyBag",
            cast("tlc2.value.impl.Value tlc2.module.Bags.BagDiff"),
        ),
        (
            "Integers",
            "<<\"a\">> \\sqsubseteq EmptyBag",
            cast("tlc2.value.IBoolValue tlc2.module.Bags.SqSubseteq"),
        ),
        (
            "Integers",
            "BagOfAll(LAMBDA e : TRUE, <<\"a\", 1>>)",
            cast("tlc2.value.impl.Value tlc2.module.Bags.BagOfAll"),
        ),
        (
            "Integers",
            "BagOfAll(LAMBDA e : \"c\", <<1>>)",
            operator("\"c\""),
        ),
        (
            "Integers",
            "LET H(e) == 1 IN BagOfAll(H, <<1>>)",
            operator("1"),
        ),
        (
            "Integers",
            "LET H(e) == \"c\"\n    G(Op(_)) == BagOfAll(Op, <<1>>)\nIN G(H)",
            operator("\"c\""),
        ),
        // SubBag compares the counts with the >= of Naturals, which names itself >, and which
        // Integers replaces.
        (
            "Integers",
            "SubBag(<<\"a\">>) /\\ 1 >= 0",
            "The first argument of >= should be an integer, but instead it is:\n\"a\"".to_string(),
        ),
        (
            "Naturals",
            "SubBag(<<\"a\">>) /\\ 1 >= 0",
            "The first argument of > should be an integer, but instead it is:\n\"a\"".to_string(),
        ),
        // A count that isn't positive leaves the bag outside the domain of Bags.tla's RSB,
        // which TLC prints as a function of RSB's domain.
        (
            "Integers",
            "SubBag(<<0>>)",
            "In applying the function\n(<<>> :> {<<>>}),\nthe first argument is:\n<<0>>\nwhich is not in its domain.\n".to_string(),
        ),
        (
            "Integers",
            "SubBag(<<2, 0>>)",
            "In applying the function\n( <<>> :> {<<>>} @@\n  <<1>> :> {<<>>, <<1>>, <<2>>} @@\n  <<2>> :> {<<>>, <<1>>, <<2>>} @@\n  (2 :> 1) :> {<<>>} @@\n  (2 :> 2) :> {<<>>} @@\n  <<1, 1>> :> {<<>>, <<1>>, <<2>>} @@\n  <<1, 2>> :> {<<>>, <<1>>, <<2>>} @@\n  <<2, 1>> :> {<<>>, <<1>>, <<2>>} @@\n  <<2, 2>> :> {<<>>, <<1>>, <<2>>} ),\nthe first argument is:\n<<2, 0>>\nwhich is not in its domain.\n".to_string(),
        ),
        // Comparisons that fail inside a method.
        (
            "Integers",
            "<<1, 2>> (+) [a |-> 3]",
            java(BAG_CUP, string_with_integer),
        ),
        (
            "Integers",
            "<<1, 2>> (-) [a |-> 3]",
            java(
                BAG_DIFF,
                "Attempted to check equality of integer 1 with non-integer:\n\"a\"",
            ),
        ),
        (
            "Integers",
            "<<1, 2>> \\sqsubseteq [a |-> 3]",
            java(
                SQ_SUBSETEQ,
                "Attempted to check equality of integer 1 with non-integer:\n\"a\"",
            ),
        ),
        (
            "Integers",
            "CopiesIn(\"a\", <<1>>)",
            java(
                "tlc2.value.impl.IntValue tlc2.module.Bags.CopiesIn",
                string_with_integer,
            ),
        ),
        (
            "Integers",
            "BagIn(\"a\", <<1>>)",
            java(
                "tlc2.value.IBoolValue tlc2.module.Bags.BagIn",
                string_with_integer,
            ),
        ),
        (
            "Integers",
            "BagUnion({<<1>>, [a |-> 1]})",
            java(
                BAG_UNION,
                "Attempted to compare record:\n[a |-> 1]\nwith non-record\n<<1>>",
            ),
        ),
        (
            "Integers",
            "SetToBag({1, \"a\"})",
            java(
                "tlc2.value.impl.Value tlc2.module.Bags.SetToBag",
                "Attempted to compare string \"a\" with non-string:\n1",
            ),
        ),
        (
            "Integers",
            "BagOfAll(LAMBDA e : IF e = 1 THEN 1 ELSE \"a\", <<1, 1>>)",
            java(
                "tlc2.value.impl.Value tlc2.module.Bags.BagOfAll",
                string_with_integer,
            ),
        ),
        // A function TLC keeps lazy over Nat, which the method converts.
        (
            "Integers",
            "IsABag([n \\in Nat |-> 1])",
            java("tlc2.value.IBoolValue tlc2.module.Bags.IsABag", lazy_nat),
        ),
        (
            "Integers",
            "BagCardinality([n \\in Nat |-> 1])",
            java(
                "tlc2.value.impl.IntValue tlc2.module.Bags.BagCardinality",
                lazy_nat,
            ),
        ),
        (
            "Integers",
            "BagToSet([n \\in Nat |-> 1])",
            java("tlc2.value.impl.Value tlc2.module.Bags.BagToSet", lazy_nat),
        ),
        (
            "Integers",
            "<<1>> (+) [n \\in Nat |-> 1]",
            java(BAG_CUP, lazy_nat),
        ),
        // The class of a count that isn't an integer.
        (
            "Integers",
            "<<{1}>> (-) EmptyBag",
            java(BAG_DIFF, &class_cast("SetEnumValue")),
        ),
        (
            "Integers",
            "<<SUBSET {1}>> (-) EmptyBag",
            java(BAG_DIFF, &class_cast("SubsetValue")),
        ),
        (
            "Integers",
            "<<{1}>> \\sqsubseteq EmptyBag",
            java(SQ_SUBSETEQ, &class_cast("SetEnumValue")),
        ),
        (
            "Integers",
            "BagUnion({<<{1}>>, <<{2}>>})",
            java(BAG_UNION, &class_cast("SetEnumValue")),
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let spec = format!(
            "---- MODULE Bagged ----\nEXTENDS {extends}, FiniteSets, TLC, Bags\nCONSTANT C\nVARIABLE x\nInit == x = 0\nNext == x' = x\nASSUME PrintT({assumption})\n====\n"
        );
        let (output, directory) = run_spec(
            &format!("{index}"),
            &spec,
            "CONSTANT C = C\nINIT Init\nNEXT Next\n",
        );
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(10), "{assumption}: {text}");
        assert!(
            text.contains(&format!(" of module Bagged failed.\n{message}\n")),
            "{assumption}: {text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

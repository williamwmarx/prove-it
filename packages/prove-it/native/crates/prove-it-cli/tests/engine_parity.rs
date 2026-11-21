//! The binary against TLC built at d8fb231 where the engine once printed what TLC doesn't: SortSeq's
//! order and failures, a tuple pattern bound to a function TLC doesn't hold as a tuple, and a
//! non-function the walk applies.

use std::process::{Command, Output};

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

// TLC's output but the lines that name its version, the machine and where its jar unpacks the
// standard modules, with each date and duration masked and without the rates of progress.
fn get_untimed_text(text: &str) -> String {
    let mut result = String::new();
    for line in text.lines() {
        if ["TLC2 Version", "Running ", "Parsing file "]
            .iter()
            .any(|prefix| line.starts_with(prefix))
        {
            continue;
        }
        let line = match line.strip_prefix("Finished in ") {
            Some(rest) => format!(
                "Finished in <time>{}",
                &rest[rest.find(' ').unwrap_or(rest.len())..]
            ),
            None => line.to_owned(),
        };
        result.push_str(&mask_dates(&drop_rates(&line)));
        result.push('\n');
    }
    result
}

// A progress report without the rates it computes from the time, as ` (12 s/min)`.
fn drop_rates(line: &str) -> String {
    let mut line = line.to_owned();
    while let Some(end) = line.find("s/min)") {
        let start = line[..end].rfind(" (").expect("a rate's parenthesis");
        line.replace_range(start..end + "s/min)".len(), "");
    }
    line
}

// The text with each `yyyy-mm-dd hh:mm:ss` as `<date>`.
fn mask_dates(line: &str) -> String {
    let shape = b"0000-00-00 00:00:00";
    let bytes = line.as_bytes();
    let mut result = String::new();
    let mut at = 0;
    while at < bytes.len() {
        let is_date = bytes.len() - at >= shape.len()
            && shape.iter().zip(&bytes[at..]).all(|(shape, byte)| {
                if *shape == b'0' {
                    byte.is_ascii_digit()
                } else {
                    byte == shape
                }
            });
        if is_date {
            result.push_str("<date>");
            at += shape.len();
        } else {
            let character = line[at..].chars().next().expect("a character");
            result.push(character);
            at += character.len_utf8();
        }
    }
    result
}

// Checks M, its definitions after its variable x, on one thread and on four, plainly and with
// -tool, giving each run's flags and output.
fn check_on_threads(test: &str, definitions: &str, config: &str) -> Vec<(String, Output)> {
    check_on_threads_with(test, definitions, config, &[])
}

// As `check_on_threads`, with more options of TLC's command line.
fn check_on_threads_with(
    test: &str,
    definitions: &str,
    config: &str,
    options: &[&str],
) -> Vec<(String, Output)> {
    let directory =
        std::env::temp_dir().join(format!("prove-it-parity-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(
        directory.join("M.tla"),
        format!(
            "---- MODULE M ----\nEXTENDS TLC, Sequences, Naturals, FiniteSets, Bags\nVARIABLE x\nNext == UNCHANGED x\n{definitions}\n====\n"
        ),
    )
    .expect("a spec");
    std::fs::write(directory.join("M.cfg"), config).expect("a configuration");
    let mut outputs = Vec::new();
    for threads in ["1", "4"] {
        for flags in [&[][..], &["-tool"][..]] {
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .arg("-noGenerateSpecTE")
                .args(options)
                .args(flags)
                .arg("M")
                .current_dir(&directory)
                .env("PROVE_IT_WORKERS", threads)
                .env("PROVE_IT_SHARED_LEVEL", "1")
                .output()
                .expect("the binary runs");
            outputs.push((format!("{threads} {flags:?}"), output));
        }
    }
    std::fs::remove_dir_all(directory).expect("removed");
    outputs
}

#[test]
fn sorts_as_tlcs_sort_seq() {
    // TLC's SortSeq moves each element back past those sorted before it while the comparison
    // holds, so it keeps an order the comparison isn't, and never compares 5 with 1 here. What it
    // prints is what TLC at d8fb231 prints, and with -tool.
    for (definitions, printed) in [
        (
            "Init == PrintT(SortSeq(<<1, 2, 1>>, LAMBDA u, v : u = v)) /\\ x = 0",
            "<<1, 2, 1>>",
        ),
        (
            "Init == PrintT(SortSeq(<<3, 1, 2, 5, 4>>, LAMBDA u, v : IF <<u, v>> = <<5, 1>> THEN 0 ELSE u < v)) /\\ x = 0",
            "<<1, 2, 3, 4, 5>>",
        ),
    ] {
        for (run, output) in check_on_threads("sort-seq", definitions, "INIT Init\nNEXT Next\n") {
            let text = stdout(&output);
            let expected = if run.ends_with("[]") {
                format!(
                    "Computing initial states...\n{printed}\nFinished computing initial states: 1 distinct state generated at "
                )
            } else {
                format!(
                    "Computing initial states...\n@!@!@ENDMSG 2189 @!@!@\n{printed}\n@!@!@STARTMSG 2190:0 @!@!@\nFinished computing initial states: 1 distinct state generated at "
                )
            };
            assert!(text.contains(&expected), "{definitions} on {run}:\n{text}");
            assert!(
                text.contains("Model checking completed. No error has been found.\n"),
                "{definitions} on {run}:\n{text}"
            );
        }
    }
}

#[test]
fn stops_where_tlcs_sort_seq_fails() {
    // TLC's SortSeq fails on a comparison that isn't a boolean, which the engine stops at and the
    // replay prints as TLC at d8fb231 does, and with -tool; and on an operator whose body is a
    // literal, which TLC passes as the literal and the replay declines.
    for (definitions, is_printed, printed, tool) in [
        (
            "Init == x = SortSeq(<<1, 2>>, LAMBDA u, v : u + 7)",
            true,
            "Error: The second argument of SortSeq should be a boolean function, but instead it is:\n9\nError: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 5, column 9 to line 5, column 50 in M\n1. Line 5, column 13 to line 5, column 50 in M\n\n\n",
            "@!@!@STARTMSG 1000:1 @!@!@\n@!@!@STARTMSG 2169:0 @!@!@\nThe second argument of SortSeq should be a boolean function, but instead it is:\n9\n@!@!@ENDMSG 2169 @!@!@\n@!@!@ENDMSG 1000 @!@!@\n@!@!@STARTMSG 2103:1 @!@!@\nThe error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 5, column 9 to line 5, column 50 in M\n1. Line 5, column 13 to line 5, column 50 in M\n\n\n@!@!@ENDMSG 2103 @!@!@\n",
        ),
        (
            "Init == x = SortSeq(<<2, 1>>, LAMBDA u, v : \"a\")",
            false,
            "Error: The second argument of SortSeq should be a operator, but instead it is:\n\"a\"\nError: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 5, column 9 to line 5, column 48 in M\n1. Line 5, column 13 to line 5, column 48 in M\n\n\n",
            "@!@!@STARTMSG 1000:1 @!@!@\n@!@!@STARTMSG 2169:0 @!@!@\nThe second argument of SortSeq should be a operator, but instead it is:\n\"a\"\n@!@!@ENDMSG 2169 @!@!@\n@!@!@ENDMSG 1000 @!@!@\n@!@!@STARTMSG 2103:1 @!@!@\nThe error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 5, column 9 to line 5, column 48 in M\n1. Line 5, column 13 to line 5, column 48 in M\n\n\n@!@!@ENDMSG 2103 @!@!@\n",
        ),
    ] {
        for (run, output) in
            check_on_threads("sort-seq-fails", definitions, "INIT Init\nNEXT Next\n")
        {
            let text = stdout(&output);
            let expected = if run.ends_with("[]") { printed } else { tool };
            assert!(
                text.contains(expected)
                    || !is_printed
                        && String::from_utf8_lossy(&output.stderr).contains("not native yet"),
                "{definitions} on {run}:\n{text}"
            );
            assert!(
                !text.contains("No error has been found"),
                "{definitions} on {run}:\n{text}"
            );
        }
    }
}

#[test]
fn reports_or_declines_a_tuple_pattern_over_a_tuple_tlc_built_as_a_function() {
    // TLC binds a tuple of names in `\E`, `\A`, a set of all, a set filter and a function's
    // construction only to a `TupleValue` (`ContextEnumerator`, `Tool.evalImpl`), which a function
    // over 1..n it built otherwise isn't, while CHOOSE and Append take one as a tuple (`toTuple`).
    // Where TLC at d8fb231 fails, the replay prints what it prints, plainly and with -tool, or
    // declines; where it binds the tuple, the check prints what it prints.
    // `tests/tuple-pattern/<name>.out` and `<name>.tool.out` hold TLC's exit code and output at
    // `-fp 0 -noGenerateSpecTE`, run as `java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC`, as
    // `get_untimed_text` has it.
    let config = "INIT Init\nNEXT Next\n";
    let action = "INIT Init\nNEXT Next2\n";
    let invariant = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let failing: [(&str, &str, &str); 14] = [
        (
            "exists",
            "Init == x = 0 /\\ \\E <<a, b>> \\in {[k \\in 1..2 |-> k]} : a = 1",
            config,
        ),
        (
            "forall",
            "Init == x = (\\A <<a, b>> \\in {[k \\in {1, 2} |-> k]} : a = 1)",
            config,
        ),
        (
            "set-of-all",
            "Init == x = {a + b : <<a, b>> \\in {[k \\in 1..2 |-> k]}}",
            config,
        ),
        (
            "filter",
            "Init == x = {<<a, b>> \\in {[k \\in 1..2 |-> k]} : a = 1}",
            config,
        ),
        (
            "function",
            "Init == x = [<<a, b>> \\in {[k \\in 1..2 |-> k]} |-> a]",
            config,
        ),
        (
            "action",
            "Init == x = [k \\in 1..2 |-> k]\nNext2 == \\E <<a, b>> \\in {x} : x' = x",
            action,
        ),
        (
            "invariant",
            "Init == x = [k \\in 1..2 |-> k]\nInv == \\E <<a, b>> \\in {x} : a = 1",
            invariant,
        ),
        (
            "except",
            "Init == x = (\\E <<a, b>> \\in {[[k \\in 1..2 |-> k] EXCEPT ![1] = 3]} : a = 3)",
            config,
        ),
        (
            "single",
            "Init == x = (\\E <<a>> \\in {1 :> 7} : a = 7)",
            config,
        ),
        (
            "at-at",
            "Init == x = (\\E <<a, b>> \\in {[k \\in 1..2 |-> k] @@ <<>>} : a = 1)",
            config,
        ),
        (
            "function-set",
            "Init == x = (\\E <<a, b>> \\in [1..2 -> {7}] : a = 7)",
            config,
        ),
        (
            "permutations",
            "Init == x = (\\E <<a, b>> \\in Permutations({1, 2}) : a = 1)",
            config,
        ),
        (
            "bag",
            "Init == x = (\\E <<a, b>> \\in {SetToBag({1, 2})} : a = 1)",
            config,
        ),
        // A thread builds the function that another binds, where it is a tuple the store held
        // already.
        (
            "threads",
            "VARIABLE y, z\nInit == x \\in 1..400 /\\ y = {} /\\ z = <<1, 2>>\nNext2 == \\/ y = {} /\\ y' = (IF x = 337 THEN {[k \\in 1..2 |-> k]} ELSE {<<x, x>>}) /\\ UNCHANGED <<x, z>>\n         \\/ y # {} /\\ (\\A <<a, b>> \\in y : a <= b) /\\ UNCHANGED <<x, y, z>>",
            action,
        ),
    ];
    let bound = [
        (
            "tuple",
            "Init == x = (\\E <<a, b>> \\in {<<1, 2>>} : a = 1)",
        ),
        (
            "except-tuple",
            "Init == x = (\\E <<a, b>> \\in {[<<1, 2>> EXCEPT ![1] = 3]} : a = 3)",
        ),
        (
            "choose",
            "Init == x = CHOOSE <<a, b>> \\in {[k \\in 1..2 |-> k]} : a = 1",
        ),
        (
            "append",
            "Init == x = (\\E <<a, b>> \\in {Append([k \\in 1..1 |-> k], 2)} : a = 1)",
        ),
    ];
    let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/tuple-pattern");
    let runs = failing
        .into_iter()
        .map(|(name, definitions, config)| (name, definitions, config, true))
        .chain(
            bound
                .into_iter()
                .map(|(name, definitions)| (name, definitions, config, false)),
        );
    for (name, definitions, config, may_decline) in runs {
        for (run, output) in
            check_on_threads_with("tuple-pattern", definitions, config, &["-fp", "0"])
        {
            let file = if run.ends_with("[]") {
                format!("{name}.out")
            } else {
                format!("{name}.tool.out")
            };
            let expected = std::fs::read_to_string(fixtures.join(&file)).expect("TLC's output");
            let actual = format!(
                "exit {}\n{}",
                output.status.code().unwrap_or(-1),
                get_untimed_text(&stdout(&output))
            );
            if actual == expected {
                continue;
            }
            assert!(
                may_decline
                    && output.stdout.is_empty()
                    && output.status.code() == Some(1)
                    && String::from_utf8_lossy(&output.stderr).contains(
                        "not native yet: the engine stopped: unsupported: a tuple pattern bound to a tuple TLC may hold as a function"
                    ),
                "{name} on {run}:\n{actual}\nTLC printed:\n{expected}"
            );
        }
    }
}

#[test]
fn words_a_non_function_the_walk_applies_as_tlc() {
    // A non-function the walk of the initial predicate, an action or ENABLED applies, which
    // `getInitStates`, `getNextStates` and `enabled` each word apart (`OPCODE_fa`), and one
    // applied inside an argument, which `Tool#eval` words. Each text is what TLC at d8fb231
    // prints, and with -tool.
    // Its name, definitions, configuration, and what TLC prints, and with -tool.
    type Case<'a> = (&'a str, &'a str, &'a str, &'a str, &'a str);
    let cases: [Case; 4] = [
        (
            "a non-function the initial predicate applies",
            "Init == 1[1] /\\ x = 0\nNext == x' = x",
            "INIT Init\nNEXT Next\n",
            "Error: In computing initial states, a non-function (an integer) was applied as a function.\nline 4, col 9 to line 4, col 12 of module M\nError: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 4, column 9 to line 4, column 21 in M\n1. Line 4, column 9 to line 4, column 12 in M\n\n\n",
            "@!@!@STARTMSG 1000:1 @!@!@\nIn computing initial states, a non-function (an integer) was applied as a function.\nline 4, col 9 to line 4, col 12 of module M\n@!@!@ENDMSG 1000 @!@!@\n@!@!@STARTMSG 2103:1 @!@!@\nThe error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 4, column 9 to line 4, column 21 in M\n1. Line 4, column 9 to line 4, column 12 in M\n\n\n@!@!@ENDMSG 2103 @!@!@\n",
        ),
        (
            "a non-function an action applies",
            "Init == x = 0\nNext == 1[1] /\\ UNCHANGED x",
            "INIT Init\nNEXT Next\n",
            "Error: TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: In computing next states, a non-function (an integer) was applied as a function.\nline 5, col 9 to line 5, col 12 of module M\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nError: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 5, column 9 to line 5, column 27 in M\n1. Line 5, column 9 to line 5, column 12 in M\n\n\n",
            "@!@!@STARTMSG 1000:1 @!@!@\nTLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: In computing next states, a non-function (an integer) was applied as a function.\nline 5, col 9 to line 5, col 12 of module M\n@!@!@ENDMSG 1000 @!@!@\n@!@!@STARTMSG 2121:1 @!@!@\nThe behavior up to this point is:\n@!@!@ENDMSG 2121 @!@!@\n@!@!@STARTMSG 2217:4 @!@!@\n1: <Initial predicate>\nx = 0\n\n@!@!@ENDMSG 2217 @!@!@\n@!@!@STARTMSG 2103:1 @!@!@\nThe error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 5, column 9 to line 5, column 27 in M\n1. Line 5, column 9 to line 5, column 12 in M\n\n\n@!@!@ENDMSG 2103 @!@!@\n",
        ),
        (
            "a non-function ENABLED applies",
            "Init == x = 0\nA == x' = x /\\ 1[1]\nSpec == Init /\\ [][x' = x]_x /\\ WF_x(A)\nP == <>(x = 0)",
            "SPECIFICATION Spec\nPROPERTY P\n",
            "Error: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 6, column 38 to line 6, column 38 in M\n1. Line 5, column 6 to line 5, column 19 in M\n2. Line 5, column 6 to line 5, column 11 in M\n3. Line 5, column 16 to line 5, column 19 in M\n\n\nError: TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: In computing ENABLED, a non-function (an integer) was applied as a function.\nline 5, col 16 to line 5, col 19 of module M\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\n",
            "@!@!@STARTMSG 2103:1 @!@!@\nThe error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 6, column 38 to line 6, column 38 in M\n1. Line 5, column 6 to line 5, column 19 in M\n2. Line 5, column 6 to line 5, column 11 in M\n3. Line 5, column 16 to line 5, column 19 in M\n\n\n@!@!@ENDMSG 2103 @!@!@\n@!@!@STARTMSG 1000:1 @!@!@\nTLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: In computing ENABLED, a non-function (an integer) was applied as a function.\nline 5, col 16 to line 5, col 19 of module M\n@!@!@ENDMSG 1000 @!@!@\n@!@!@STARTMSG 2121:1 @!@!@\nThe behavior up to this point is:\n@!@!@ENDMSG 2121 @!@!@\n@!@!@STARTMSG 2217:4 @!@!@\n1: <Initial predicate>\nx = 0\n\n@!@!@ENDMSG 2217 @!@!@\n",
        ),
        (
            "a non-function applied inside an argument",
            "f == <<1>>\nInit == x = 0\nNext == f[2[1]] /\\ UNCHANGED x",
            "INIT Init\nNEXT Next\n",
            "Error: TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: A non-function (an integer) was applied as a function.\nline 6, col 11 to line 6, col 14 of module M\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nError: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 6, column 9 to line 6, column 30 in M\n1. Line 6, column 9 to line 6, column 15 in M\n2. Line 6, column 11 to line 6, column 14 in M\n\n\n",
            "@!@!@STARTMSG 1000:1 @!@!@\nTLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: A non-function (an integer) was applied as a function.\nline 6, col 11 to line 6, col 14 of module M\n@!@!@ENDMSG 1000 @!@!@\n@!@!@STARTMSG 2121:1 @!@!@\nThe behavior up to this point is:\n@!@!@ENDMSG 2121 @!@!@\n@!@!@STARTMSG 2217:4 @!@!@\n1: <Initial predicate>\nx = 0\n\n@!@!@ENDMSG 2217 @!@!@\n@!@!@STARTMSG 2103:1 @!@!@\nThe error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 6, column 9 to line 6, column 30 in M\n1. Line 6, column 9 to line 6, column 15 in M\n2. Line 6, column 11 to line 6, column 14 in M\n\n\n@!@!@ENDMSG 2103 @!@!@\n",
        ),
    ];
    let directory = std::env::temp_dir().join(format!(
        "prove-it-parity-non-function-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (name, definitions, config, printed, tool) in cases {
        std::fs::write(
            directory.join("M.tla"),
            format!("---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\n{definitions}\n====\n"),
        )
        .expect("a spec");
        std::fs::write(directory.join("M.cfg"), config).expect("a configuration");
        for threads in ["1", "4"] {
            for (flags, expected) in [(&[][..], printed), (&["-tool"][..], tool)] {
                let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                    .arg("-noGenerateSpecTE")
                    .args(flags)
                    .arg("M")
                    .current_dir(&directory)
                    .env("PROVE_IT_WORKERS", threads)
                    .env("PROVE_IT_SHARED_LEVEL", "1")
                    .output()
                    .expect("the binary runs");
                let text = stdout(&output);
                assert!(
                    text.contains(expected),
                    "{name} on {threads} {flags:?}:\n{text}"
                );
            }
        }
    }
    std::fs::remove_dir_all(directory).expect("removed");
}

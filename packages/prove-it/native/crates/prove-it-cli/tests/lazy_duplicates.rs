//! The states a set TLC keeps lazy generates where it streams duplicates, against TLC built at
//! d8fb231: a source set, eager or lazy, reaches `x \in` through a route that holds it as built or
//! normalizes it first, in the initial predicate and in the next-state relation. Each cell prints
//! what TLC prints (`lazy-grid/*.out`, its output with the lines that hold times, paths and
//! versions left out), or declines where the file says so, on one thread and with every level
//! shared between four.

use std::path::Path;
use std::process::Command;

// Each source set, with a set of its elements' kind that `\cup` adds to it.
const SOURCES: [(&str, &str, &str); 10] = [
    ("unionEager", "UNION {{1, 2}, {2, 3}}", "{9}"),
    ("unionLazy", "UNION {1..2, 2..3}", "{9}"),
    ("unionSub", "UNION (SUBSET {{1}, {1, 2}})", "{{9}}"),
    ("cupEager", "{1, 2} \\cup {2, 3}", "{9}"),
    ("cupSub", "(SUBSET {1}) \\cup SUBSET {2}", "{{9}}"),
    ("setof", "{v % 2 : v \\in 0..3}", "{9}"),
    ("pred", "{v \\in UNION {1..2, 2..3} : TRUE}", "{9}"),
    ("unionNest", "UNION {UNION {0..2, {1}}, {7}}", "{9}"),
    (
        "capLazy",
        "(UNION {1..2, 2..3}) \\cap (UNION {2..3, 3..4})",
        "{9}",
    ),
    ("ctrl", "SUBSET {1, 2}", "{{9}}"),
];

// The configuration of a cell with no invariant.
const PLAIN: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";

const ROUTES: [&str; 14] = [
    "inline", "opOnce", "opAfter", "opEval", "letOnce", "letAfter", "letEval", "varCup",
    "varPlain", "ex1", "ex2", "ex2r", "const", "constVar",
];

// The spec of a cell: `x` assigned from the source through the route, in Init or in Next.
fn get_spec(source: &str, extra: &str, route: &str, is_next: bool) -> String {
    let primed = |name: &str| {
        if is_next {
            format!("{name}'")
        } else {
            name.to_string()
        }
    };
    let (x, s) = (primed("x"), primed("s"));
    let mut definitions = Vec::new();
    let mut variables = vec!["x"];
    let body = match route {
        "inline" => format!("{x} \\in {source}"),
        "opOnce" => {
            definitions.push(format!("Op(u) == {x} \\in u"));
            format!("Op({source})")
        }
        "opAfter" => {
            definitions.push(format!("Op(u) == Cardinality(u) > 0 /\\ {x} \\in u"));
            format!("Op({source})")
        }
        "opEval" => {
            definitions.push("F(u) == IF Cardinality(u) > 0 THEN u ELSE {}".to_string());
            format!("{x} \\in F({source})")
        }
        "letOnce" => format!("LET u == {source} IN {x} \\in u"),
        "letAfter" => format!("LET u == {source} IN Cardinality(u) > 0 /\\ {x} \\in u"),
        "letEval" => {
            format!("{x} \\in (LET u == {source} IN IF Cardinality(u) > 0 THEN u ELSE {{}})")
        }
        "varCup" | "varPlain" => {
            variables = vec!["s", "x"];
            let tail = if route == "varCup" {
                format!(" \\cup {extra}")
            } else {
                String::new()
            };
            format!("{s} = {source} /\\ {x} \\in {s}{tail}")
        }
        "ex1" => format!("\\E t \\in {{{source}}} : {x} \\in t"),
        "ex2" => format!("\\E t \\in {{{source}, {{42}}}} : {x} \\in t"),
        "ex2r" => format!("\\E t \\in {{{{42}}, {source}}} : {x} \\in t"),
        "const" => {
            definitions.push(format!("C == {source}"));
            format!("{x} \\in C")
        }
        "constVar" => {
            variables = vec!["s", "x"];
            definitions.push(format!("C == {source}"));
            format!("{s} = C /\\ {x} \\in {s}")
        }
        _ => panic!("the route {route}"),
    };
    let listed = variables.join(", ");
    let (init, next) = if is_next {
        let zeros: Vec<String> = variables
            .iter()
            .map(|variable| format!("{variable} = 0"))
            .collect();
        (zeros.join(" /\\ "), body)
    } else {
        (body, format!("UNCHANGED <<{listed}>>"))
    };
    let mut lines = vec![
        "---- MODULE M ----".to_string(),
        "EXTENDS Naturals, FiniteSets".to_string(),
        format!("VARIABLES {listed}"),
    ];
    lines.extend(definitions);
    lines.extend([
        format!("Init == {init}"),
        format!("Next == {next}"),
        "====".to_string(),
    ]);
    lines.join("\n") + "\n"
}

// The output with the lines that hold times, paths and versions left out, as `lazy-grid/*.out`
// records TLC's.
fn get_untimed(text: &str) -> String {
    const DROPPED: [&str; 6] = [
        "Picked up JAVA_TOOL_OPTIONS",
        "TLC2 Version",
        "Running breadth-first",
        "Parsing file",
        "Starting...",
        "Finished in",
    ];
    text.lines()
        .filter(|line| !DROPPED.iter().any(|dropped| line.starts_with(dropped)))
        .map(|line| {
            if line.starts_with("Finished computing initial states:") {
                line.rsplit_once(" at ").map_or(line, |(kept, _)| kept)
            } else {
                line
            }
        })
        .map(|line| format!("{line}\n"))
        .collect()
}

// Checks each spec, named by its cell, on one thread and with every level shared between four:
// what differs from `lazy-grid/<cell>.out`, TLC's output or "not native yet" for a decline.
fn get_differences(test: &str, configuration: &str, cells: &[(String, String)]) -> Vec<String> {
    let grid = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/lazy-grid");
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("M.cfg"), configuration).expect("a configuration");
    let mut differences = Vec::new();
    for (cell, spec) in cells {
        std::fs::write(directory.join("M.tla"), spec).expect("a spec");
        let expected =
            std::fs::read_to_string(grid.join(format!("{cell}.out"))).expect("TLC's output");
        let is_declined = expected == "not native yet\n";
        for threads in ["1", "4"] {
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args(["-noGenerateSpecTE", "M"])
                .current_dir(&directory)
                .env("PROVE_IT_WORKERS", threads)
                .env("PROVE_IT_SHARED_LEVEL", "1")
                .output()
                .expect("the binary runs");
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            let is_as_expected = if is_declined {
                stderr.contains("prove-it: not native yet: ")
                    && !stdout.contains("states generated")
            } else {
                get_untimed(&stdout) == expected
            };
            if !is_as_expected {
                differences.push(format!("{cell} on {threads}:\n{stdout}{stderr}"));
            }
        }
    }
    std::fs::remove_dir_all(directory).expect("removed");
    differences
}

#[test]
fn generates_the_states_tlc_generates_from_a_lazy_set_or_declines() {
    let mut cells = Vec::new();
    for (name, source, extra) in SOURCES {
        for route in ROUTES {
            for (context, is_next) in [("init", false), ("next", true)] {
                cells.push((
                    format!("{name}.{route}.{context}"),
                    get_spec(source, extra, route, is_next),
                ));
            }
        }
    }
    let differences = get_differences("lazy-grid", PLAIN, &cells);
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

// A variable assigned a UNION that streams 2 twice, sized before it is streamed: Cardinality
// caches the set as its normalized set, in the branches after it too, whether or not the guard
// holds, so TLC streams 2 once (`sized.*.out`). Streamed before it is sized, it streams 2 twice,
// which the binary declines.
#[test]
fn streams_a_variable_sized_before_as_its_normalized_set() {
    let cases = [
        (
            "cardfirst",
            "Init == s = 0 /\\ x = 0\nNext == s' = UNION {1..2, 2..3} /\\ Cardinality(s') > 0 /\\ x' \\in s'",
        ),
        (
            "cardfirstInit",
            "Init == s = UNION {1..2, 2..3} /\\ Cardinality(s) > 0 /\\ x \\in s\nNext == UNCHANGED <<s, x>>",
        ),
        (
            "cardBranch",
            "Init == s = 0 /\\ x = 0\nNext == s' = UNION {1..2, 2..3} /\\ ((Cardinality(s') > 9 /\\ x' = 0) \\/ x' \\in s')",
        ),
        (
            "cardAfter",
            "Init == s = 0 /\\ x = 0\nNext == s' = UNION {1..2, 2..3} /\\ x' \\in s' /\\ Cardinality(s') > 0",
        ),
    ];
    let cells: Vec<(String, String)> = cases
        .into_iter()
        .map(|(name, body)| {
            (
                format!("sized.{name}"),
                format!(
                    "---- MODULE M ----\nEXTENDS Naturals, FiniteSets\nVARIABLES s, x\n{body}\n====\n"
                ),
            )
        })
        .collect();
    let differences = get_differences("lazy-sized", PLAIN, &cells);
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

// The sources, and three sets TLC streams out of their normalized order without duplicates, each
// with the elements an invariant excludes, which TLC reaches at another state where it streams
// the set as built than where it streams it normalized.
const KEPT_SOURCES: [(&str, &str, &str, &str); 13] = [
    ("unionEager", "UNION {{1, 2}, {2, 3}}", "{9}", "{3}"),
    ("unionLazy", "UNION {1..2, 2..3}", "{9}", "{3}"),
    (
        "unionSub",
        "UNION (SUBSET {{1}, {1, 2}})",
        "{{9}}",
        "{{1, 2}}",
    ),
    ("cupEager", "{1, 2} \\cup {2, 3}", "{9}", "{3}"),
    ("cupSub", "(SUBSET {1}) \\cup SUBSET {2}", "{{9}}", "{{2}}"),
    ("setof", "{v % 2 : v \\in 0..3}", "{9}", "{1}"),
    ("pred", "{v \\in UNION {1..2, 2..3} : TRUE}", "{9}", "{3}"),
    ("unionNest", "UNION {UNION {0..2, {1}}, {7}}", "{9}", "{7}"),
    (
        "capLazy",
        "(UNION {1..2, 2..3}) \\cap (UNION {2..3, 3..4})",
        "{9}",
        "{3}",
    ),
    ("ctrl", "SUBSET {1, 2}", "{{9}}", "{{1, 2}}"),
    (
        "cupOrder",
        "(SUBSET {2}) \\cup {{1}}",
        "{{9}}",
        "{{1}, {2}}",
    ),
    ("unionOrder", "UNION {{3}, 1..2}", "{9}", "{3}"),
    (
        "predOrder",
        "{v \\in UNION {{3}, 1..2} : TRUE}",
        "{9}",
        "{3}",
    ),
];

// Routes that stream the source where TLC may have normalized the object it streams, in Init and
// in Next, and where a constant definition is normalized in Init and streamed in Next.
const KEPT_ROUTES: [&str; 7] = [
    "inline", "varPlain", "constVar", "ex1", "letEval", "opAfter", "const",
];
const CONSTANT_ROUTES: [&str; 6] = [
    "constHeld",
    "constSized",
    "constEqual",
    "constCup",
    "constFirst",
    "constBound",
];

// The spec of a cell of `KEPT_ROUTES`: `x` assigned from the source through the route, with an
// invariant that excludes `probes`.
fn get_kept_spec(source: &str, extra: &str, probes: &str, route: &str, is_next: bool) -> String {
    let (x, s) = if is_next { ("x'", "s'") } else { ("x", "s") };
    let start = &extra[1..extra.len() - 1];
    let mut definitions = Vec::new();
    let body = match route {
        "inline" => format!("{s} = 0 /\\ {x} \\in {source}"),
        "varPlain" => format!("{s} = {source} /\\ {x} \\in {s}"),
        "constVar" => {
            definitions.push(format!("C == {source}"));
            format!("{s} = C /\\ {x} \\in {s}")
        }
        "ex1" => format!("{s} = 0 /\\ \\E t \\in {{{source}}} : {x} \\in t"),
        "letEval" => format!(
            "{s} = 0 /\\ {x} \\in (LET u == {source} IN IF Cardinality(u) > 0 THEN u ELSE {{}})"
        ),
        "opAfter" => {
            definitions.push(format!("Op(u) == Cardinality(u) > 0 /\\ {x} \\in u"));
            format!("{s} = 0 /\\ Op({source})")
        }
        "const" => {
            definitions.push(format!("C == {source}"));
            format!("{s} = 0 /\\ {x} \\in C")
        }
        _ => panic!("the route {route}"),
    };
    let (init, next) = if is_next {
        (format!("s = 0 /\\ x = {start}"), body)
    } else {
        (body, "UNCHANGED <<s, x>>".to_string())
    };
    get_module(&definitions, &init, &next, probes)
}

// The spec of a cell of `CONSTANT_ROUTES`: a constant definition of the source, which Init
// assigns, sizes or compares, or streams before it assigns it, or only quantifies over, which
// leaves it as built, and Next streams.
fn get_constant_spec(source: &str, extra: &str, probes: &str, route: &str) -> String {
    let start = &extra[1..extra.len() - 1];
    let (init, next) = match route {
        "constHeld" => (
            format!("s = C /\\ x = {start}"),
            "s' = s /\\ x' \\in C".to_string(),
        ),
        "constSized" => (
            format!("s = 0 /\\ x = {start} /\\ Cardinality(C) > 0"),
            "s' = s /\\ x' \\in C".to_string(),
        ),
        "constEqual" => (
            format!("s = 0 /\\ x = {start} /\\ C # {{}}"),
            "s' = s /\\ x' \\in C".to_string(),
        ),
        "constCup" => (
            format!("s = C /\\ x = {start}"),
            format!("s' = s /\\ x' \\in C \\cup {extra}"),
        ),
        "constFirst" => (
            "s = C /\\ x \\in C".to_string(),
            "UNCHANGED <<s, x>>".to_string(),
        ),
        "constBound" => (
            format!("s = 0 /\\ x = {start} /\\ \\E e \\in C : \\A f \\in C : e = e"),
            "s' = s /\\ x' \\in C".to_string(),
        ),
        _ => panic!("the route {route}"),
    };
    get_module(&[format!("C == {source}")], &init, &next, probes)
}

fn get_module(definitions: &[String], init: &str, next: &str, probes: &str) -> String {
    let mut lines = vec![
        "---- MODULE M ----".to_string(),
        "EXTENDS Naturals, FiniteSets".to_string(),
        "VARIABLES s, x".to_string(),
    ];
    lines.extend_from_slice(definitions);
    lines.extend([
        format!("Init == {init}"),
        format!("Next == {next}"),
        format!("Inv == x \\notin {probes}"),
        "====".to_string(),
    ]);
    lines.join("\n") + "\n"
}

// A set TLC keeps lazy streams as built until a use caches it as its normalized set, after which
// it streams that set: an element once, and in order. Where TLC may have cached the object it
// streams, an argument or LET named again, a variable or a bound name, or a constant definition
// the spec names elsewhere, each cell prints what TLC prints, at the violation of an invariant
// the order decides too, or declines.
#[test]
fn streams_a_set_tlc_may_have_normalized_as_tlc_does_or_declines() {
    let mut cells = Vec::new();
    for (name, source, extra, probes) in KEPT_SOURCES {
        for route in KEPT_ROUTES {
            for (context, is_next) in [("init", false), ("next", true)] {
                cells.push((
                    format!("kept.{name}.{route}.{context}"),
                    get_kept_spec(source, extra, probes, route, is_next),
                ));
            }
        }
        for route in CONSTANT_ROUTES {
            cells.push((
                format!("kept.{name}.{route}"),
                get_constant_spec(source, extra, probes, route),
            ));
        }
    }
    let differences = get_differences(
        "lazy-kept",
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
        &cells,
    );
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

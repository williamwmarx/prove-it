//! `-dump dot`: the state graph the binary writes, pinned to TLC's at d8fb231.

mod common;

use common::{read_dump, run_spec_with, stderr, stdout};

// A spec whose graph TLC wrote with `-dump dot` at d8fb231, with `-workers 1` and `-fp 0`: B's
// steps are those of its parameter's values, each an action of its own.
const DOT_SPEC: &str = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLES x, b\nInit == x = 0 /\\ b \\in BOOLEAN\nA == b /\\ b' = FALSE /\\ x' = x\nB(n) == ~b /\\ b' = TRUE /\\ x' = (x + n) % 3\nNext == A \\/ \\E n \\in {1, 2}: B(n)\nInv == x < 2\n====\n";

#[test]
fn dumps_the_state_graph_as_tlc_writes_it() {
    let plain = include_str!("dot/plain.dot");
    for (test, args, file, expected) in [
        ("dot", &["-dump", "dot", "graph"][..], "graph.dot", plain),
        // A name that ends in .dot keeps it, and TLC reads the options in any case.
        (
            "dot-labelled",
            &["-dump", "dot,Colorize,actionLabels", "graph.dot"],
            "graph.dot",
            include_str!("dot/labelled.dot"),
        ),
        // Without temporal properties, TLC writes no stuttering step.
        (
            "dot-stuttering",
            &["-dump", "dot,stuttering", "graph"],
            "graph.dot",
            plain,
        ),
        // The last copy TLC makes of the graph is the graph.
        (
            "dot-snapshot",
            &["-dump", "dotsnapshot", "graph"],
            "graph_snapshot.dot",
            plain,
        ),
    ] {
        let (output, directory) = run_spec_with(test, DOT_SPEC, "INIT Init\nNEXT Next\n", args);
        assert_eq!(output.status.code(), Some(0), "{test}: {}", stdout(&output));
        assert_eq!(read_dump(&directory, file), expected, "{test}");
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// TLC writes a step under `strict` only where it wrote none whose states' fingerprints have the
// same xor, which the step back has.
#[test]
fn dumps_a_strict_state_graph_as_tlc() {
    let spec = "---- MODULE Stop ----\nVARIABLE s\nInit == s = \"say \\\"hi\\\"\"\nNext == s' = IF s = \"back\\\\\" THEN \"say \\\"hi\\\"\" ELSE \"back\\\\\"\n====\n";
    let (output, directory) = run_spec_with(
        "dot-strict",
        spec,
        "INIT Init\nNEXT Next\n",
        &["-dump", "dot,strict", "graph"],
    );
    assert_eq!(output.status.code(), Some(0), "{}", stdout(&output));
    assert_eq!(
        read_dump(&directory, "graph.dot"),
        include_str!("dot/strict.dot")
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC writes the step to a state as it adds the state to its set, before it checks it, and writes
// its header as it opens the file, before it reads the configuration.
#[test]
fn dumps_the_state_graph_up_to_the_stop_as_tlc() {
    let counter = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1\n====\n";
    let header = "strict digraph DiskGraph {\nnode [shape=box,style=rounded]\nnodesep=0.35;\nsubgraph cluster_graph {\ncolor=\"white\";\n";
    let deadlocked = format!(
        "{header}-3406341414084290173 [label=\"x = 0\",style = filled]\n-3406341414084290173 -> -686636423115914061 [label=\"\",color=\"black\",fontcolor=\"black\"];\n-686636423115914061 [label=\"x = 1\",tooltip=\"x = 1\"];\n-686636423115914061 -> -7115858903467826205 [label=\"\",color=\"black\",fontcolor=\"black\"];\n-7115858903467826205 [label=\"x = 2\",tooltip=\"x = 2\"];\n{{rank = same; -3406341414084290173;}}\n{{rank = same; -686636423115914061;}}\n}}\n}}"
    );
    let invariant = include_str!("dot/invariant.dot").to_string();
    let colorized = header.replace("nodesep", "edge [colorscheme=\"paired12\"]\nnodesep");
    for (test, spec, config, format, code, expected) in [
        (
            "dot-invariant",
            DOT_SPEC,
            "INIT Init\nNEXT Next\nINVARIANT Inv\n",
            "dot,actionlabels",
            12,
            invariant,
        ),
        (
            "dot-deadlock",
            counter,
            "INIT Init\nNEXT Next\n",
            "dot",
            11,
            deadlocked,
        ),
        (
            "dot-configuration",
            counter,
            "INIT Init\n\"unterminated\n",
            "dot,colorize",
            151,
            colorized,
        ),
    ] {
        let (output, directory) = run_spec_with(test, spec, config, &["-dump", format, "graph"]);
        assert_eq!(
            output.status.code(),
            Some(code),
            "{test}: {}",
            stdout(&output)
        );
        assert_eq!(read_dump(&directory, "graph.dot"), expected, "{test}");
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// Where TLC writes what the binary doesn't model.
#[test]
fn declines_a_state_graph_tlc_writes_otherwise() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1\nLive == <>(x = 2)\nAlias == [y |-> x]\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\n====\n";
    for (test, config, format, reason) in [
        // TLC writes a step to each successor the constraints exclude, and to each an action's
        // guard excludes.
        (
            "dot-constrained",
            "INIT Init\nNEXT Next\n",
            "dot,constrained",
            "-dump dot,constrained",
        ),
        (
            "dot-alias",
            "INIT Init\nNEXT Next\nALIAS Alias\n",
            "dot",
            "-dump dot with an ALIAS",
        ),
        // TLC writes the behavior graph to a file of its own.
        (
            "dot-temporal",
            "SPECIFICATION Spec\nPROPERTY Live\n",
            "dot,stuttering",
            "-dump with temporal properties",
        ),
    ] {
        let (output, directory) = run_spec_with(test, spec, config, &["-dump", format, "graph"]);
        assert_eq!(output.status.code(), Some(1), "{test}: {}", stdout(&output));
        assert_eq!(
            stderr(&output),
            format!("prove-it: not native yet: {reason}\n"),
            "{test}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// TLC keeps writing a graph once any -dump asks for one, so `-dump dot g -dump plain` writes the
// graph into plain.dump.
#[test]
fn declines_a_dump_after_a_dump_dot() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1\n====\n";
    let (output, directory) = run_spec_with(
        "dot-then-plain",
        spec,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
        &["-dump", "dot", "graph", "-dump", "plain"],
    );
    assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
    assert_eq!(
        stderr(&output),
        "prove-it: not native yet: -dump after -dump dot\n"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC takes a state predicate a LET defines whole, a FALSE among its conjuncts included, and
// finds no initial state, where the front end would find the spec trivially false: it declines.
#[test]
fn declines_a_let_initial_predicate_with_a_constant_conjunct() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLES x, y\nNext == x < 3 /\\ x' = x + 1 /\\ y' = y\nInv == TRUE\nSpec == LET In == x = 0 /\\ y = 0 /\\ FALSE IN In /\\ [][Next]_<<x, y>>\n====\n";
    let (output, directory) = run_spec_with(
        "dot-let-false",
        spec,
        "SPECIFICATION Spec\nINVARIANT Inv\n",
        &[
            "-workers",
            "1",
            "-fp",
            "1",
            "-dump",
            "dot,snapshot",
            "g.dot",
        ],
    );
    assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
    assert!(
        stderr(&output).contains("a constant conjunct of a state predicate a LET defines"),
        "{}",
        stderr(&output)
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC drops a TRUE conjunct of a LET's predicate as it would one of the specification.
#[test]
fn checks_a_let_initial_predicate_with_a_true_conjunct() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nNext == x' = (x + 1) % 3\nSpec == LET In == x \\in {0,1} /\\ TRUE IN In /\\ [][Next]_x\n====\n";
    let (output, directory) = run_spec_with("let-true", spec, "SPECIFICATION Spec\n", &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains("Finished computing initial states: 2 distinct states generated"),
        "{text}"
    );
    assert!(
        text.contains("5 states generated, 3 distinct states found, 0 states left on queue.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC's workers write the graph's states and edges in the order they reach them, which differs
// from run to run.
#[test]
fn declines_a_dump_dot_on_several_workers() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1\n====\n";
    let (output, directory) = run_spec_with(
        "dot-workers",
        spec,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
        &["-workers", "2", "-dump", "dot", "graph"],
    );
    assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
    assert_eq!(
        stderr(&output),
        "prove-it: not native yet: -dump dot on more than one worker\n"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC copies the graph to the snapshot as it writes each state (`DotStateWriter.writeState`), so a
// search that writes none leaves no snapshot.
#[test]
fn writes_no_snapshot_of_a_graph_without_states() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLES x, y\nInit == x \\in {} /\\ y = 0\nNext == x' = x /\\ y' = y\n====\n";
    let (output, directory) = run_spec_with(
        "dot-empty-snapshot",
        spec,
        "INIT Init\nNEXT Next\n",
        &["-fp", "0", "-dump", "dot,snapshot", "graph"],
    );
    assert_eq!(output.status.code(), Some(0), "{}", stdout(&output));
    assert!(directory.join("graph.dot").exists());
    assert!(!directory.join("graph_snapshot.dot").exists());
    std::fs::remove_dir_all(directory).expect("removed");
}

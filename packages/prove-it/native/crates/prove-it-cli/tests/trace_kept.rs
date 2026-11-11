//! The trace evaluator keeps an argument's value once evaluated, as TLC's `LazyValue` does, so an
//! assumption the engine leaves to it costs what it costs TLC.

mod common;

use common::{run_spec, stderr, stdout};

// The engine leaves the assumption to the trace evaluator: it binds a tuple pattern to a set of
// functions. Each call names its argument twice, so evaluating an argument again at each use
// would double the work at each of the 60 calls.
#[test]
fn checks_an_assumption_naming_each_argument_twice_as_tlc_does() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nRECURSIVE Doubled(_, _)\nDoubled(n, S) == IF n = 0 THEN S ELSE Doubled(n - 1, S \\cup S)\nASSUME {<<s, t>> \\in {f \\in [1..2 -> Doubled(60, {1})] : TRUE} : TRUE} # {}\n====\n";
    let (output, directory) = run_spec("trace-kept", spec, "");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}{}", stderr(&output));
    assert!(
        text.contains(
            "Model checking completed. No error has been found.\n  Estimates of the probability that TLC did not check all reachable states\n  because two distinct states had the same fingerprint:\n  calculated (optimistic):  val = 0.0\n0 states generated, 0 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 0.\n"
        ),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// An argument that builds a lazy function holds the states it was built in, so the walk keeps its
// value only for those states: TLC's `LazyValue` keeps it per state, and each successor the walk
// tries applies the function to its own x'.
#[test]
fn applies_an_argument_built_lazy_in_each_successor_as_tlc_does() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nP(F) == /\\ x' \\in {1, 2} /\\ F[0] = x'\nNext == P([i \\in Nat |-> x'])\nInv == x # 2\n====\n";
    let (output, directory) = run_spec(
        "trace-kept-lazy",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}{}", stderr(&output));
    assert!(
        text.contains(
            "Error: Invariant Inv is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <P line 6, col 9 to line 6, col 29 of module Stop>\nx = 2\n\n3 states generated, 3 distinct states found, 1 states left on queue.\n"
        ),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// An argument whose value is another's, holding the states, holds them too: Q's B is F's value,
// kept for the states F was built in.
#[test]
fn applies_an_argument_passed_on_lazy_in_each_successor_as_tlc_does() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nQ(A, B) == /\\ x' \\in {1, 2} /\\ A[0] = x' /\\ B[0] = x'\nP(F) == Q(F, F)\nNext == P([i \\in Nat |-> x'])\nInv == x # 2\n====\n";
    let (output, directory) = run_spec(
        "trace-kept-passed",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}{}", stderr(&output));
    assert!(
        text.contains(
            "Error: Invariant Inv is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <P line 7, col 9 to line 7, col 29 of module Stop>\nx = 2\n\n3 states generated, 3 distinct states found, 1 states left on queue.\n"
        ),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// A definition that builds a lazy function of x' holds the states, so it isn't the same value in
// each successor, though it reads none as it is built.
#[test]
fn applies_a_definition_built_lazy_in_each_successor_as_tlc_does() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nD == [i \\in Nat |-> x']\nNext == x' \\in {1, 2} /\\ D[0] = x'\nInv == x # 2\n====\n";
    let (output, directory) = run_spec(
        "trace-kept-definition",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}{}", stderr(&output));
    assert!(
        text.contains(
            "Error: Invariant Inv is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Next line 6, col 9 to line 6, col 34 of module Stop>\nx = 2\n\n3 states generated, 3 distinct states found, 1 states left on queue.\n"
        ),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

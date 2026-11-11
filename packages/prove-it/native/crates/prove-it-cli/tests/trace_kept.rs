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

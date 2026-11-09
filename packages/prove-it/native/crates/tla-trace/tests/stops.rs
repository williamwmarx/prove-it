//! The engine's search reports where it stops on a failure evaluating the model, and the report
//! is what the rebuilder needs to evaluate the failure again as TLC reports it.

// The tests share the module, and this one reads less of what a stop keeps.
#[allow(dead_code)]
mod common;

use common::{Quiet, ir_directory, path_to, stop_search};
use tla_engine::search::{
    ErrorSite, OUT_DEGREE_BUCKETS, SearchOutcome, Settings, Violation, ViolationKind, search,
};
use tla_trace::{Failure, Rebuilder, Replay, Site};
use tla_values::Id;

const MODELS: &str = "tlc/tlatools/org.lamport.tlatools/test-model";

// The search's report of where it stopped on a failure.
fn error_stop(path: &str) -> (ErrorSite, Box<Violation>) {
    let bytes = std::fs::read(ir_directory().join(format!("{MODELS}/{path}.ir"))).expect("an IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    let settings = Settings {
        is_violation_reported: true,
        ..Settings::default()
    };
    let SearchOutcome::Stopped {
        violation: Some(violation),
        ..
    } = tla_values::on_nesting_stack(|| {
        tla_engine::on_nesting_stack(|| search(&ir, &settings, &mut Quiet))
    })
    else {
        panic!("{path}: a search that stops with a report");
    };
    let ViolationKind::Error { site } = violation.kind else {
        panic!("{path}: a stop on a failure");
    };
    (site, violation)
}

// The search's report of where it stopped, and TLC's report of the failure from the rebuilder.
fn stop(path: &str) -> (ErrorSite, usize, Failure, [u64; OUT_DEGREE_BUCKETS]) {
    let (site, violation) = error_stop(path);
    let bytes = std::fs::read(ir_directory().join(format!("{MODELS}/{path}.ir"))).expect("an IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    tla_values::on_nesting_stack(|| {
        let states: Vec<&[Id]> = violation.states.iter().map(Vec::as_slice).collect();
        let rebuilt_site = match site {
            ErrorSite::Init => Site::Init,
            ErrorSite::Next => Site::Next,
            ErrorSite::Invariant(position) => Site::Invariant(position),
            ErrorSite::Atom { atom, is_extra } => Site::Atom { atom, is_extra },
            ErrorSite::InitialConstraint(_)
            | ErrorSite::InitialInvariant(_)
            | ErrorSite::InitialPredicate(_) => {
                panic!("{path}: a failure on an initial state, which the rebuilder doesn't take")
            }
        };
        let failure = Rebuilder::new(&ir)
            .and_then(|mut rebuilder| {
                rebuilder.set_fingerprints(&violation.fingerprints);
                rebuilder.evaluate_failure(
                    &violation.store,
                    &states,
                    &violation.labels,
                    rebuilt_site,
                )
            })
            .unwrap_or_else(|unsupported| panic!("{path}: {}", unsupported.0));
        (site, states.len(), failure, violation.counts.out_degrees)
    })
}

#[test]
fn reports_a_failure_in_the_initial_predicate_with_no_states() {
    let (site, count, failure, _) = stop("suite/etest9");
    assert_eq!((site, count, failure.code), (ErrorSite::Init, 0, 1000));
    assert_eq!(
        failure.message,
        "Attempted to check if the value:\n\"a\"\nis an element of Nat."
    );
}

#[test]
fn reports_a_failure_in_an_action_with_the_path_to_the_state_it_expands() {
    let (site, count, failure, _) = stop("AssertExpressionStack");
    // The path the search kept to the state it was expanding.
    let bytes = std::fs::read(ir_directory().join(format!("{MODELS}/AssertExpressionStack.ir")))
        .expect("an IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    let stopped = tla_values::on_nesting_stack(|| {
        tla_engine::on_nesting_stack(|| stop_search(&ir, None)).expect("a search that stops")
    });
    let kept = path_to(&stopped.parents, stopped.expanding).len();
    assert_eq!((site, count, failure.code), (ErrorSite::Next, kept, 2132));
    assert_eq!(
        failure.message,
        "The first argument of Assert evaluated to FALSE; the second argument was:\n\"Fails after initial state\""
    );
}

#[test]
fn reports_a_failing_invariant_with_the_successor_that_fails_it() {
    let (site, count, failure, out_degrees) = stop("EvaluatingValueTest");
    assert_eq!((site, failure.code), (ErrorSite::Invariant(0), 2111));
    assert!(count >= 2, "the path and the successor");
    let text = "Attempted to check if the value:\nFALSE\nis an element of Nat.";
    assert_eq!(
        failure.message,
        format!("Evaluating invariant Inv failed.\n{text}")
    );
    assert_eq!(
        failure.tool_message,
        format!(
            "Evaluating invariant Inv failed.\n@!@!@STARTMSG 2158:0 @!@!@\n{text}\n@!@!@ENDMSG 2158 @!@!@"
        )
    );
    // TLC's replay of the expansion finds the successor in its set, and nothing else.
    assert_eq!(failure.exit_code, 76);
    assert!(failure.call_stack.is_empty());
    assert_eq!(failure.replay, Replay::default());
    // TLC counts the initial state it was expanding, with the new state that fails the invariant:
    // "The average outdegree ... is 1 (minimum is 1, the maximum 1 ...)".
    let mut expected = [0; OUT_DEGREE_BUCKETS];
    expected[1] = 1;
    assert_eq!(out_degrees, expected);
}

#[test]
fn replays_the_expansion_past_the_successor_that_fails_an_invariant() {
    // TLC's set holds the successor that failed TypeOK, of node A. Its replay finds node B's,
    // which the search never reached, and TypeOK fails of it in the methods of the sets of
    // functions and of records the replay built.
    let (site, count, failure, _) = stop("FingerprintExceptionHang");
    assert_eq!(
        (site, count, failure.code),
        (ErrorSite::Invariant(0), 2, 2111)
    );
    let reason = "Attempted to compare integer 1 with non-integer:\n{}";
    assert_eq!(
        failure.message,
        format!("Evaluating invariant TypeOK failed.\n{reason}")
    );
    assert_eq!(
        failure.replay,
        Replay {
            found: 1,
            queued: 0,
            is_failed: true
        }
    );
    assert_eq!(failure.exit_code, 75);
    let fingerprint = failure.fingerprint.expect("a FingerprintException");
    assert!(fingerprint.is_replayed);
    assert_eq!(fingerprint.reason, reason);
    let columns: Vec<_> = fingerprint
        .sources
        .iter()
        .map(|range| (range.start_line, range.start_column, range.end_column))
        .collect();
    assert_eq!(columns, [(16, 5, 46), (16, 20, 46), (16, 30, 45)]);
}

#[test]
fn reports_a_failing_constraint_with_the_initial_state_it_evaluates() {
    // TLC: "TLC expected a boolean value ... While working on the initial state: x = 1", then
    // "1 states generated, 0 distinct states found, 0 states left on queue", depth 1.
    let (site, violation) = error_stop("DoInitFunctor/DoInitFunctorEvalException");
    assert_eq!(site, ErrorSite::InitialConstraint(0));
    assert_eq!(violation.states.len(), 1);
    let counts = violation.counts;
    assert_eq!(
        (
            counts.generated,
            counts.distinct,
            counts.queued,
            counts.depth
        ),
        (1, 0, 0, 1)
    );
}

#[test]
fn reports_a_failing_invariant_with_the_initial_state_it_evaluates() {
    // TLC: "The first argument of > should be an integer", then "1 states generated, 1 distinct
    // states found, 1 states left on queue", depth 1.
    let (site, violation) = error_stop("DoInitFunctor/DoInitFunctorMinimalErrorStack");
    assert_eq!(site, ErrorSite::InitialInvariant(0));
    assert_eq!(violation.states.len(), 1);
    let counts = violation.counts;
    assert_eq!(
        (
            counts.generated,
            counts.distinct,
            counts.queued,
            counts.depth
        ),
        (1, 1, 1, 1)
    );
}

#[test]
fn reports_an_assumption_that_fails_to_evaluate_where_it_reports_failures() {
    // TLC: "Evaluating assumption line 4, col 6 to line 4, col 57 of module etest14 failed."
    let bytes =
        std::fs::read(ir_directory().join(format!("{MODELS}/suite/etest14.ir"))).expect("an IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    let outcome = |is_violation_reported| {
        let settings = Settings {
            is_violation_reported,
            ..Settings::default()
        };
        tla_values::on_nesting_stack(|| {
            tla_engine::on_nesting_stack(|| search(&ir, &settings, &mut Quiet))
        })
    };
    assert!(matches!(
        outcome(true),
        SearchOutcome::AssumptionFailed { position: 0 }
    ));
    assert!(matches!(outcome(false), SearchOutcome::Declined(_)));
}

#[test]
fn reports_a_failing_implied_init_with_the_initial_state_it_evaluates() {
    // TLC checks Prop2 == ENABLED Next of the initial state after the invariants, and fails where
    // ENABLED reaches A(n) \cdot B(n): "1 states generated, 1 distinct states found, 1 states
    // left on queue", depth 1.
    let (site, violation) = error_stop("cdot/CdotWithContextB");
    // Prop is temporal, so Prop2 is the model's first initial predicate.
    assert_eq!(site, ErrorSite::InitialPredicate(0));
    assert_eq!(violation.states.len(), 1);
    let counts = violation.counts;
    assert_eq!(
        (
            counts.generated,
            counts.distinct,
            counts.queued,
            counts.depth
        ),
        (1, 1, 1, 1)
    );
}

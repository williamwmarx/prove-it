//! The engine's search reports where it stops on a failure evaluating the model, and the report
//! is what the rebuilder needs to evaluate the failure again as TLC reports it.

// The tests share the module, and this one reads less of what a stop keeps.
#[allow(dead_code)]
mod common;

use common::{Quiet, ir_directory, path_to, stop_search};
use tla_engine::search::{
    ErrorSite, OUT_DEGREE_BUCKETS, SearchOutcome, Settings, ViolationKind, search,
};
use tla_trace::{Rebuilder, Site};
use tla_values::Id;

const MODELS: &str = "tlc/tlatools/org.lamport.tlatools/test-model";

// The search's report of where it stopped, and TLC's message code for it from the rebuilder.
fn stop(path: &str) -> (ErrorSite, usize, u32, String, [u64; OUT_DEGREE_BUCKETS]) {
    let bytes = std::fs::read(ir_directory().join(format!("{MODELS}/{path}.ir"))).expect("an IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    tla_values::on_nesting_stack(|| {
        let settings = Settings {
            is_violation_reported: true,
            ..Settings::default()
        };
        let SearchOutcome::Stopped {
            violation: Some(violation),
            ..
        } = tla_engine::on_nesting_stack(|| search(&ir, &settings, &mut Quiet))
        else {
            panic!("{path}: a search that stops with a report");
        };
        let ViolationKind::Error { site } = violation.kind else {
            panic!("{path}: a stop on a failure");
        };
        let states: Vec<&[Id]> = violation.states.iter().map(Vec::as_slice).collect();
        let rebuilt_site = match site {
            ErrorSite::Init => Site::Init,
            ErrorSite::Next => Site::Next,
            ErrorSite::Invariant(position) => Site::Invariant(position),
        };
        let failure = Rebuilder::new(&ir)
            .and_then(|mut rebuilder| {
                rebuilder.evaluate_failure(
                    &violation.store,
                    &states,
                    &violation.labels,
                    rebuilt_site,
                )
            })
            .unwrap_or_else(|unsupported| panic!("{path}: {}", unsupported.0));
        (
            site,
            states.len(),
            failure.code,
            failure.message,
            violation.counts.out_degrees,
        )
    })
}

#[test]
fn reports_a_failure_in_the_initial_predicate_with_no_states() {
    let (site, count, code, message, _) = stop("suite/etest9");
    assert_eq!((site, count, code), (ErrorSite::Init, 0, 1000));
    assert_eq!(
        message,
        "Attempted to check if the value:\n\"a\"\nis an element of Nat."
    );
}

#[test]
fn reports_a_failure_in_an_action_with_the_path_to_the_state_it_expands() {
    let (site, count, code, message, _) = stop("AssertExpressionStack");
    // The path the search kept to the state it was expanding.
    let bytes = std::fs::read(ir_directory().join(format!("{MODELS}/AssertExpressionStack.ir")))
        .expect("an IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    let stopped = tla_values::on_nesting_stack(|| {
        tla_engine::on_nesting_stack(|| stop_search(&ir, None)).expect("a search that stops")
    });
    let kept = path_to(&stopped.parents, stopped.expanding).len();
    assert_eq!((site, count, code), (ErrorSite::Next, kept, 2132));
    assert_eq!(
        message,
        "The first argument of Assert evaluated to FALSE; the second argument was:\n\"Fails after initial state\""
    );
}

#[test]
fn reports_a_failing_invariant_with_the_successor_that_fails_it() {
    let (site, count, code, message, out_degrees) = stop("EvaluatingValueTest");
    assert_eq!((site, code), (ErrorSite::Invariant(0), 2111));
    assert!(count >= 2, "the path and the successor");
    assert!(message.starts_with("Evaluating invariant Inv failed."));
    // TLC counts the initial state it was expanding, with the new state that fails the invariant:
    // "The average outdegree ... is 1 (minimum is 1, the maximum 1 ...)".
    let mut expected = [0; OUT_DEGREE_BUCKETS];
    expected[1] = 1;
    assert_eq!(out_degrees, expected);
}

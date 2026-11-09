//! Evaluates again where the engine's search stops on an error, on golden IRs of TLC's tests, and
//! compares the message and call stack with what TLC prints for them.

mod common;

use common::{ir_directory, path_to, stop_search};
use tla_trace::{Failure, Rebuilder, Site, format_call_stack};
use tla_values::Id;

// The search's stop on the model, evaluated again: in the initial predicate when the search kept
// no state, and otherwise in the successors of the state it was expanding.
fn evaluate_failure(path: &str) -> (Failure, String) {
    let bytes = std::fs::read(ir_directory().join(format!("{path}.ir"))).expect("a golden IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    tla_values::on_nesting_stack(|| {
        let stopped =
            tla_engine::on_nesting_stack(|| stop_search(&ir, None)).expect("a search that stops");
        let positions = if stopped.states.is_empty() {
            Vec::new()
        } else {
            path_to(&stopped.parents, stopped.expanding)
        };
        let states: Vec<&[Id]> = positions
            .iter()
            .map(|&position| stopped.states[position].as_slice())
            .collect();
        let site = if states.is_empty() {
            Site::Init
        } else {
            Site::Next
        };
        let actions = vec![None; states.len().saturating_sub(1)];
        let failure = Rebuilder::new(&ir)
            .and_then(|mut rebuilder| {
                rebuilder.evaluate_failure(&stopped.store, &states, &actions, site)
            })
            .unwrap_or_else(|unsupported| {
                panic!("{path}, stopped by {}: {}", stopped.reason, unsupported.0)
            });
        let call_stack = format_call_stack(&ir, &failure.call_stack);
        (failure, call_stack)
    })
}

const MODELS: &str = "tlc/tlatools/org.lamport.tlatools/test-model";

#[test]
fn reports_a_mistyped_membership_in_the_initial_predicate() {
    for (name, value, set, end) in [
        ("etest9", "\"a\"", "Nat", (33, 18, 26)),
        ("etest10", "\"a\"", "Int", (33, 18, 26)),
        ("etest11", "1", "STRING", (36, 18, 29)),
    ] {
        let (failure, call_stack) = evaluate_failure(&format!("{MODELS}/suite/{name}"));
        assert_eq!(failure.code, 1000);
        let text = format!("Attempted to check if the value:\n{value}\nis an element of {set}.");
        assert_eq!(failure.message, text);
        assert_eq!(
            failure.tool_message,
            format!("@!@!@STARTMSG 2158:0 @!@!@\n{text}\n@!@!@ENDMSG 2158 @!@!@")
        );
        let (whole, start, finish) = end;
        let first = if name == "etest11" { 16 } else { 18 };
        assert_eq!(
            call_stack,
            format!(
                "0. Line 9, column 9 to line 11, column {whole} in {name}\n\
                 1. Line 9, column 12 to line 9, column {first} in {name}\n\
                 2. Line 11, column 12 to line 11, column {whole} in {name}\n\
                 3. Line 11, column {start} to line 11, column {finish} in {name}\n\n"
            )
        );
    }
}

#[test]
fn reports_a_failed_assertion_in_an_action() {
    let (failure, call_stack) = evaluate_failure(&format!("{MODELS}/AssertExpressionStack"));
    let text = "The first argument of Assert evaluated to FALSE; the second argument was:\n\"Fails after initial state\"";
    assert_eq!(
        (
            failure.code,
            failure.message.as_str(),
            failure.tool_message.as_str()
        ),
        (2132, text, text)
    );
    assert_eq!(
        call_stack,
        "0. Line 6, column 21 to line 6, column 66 in AssertExpressionStack\n\
         1. Line 6, column 21 to line 6, column 24 in AssertExpressionStack\n\
         2. Line 6, column 27 to line 6, column 66 in AssertExpressionStack\n\n"
    );
    let (failure, call_stack) = evaluate_failure(&format!("{MODELS}/Github461"));
    assert_eq!(
        failure.message,
        "The first argument of Assert evaluated to FALSE; the second argument was:\n\"Failure of assertion at line 8, column 4.\""
    );
    assert_eq!(
        call_stack,
        "0. Line 9, column 5 to line 10, column 17 in Github461\n\
         1. Line 9, column 8 to line 9, column 65 in Github461\n\n"
    );
}

#[test]
fn reports_an_invariant_that_fails_to_evaluate() {
    let path = format!("{MODELS}/EvaluatingValueTest");
    let bytes = std::fs::read(ir_directory().join(format!("{path}.ir"))).expect("a golden IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    let failure = tla_values::on_nesting_stack(|| {
        let stopped =
            tla_engine::on_nesting_stack(|| stop_search(&ir, None)).expect("a search that stops");
        // The successor that fails Inv, x = FALSE, which the search doesn't keep.
        let successor = [stopped.store.bool(false)];
        let mut states: Vec<&[Id]> = path_to(&stopped.parents, stopped.expanding)
            .into_iter()
            .map(|position| stopped.states[position].as_slice())
            .collect();
        states.push(&successor);
        let actions = vec![None; states.len() - 1];
        Rebuilder::new(&ir)
            .and_then(|mut rebuilder| {
                rebuilder.evaluate_failure(&stopped.store, &states, &actions, Site::Invariant(0))
            })
            .unwrap_or_else(|unsupported| panic!("{}", unsupported.0))
    });
    let text = "Attempted to check if the value:\nFALSE\nis an element of Nat.";
    assert_eq!(failure.code, 2111);
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
    assert!(failure.call_stack.is_empty());
}

#[test]
fn reports_a_missing_field_in_an_action_as_an_unexpected_exception() {
    let (failure, call_stack) =
        evaluate_failure(&format!("{MODELS}/TESpecTest/TESpecRuntimeErrorTest"));
    let text = "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: Attempted to select nonexistent field \"val\" from the record\n[val2 |-> 4]\nline 10, col 12 to line 10, col 16 of module TESpecRuntimeErrorTest";
    assert_eq!(
        (
            failure.code,
            failure.message.as_str(),
            failure.tool_message.as_str()
        ),
        (1000, text, text)
    );
    assert_eq!(
        call_stack,
        "0. Line 10, column 9 to line 11, column 35 in TESpecRuntimeErrorTest\n\
         1. Line 10, column 12 to line 10, column 20 in TESpecRuntimeErrorTest\n\
         2. Line 10, column 12 to line 10, column 16 in TESpecRuntimeErrorTest\n\n"
    );
}

#[test]
fn reports_a_primed_variable_an_action_reads_before_it_assigns_it() {
    let (failure, call_stack) = evaluate_failure(&format!("{MODELS}/suite/etest6"));
    let text = "In evaluation, the identifier x is either undefined or not an operator.\nline 16, col 23 to line 16, col 23 of module etest6";
    let prefix = "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: ";
    assert_eq!(failure.code, 1000);
    assert_eq!(failure.message, format!("{prefix}{text}"));
    assert_eq!(
        failure.tool_message,
        format!("{prefix}@!@!@STARTMSG 2280:0 @!@!@\n{text}\n@!@!@ENDMSG 2280 @!@!@")
    );
    assert_eq!(
        call_stack,
        "0. Line 15, column 13 to line 17, column 53 in etest6\n\
         1. Line 15, column 16 to line 15, column 23 in etest6\n\
         2. Line 16, column 16 to line 16, column 24 in etest6\n\
         3. Line 13, column 14 to line 13, column 43 in etest6\n\
         4. Line 13, column 19 to line 13, column 43 in etest6\n\
         5. Line 13, column 36 to line 13, column 42 in etest6\n\
         6. Line 13, column 37 to line 13, column 40 in etest6\n\
         7. Line 13, column 37 to line 13, column 37 in etest6\n\
         8. Line 16, column 23 to line 16, column 23 in etest6\n\n"
    );
}

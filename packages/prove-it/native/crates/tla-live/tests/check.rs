//! The native liveness checker on small graphs: two states that step to each other, from state 0.

use tla_live::{Declined, Graph, Term, Verdict, check};

const PARENTS: [i32; 2] = [-1, 0];
const OFFSETS: [u32; 3] = [0, 1, 2];
const EDGES: [u32; 2] = [1, 0];
const FINGERPRINTS: [u64; 2] = [0x1234, 0x5678];

fn graph() -> Graph<'static> {
    Graph {
        parents: &PARENTS,
        edge_offsets: &OFFSETS,
        edges: &EDGES,
        fingerprints: &FINGERPRINTS,
    }
}

// The negation of []<>P, P the state predicate of atom 0.
const NOT_INFINITELY_OFTEN: [Term; 4] = [Term::Not, Term::Always, Term::Eventually, Term::State(0)];

#[test]
fn finds_a_cycle_that_never_meets_the_predicate() {
    let verdict = check(&NOT_INFINITELY_OFTEN, &graph(), &[Some(&[0, 0])]);
    assert_eq!(
        verdict,
        Verdict::Lasso {
            path: vec![0],
            loop_start: 0,
            is_cycle_constrained: true,
        }
    );
}

#[test]
fn finds_stuttering_without_fairness() {
    let verdict = check(&NOT_INFINITELY_OFTEN, &graph(), &[Some(&[1, 0])]);
    assert_eq!(
        verdict,
        Verdict::Lasso {
            path: vec![0, 1],
            loop_start: 1,
            is_cycle_constrained: true,
        }
    );
}

#[test]
fn holds_where_every_state_meets_the_predicate() {
    assert_eq!(
        check(&NOT_INFINITELY_OFTEN, &graph(), &[Some(&[1, 1])]),
        Verdict::Holds
    );
}

#[test]
fn declines_what_the_engine_leaves_to_the_interpreter() {
    assert_eq!(
        check(&NOT_INFINITELY_OFTEN, &graph(), &[Some(&[1, 2])]),
        Verdict::Declined(Declined::from(
            "a predicate the engine leaves to the interpreter"
        ))
    );
    assert!(matches!(
        check(&NOT_INFINITELY_OFTEN, &graph(), &[None]),
        Verdict::Declined(_)
    ));
}

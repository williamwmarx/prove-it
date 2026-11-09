//! The native liveness checker on small graphs: two states that step to each other, from state 0.

use tla_live::{Declined, Graph, Term, Verdict, check, find_accepted};

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
        reals: None,
        diameters: None,
    }
}

// The negation of []<>P, P the state predicate of atom 0, and []<>P as the one property.
const NOT_INFINITELY_OFTEN: [Term; 4] = [Term::Not, Term::Always, Term::Eventually, Term::State(0)];
const INFINITELY_OFTEN: [Term; 3] = [Term::Always, Term::Eventually, Term::State(0)];

fn verdict(answers: Option<&[u8]>) -> Verdict {
    let liveness = check(
        &NOT_INFINITELY_OFTEN,
        &[&INFINITELY_OFTEN],
        &graph(),
        &[answers],
        false,
    );
    if let Verdict::Declined(_) = liveness.verdict {
    } else {
        assert_eq!(liveness.branches, Some(1));
    }
    liveness.verdict
}

#[test]
fn finds_a_cycle_that_never_meets_the_predicate() {
    assert_eq!(
        verdict(Some(&[0, 0])),
        Verdict::Lasso {
            path: vec![0],
            loop_start: 0,
            is_cycle_constrained: true,
            violated: vec![0],
        }
    );
}

#[test]
fn finds_stuttering_without_fairness() {
    assert_eq!(
        verdict(Some(&[1, 0])),
        Verdict::Lasso {
            path: vec![0, 1],
            loop_start: 1,
            is_cycle_constrained: true,
            violated: vec![0],
        }
    );
}

#[test]
fn holds_where_every_state_meets_the_predicate() {
    assert_eq!(verdict(Some(&[1, 1])), Verdict::Holds);
}

#[test]
fn declines_what_the_engine_leaves_to_the_interpreter() {
    assert_eq!(
        verdict(Some(&[1, 2])),
        Verdict::Declined(Declined::from(
            "a predicate the engine leaves to the interpreter"
        ))
    );
    assert!(matches!(verdict(None), Verdict::Declined(_)));
}

#[test]
fn passes_by_the_states_a_check_part_way_hasnt_expanded() {
    // Only state 0 is expanded: state 1, where the predicate fails as it stutters, is undone.
    let graph = Graph {
        edge_offsets: &OFFSETS[..2],
        ..graph()
    };
    let liveness = check(
        &NOT_INFINITELY_OFTEN,
        &[&INFINITELY_OFTEN],
        &graph,
        &[Some(&[1, 0])],
        false,
    );
    assert_eq!(liveness.verdict, Verdict::Holds);
}

// The negation of []P, which TLC finds as it adds the states, even under -lncheck final: as it
// adds state 1, where P is false, the step back to state 0 reaches the node that accepts every
// behavior. []P is the one property.
const NOT_ALWAYS: [Term; 3] = [Term::Not, Term::Always, Term::State(0)];
const ALWAYS: [Term; 2] = [Term::Always, Term::State(0)];

#[test]
fn finds_a_state_whose_tableau_node_accepts_every_behavior() {
    assert_eq!(
        find_accepted(&NOT_ALWAYS, &[&ALWAYS], &graph(), &[Some(&[1, 0])]),
        Ok(Some(Verdict::Accepted {
            state: 1,
            path: vec![0, 1, 0],
            violated: vec![0],
        }))
    );
    assert_eq!(
        find_accepted(&NOT_ALWAYS, &[&ALWAYS], &graph(), &[Some(&[1, 1])]),
        Ok(None)
    );
}

#[test]
fn asks_nothing_where_no_tableau_node_accepts_every_behavior() {
    // Unknown answers decline the whole check, but []<>P's negation asks for a cycle, which no
    // state reaches as TLC adds it.
    assert_eq!(
        find_accepted(
            &NOT_INFINITELY_OFTEN,
            &[&INFINITELY_OFTEN],
            &graph(),
            &[Some(&[1, 2])]
        ),
        Ok(None)
    );
}

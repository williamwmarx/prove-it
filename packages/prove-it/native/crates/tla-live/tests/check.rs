//! The native liveness checker on small graphs: two states that step to each other, from state 0.

use std::cell::RefCell;

use tla_live::{
    Answers, Declined, Event, Graph, Online, Slot, Source, Term, Unanswered, Verdict, atom_order,
    check, find_accepted, violated_on_lasso,
};

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
        levels: None,
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
        1,
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
        1,
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

#[test]
fn orders_the_atoms_as_the_checker_asks_about_them() {
    // WF of action 2, whose ENABLED is atom 1, and the negation of []<>P, P atom 0: the checks ask
    // of ENABLED and P first, then of the action.
    let formula = [
        Term::And(2),
        Term::Always,
        Term::Eventually,
        Term::Or(2),
        Term::Not,
        Term::Enabled(1),
        Term::Action {
            atom: 2,
            enabled: Some(1),
        },
        Term::Not,
        Term::Always,
        Term::Eventually,
        Term::State(0),
    ];
    assert_eq!(atom_order(&formula), Ok(vec![1, 0, 2]));
    // A property that always holds, whose negation is false, is a tautology.
    assert_eq!(
        atom_order(&[Term::Boolean(false)]),
        Err(Declined::from("a tautology"))
    );
}

#[test]
fn names_the_properties_a_lasso_violates() {
    // A lasso of three states, whose cycle is the last two, with P true in the first only: <>P
    // holds, []<>P doesn't, nor does []P.
    let answers = [true, false, false];
    let eventually = [Term::Eventually, Term::State(0)];
    let always = [Term::Always, Term::State(0)];
    let violated = violated_on_lasso(
        &[&eventually, &INFINITELY_OFTEN, &always],
        3,
        1,
        &mut |term, position, _| match term {
            Term::State(0) => Ok(answers[position]),
            _ => Err(Declined::from("another atom")),
        },
    );
    assert_eq!(violated, Ok(vec![1, 2]));
}

#[test]
fn names_the_first_atom_it_leaves_unanswered_as_it_adds_the_states() {
    let unanswered = |answers: &[u8]| {
        check(
            &NOT_INFINITELY_OFTEN,
            &[&INFINITELY_OFTEN],
            &graph(),
            &[Some(answers)],
            false,
            1,
        )
        .unanswered
    };
    assert_eq!(unanswered(&[1, 0]), None);
    // State 1's predicate, which TLC evaluates as it adds state 1.
    assert_eq!(
        unanswered(&[1, 2]),
        Some(Unanswered {
            state: 1,
            atom: 0,
            slot: 1,
            is_initial: false,
        })
    );
}

// Answers atom 0 of each state from a list, and records each time the checker asks.
struct Asked<'a> {
    answers: &'a [bool],
    asked: RefCell<Vec<Slot>>,
}

impl Answers for Asked<'_> {
    fn answer(&self, _atom: u32, slot: Slot, _diameter: u32) -> Result<bool, Declined> {
        self.asked.borrow_mut().push(slot);
        match slot {
            Slot::State(state) => Ok(self.answers[state as usize]),
            _ => Err(Declined::from("a step")),
        }
    }

    fn position(&self, _atom: u32, slot: Slot, _diameter: u32) -> usize {
        match slot {
            Slot::State(state) | Slot::Reached { state, .. } | Slot::Stutter(state) => {
                state as usize
            }
            Slot::Step { edge, .. } => edge as usize,
        }
    }
}

#[test]
fn asks_each_atom_as_the_search_adds_its_state() {
    // The search adds a state once it has expanded it, when the graph holds the state's steps
    // and no later state's: the checker asks the state's predicate then, each time TLC evaluates
    // it, which for this formula is twice, as a predicate that counts in a register shows of TLC.
    let check_online = |answers: &[bool]| {
        let mut online =
            Online::new(&NOT_INFINITELY_OFTEN, &[&INFINITELY_OFTEN]).expect("a checker");
        assert!(!online.asks_initial_states());
        let asked = Asked {
            answers,
            asked: RefCell::new(Vec::new()),
        };
        let mut asked_by_state = Vec::new();
        for expanded in 0..2 {
            let graph = Graph {
                parents: &PARENTS[..expanded + 1],
                edge_offsets: &OFFSETS[..expanded + 2],
                edges: &EDGES[..expanded + 1],
                fingerprints: &FINGERPRINTS,
                reals: None,
                diameters: None,
                levels: None,
            };
            let source = Source {
                graph: &graph,
                answers: &asked,
            };
            if expanded == 0 {
                online.add_initial_state(&source, 0).expect("added");
                assert_eq!(online.take_events(), [Event::Initial(0)]);
            }
            assert_eq!(online.add_state(&source, expanded as u32), Ok(None));
            assert_eq!(
                online.take_events(),
                [
                    Event::Expanded(expanded as u32),
                    Event::Atom {
                        atom: 0,
                        slot: expanded
                    },
                    Event::Atom {
                        atom: 0,
                        slot: expanded
                    }
                ]
            );
            asked_by_state.push(std::mem::take(&mut *asked.asked.borrow_mut()));
        }
        assert_eq!(
            asked_by_state,
            [
                [Slot::State(0), Slot::State(0)],
                [Slot::State(1), Slot::State(1)]
            ]
        );
        let whole = graph();
        online.finish(&Source {
            graph: &whole,
            answers: &asked,
        })
    };
    assert_eq!(check_online(&[true, true]), Ok(Verdict::Holds));
    assert_eq!(check_online(&[true, false]), Ok(verdict(Some(&[1, 0]))));
    assert_eq!(online_unanswered(), None);
}

fn online_unanswered() -> Option<Unanswered> {
    Online::new(&NOT_INFINITELY_OFTEN, &[&INFINITELY_OFTEN])
        .expect("a checker")
        .unanswered()
}

#[test]
fn names_the_first_action_it_leaves_unanswered_step_by_step() {
    // WF of actions 2 and 4, whose ENABLED are atoms 1 and 3, and the negation of []<>P, P atom 0.
    // TLC checks every action on one step before the next step, so the first unanswered atom is
    // the first of the step it meets first, whichever of the actions has it.
    let fairness = |enabled: u32, atom: u32| {
        [
            Term::Always,
            Term::Eventually,
            Term::Or(2),
            Term::Not,
            Term::Enabled(enabled),
            Term::Action {
                atom,
                enabled: Some(enabled),
            },
        ]
    };
    let formula: Vec<Term> = [Term::And(3)]
        .into_iter()
        .chain(fairness(1, 2))
        .chain(fairness(3, 4))
        .chain(NOT_INFINITELY_OFTEN)
        .collect();
    let unanswered = |first: &[u8], second: &[u8]| {
        check(
            &formula,
            &[&INFINITELY_OFTEN],
            &graph(),
            &[
                Some(&[0, 0]),
                Some(&[1, 1]),
                Some(first),
                Some(&[1, 1]),
                Some(second),
            ],
            false,
            1,
        )
        .unanswered
        .map(|unanswered| (unanswered.atom, unanswered.slot))
    };
    // The steps' answers: from state 0, from state 1, then each state's stuttering step.
    assert_eq!(unanswered(&[1, 1, 1, 1], &[0, 0, 0, 0]), None);
    assert_eq!(unanswered(&[2, 1, 1, 1], &[1, 1, 2, 1]), Some((4, 2)));
    assert_eq!(unanswered(&[1, 1, 2, 1], &[2, 1, 1, 1]), Some((2, 2)));
}

#[test]
fn finds_on_several_threads_what_it_finds_on_one() {
    // The negation of []<>P /\ []Q, P atom 0 and Q atom 1: a behavior graph for each of <>[]~P
    // and <>~Q, built on a thread each, whatever the answers, unanswered ones included.
    let always_q = [Term::Always, Term::State(1)];
    let formula: Vec<Term> = [Term::Or(2)]
        .into_iter()
        .chain(NOT_INFINITELY_OFTEN)
        .chain([Term::Not, Term::Always, Term::State(1)])
        .collect();
    let answers = [0u8, 1, 2];
    for p in answers
        .iter()
        .flat_map(|&first| answers.map(|second| [first, second]))
    {
        for q in answers
            .iter()
            .flat_map(|&first| answers.map(|second| [first, second]))
        {
            let on = |threads: usize| {
                check(
                    &formula,
                    &[&INFINITELY_OFTEN, &always_q],
                    &graph(),
                    &[Some(&p), Some(&q)],
                    false,
                    threads,
                )
            };
            let one = on(1);
            assert_eq!(one.branches, Some(2));
            assert_eq!(on(2), one, "P {p:?}, Q {q:?}");
        }
    }
}

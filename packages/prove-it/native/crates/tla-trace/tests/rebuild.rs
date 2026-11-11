//! Rebuilds paths of the engine's search on the golden IRs of `tests/conformance/ir`: the search
//! stops partway, and the path to each of its last states, from the checkpoint's parents, must
//! rebuild to states equal to the search's.

mod common;

use common::{Quiet, ir_directory, path_to, stop_search};
use tla_engine::search::{SearchOutcome, Settings, ViolationKind, search};
use tla_trace::{
    Alias, CounterExample, Ending, PostconditionInputs, Rebuilder, Stats, Trace, TraceState,
    Unsupported, Value, Verdict, add_actions, format_value,
};
use tla_values::Id;

fn golden_irs(directory: &std::path::Path, found: &mut Vec<std::path::PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(directory)
        .expect("the golden IRs")
        .map(|entry| entry.expect("an entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            golden_irs(&path, found);
        } else if path.extension().is_some_and(|extension| extension == "ir") {
            found.push(path);
        }
    }
}

// Rebuilds the paths to the last few states the search kept, and says what failed.
fn check(path: &std::path::Path) -> Result<usize, String> {
    let bytes = std::fs::read(path).map_err(|error| error.to_string())?;
    let ir = tla_ir::decode(&bytes).map_err(|error| format!("{error:?}"))?;
    // The search stops before a state it reaches: past the first few, if it reaches them.
    let Some(stopped) = [60, 12, 3]
        .into_iter()
        .find_map(|stop_at| tla_engine::on_nesting_stack(|| stop_search(&ir, Some(stop_at))))
    else {
        return Ok(0);
    };
    let mut rebuilder = match Rebuilder::new(&ir) {
        Ok(rebuilder) => rebuilder,
        Err(Unsupported(reason)) => return Err(reason),
    };
    rebuilder
        .set_startup(&stopped.store, &stopped.startup, stopped.startup_random)
        .expect("startup values");
    if let Some(group) = &stopped.symmetry {
        rebuilder.set_symmetry(group);
    }
    let count = stopped.states.len();
    let mut rebuilt = 0;
    for index in count.saturating_sub(3)..count {
        let positions = path_to(&stopped.parents, index);
        let states: Vec<&[Id]> = positions
            .iter()
            .map(|&position| stopped.states[position].as_slice())
            .collect();
        let trace = rebuilder
            .rebuild(
                &stopped.store,
                &states,
                &vec![None; states.len() - 1],
                Ending::Kept,
            )
            .map_err(|Unsupported(reason)| format!("state {index}: {reason}"))?;
        assert_eq!(trace.states.len(), states.len());
        // A violation's last state is found by its value, even where VIEW or SYMMETRY would take
        // another state for it, so it rebuilds only as the search's own. TLC draws the step to
        // a violating successor of an initial state from the generator its search left, which a
        // path the search didn't stop at gives none of.
        match rebuilder.rebuild(
            &stopped.store,
            &states,
            &vec![None; states.len() - 1],
            Ending::Violation,
        ) {
            Err(Unsupported(reason))
                if states.len() == 2
                    && reason.ends_with(
                        "a random draw where the evaluator doesn't follow TLC's generator",
                    ) => {}
            violation => {
                violation.map_err(|Unsupported(reason)| {
                    format!("state {index} as a violation: {reason}")
                })?;
            }
        }
        let last = &trace.states[states.len() - 1];
        let text: Vec<String> = last.values.iter().map(format_value).collect();
        assert!(!text.is_empty() || ir.variables.is_empty());
        rebuilt += 1;
    }
    Ok(rebuilt)
}

#[test]
fn rebuilds_paths_of_the_golden_irs() {
    let mut paths = Vec::new();
    golden_irs(&ir_directory(), &mut paths);
    let mut failures = Vec::new();
    for path in &paths {
        let name = path
            .strip_prefix(ir_directory())
            .unwrap_or(path)
            .display()
            .to_string();
        // MCBakery's initial predicate has 1.7 million states, which the search takes a minute and
        // a half to enumerate in a debug build.
        if cfg!(debug_assertions) && name.contains("MCBakery") {
            continue;
        }
        let result = tla_values::on_nesting_stack(|| check(path));
        match result {
            Ok(count) => eprintln!("{name}: rebuilt {count}"),
            Err(reason) => {
                eprintln!("{name}: {reason}");
                failures.push(format!("{name}: {reason}"));
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

include!("expected.in");

// The states of TLC's text of a trace, each without its label line and without whitespace, which
// TLC's pretty printer adds.
fn tlc_states(trace: &str) -> Vec<String> {
    trace
        .split("\n\n")
        .filter(|block| !block.trim().is_empty())
        .map(|block| {
            let body = block.split_once('\n').map_or("", |(_, body)| body);
            body.chars()
                .filter(|character| !character.is_whitespace())
                .collect()
        })
        .collect()
}

// A rebuilt state as TLC prints it, in TLC's order of the variables, without whitespace.
fn rebuilt_state(ir: &tla_ir::Ir, values: &[tla_trace::Value]) -> String {
    ir.tlc_order
        .iter()
        .map(|&position| {
            let name = &ir.texts[ir.variables[position as usize] as usize];
            format!("/\\{name}={}", format_value(&values[position as usize]))
        })
        .collect::<String>()
        .chars()
        .filter(|character| !character.is_whitespace())
        .collect()
}

// The label of each state of TLC's text of a trace: what is between `<` and `>`.
fn tlc_labels(trace: &str) -> Vec<String> {
    trace
        .split("\n\n")
        .filter(|block| !block.trim().is_empty())
        .filter_map(|block| {
            let line = block.lines().next()?;
            let start = line.find('<')?;
            Some(line[start + 1..line.rfind('>')?].to_string())
        })
        .collect()
}

// A rebuilt trace's states, without whitespace, and, where the IR carries TLC's actions, the label
// of each, from the action the evaluator found for its step. With `is_split`, the actions are
// those the trace evaluator splits the next-state relation into, as for an IR the front end
// lowers, in place of those check.ts wrote.
fn deadlock_trace(path: &str, is_split: bool) -> (Vec<String>, Option<Vec<String>>) {
    let bytes = std::fs::read(ir_directory().join(format!("{path}.ir"))).expect("a golden IR");
    let written = tla_ir::decode(&bytes).expect("an IR that decodes");
    tla_values::on_nesting_stack(|| {
        let ir = if is_split {
            let mut stripped = written.clone();
            stripped.model.actions.clear();
            add_actions(&stripped).expect("actions the evaluator splits")
        } else {
            written.clone()
        };
        let stopped =
            tla_engine::on_nesting_stack(|| stop_search(&ir, None)).expect("a search that stops");
        assert_eq!(stopped.reason, "deadlock");
        let positions = path_to(&stopped.parents, stopped.expanding);
        let states: Vec<&[Id]> = positions
            .iter()
            .map(|&position| stopped.states[position].as_slice())
            .collect();
        let trace = Rebuilder::new(&ir)
            .and_then(|mut rebuilder| {
                rebuilder
                    .set_startup(&stopped.store, &stopped.startup, stopped.startup_random)
                    .expect("startup values");
                if let Some(group) = &stopped.symmetry {
                    rebuilder.set_symmetry(group);
                }
                rebuilder.rebuild(
                    &stopped.store,
                    &states,
                    &vec![None; states.len() - 1],
                    Ending::Kept,
                )
            })
            .expect("a trace the evaluator rebuilds");
        let labels = (!ir.model.actions.is_empty()).then(|| {
            trace
                .states
                .iter()
                .map(|state| match state.action {
                    Some(action) => {
                        ir.texts[ir.model.actions[action as usize].label as usize].to_string()
                    }
                    None => "Initial predicate".to_string(),
                })
                .collect()
        });
        let states = trace
            .states
            .iter()
            .map(|state| rebuilt_state(&ir, &state.values))
            .collect();
        (states, labels)
    })
}

#[test]
fn rebuilds_deadlock_traces_as_tlc_prints_them() {
    for (path, expected) in [
        (
            "kafka/transactions/diary/01_InitPidRequest/tlaplus/kafka_transactions",
            KAFKA_TRACE,
        ),
        (
            "tlc/tlatools/org.lamport.tlatools/test-model/TLCGetLevel",
            TLC_GET_LEVEL_TRACE,
        ),
    ] {
        // The IR carries TLC's actions only where nothing the spec evaluates has an effect, which
        // TLCGet has, so TLCGetLevel's trace is checked without its labels.
        for is_split in [false, true] {
            let (states, labels) = deadlock_trace(path, is_split);
            assert_eq!(states, tlc_states(expected), "{path}");
            if let Some(labels) = labels {
                assert_eq!(labels, tlc_labels(expected), "{path}");
            }
        }
    }
}

#[test]
fn sorts_the_records_of_built_lambdas_under_view_and_symmetry() {
    // TLC permutes the state under SYMMETRY, which builds each lambda into the function it
    // enumerates, and deep-normalizes it under the VIEW, so the records within print sorted.
    let (states, _) = deadlock_trace(
        "raft/specifications/standard-raft/RaftWithReconfigJointConsensus",
        false,
    );
    assert_eq!(states[0], tlc_states(RAFT_RECONFIG_INITIAL_STATE)[0]);
}

#[test]
fn sorts_the_records_tlc_permutes_under_symmetry() {
    // TLC permutes the state under SYMMETRY, which sorts each record it permutes, so a state it
    // finds the least of its orbit prints its records sorted.
    let (states, _) = deadlock_trace("mongodb-txns/MultiShardTxn/Storage", false);
    assert_eq!(states[..2], tlc_states(STORAGE_TRACE_START));
}

// Rebuilds the trace of the violation the search stops at, and hands it to `then` with the
// rebuilder and the start of a lasso's cycle.
fn rebuild_violation<T: Send>(
    path: &str,
    then: impl FnOnce(
        &tla_ir::Ir,
        &mut Rebuilder,
        &tla_trace::Trace,
        Option<usize>,
    ) -> Result<T, Unsupported>
    + Send,
) -> Result<T, Unsupported> {
    let bytes = std::fs::read(ir_directory().join(format!("{path}.ir"))).expect("a golden IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    tla_values::on_nesting_stack(|| {
        let SearchOutcome::Stopped {
            violation: Some(violation),
            ..
        } = tla_engine::on_nesting_stack(|| {
            let settings = Settings {
                is_violation_reported: true,
                ..Settings::default()
            };
            search(&ir, &settings, &mut Quiet)
        })
        else {
            panic!("{path}: a search that stops at a violation");
        };
        let (ending, cycle_start) = match violation.kind {
            ViolationKind::Deadlock { .. } => (Ending::Kept, None),
            ViolationKind::Invariant(_)
            | ViolationKind::ActionProperty(_)
            | ViolationKind::InitialInvariant(_)
            | ViolationKind::InitialPredicate(_) => (Ending::Violation, None),
            ViolationKind::Lasso { loop_start, .. } => (Ending::Lasso, Some(loop_start)),
            ViolationKind::Accepted { .. } => (Ending::Lasso, None),
            ViolationKind::NoNextState | ViolationKind::Error { .. } => {
                panic!("{path}: a stop with no trace")
            }
        };
        let states: Vec<&[Id]> = violation.states.iter().map(Vec::as_slice).collect();
        let mut rebuilder = Rebuilder::new(&ir)?;
        rebuilder.set_startup(
            &violation.store,
            &violation.startup,
            violation.startup_random,
        )?;
        let trace = rebuilder.rebuild(&violation.store, &states, &violation.labels, ending)?;
        then(&ir, &mut rebuilder, &trace, cycle_start)
    })
}

#[test]
fn draws_random_elements_and_subsets_as_tlc_does() {
    // TLC draws in the initial predicate from the generator startup left, and in each step from
    // one seeded with the predecessor's fingerprint.
    for (name, expected) in [
        ("RandomElement", RANDOM_ELEMENT_TRACE),
        ("RandomElementXandY", RANDOM_ELEMENT_X_AND_Y_TRACE),
        ("RandomSubset", RANDOM_SUBSET_TRACE),
        ("RandomSubsetNextTuples", RANDOM_SUBSET_NEXT_TUPLES_TRACE),
    ] {
        let states = rebuild_violation(
            &format!("tlc/tlatools/org.lamport.tlatools/test-model/{name}"),
            |ir, _, trace, _| {
                Ok(trace
                    .states
                    .iter()
                    .map(|state| rebuilt_state(ir, &state.values))
                    .collect::<Vec<_>>())
            },
        );
        assert_eq!(states, Ok(tlc_states(expected)), "{name}");
    }
}

// Each state of the trace the search stops with, through the ALIAS, as TLC prints it without
// whitespace: the alias record's fields in order, or the state's variables where it gives none.
fn aliased_trace(path: &str) -> Result<Vec<String>, Unsupported> {
    rebuild_violation(path, |ir, rebuilder, trace, cycle_start| {
        let aliases = rebuilder
            .alias(trace, cycle_start, None, false)?
            .expect("a model with an ALIAS");
        let text = |fields: Vec<(String, String)>| {
            fields
                .into_iter()
                .map(|(name, value)| format!("/\\{name}={value}"))
                .collect::<String>()
                .chars()
                .filter(|character| !character.is_whitespace())
                .collect()
        };
        Ok(aliases
            .into_iter()
            .zip(&trace.states)
            .map(|(alias, state)| match alias {
                Alias::Record(fields) => text(
                    fields
                        .into_iter()
                        .map(|(name, value)| (name, format_value(&value)))
                        .collect(),
                ),
                Alias::State => text(
                    ir.tlc_order
                        .iter()
                        .map(|&position| {
                            (
                                ir.texts[ir.variables[position as usize] as usize].to_string(),
                                format_value(&state.values[position as usize]),
                            )
                        })
                        .collect(),
                ),
            })
            .collect())
    })
}

#[test]
fn prints_a_state_through_the_alias_record_in_the_order_written() {
    // Github746's alias reads the next state, which for the initial state that violates the
    // invariant is the state itself.
    assert_eq!(
        aliased_trace("tlc/tlatools/org.lamport.tlatools/test-model/Github746"),
        Ok(vec!["/\\i=1/\\foo=\"bar\"/\\j=TRUE".to_string()])
    );
}

#[test]
fn checks_a_postcondition_on_the_counter_example() {
    // Github1389Counting's postcondition reads the states and steps of the stuttering lasso TLC
    // prints: x alternating from FALSE over ten states, each step Next. It holds there, and not
    // on a trace one state short.
    let bytes = std::fs::read(
        ir_directory().join("tlc/tlatools/org.lamport.tlatools/test-model/Github1389Counting.ir"),
    )
    .expect("a golden IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    let check = |count: usize| {
        let trace = Trace {
            states: (0..count)
                .map(|position| TraceState {
                    values: vec![Value::Bool(position % 2 == 1)],
                    action: (position > 0).then_some(0),
                    printed: Vec::new(),
                })
                .collect(),
            trace_output: Vec::new(),
        };
        Rebuilder::new(&ir)?.postcondition(
            0,
            &PostconditionInputs {
                possible: &[],
                stats: Stats {
                    queue: 0,
                    distinct: 2,
                    initial: 1,
                    generated: 5,
                    diameter: 2,
                    duration: 0,
                },
                counter_example: Some(CounterExample {
                    trace: &trace,
                    cycle: None,
                }),
            },
        )
    };
    let verdict = |count| check(count).map(|checked| checked.verdict);
    assert_eq!(verdict(10), Ok(Verdict::Holds));
    assert_eq!(verdict(9), Ok(Verdict::False));
}

#[test]
fn records_the_parameters_of_the_counter_examples_actions() {
    // AsyncTerminationDetection's postcondition is the lasso TLC finds: SendMsg(3, 3), then
    // RcvMsg(3) back into the initial state, each step's action recorded with the values of its
    // parameters.
    let bytes = std::fs::read(ir_directory().join(
        "tlc/tlatools/org.lamport.tlatools/test-model/examples/ewd998/AsyncTerminationDetection.ir",
    ))
    .expect("a golden IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    let action = |name: &str| {
        ir.model
            .actions
            .iter()
            .position(|action| ir.texts[action.label as usize].starts_with(name))
            .expect("the action") as u32
    };
    let (send, receive, terminate) = (
        action("SendMsg(3,3) "),
        action("RcvMsg(3) "),
        action("Terminate(3) "),
    );
    let verdict = tla_values::on_nesting_stack(|| {
        let stopped = tla_engine::on_nesting_stack(|| stop_search(&ir, Some(400)))
            .expect("a search that stops");
        let mut rebuilder = Rebuilder::new(&ir)?;
        rebuilder
            .set_startup(&stopped.store, &stopped.startup, stopped.startup_random)
            .expect("startup values");
        // TLC's lasso starts in the initial state where only node 3 is active.
        let active = ir
            .variables
            .iter()
            .position(|&name| &*ir.texts[name as usize] == "active")
            .expect("the variable");
        let trace = (1..stopped.states.len())
            .filter(|&index| {
                let parent = stopped.parents[index];
                parent >= 0 && stopped.parents[parent as usize] == -1
            })
            .find_map(|index| {
                let parent = stopped.parents[index] as usize;
                rebuilder
                    .rebuild(
                        &stopped.store,
                        &[&stopped.states[parent], &stopped.states[index]],
                        &[None],
                        Ending::Kept,
                    )
                    .ok()
                    .filter(|trace| {
                        trace.states[1].action == Some(send)
                            && format_value(&trace.states[0].values[active])
                                == "(0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE)"
                    })
            })
            .expect("the step SendMsg(3, 3)");
        let mut check = |closing| {
            rebuilder
                .postcondition(
                    0,
                    &PostconditionInputs {
                        possible: &[],
                        stats: Stats {
                            queue: 0,
                            distinct: 0,
                            initial: 0,
                            generated: 0,
                            diameter: 0,
                            duration: 0,
                        },
                        counter_example: Some(CounterExample {
                            trace: &trace,
                            cycle: Some((0, Some(closing))),
                        }),
                    },
                )
                .map(|checked| checked.verdict)
        };
        Ok::<_, Unsupported>((check(receive)?, check(terminate)?))
    });
    assert_eq!(verdict, Ok((Verdict::Holds, Verdict::False)));
}

#[test]
fn reads_the_possible_counts_in_a_postcondition() {
    // PossibleCountsTest's postcondition holds where TLC counted each _POSSIBLE predicate once.
    let bytes = std::fs::read(
        ir_directory().join("tlc/tlatools/org.lamport.tlatools/test-model/PossibleCountsTest.ir"),
    )
    .expect("a golden IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    let verdict = |at_one: i64| {
        Rebuilder::new(&ir)?
            .postcondition(
                0,
                &PostconditionInputs {
                    possible: &[("AtOne".to_string(), at_one), ("WrapAround".to_string(), 1)],
                    stats: Stats {
                        queue: 0,
                        distinct: 3,
                        initial: 1,
                        generated: 4,
                        diameter: 3,
                        duration: 0,
                    },
                    counter_example: None,
                },
            )
            .map(|checked| checked.verdict)
    };
    assert_eq!(verdict(1), Ok(Verdict::Holds));
    assert_eq!(verdict(2), Ok(Verdict::False));
}

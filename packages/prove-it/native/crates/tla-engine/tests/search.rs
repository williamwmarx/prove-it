//! The search on the golden IRs of `tests/conformance/ir`, against TLC's recorded outcomes in
//! `tests/conformance/expected.json`: the counts of a model it completes, or where it stops. The
//! models are the small ones, which a debug build searches in a moment.

use tla_engine::search::{DumpedStep, DumpedSteps, Reporter, SearchOutcome, Settings, search};

struct Quiet;

impl Reporter for Quiet {
    fn initial_states_started(&mut self) {}
    fn initial_states_progress(&mut self, _count: u64) {}
    fn initial_states(&mut self, _generated: u64, _distinct: u64) {}
    fn progress(&mut self, _generated: u64, _distinct: u64, _queued: u64, _depth: u64) {}
    fn print(&mut self, _store: &tla_values::Store, _prints: &tla_engine::Prints) {}
}

fn run(path: &str, settings: &Settings) -> SearchOutcome {
    let bytes = std::fs::read(format!(
        "{}/../../../tests/conformance/ir/{path}.ir",
        env!("CARGO_MANIFEST_DIR")
    ))
    .expect("a golden IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    tla_engine::on_nesting_stack(|| search(&ir, settings, &mut Quiet))
}

// What a search found: its generated and distinct counts and depth, or where it stopped.
fn describe(outcome: &SearchOutcome) -> String {
    match outcome {
        SearchOutcome::Declined(reason) => format!("declined: {reason}"),
        SearchOutcome::AssumptionViolated { name } => format!("assumption {name} is false"),
        SearchOutcome::ConfigError { message } => format!("configuration error: {message}"),
        SearchOutcome::AssumptionFailed { position } => {
            format!("assumption {position} failed to evaluate")
        }
        SearchOutcome::Invariant(reason) => format!("invariant: {reason}"),
        SearchOutcome::Complete { counts, .. } => format!(
            "complete: {} generated, {} distinct, depth {}",
            counts.generated, counts.distinct, counts.depth
        ),
        SearchOutcome::Stopped {
            reason, checkpoint, ..
        } => format!(
            "stopped: {reason} before state {}",
            checkpoint
                .as_ref()
                .map_or(-1, |checkpoint| checkpoint.expanding as i64)
        ),
    }
}

#[test]
fn completes_with_tlc_counts() {
    let models = [
        (
            "examples/specifications/transaction_commit/TCommit",
            94,
            34,
            7,
        ),
        (
            "examples/specifications/transaction_commit/2PCwithBTM",
            5841,
            1245,
            15,
        ),
        (
            "examples/specifications/byihive/VoucherRedeem",
            26848,
            4199,
            11,
        ),
        (
            "tlc/tlatools/org.lamport.tlatools/test-model/suite/test37",
            2,
            1,
            1,
        ),
        (
            "tlc/tlatools/org.lamport.tlatools/test-model/suite/test61",
            6,
            5,
            5,
        ),
        ("spectacle/specs/with_state_graphs/simple_folds", 6, 3, 1),
        // A graph drawn at random at startup, from the seed the IR carries.
        (
            "tlc/tlatools/org.lamport.tlatools/test-model/Github648",
            1332,
            36,
            1,
        ),
    ];
    for (path, generated, distinct, depth) in models {
        assert_eq!(
            describe(&run(path, &Settings::default())),
            format!("complete: {generated} generated, {distinct} distinct, depth {depth}"),
            "{path}"
        );
    }
}

// What a search reported of TLC's startup and of the search after it, in order.
#[derive(Default)]
struct Recorded(Vec<String>);

impl Reporter for Recorded {
    fn initial_states_started(&mut self) {
        self.0.push("initial states".into());
    }
    fn initial_states_progress(&mut self, _count: u64) {}
    fn initial_states(&mut self, _generated: u64, _distinct: u64) {}
    fn progress(&mut self, _generated: u64, _distinct: u64, _queued: u64, _depth: u64) {}
    fn print(&mut self, store: &tla_values::Store, prints: &tla_engine::Prints) {
        self.0
            .push(format!("print {}", format_values(store, &prints.values)));
    }
    fn startup_print(&mut self, store: &tla_values::Store, prints: &tla_engine::Prints) {
        self.0
            .push(format!("startup {}", format_values(store, &prints.values)));
    }
    fn startup_done(&mut self) {
        self.0.push("startup done".into());
    }
}

fn format_values(store: &tla_values::Store, values: &[tla_values::Id]) -> String {
    values
        .iter()
        .map(|&value| tla_values::print::format_value(store, value).expect("printable"))
        .collect::<Vec<_>>()
        .join("  ")
}

// TLC's Euclid prints from its assumptions, which TLC checks after it prints what it prints
// itself, and before it computes the initial states.
#[test]
fn prints_what_the_assumptions_print_after_the_constant_definitions() {
    let bytes = std::fs::read(format!(
        "{}/../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/pcal/Euclid.ir",
        env!("CARGO_MANIFEST_DIR")
    ))
    .expect("a golden IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    let mut recorded = Recorded::default();
    let outcome = tla_engine::on_nesting_stack(|| search(&ir, &Settings::default(), &mut recorded));
    assert_eq!(
        describe(&outcome),
        "complete: 6752 generated, 6352 distinct, depth 42"
    );
    assert_eq!(
        recorded.0,
        [
            "startup done",
            "startup <<\"Testing Euclid's algorithm on all numbers between 1 and \", 20>>  TRUE",
            "startup \"Most time spent evaluating naive definition of GCD for test\"  TRUE",
            "initial states",
        ]
    );
}

#[test]
fn stops_where_tlc_finds_deadlock() {
    for path in [
        "tlc/tlatools/org.lamport.tlatools/test-model/TLCGetLevel",
        "kafka/transactions/diary/01_InitPidRequest/tlaplus/kafka_transactions",
    ] {
        let outcome = describe(&run(path, &Settings::default()));
        assert!(
            outcome.starts_with("stopped: deadlock before state "),
            "{path}: {outcome}"
        );
    }
}

// With temporal properties, a search hands over its graph and the answers to each atom the
// liveness checker asks about, for every state and step, but the steps of an action from a state
// where the ENABLED of its fairness is false, which the checker doesn't ask about.
#[test]
fn records_the_graph_and_answers_the_atoms() {
    let path = "examples/specifications/ReadersWriters/MC";
    let bytes = std::fs::read(format!(
        "{}/../../../tests/conformance/ir/{path}.ir",
        env!("CARGO_MANIFEST_DIR")
    ))
    .expect("a golden IR");
    let atoms = tla_ir::decode(&bytes).expect("an IR").model.atoms;
    let outcome = run(
        path,
        &Settings {
            is_live_checked: true,
            ..Settings::default()
        },
    );
    let SearchOutcome::Complete {
        counts,
        checkpoint: Some(checkpoint),
        ..
    } = outcome
    else {
        panic!("ReadersWriters didn't complete with a graph");
    };
    let graph = checkpoint.graph.expect("a graph");
    assert_eq!(graph.expanded, counts.distinct);
    assert_eq!(
        graph.edges.len() as u64,
        counts.generated - counts.initial_generated
    );
    assert_eq!(
        graph
            .successor_counts
            .iter()
            .map(|&count| u64::from(count))
            .sum::<u64>(),
        graph.edges.len() as u64
    );
    assert!(graph.is_enabled_exact);
    assert!(graph.labels.is_some());
    assert_eq!(graph.tables.len(), atoms.len());
    let mut skipped = 0;
    for (table, atom) in graph.tables.iter().zip(&atoms) {
        assert_eq!(table.unknown, None);
        let tla_ir::AtomKind::Action {
            enabled: Some(enabled),
            ..
        } = atom.kind
        else {
            assert!(table.answers.iter().all(|&answer| answer < 2));
            continue;
        };
        let enabled = &graph.tables[enabled as usize].answers;
        let edge_count = graph.edges.len();
        for (index, &is_enabled) in enabled.iter().enumerate().take(graph.expanded as usize) {
            let start = graph.edge_offsets[index] as usize;
            let end = graph.edge_offsets[index + 1] as usize;
            let steps = (start..end).chain([edge_count + index]);
            for answer in steps.map(|step| table.answers[step]) {
                assert_eq!(answer == 2, is_enabled == 0);
                skipped += usize::from(answer == 2);
            }
        }
    }
    assert!(skipped > 0);
    assert!(graph.tables.iter().any(|table| table.is_from_steps));
}

// Where one of TLC's actions doesn't compile, the search walks the next-state relation unlabelled
// and runs ENABLED, finding what the labelled search finds.
#[test]
fn walks_the_next_state_relation_where_an_action_doesnt_compile() {
    let bytes = std::fs::read(format!(
        "{}/../../../tests/conformance/ir/examples/specifications/ReadersWriters/MC.ir",
        env!("CARGO_MANIFEST_DIR")
    ))
    .expect("a golden IR");
    let ir = tla_ir::decode(&bytes).expect("an IR");
    assert!(ir.model.is_labelled);
    let mut broken = ir.clone();
    // A scope whose value the IR can't hold, which the TypeScript engine reads and this one
    // declines.
    let name = broken.scopes.first().map_or(0, |scope| scope.name);
    broken.scopes.push(tla_ir::Scope {
        parent: None,
        name,
        binding: tla_ir::ScopeBinding::Value(None),
    });
    let scope = Some((broken.scopes.len() - 1) as tla_ir::Index);
    broken.model.actions.last_mut().expect("an action").scope = scope;
    let settings = Settings {
        is_live_checked: true,
        ..Settings::default()
    };
    let graphs = [&ir, &broken].map(|ir| {
        let outcome = tla_engine::on_nesting_stack(|| search(ir, &settings, &mut Quiet));
        let SearchOutcome::Complete {
            counts,
            checkpoint: Some(checkpoint),
            ..
        } = outcome
        else {
            panic!("ReadersWriters didn't complete with a graph");
        };
        (counts, checkpoint.graph.expect("a graph"))
    });
    let [(counts, labelled), (broken_counts, unlabelled)] = graphs;
    assert!(labelled.labels.is_some());
    assert!(unlabelled.labels.is_none());
    assert_eq!(
        (broken_counts.generated, broken_counts.distinct),
        (counts.generated, counts.distinct)
    );
    assert_eq!(unlabelled.edges, labelled.edges);
    for (table, broken_table) in labelled.tables.iter().zip(&unlabelled.tables) {
        assert_eq!(broken_table.answers, table.answers);
    }
}

#[test]
fn stops_where_asked_with_the_states_before() {
    let settings = Settings {
        stop_at: Some(10),
        ..Settings::default()
    };
    let outcome = run(
        "examples/specifications/transaction_commit/TCommit",
        &settings,
    );
    let SearchOutcome::Stopped {
        reason,
        checkpoint: Some(checkpoint),
        ..
    } = outcome
    else {
        panic!("TCommit didn't stop");
    };
    assert_eq!(reason, "stopped where PROVE_IT_STOP_AT asked");
    assert_eq!(checkpoint.expanding, 10);
    assert_eq!(checkpoint.parents.len() as u64, checkpoint.count);
    // TCommit has one variable.
    assert_eq!(checkpoint.states.states.len() as u64, checkpoint.count);
    assert!(checkpoint.count > 10);
}

#[test]
fn finds_no_fingerprint_collision() {
    let settings = Settings {
        is_fingerprint_verified: true,
        ..Settings::default()
    };
    let SearchOutcome::Complete { collisions, .. } =
        run("examples/specifications/byihive/VoucherRedeem", &settings)
    else {
        panic!("VoucherRedeem didn't complete");
    };
    assert_eq!(collisions, 0);
}

// What a search found and wrote to its state log, with its counts and where it stopped.
fn search_on_threads(path: &str, threads: usize, stop_at: Option<usize>) -> (String, String) {
    let log = std::env::temp_dir().join(format!(
        "prove-it-{}-{threads}-{stop_at:?}-{}.ndjson",
        std::process::id(),
        path.replace('/', "-")
    ));
    let settings = Settings {
        threads,
        minimum_shared_level: 1,
        stop_at,
        is_fingerprint_verified: true,
        state_log: Some(log.to_string_lossy().into_owned()),
        ..Settings::default()
    };
    let outcome = run(path, &settings);
    let found = match &outcome {
        SearchOutcome::Complete {
            counts,
            fingerprints,
            collisions,
            ..
        } => format!("{counts:?} {fingerprints:?} {collisions}"),
        SearchOutcome::Stopped {
            reason,
            checkpoint,
            collisions,
            ..
        } => format!(
            "{reason} {collisions} {:?}",
            checkpoint.as_ref().map(|checkpoint| (
                checkpoint.expanding,
                checkpoint.count,
                checkpoint.generated,
                checkpoint.initial_generated,
                checkpoint.out_degrees,
                &checkpoint.parents,
                &checkpoint.states.states,
                checkpoint.keys.as_ref().map(|keys| &keys.0.states),
                checkpoint.graph.as_ref().map(|graph| (
                    graph.expanded,
                    &graph.successor_counts,
                    &graph.new_counts,
                    &graph.edge_offsets,
                    &graph.edges,
                    &graph.labels,
                    &graph.initial_counts,
                    graph.is_enabled_exact,
                    graph
                        .tables
                        .iter()
                        .map(|table| &table.answers)
                        .collect::<Vec<_>>(),
                )),
            ))
        ),
        other => describe(other),
    };
    let written = std::fs::read_to_string(&log).unwrap_or_default();
    let _ = std::fs::remove_file(&log);
    (found, written)
}

// Threads sharing a level find the states one thread finds, in its order, with its counts, and
// stop where it stops: at a deadlock, a TLCGet, a VIEW and symmetry, whatever the number of threads.
#[test]
fn finds_on_any_number_of_threads_what_one_thread_finds() {
    let models = [
        "examples/specifications/transaction_commit/2PCwithBTM",
        "examples/specifications/byihive/VoucherRedeem",
        "tlc/tlatools/org.lamport.tlatools/test-model/pcal/SyncCons",
        "tlc/tlatools/org.lamport.tlatools/test-model/Echo/MCEcho",
        "tlc/tlatools/org.lamport.tlatools/test-model/EWD840/MC02",
        "tlc/tlatools/org.lamport.tlatools/test-model/TLCGetLevel",
        "tlc/tlatools/org.lamport.tlatools/test-model/suite/test216",
        "tla-rs/test_cases/should_pass/view_symmetry",
        "examples/specifications/ReadersWriters/MC",
    ];
    let mut logged = Vec::new();
    for path in models {
        let one = search_on_threads(path, 1, None);
        if !one.1.is_empty() {
            logged.push(path);
        }
        for threads in [2, 4, 16] {
            assert_eq!(
                search_on_threads(path, threads, None),
                one,
                "{path} on {threads} threads"
            );
        }
    }
    assert_eq!(logged.len(), 9);
}

// A search stopped where PROVE_IT_STOP_AT asks, inside a level the threads share or at its end,
// hands over the states one thread found before that state, and the graph of their steps where it
// records one.
#[test]
fn stops_on_any_number_of_threads_where_one_thread_stops() {
    let stops = [
        (
            "examples/specifications/transaction_commit/2PCwithBTM",
            &[0, 1, 7, 100, 333, 1000, 1244, 1245][..],
        ),
        (
            "examples/specifications/ReadersWriters/MC",
            &[1, 7, 100, 1000, 4321, 21_526][..],
        ),
    ];
    for (path, stops) in stops {
        for &stop_at in stops {
            let one = search_on_threads(path, 1, Some(stop_at));
            for threads in [2, 4] {
                assert_eq!(
                    search_on_threads(path, threads, Some(stop_at)),
                    one,
                    "{path} stopped at {stop_at} on {threads} threads"
                );
            }
        }
    }
}

// What a search hands its reporter for -dump: how often, each state it found as printed, and for
// -dump dot each state's fingerprint and parent and the steps.
#[derive(Default)]
struct Dumped {
    calls: usize,
    states: Vec<String>,
    steps: Option<(Vec<u64>, Vec<i32>, Vec<DumpedStep>)>,
}

impl Reporter for Dumped {
    fn initial_states_started(&mut self) {}
    fn initial_states_progress(&mut self, _count: u64) {}
    fn initial_states(&mut self, _generated: u64, _distinct: u64) {}
    fn progress(&mut self, _generated: u64, _distinct: u64, _queued: u64, _depth: u64) {}
    fn print(&mut self, _store: &tla_values::Store, _prints: &tla_engine::Prints) {}
    fn dumped(
        &mut self,
        store: &tla_values::Store,
        states: &[tla_values::Id],
        width: usize,
        steps: Option<&DumpedSteps<'_>>,
    ) {
        self.calls += 1;
        self.states = states
            .chunks(width)
            .map(|state| format_values(store, state))
            .collect();
        self.steps = steps.map(|steps| {
            (
                steps.fingerprints.to_vec(),
                steps.parents.to_vec(),
                steps.steps.to_vec(),
            )
        });
    }
}

fn dump(path: &str, threads: usize) -> (String, Dumped) {
    dump_with(path, threads, false)
}

fn dump_with(path: &str, threads: usize, is_step_dumped: bool) -> (String, Dumped) {
    let bytes = std::fs::read(format!(
        "{}/../../../tests/conformance/ir/{path}.ir",
        env!("CARGO_MANIFEST_DIR")
    ))
    .expect("a golden IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    let settings = Settings {
        threads,
        minimum_shared_level: 1,
        is_dumped: true,
        is_step_dumped,
        // As the binary does, which reports the violation itself.
        is_violation_reported: true,
        ..Settings::default()
    };
    let mut dumped = Dumped::default();
    let outcome = tla_engine::on_nesting_stack(|| search(&ir, &settings, &mut dumped));
    (describe(&outcome), dumped)
}

#[test]
fn hands_the_dump_every_state_found_in_order_on_any_number_of_threads() {
    // TLC's distinct states, which -dump writes: all of TCommit's, and those ACP_NB_WRONG_TLC
    // found up to the state that violates AC1, that one included.
    for (path, distinct) in [
        ("examples/specifications/transaction_commit/TCommit", 34),
        ("examples/specifications/acp/ACP_NB_WRONG_TLC", 11852),
    ] {
        let (outcome, one) = dump(path, 1);
        assert_eq!(one.calls, 1, "{path}: {outcome}");
        assert_eq!(one.states.len(), distinct, "{path}: {outcome}");
        let (_, four) = dump(path, 4);
        assert_eq!(four.calls, 1, "{path}");
        assert_eq!(four.states, one.states, "{path}");
    }
}

#[test]
fn hands_the_dump_each_step_in_the_order_tlc_takes_them() {
    // TCommit's 34 states, one initial, and the 93 steps TLC takes between them (those generated
    // past the initial state), on one thread whatever the threads asked for.
    let path = "examples/specifications/transaction_commit/TCommit";
    let (outcome, one) = dump_with(path, 1, true);
    assert_eq!(outcome, "complete: 94 generated, 34 distinct, depth 7");
    let (fingerprints, parents, steps) = one.steps.clone().expect("the steps");
    assert_eq!((fingerprints.len(), parents.len()), (34, 34));
    assert_eq!(steps.len(), 93);
    assert!(steps.windows(2).all(|pair| pair[0].from <= pair[1].from));
    // Each state past the initial ones is found by the first step to it, from its parent.
    let mut found = parents.iter().take_while(|&&parent| parent < 0).count() as u32;
    for step in &steps {
        if step.to == found {
            assert_eq!(parents[step.to as usize], step.from as i32);
            found += 1;
        }
        assert!(step.to < found);
    }
    assert_eq!(found, 34);
    let (_, four) = dump_with(path, 4, true);
    assert_eq!(four.steps, one.steps);
    assert_eq!(dump(path, 1).1.steps, None);
}

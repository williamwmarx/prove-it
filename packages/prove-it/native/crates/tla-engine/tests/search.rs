//! The search on the golden IRs of `tests/conformance/ir`, against TLC's recorded outcomes in
//! `tests/conformance/expected.json`: the counts of a model it completes, or where it stops. The
//! models are the small ones, which a debug build searches in a moment.

use tla_engine::search::{Reporter, SearchOutcome, Settings, search};

struct Quiet;

impl Reporter for Quiet {
    fn initial_states_started(&mut self) {}
    fn initial_states_progress(&mut self, _count: u64) {}
    fn initial_states(&mut self, _generated: u64, _distinct: u64) {}
    fn progress(&mut self, _generated: u64, _distinct: u64, _queued: u64, _depth: u64) {}
    fn print(&mut self, _store: &tla_values::Store, _values: &[tla_values::Id]) {}
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
    ];
    for (path, generated, distinct, depth) in models {
        assert_eq!(
            describe(&run(path, &Settings::default())),
            format!("complete: {generated} generated, {distinct} distinct, depth {depth}"),
            "{path}"
        );
    }
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

//! The counterexamples tla-trace dumps, against what TLC's `-dumpTrace tlc` and `-dumpTrace json`
//! wrote for the same specs (tests/dump, from a jar built at tlaplus d8fb231): the gzipped
//! serialization byte for byte but for the tokens of its strings, and the JSON byte for byte.
//! Each spec is lowered by tla-front and searched by the engine, as the binary does.

#[path = "dump/payload.rs"]
mod payload;

use std::path::PathBuf;

use payload::{compare_dumps, compare_values};
use tla_engine::search::{Reporter, SearchOutcome, Settings, ViolationKind, search};
use tla_front::config::parse_config;
use tla_front::model::{ModelOptions, lower_front_ranking};
use tla_trace::{CounterExample, Ending, Rebuilder, Registers, add_actions};
use tla_values::{Id, Store};

struct Quiet;

impl Reporter for Quiet {
    fn initial_states_started(&mut self) {}
    fn initial_states_progress(&mut self, _count: u64) {}
    fn initial_states(&mut self, _generated: u64, _distinct: u64) {}
    fn progress(&mut self, _generated: u64, _distinct: u64, _queued: u64, _depth: u64) {}
    fn print(&mut self, _store: &Store, _prints: &tla_engine::Prints) {}
}

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/dump")
        .join(name)
}

/// What tla-trace dumps of the spec's counterexample: the `-dumpTrace tlc` file and the
/// `-dumpTrace json` one, written in the order the command line gives them, as TLC writes them.
/// The spec is lowered as the binary lowers it, with the strings its constant definitions make
/// ranked as TLC interns them.
fn dump(spec: &str, is_json_first: bool) -> (Vec<u8>, String) {
    let config = std::fs::read_to_string(fixture(&format!("{spec}.cfg"))).expect("a configuration");
    let get_startup_texts = |ir: &tla_ir::Ir, definitions: &[tla_ir::Index], interned: usize| {
        tla_values::on_nesting_stack(|| tla_trace::get_startup_texts(ir, definitions, interned))
    };
    let bytes = lower_front_ranking(
        &fixture(&format!("{spec}.tla")),
        &config,
        &ModelOptions {
            libraries: &[],
            version: None,
            is_warning_enabled: true,
            is_spec_described: true,
            random_seed: 0,
            root_extendees: &[],
        },
        &get_startup_texts,
    )
    .map(|lowered| lowered.ir)
    .expect("a model tla-front lowers");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    // The binary splits TLC's actions as it checks a model.
    let ir = tla_values::on_nesting_stack(|| add_actions(&ir)).expect("TLC's actions");
    let model = parse_config(&config, tla_front::TlcVersion::Master).expect("a configuration");
    let model_values = model.get_model_values();
    tla_values::on_nesting_stack(|| {
        let settings = Settings {
            is_violation_reported: true,
            ..Settings::default()
        };
        let violation = match search(&ir, &settings, &mut Quiet) {
            SearchOutcome::Stopped {
                violation: Some(violation),
                ..
            }
            | SearchOutcome::Complete {
                violation: Some(violation),
                ..
            } => violation,
            _ => panic!("a search that finds a violation"),
        };
        let mut rebuilder = Rebuilder::new(&ir).expect("a rebuilder");
        rebuilder
            .set_startup(
                &violation.store,
                &violation.startup,
                violation.startup_random,
            )
            .expect("startup values");
        rebuilder.set_registers(
            Registers::from_store(
                &violation.store,
                &violation.registers.numbered,
                &violation.registers.named,
            )
            .expect("registers"),
        );
        let states: Vec<&[Id]> = violation.states.iter().map(Vec::as_slice).collect();
        let labels = &violation.labels;
        let (trace, cycle) = match violation.kind {
            ViolationKind::Invariant(_) | ViolationKind::InitialInvariant(_) => (
                rebuilder.rebuild_counter_example(&violation.store, &states, labels),
                None,
            ),
            ViolationKind::Deadlock { .. } => (
                rebuilder.rebuild(&violation.store, &states, labels, Ending::Kept),
                None,
            ),
            ViolationKind::Lasso {
                loop_start,
                loop_label,
                ..
            } => (
                rebuilder.rebuild(&violation.store, &states, labels, Ending::Lasso),
                Some((loop_start, loop_label)),
            ),
            _ => panic!("a violation with a trace"),
        };
        let trace = trace.expect("a trace that rebuilds");
        let dumped = rebuilder
            .dump_trace(
                &CounterExample {
                    trace: &trace,
                    cycle,
                },
                true,
                false,
                false,
            )
            .expect("a dump");
        let json = is_json_first.then(|| dumped.to_json().expect("a JSON dump"));
        let tlc = dumped.to_tlc(&model_values).expect("a tlc dump");
        let json = json.unwrap_or_else(|| dumped.to_json().expect("a JSON dump"));
        (tlc, json)
    })
}

// Each spec's dumps, against TLC's as `-dumpTrace tlc <spec>.bin -dumpTrace json <spec>.json`
// writes them, and as `-dumpTrace json <spec>.first.json -dumpTrace tlc <spec>.first.bin` does,
// where the JSON writes the records TLC hasn't sorted yet in the order they were written.
fn check(spec: &str) {
    for (is_json_first, name) in [(false, spec.to_owned()), (true, format!("{spec}.first"))] {
        let (tlc, json) = dump(spec, is_json_first);
        let expected = std::fs::read(fixture(&format!("{name}.bin"))).expect("TLC's dump");
        if let Err(difference) = compare_dumps(&expected, &tlc) {
            panic!("{name}.bin: {difference}");
        }
        let expected =
            std::fs::read_to_string(fixture(&format!("{name}.json"))).expect("TLC's JSON");
        assert_eq!(json, expected, "{name}.json");
    }
}

#[test]
fn compares_dumps_but_for_their_tokens() {
    // TLC's two runs of DumpValues intern `vars` and the trace's texts as different tokens.
    let read = |name: &str| std::fs::read(fixture(name)).expect("TLC's dump");
    let (sorted, first) = (read("DumpValues.bin"), read("DumpValues.first.bin"));
    assert_ne!(sorted, first);
    assert_eq!(compare_dumps(&sorted, &first), Ok(()));
    assert!(compare_dumps(&sorted, &read("DumpNested.bin")).is_err());
    // TLC's reader rebuilds the same value from both, and another from another trace's.
    assert_eq!(compare_values(&sorted, &first), Ok(()));
    assert!(compare_values(&sorted, &read("DumpNested.bin")).is_err());
}

#[test]
fn dumps_an_invariant_violation() {
    // Strings, records, model values, sets, functions over model values, tuples, an interval,
    // and strings that name variables, over a violation TLC finds again from the state it held.
    check("DumpValues");
}

#[test]
fn dumps_a_deadlock() {
    // Functions over strings and over tuples, a set of records whose field names a variable, and
    // a sequence growing step by step.
    check("DumpDeadlock");
}

#[test]
fn dumps_a_lasso() {
    // The step back into the cycle closes the action edges.
    check("DumpLasso");
}

#[test]
fn dumps_nested_values() {
    // Functions over intervals that aren't tuples, strings JSON escapes, sets of sets, and the
    // action's parameters, over a violation three states long.
    check("DumpNested");
}

#[test]
fn dumps_values_as_tlc_makes_them_once_or_again() {
    // A function into a record set TLC enumerates once for each argument, so no two share a
    // record; the empty sequence SubSeq gives and `\o` passes on, which is TLC's one; and the
    // strings DOMAIN makes of a record's fields, new each time.
    check("DumpShared");
}

#[test]
fn dumps_function_keys_with_unpaired_surrogates() {
    // Two keys that are each half of a different character stay apart, written as `?`, as TLC
    // keeps them as Java strings. The constant definitions make them as TLC starts, which ranks
    // them: two strings the search made, the engine couldn't order as TLC does, and declines.
    check("DumpSurrogate");
}

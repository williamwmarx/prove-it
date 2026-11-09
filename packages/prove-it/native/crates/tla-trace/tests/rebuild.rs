//! Rebuilds paths of the engine's search on the golden IRs of `tests/conformance/ir`: the search
//! stops partway, and the path to each of its last states, from the checkpoint's parents, must
//! rebuild to states equal to the search's.

use tla_engine::search::{Reporter, SearchOutcome, Settings, search};
use tla_trace::{Ending, Rebuilder, Unsupported, format_value};
use tla_values::transfer::decode_shared_states;
use tla_values::{Id, Store};

struct Quiet;

impl Reporter for Quiet {
    fn initial_states_started(&mut self) {}
    fn initial_states_progress(&mut self, _count: u64) {}
    fn initial_states(&mut self, _generated: u64, _distinct: u64) {}
    fn progress(&mut self, _generated: u64, _distinct: u64, _queued: u64, _depth: u64) {}
    fn print(&mut self, _store: &Store, _values: &[Id]) {}
}

fn ir_directory() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../tests/conformance/ir")
}

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

/// The search's states up to where it stopped, in a store of their own, with their parents, why
/// it stopped and the state it was expanding.
struct Stopped {
    store: Store,
    states: Vec<Vec<Id>>,
    parents: Vec<i32>,
    reason: String,
    expanding: usize,
}

fn stop_search(ir: &tla_ir::Ir, stop_at: Option<usize>) -> Option<Stopped> {
    let settings = Settings {
        stop_at,
        ..Settings::default()
    };
    let SearchOutcome::Stopped {
        reason,
        checkpoint: Some(checkpoint),
        ..
    } = search(ir, &settings, &mut Quiet)
    else {
        return None;
    };
    let width = ir.variables.len();
    let mut store = Store::new();
    let ranked: Vec<Vec<u16>> = ir.texts[..ir.ranked_count as usize]
        .iter()
        .map(|text| text.encode_utf16().collect())
        .collect();
    store.reset(ranked.iter().map(Vec::as_slice));
    let ids = decode_shared_states(&mut store, &checkpoint.states, width).ok()?;
    let states = if width == 0 {
        Vec::new()
    } else {
        ids.chunks(width).map(<[Id]>::to_vec).collect()
    };
    Some(Stopped {
        store,
        states,
        parents: checkpoint.parents.clone(),
        reason,
        expanding: checkpoint.expanding as usize,
    })
}

fn path_to(parents: &[i32], index: usize) -> Vec<usize> {
    let mut path = vec![index];
    while parents[path[0]] >= 0 {
        path.insert(0, parents[path[0]] as usize);
    }
    path
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
        // another state for it, so it rebuilds only as the search's own.
        rebuilder
            .rebuild(
                &stopped.store,
                &states,
                &vec![None; states.len() - 1],
                Ending::Violation,
            )
            .map_err(|Unsupported(reason)| format!("state {index} as a violation: {reason}"))?;
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

fn deadlock_trace(path: &str) -> Vec<String> {
    let bytes = std::fs::read(ir_directory().join(format!("{path}.ir"))).expect("a golden IR");
    let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
    tla_values::on_nesting_stack(|| {
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
                rebuilder.rebuild(
                    &stopped.store,
                    &states,
                    &vec![None; states.len() - 1],
                    Ending::Kept,
                )
            })
            .expect("a trace the evaluator rebuilds");
        trace
            .states
            .iter()
            .map(|state| rebuilt_state(&ir, &state.values))
            .collect()
    })
}

#[test]
fn rebuilds_deadlock_traces_as_tlc_prints_them() {
    assert_eq!(
        deadlock_trace("kafka/transactions/diary/01_InitPidRequest/tlaplus/kafka_transactions"),
        tlc_states(KAFKA_TRACE)
    );
    assert_eq!(
        deadlock_trace("tlc/tlatools/org.lamport.tlatools/test-model/TLCGetLevel"),
        tlc_states(TLC_GET_LEVEL_TRACE)
    );
}

//! `check(ir, settings, stateLog, report, print)`'s settings, the calls it makes as the search
//! reports, and what it returns, as `src/engine/native.ts` reads them:
//!
//! - `report(kind, a, b, c, d, e)` for each thing the search reports as it runs: 0 the initial
//!   states started, 1 a count of initial states, 2 the initial states (generated, distinct), 3
//!   progress (generated, distinct, queued, depth), 4 a check of the temporal properties part way
//!   through the search (branches, expanded, generated, distinct, depth) and 5 its end; and
//!   `print(width, words, strings)` for what Print or PrintT printed, `width` values in
//!   `transfer.ts`'s encoding.
//! - `settings` is an Int32Array: whether the memo tables are off, whether epoch caches are
//!   checked, the state to stop before (-1 for none), whether fingerprints are verified, whether
//!   the liveness answers are checked (PROVE_IT_LIVE_CHECK), the threads, the lowest level the
//!   threads share, whether liveness is checked periodically, and the state to test the liveness
//!   check at (-1 for none). `stateLog` is the file to write the state log to, or "".
//! - It returns `{ status: "declined", reason }`; `{ status: "complete", counts, outDegrees,
//!   fingerprints[, liveness, checkpoint] }`, with `counts` the generated, distinct and initial
//!   counts, the depth, the values, the most threads a level was shared between, the queued
//!   states and the collisions, and with temporal properties what checking them found, `{ status:
//!   "holds" | "lasso" | "accepted" | "declined", reason, path, loopStart, state,
//!   isCycleConstrained, violated, branches }`, and the checkpoint of the whole search unless they
//!   hold; `{ status: "stopped", reason, counts, outDegrees, parents, words, strings, states[,
//!   keyWords, keyStrings, keyStates, keyWidth] }`, with `counts` the state being expanded, the
//!   states before it, the generated and initial generated counts and the collisions, and the
//!   states and keys as the table of their values in `transfer.ts`'s encoding, each value once
//!   with its parts by position, and each state's values by position in it (`SharedStates`), and
//!   with temporal properties `graph`; or, for a stop that hands over no checkpoint, `{ status:
//!   "stopped", reason, counts }` with only the collisions; or `{ status: "invariant", reason }`
//!   where a self-check failed.
//! - A graph is `{ expanded, counts, edges, labels?, initialCounts, isEnabledExact, tables,
//!   fromSteps, unknown }`: `counts` each expanded state's successors, new states and edge offset
//!   (with one more offset), `tables` a Uint8Array per atom of the liveness checker, `fromSteps`
//!   whether each ENABLED atom is answered from the steps, and `unknown` why the engine answers an
//!   atom not at all, or "".

use tla_engine::Options;
use tla_engine::search::{
    Checkpoint, GraphCheckpoint, MINIMUM_SHARED_LEVEL, SearchOutcome, Settings,
};
use tla_live::{Liveness, Verdict};
use tla_values::transfer::{EncodedStates, SharedStates};

use crate::Event;
use crate::value::HostValue;

/// The settings the Int32Array gives, and the state log's file.
pub fn get_settings(words: &[i32], state_log: String) -> Result<Settings, String> {
    let [
        memo_off,
        epoch_checked,
        stop_at,
        fingerprint_verified,
        live_checked,
        threads,
        minimum_shared_level,
        liveness_periodic,
        test_live_check_at,
    ] = words[..]
    else {
        return Err("the settings must hold nine numbers".into());
    };
    Ok(Settings {
        compile: Options {
            is_memo_off: memo_off != 0,
            is_epoch_checked: epoch_checked != 0,
        },
        stop_at: usize::try_from(stop_at).ok(),
        is_fingerprint_verified: fingerprint_verified != 0,
        state_log: (!state_log.is_empty()).then_some(state_log),
        is_live_checked: live_checked != 0,
        threads: usize::try_from(threads).unwrap_or(1).max(1),
        // The engine declines TLCGet("config") here.
        workers: 1,
        minimum_shared_level: usize::try_from(minimum_shared_level).unwrap_or(MINIMUM_SHARED_LEVEL),
        // The interpreter reports a violation itself.
        is_violation_reported: false,
        is_liveness_periodic: liveness_periodic != 0,
        test_live_check_at: usize::try_from(test_live_check_at).ok(),
    })
}

/// The call a search's event makes: `report(kind, a, b, c, d, e)`, or `print(width, words,
/// strings)`.
pub enum EventCall {
    Report([f64; 6]),
    Print(f64, EncodedStates),
}

pub fn get_event_call(event: Event) -> EventCall {
    let report = |values: [u64; 6]| EventCall::Report(values.map(|value| value as f64));
    match event {
        Event::InitialStatesStarted => report([0; 6]),
        Event::InitialStatesProgress(count) => report([1, count, 0, 0, 0, 0]),
        Event::InitialStates(generated, distinct) => report([2, generated, distinct, 0, 0, 0]),
        Event::Progress(generated, distinct, queued, depth) => {
            report([3, generated, distinct, queued, depth, 0])
        }
        Event::LivenessStarted(branches, expanded, [generated, distinct, depth]) => {
            report([4, branches, expanded, generated, distinct, depth])
        }
        Event::LivenessFinished => report([5, 0, 0, 0, 0, 0]),
        Event::Print(values, width) => EventCall::Print(width as f64, values),
    }
}

/// What each _POSSIBLE predicate counted, or -1 where it wasn't evaluated.
fn get_possible(counts: &[i64]) -> HostValue {
    HostValue::Float64s(counts.iter().map(|&count| count as f64).collect())
}

fn get_shared(
    properties: &mut Vec<(&'static str, HostValue)>,
    names: [&'static str; 3],
    shared: &SharedStates,
) {
    let [words, strings, states] = names;
    properties.push((words, HostValue::Int32s(shared.values.words.clone())));
    properties.push((strings, HostValue::texts(&shared.values.strings)));
    properties.push((states, HostValue::Int32s(shared.states.clone())));
}

/// A checkpoint's properties, as above.
fn get_checkpoint(
    properties: &mut Vec<(&'static str, HostValue)>,
    checkpoint: &Checkpoint,
    collisions: u64,
) {
    let numbers = [
        checkpoint.expanding,
        checkpoint.count,
        checkpoint.generated,
        checkpoint.initial_generated,
        collisions,
    ];
    properties.push(("counts", HostValue::counts(&numbers)));
    properties.push(("possible", get_possible(&checkpoint.possible)));
    properties.push(("outDegrees", HostValue::counts(&checkpoint.out_degrees)));
    properties.push(("parents", HostValue::Int32s(checkpoint.parents.clone())));
    get_shared(
        properties,
        ["words", "strings", "states"],
        &checkpoint.states,
    );
    if let Some((keys, key_width)) = &checkpoint.keys {
        get_shared(properties, ["keyWords", "keyStrings", "keyStates"], keys);
        properties.push(("keyWidth", HostValue::Number(f64::from(*key_width))));
    }
    if let Some(graph) = &checkpoint.graph {
        properties.push(("graph", get_graph(graph)));
    }
}

/// What checking the temporal properties found, `branches` -1 where the check declined before
/// it knew them.
fn get_verdict(liveness: &Liveness) -> HostValue {
    let violated = match &liveness.verdict {
        Verdict::Lasso { violated, .. } => {
            violated.iter().map(|&position| position as i32).collect()
        }
        _ => Vec::new(),
    };
    let (kind, reason, path, loop_start, state, is_cycle_constrained) = match &liveness.verdict {
        Verdict::Holds => ("holds", "", &[][..], 0, 0, false),
        Verdict::Lasso {
            path,
            loop_start,
            is_cycle_constrained,
            ..
        } => (
            "lasso",
            "",
            &path[..],
            *loop_start,
            0,
            *is_cycle_constrained,
        ),
        Verdict::Accepted { state, path, .. } => ("accepted", "", &path[..], 0, *state, false),
        Verdict::Declined(declined) => ("declined", declined.0.as_str(), &[][..], 0, 0, false),
        Verdict::Unexpanded => ("declined", tla_live::UNEXPANDED, &[][..], 0, 0, false),
    };
    HostValue::Object(vec![
        ("status", HostValue::text(kind)),
        ("reason", HostValue::text(reason)),
        ("path", HostValue::words(path)),
        ("loopStart", HostValue::Number(loop_start as f64)),
        ("state", HostValue::Number(f64::from(state))),
        ("violated", HostValue::Int32s(violated)),
        (
            "branches",
            HostValue::Number(liveness.branches.map_or(-1.0, |branches| branches as f64)),
        ),
        (
            "isCycleConstrained",
            HostValue::Number(f64::from(u8::from(is_cycle_constrained))),
        ),
    ])
}

fn get_graph(graph: &GraphCheckpoint) -> HostValue {
    let mut counts = graph.successor_counts.clone();
    counts.extend(&graph.new_counts);
    counts.extend(&graph.edge_offsets);
    let mut properties = vec![
        ("expanded", HostValue::Number(graph.expanded as f64)),
        ("counts", HostValue::words(&counts)),
        ("edges", HostValue::words(&graph.edges)),
    ];
    if let Some(labels) = &graph.labels {
        properties.push(("labels", HostValue::words(labels)));
    }
    properties.push(("initialCounts", HostValue::counts(&graph.initial_counts)));
    properties.push((
        "isEnabledExact",
        HostValue::Number(f64::from(u8::from(graph.is_enabled_exact))),
    ));
    let tables = graph
        .tables
        .iter()
        .map(|table| HostValue::Uint8s(table.answers.clone()))
        .collect();
    let unknown: Vec<Vec<u16>> = graph
        .tables
        .iter()
        .map(|table| {
            table
                .unknown
                .as_deref()
                .unwrap_or("")
                .encode_utf16()
                .collect()
        })
        .collect();
    let from_steps = graph
        .tables
        .iter()
        .map(|table| f64::from(u8::from(table.is_from_steps)))
        .collect();
    properties.push(("tables", HostValue::Array(tables)));
    properties.push(("unknown", HostValue::texts(&unknown)));
    properties.push(("fromSteps", HostValue::Float64s(from_steps)));
    HostValue::Object(properties)
}

/// What `check` returns for the search's outcome.
pub fn get_outcome(outcome: &SearchOutcome) -> HostValue {
    let declined = |reason: &str| {
        HostValue::Object(vec![
            ("status", HostValue::text("declined")),
            ("reason", HostValue::text(reason)),
        ])
    };
    match outcome {
        SearchOutcome::Declined(reason) => declined(reason),
        // The search doesn't report violations here, so it declines an assumption that fails to
        // evaluate rather than report it.
        SearchOutcome::AssumptionFailed { .. } => {
            declined("an assumption's failure reported without is_violation_reported")
        }
        // The interpreter rejects the configuration before it hands the search over.
        SearchOutcome::ConfigError { message } => declined(message),
        // The interpreter checks the assumptions before it hands the search over.
        SearchOutcome::AssumptionViolated { name } => {
            declined(&format!("the assumption {name} is false"))
        }
        SearchOutcome::Complete {
            counts,
            checkpoint,
            liveness,
            lasso_actions,
            fingerprints,
            value_count,
            threads,
            collisions,
            possible,
            // The interpreter prints a lasso.
            violation: _,
            registers: _,
        } => {
            let mut properties = vec![("possible", get_possible(possible))];
            if let Some(verdict) = liveness {
                properties.push(("liveness", get_verdict(verdict)));
            }
            let actions = lasso_actions
                .iter()
                .map(|action| action.map_or(-1, |position| position as i32))
                .collect();
            properties.push(("lassoActions", HostValue::Int32s(actions)));
            if let Some(checkpoint) = checkpoint {
                let mut handed = Vec::new();
                get_checkpoint(&mut handed, checkpoint, *collisions);
                properties.push(("checkpoint", HostValue::Object(handed)));
            }
            properties.push(("status", HostValue::text("complete")));
            properties.push(("reason", HostValue::text("")));
            let numbers = [
                counts.generated,
                counts.distinct,
                counts.initial_generated,
                counts.initial_distinct,
                counts.depth,
                *value_count as u64,
                *threads as u64,
                counts.queued,
                *collisions,
            ];
            properties.push(("counts", HostValue::counts(&numbers)));
            properties.push(("outDegrees", HostValue::counts(&counts.out_degrees)));
            properties.push((
                "fingerprints",
                HostValue::BigInt64s(fingerprints.iter().map(|&value| value as i64).collect()),
            ));
            HostValue::Object(properties)
        }
        SearchOutcome::Stopped {
            reason,
            checkpoint,
            collisions,
            ..
        } => {
            let mut properties = vec![
                ("status", HostValue::text("stopped")),
                ("reason", HostValue::text(reason)),
            ];
            match checkpoint {
                Some(checkpoint) => get_checkpoint(&mut properties, checkpoint, *collisions),
                None => properties.push(("counts", HostValue::Float64s(vec![*collisions as f64]))),
            }
            HostValue::Object(properties)
        }
        SearchOutcome::Invariant(reason) => HostValue::Object(vec![
            ("status", HostValue::text("invariant")),
            ("reason", HostValue::text(reason)),
        ]),
    }
}

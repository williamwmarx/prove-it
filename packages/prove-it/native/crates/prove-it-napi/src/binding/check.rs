//! `check(ir, settings, stateLog, report, print)`: searches the model the engine IR describes, on a
//! thread with a deep stack, and calls `report(kind, a, b, c, d)` on the calling thread for each
//! thing the search reports as it runs: 0 the initial states started, 1 a count of initial states,
//! 2 the initial states (generated, distinct), 3 progress (generated, distinct, queued, depth); and
//! `print(width, words, strings)` for what Print or PrintT printed, `width` values in
//! `transfer.ts`'s encoding.
//!
//! `settings` is an Int32Array: whether the memo tables are off, whether epoch caches are checked,
//! the state to stop before (-1 for none), whether fingerprints are verified, and whether the
//! liveness answers are checked (PROVE_IT_LIVE_CHECK). `stateLog` is
//! the file to write the state log to, or "". It returns:
//! - `{ status: "declined", reason }`;
//! - `{ status: "complete", counts, outDegrees, fingerprints[, liveness, checkpoint] }`, with
//!   `counts` a Float64Array of the generated, distinct and initial counts, the depth, the values,
//!   the most threads a level was shared between and the collisions, and with temporal properties what checking them found, `{ status:
//!   "holds" | "lasso" | "accepted" | "declined", reason, path, loopStart, state,
//!   isCycleConstrained, violated, branches }`, and the checkpoint of the whole search unless they hold;
//! - `{ status: "stopped", reason, counts, outDegrees, parents, words, strings, states[,
//!   keyWords, keyStrings, keyStates, keyWidth] }`, with `counts` the state being expanded, the
//!   states before it, the generated and initial generated counts and the collisions, and the
//!   states and keys as the table of their values in `transfer.ts`'s encoding, each value once
//!   with its parts by position, and each state's values by position in it (`SharedStates`), and
//!   with temporal properties `graph`; or, for a stop that hands over no checkpoint,
//!   `{ status: "stopped", reason, counts }` with only the collisions;
//! - `{ status: "invariant", reason }` where a self-check failed.
//!
//! A graph is `{ expanded, counts, edges, labels?, initialCounts, isEnabledExact, tables,
//! fromSteps, unknown }`: `counts` an Int32Array of each expanded state's successors, new states
//! and edge offset (with one more offset), `tables` a Uint8Array per atom of the liveness
//! checker, `fromSteps` whether each ENABLED atom is answered from the steps, and `unknown` why
//! the engine answers an atom not at all, or "".

use std::ffi::{CStr, c_void};
use std::ptr::null_mut;

use crate::{Event, MINIMUM_SHARED_LEVEL, SearchOutcome, Settings, check_on_thread};
use tla_engine::Options;
use tla_engine::search::{Checkpoint, GraphCheckpoint};
use tla_live::{Liveness, Verdict};
use tla_values::transfer::{EncodedStates, SharedStates};

use super::store::{
    NAPI_BIGINT64_ARRAY, NAPI_STRING, create_int32s, create_number, create_text, get_arguments,
    get_int32s, get_text, napi_create_array_with_length, napi_create_arraybuffer,
    napi_create_typedarray, napi_set_element, type_of, wrong,
};
use super::{
    Thrown, create_string, guard, napi_callback_info, napi_create_object, napi_env, napi_status,
    napi_value, set_property, status,
};

const NAPI_UINT8_ARRAY: i32 = 1;
const NAPI_FLOAT64_ARRAY: i32 = 8;

napi_functions! {
    fn napi_get_undefined(env: napi_env, result: *mut napi_value) -> napi_status;
    fn napi_call_function(
        env: napi_env,
        recv: napi_value,
        function: napi_value,
        argc: usize,
        argv: *const napi_value,
        result: *mut napi_value,
    ) -> napi_status;
}

unsafe fn create_typed<T: Copy>(
    env: napi_env,
    kind: i32,
    values: &[T],
) -> Result<napi_value, Thrown> {
    let (mut data, mut buffer, mut result) = (null_mut::<c_void>(), null_mut(), null_mut());
    status(unsafe { napi_create_arraybuffer(env, size_of_val(values), &mut data, &mut buffer) })?;
    if !values.is_empty() {
        unsafe { std::slice::from_raw_parts_mut(data.cast::<T>(), values.len()) }
            .copy_from_slice(values);
    }
    status(unsafe { napi_create_typedarray(env, kind, values.len(), buffer, 0, &mut result) })?;
    Ok(result)
}

unsafe fn create_numbers(env: napi_env, values: &[f64]) -> Result<napi_value, Thrown> {
    unsafe { create_typed(env, NAPI_FLOAT64_ARRAY, values) }
}

unsafe fn create_texts(env: napi_env, texts: &[Vec<u16>]) -> Result<napi_value, Thrown> {
    let mut array = null_mut();
    status(unsafe { napi_create_array_with_length(env, texts.len(), &mut array) })?;
    for (index, text) in texts.iter().enumerate() {
        let value = unsafe { create_text(env, text) }?;
        status(unsafe { napi_set_element(env, array, index as u32, value) })?;
    }
    Ok(array)
}

unsafe fn set(
    env: napi_env,
    object: napi_value,
    name: &CStr,
    value: napi_value,
) -> Result<(), Thrown> {
    unsafe { set_property(env, object, name, value) }
}

unsafe fn set_encoded(
    env: napi_env,
    object: napi_value,
    words: &CStr,
    strings: &CStr,
    encoded: &EncodedStates,
) -> Result<(), Thrown> {
    unsafe {
        set(env, object, words, create_int32s(env, &encoded.words)?)?;
        set(env, object, strings, create_texts(env, &encoded.strings)?)
    }
}

// What each _POSSIBLE predicate counted, or -1 where it wasn't evaluated.
unsafe fn create_possible(env: napi_env, counts: &[i64]) -> Result<napi_value, Thrown> {
    let numbers: Vec<f64> = counts.iter().map(|&count| count as f64).collect();
    unsafe { create_numbers(env, &numbers) }
}

fn to_numbers(values: &[u64]) -> Vec<f64> {
    values.iter().map(|&value| value as f64).collect()
}

unsafe fn set_shared(
    env: napi_env,
    object: napi_value,
    [words, strings, states]: [&CStr; 3],
    shared: &SharedStates,
) -> Result<(), Thrown> {
    unsafe {
        set_encoded(env, object, words, strings, &shared.values)?;
        set(env, object, states, create_int32s(env, &shared.states)?)
    }
}

// Sets a checkpoint's properties, as above, on an object.
unsafe fn set_checkpoint(
    env: napi_env,
    object: napi_value,
    checkpoint: &Checkpoint,
    collisions: u64,
) -> Result<(), Thrown> {
    unsafe {
        let numbers = [
            checkpoint.expanding,
            checkpoint.count,
            checkpoint.generated,
            checkpoint.initial_generated,
            collisions,
        ];
        set(
            env,
            object,
            c"counts",
            create_numbers(env, &to_numbers(&numbers))?,
        )?;
        set(
            env,
            object,
            c"possible",
            create_possible(env, &checkpoint.possible)?,
        )?;
        set(
            env,
            object,
            c"outDegrees",
            create_numbers(env, &to_numbers(&checkpoint.out_degrees))?,
        )?;
        set(
            env,
            object,
            c"parents",
            create_int32s(env, &checkpoint.parents)?,
        )?;
        set_shared(
            env,
            object,
            [c"words", c"strings", c"states"],
            &checkpoint.states,
        )?;
        if let Some((keys, key_width)) = &checkpoint.keys {
            set_shared(
                env,
                object,
                [c"keyWords", c"keyStrings", c"keyStates"],
                keys,
            )?;
            set(
                env,
                object,
                c"keyWidth",
                create_number(env, f64::from(*key_width))?,
            )?;
        }
        if let Some(graph) = &checkpoint.graph {
            set(env, object, c"graph", create_graph(env, graph)?)?;
        }
        Ok(())
    }
}

// What checking the temporal properties found: `{ status, reason, path, loopStart, state,
// isCycleConstrained, violated, branches }`, `branches` -1 where the check declined before it
// knew them.
unsafe fn create_verdict(env: napi_env, liveness: &Liveness) -> Result<napi_value, Thrown> {
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
        Verdict::Accepted { state, path } => ("accepted", "", &path[..], 0, *state, false),
        Verdict::Declined(declined) => ("declined", declined.0.as_str(), &[][..], 0, 0, false),
        Verdict::Unexpanded => ("declined", tla_live::UNEXPANDED, &[][..], 0, 0, false),
    };
    unsafe {
        let mut object = null_mut();
        status(napi_create_object(env, &mut object))?;
        set(env, object, c"status", create_string(env, kind)?)?;
        set(env, object, c"reason", create_string(env, reason)?)?;
        set(env, object, c"path", create_int32s(env, &to_words(path))?)?;
        set(
            env,
            object,
            c"loopStart",
            create_number(env, loop_start as f64)?,
        )?;
        set(env, object, c"state", create_number(env, f64::from(state))?)?;
        set(env, object, c"violated", create_int32s(env, &violated)?)?;
        set(
            env,
            object,
            c"branches",
            create_number(
                env,
                liveness.branches.map_or(-1.0, |branches| branches as f64),
            )?,
        )?;
        set(
            env,
            object,
            c"isCycleConstrained",
            create_number(env, f64::from(u8::from(is_cycle_constrained)))?,
        )?;
        Ok(object)
    }
}

fn to_words(values: &[u32]) -> Vec<i32> {
    values.iter().map(|&value| value as i32).collect()
}

unsafe fn create_graph(env: napi_env, graph: &GraphCheckpoint) -> Result<napi_value, Thrown> {
    unsafe {
        let mut object = null_mut();
        status(napi_create_object(env, &mut object))?;
        set(
            env,
            object,
            c"expanded",
            create_number(env, graph.expanded as f64)?,
        )?;
        let mut counts = to_words(&graph.successor_counts);
        counts.extend(to_words(&graph.new_counts));
        counts.extend(to_words(&graph.edge_offsets));
        set(env, object, c"counts", create_int32s(env, &counts)?)?;
        set(
            env,
            object,
            c"edges",
            create_int32s(env, &to_words(&graph.edges))?,
        )?;
        if let Some(labels) = &graph.labels {
            set(
                env,
                object,
                c"labels",
                create_int32s(env, &to_words(labels))?,
            )?;
        }
        set(
            env,
            object,
            c"initialCounts",
            create_numbers(env, &to_numbers(&graph.initial_counts))?,
        )?;
        set(
            env,
            object,
            c"isEnabledExact",
            create_number(env, f64::from(u8::from(graph.is_enabled_exact)))?,
        )?;
        let mut tables = null_mut();
        status(napi_create_array_with_length(
            env,
            graph.tables.len(),
            &mut tables,
        ))?;
        let mut unknown = Vec::with_capacity(graph.tables.len());
        let mut from_steps = Vec::with_capacity(graph.tables.len());
        for (index, table) in graph.tables.iter().enumerate() {
            let answers = create_typed(env, NAPI_UINT8_ARRAY, &table.answers)?;
            status(napi_set_element(env, tables, index as u32, answers))?;
            unknown.push(
                table
                    .unknown
                    .as_deref()
                    .unwrap_or("")
                    .encode_utf16()
                    .collect::<Vec<u16>>(),
            );
            from_steps.push(f64::from(u8::from(table.is_from_steps)));
        }
        set(env, object, c"tables", tables)?;
        set(env, object, c"unknown", create_texts(env, &unknown)?)?;
        set(env, object, c"fromSteps", create_numbers(env, &from_steps)?)?;
        Ok(object)
    }
}

// check(ir: Uint8Array, settings: Int32Array, stateLog: string, report: Function)
pub(super) unsafe extern "C" fn check_model(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let [ir, settings, state_log, report, print] = get_arguments::<5>(env, info)?;
            let bytes = super::get_bytes(env, ir)?;
            let words = get_int32s(env, settings, "the settings")?;
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
                return Err(wrong("the settings must hold nine numbers".into()));
            };
            if type_of(env, state_log)? != NAPI_STRING {
                return Err(wrong("the state log must be a string".into()));
            }
            let state_log = String::from_utf16_lossy(&get_text(env, state_log)?);
            let settings = Settings {
                compile: Options {
                    is_memo_off: memo_off != 0,
                    is_epoch_checked: epoch_checked != 0,
                },
                stop_at: usize::try_from(stop_at).ok(),
                is_fingerprint_verified: fingerprint_verified != 0,
                state_log: (!state_log.is_empty()).then_some(state_log),
                is_live_checked: live_checked != 0,
                threads: usize::try_from(threads).unwrap_or(1).max(1),
                minimum_shared_level: usize::try_from(minimum_shared_level)
                    .unwrap_or(MINIMUM_SHARED_LEVEL),
                // The interpreter reports a violation itself.
                is_violation_reported: false,
                is_liveness_periodic: liveness_periodic != 0,
                test_live_check_at: usize::try_from(test_live_check_at).ok(),
            };
            let mut undefined = null_mut();
            status(napi_get_undefined(env, &mut undefined))?;
            // A callback that throws leaves its exception pending, and the rest aren't called.
            let mut is_thrown = false;
            let outcome = check_on_thread(bytes, &settings, |event| {
                if is_thrown {
                    return;
                }
                let numbers = |values: [u64; 6]| -> Result<Vec<napi_value>, Thrown> {
                    values
                        .iter()
                        .map(|&value| create_number(env, value as f64))
                        .collect()
                };
                let call = match event {
                    Event::InitialStatesStarted => numbers([0; 6]).map(|argv| (report, argv)),
                    Event::InitialStatesProgress(count) => {
                        numbers([1, count, 0, 0, 0, 0]).map(|argv| (report, argv))
                    }
                    Event::InitialStates(generated, distinct) => {
                        numbers([2, generated, distinct, 0, 0, 0]).map(|argv| (report, argv))
                    }
                    Event::Progress(generated, distinct, queued, depth) => {
                        numbers([3, generated, distinct, queued, depth, 0])
                            .map(|argv| (report, argv))
                    }
                    Event::LivenessStarted(branches, expanded, [generated, distinct, depth]) => {
                        numbers([4, branches, expanded, generated, distinct, depth])
                            .map(|argv| (report, argv))
                    }
                    Event::LivenessFinished => {
                        numbers([5, 0, 0, 0, 0, 0]).map(|argv| (report, argv))
                    }
                    Event::Print(values, width) => (|| {
                        Ok((
                            print,
                            vec![
                                create_number(env, width as f64)?,
                                create_int32s(env, &values.words)?,
                                create_texts(env, &values.strings)?,
                            ],
                        ))
                    })(),
                };
                let mut result = null_mut();
                is_thrown = match call {
                    Ok((function, argv)) => status(napi_call_function(
                        env,
                        undefined,
                        function,
                        argv.len(),
                        argv.as_ptr(),
                        &mut result,
                    ))
                    .is_err(),
                    Err(_) => true,
                };
            });
            if is_thrown {
                return Ok(null_mut());
            }
            let mut result = null_mut();
            status(napi_create_object(env, &mut result))?;
            match outcome {
                SearchOutcome::Declined(reason) => {
                    set(env, result, c"status", create_string(env, "declined")?)?;
                    set(env, result, c"reason", create_string(env, &reason)?)?;
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
                } => {
                    set(env, result, c"possible", create_possible(env, &possible)?)?;
                    if let Some(verdict) = &liveness {
                        set(env, result, c"liveness", create_verdict(env, verdict)?)?;
                    }
                    let actions: Vec<i32> = lasso_actions
                        .iter()
                        .map(|action| action.map_or(-1, |position| position as i32))
                        .collect();
                    set(env, result, c"lassoActions", create_int32s(env, &actions)?)?;
                    if let Some(checkpoint) = &checkpoint {
                        let mut object = null_mut();
                        status(napi_create_object(env, &mut object))?;
                        set_checkpoint(env, object, checkpoint, collisions)?;
                        set(env, result, c"checkpoint", object)?;
                    }
                    set(env, result, c"status", create_string(env, "complete")?)?;
                    set(env, result, c"reason", create_string(env, "")?)?;
                    let numbers = [
                        counts.generated,
                        counts.distinct,
                        counts.initial_generated,
                        counts.initial_distinct,
                        counts.depth,
                        value_count as u64,
                        threads as u64,
                        counts.queued,
                        collisions,
                    ];
                    set(
                        env,
                        result,
                        c"counts",
                        create_numbers(env, &to_numbers(&numbers))?,
                    )?;
                    set(
                        env,
                        result,
                        c"outDegrees",
                        create_numbers(env, &to_numbers(&counts.out_degrees))?,
                    )?;
                    set(
                        env,
                        result,
                        c"fingerprints",
                        create_typed(env, NAPI_BIGINT64_ARRAY, &fingerprints)?,
                    )?;
                }
                SearchOutcome::Stopped {
                    reason,
                    checkpoint,
                    collisions,
                    ..
                } => {
                    set(env, result, c"status", create_string(env, "stopped")?)?;
                    set(env, result, c"reason", create_string(env, &reason)?)?;
                    match &checkpoint {
                        Some(checkpoint) => set_checkpoint(env, result, checkpoint, collisions)?,
                        None => set(
                            env,
                            result,
                            c"counts",
                            create_numbers(env, &[collisions as f64])?,
                        )?,
                    }
                }
                SearchOutcome::Invariant(reason) => {
                    set(env, result, c"status", create_string(env, "invariant")?)?;
                    set(env, result, c"reason", create_string(env, &reason)?)?;
                }
            }
            Ok(result)
        })
    }
}

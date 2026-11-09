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
//! - `{ status: "complete", counts, outDegrees, fingerprints[, checkpoint] }`, with `counts` a
//!   Float64Array of the generated, distinct and initial counts, the depth, the values and the
//!   collisions, and with temporal properties the checkpoint of the whole search;
//! - `{ status: "stopped", reason, counts, outDegrees, parents, words, strings, states[,
//!   keyWords, keyStrings, keyStates, keyWidth] }`, with `counts` the state being expanded, the
//!   states before it, the generated and initial generated counts and the collisions, and the
//!   states and keys as the table of their values in `transfer.ts`'s encoding, each value once
//!   with its parts by position, and each state's values by position in it (`SharedStates`), and
//!   with temporal properties `graph`; or, for a stop that hands over no checkpoint,
//!   `{ status: "stopped", reason, counts }` with only the collisions;
//! - `ranked` on both, the texts the search ranked, such as ToString's, in the order it ranked
//!   them, for the interpreter to rank before it reads the states;
//! - `{ status: "invariant", reason }` where a self-check failed.
//!
//! A graph is `{ expanded, counts, edges, labels?, initialCounts, isEnabledExact, tables,
//! fromSteps, unknown }`: `counts` an Int32Array of each expanded state's successors, new states
//! and edge offset (with one more offset), `tables` a Uint8Array per atom of the liveness
//! checker, `fromSteps` whether each ENABLED atom is answered from the steps, and `unknown` why
//! the engine answers an atom not at all, or "".

use std::ffi::{CStr, c_void};
use std::ptr::null_mut;

use crate::{Event, SearchOutcome, Settings, check_on_thread};
use tla_engine::Options;
use tla_engine::search::{Checkpoint, GraphCheckpoint};
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

unsafe extern "C" {
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
            ] = words[..]
            else {
                return Err(wrong("the settings must hold five numbers".into()));
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
            };
            let mut undefined = null_mut();
            status(napi_get_undefined(env, &mut undefined))?;
            // A callback that throws leaves its exception pending, and the rest aren't called.
            let mut is_thrown = false;
            let outcome = check_on_thread(bytes, &settings, |event| {
                if is_thrown {
                    return;
                }
                let numbers = |values: [u64; 5]| -> Result<Vec<napi_value>, Thrown> {
                    values
                        .iter()
                        .map(|&value| create_number(env, value as f64))
                        .collect()
                };
                let call = match event {
                    Event::InitialStatesStarted => numbers([0; 5]).map(|argv| (report, argv)),
                    Event::InitialStatesProgress(count) => {
                        numbers([1, count, 0, 0, 0]).map(|argv| (report, argv))
                    }
                    Event::InitialStates(generated, distinct) => {
                        numbers([2, generated, distinct, 0, 0]).map(|argv| (report, argv))
                    }
                    Event::Progress(generated, distinct, queued, depth) => {
                        numbers([3, generated, distinct, queued, depth]).map(|argv| (report, argv))
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
                    fingerprints,
                    value_count,
                    collisions,
                    ranked,
                } => {
                    set(env, result, c"ranked", create_texts(env, &ranked)?)?;
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
                    ranked,
                } => {
                    set(env, result, c"ranked", create_texts(env, &ranked)?)?;
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

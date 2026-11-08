//! `check(ir, settings, stateLog, report)`: searches the model the engine IR describes, on a thread
//! with a deep stack, and calls `report(kind, a, b, c, d)` on the calling thread for each thing the
//! search reports as it runs: 0 the initial states started, 1 a count of initial states, 2 the
//! initial states (generated, distinct), 3 progress (generated, distinct, queued, depth).
//!
//! `settings` is an Int32Array: whether the memo tables are off, whether epoch caches are checked,
//! the state to stop before (-1 for none), and whether fingerprints are verified. `stateLog` is
//! the file to write the state log to, or "". It returns:
//! - `{ status: "declined", reason }`;
//! - `{ status: "complete", counts, outDegrees, fingerprints }`, with `counts` a Float64Array of
//!   the generated, distinct and initial counts, the depth, the values and the collisions;
//! - `{ status: "stopped", reason, counts, outDegrees, parents, words, strings[, keyWords,
//!   keyStrings, keyWidth] }`, with `counts` the state being expanded, the states before it, the
//!   generated and initial generated counts and the collisions, and the states and keys in
//!   `transfer.ts`'s encoding; or, for a stop in the initial states, which hands over no
//!   checkpoint, `{ status: "stopped", reason, counts }` with only the collisions.

use std::ffi::{CStr, c_void};
use std::ptr::null_mut;

use crate::{Event, SearchOutcome, Settings, check_on_thread};
use tla_engine::Options;
use tla_values::transfer::EncodedStates;

use super::store::{
    NAPI_BIGINT64_ARRAY, NAPI_STRING, create_int32s, create_number, create_text, get_arguments,
    get_int32s, get_text, napi_create_array_with_length, napi_create_arraybuffer,
    napi_create_typedarray, napi_set_element, type_of, wrong,
};
use super::{
    Thrown, create_string, guard, napi_callback_info, napi_create_object, napi_env, napi_status,
    napi_value, set_property, status,
};

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

// check(ir: Uint8Array, settings: Int32Array, stateLog: string, report: Function)
pub(super) unsafe extern "C" fn check_model(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let [ir, settings, state_log, report] = get_arguments::<4>(env, info)?;
            let bytes = super::get_bytes(env, ir)?;
            let words = get_int32s(env, settings, "the settings")?;
            let [memo_off, epoch_checked, stop_at, fingerprint_verified] = words[..] else {
                return Err(wrong("the settings must hold four numbers".into()));
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
            };
            let mut undefined = null_mut();
            status(napi_get_undefined(env, &mut undefined))?;
            // A callback that throws leaves its exception pending, and the rest aren't called.
            let mut is_thrown = false;
            let outcome = check_on_thread(bytes, &settings, |event| {
                if is_thrown {
                    return;
                }
                let numbers: (f64, [u64; 4]) = match event {
                    Event::InitialStatesStarted => (0.0, [0; 4]),
                    Event::InitialStatesProgress(count) => (1.0, [count, 0, 0, 0]),
                    Event::InitialStates(generated, distinct) => (2.0, [generated, distinct, 0, 0]),
                    Event::Progress(generated, distinct, queued, depth) => {
                        (3.0, [generated, distinct, queued, depth])
                    }
                };
                let mut argv = [null_mut(); 5];
                let created = (|| -> Result<(), Thrown> {
                    argv[0] = create_number(env, numbers.0)?;
                    for (index, &value) in numbers.1.iter().enumerate() {
                        argv[index + 1] = create_number(env, value as f64)?;
                    }
                    Ok(())
                })();
                let mut result = null_mut();
                is_thrown = created.is_err()
                    || status(napi_call_function(
                        env,
                        undefined,
                        report,
                        argv.len(),
                        argv.as_ptr(),
                        &mut result,
                    ))
                    .is_err();
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
                    fingerprints,
                    value_count,
                    collisions,
                } => {
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
                } => {
                    set(env, result, c"status", create_string(env, "stopped")?)?;
                    set(env, result, c"reason", create_string(env, &reason)?)?;
                    let Some(checkpoint) = checkpoint else {
                        set(
                            env,
                            result,
                            c"counts",
                            create_numbers(env, &[collisions as f64])?,
                        )?;
                        return Ok(result);
                    };
                    let numbers = [
                        checkpoint.expanding,
                        checkpoint.count,
                        checkpoint.generated,
                        checkpoint.initial_generated,
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
                        create_numbers(env, &to_numbers(&checkpoint.out_degrees))?,
                    )?;
                    set(
                        env,
                        result,
                        c"parents",
                        create_int32s(env, &checkpoint.parents)?,
                    )?;
                    set_encoded(env, result, c"words", c"strings", &checkpoint.states)?;
                    if let Some((keys, key_width)) = &checkpoint.keys {
                        set_encoded(env, result, c"keyWords", c"keyStrings", keys)?;
                        set(
                            env,
                            result,
                            c"keyWidth",
                            create_number(env, f64::from(*key_width))?,
                        )?;
                    }
                }
            }
            Ok(result)
        })
    }
}

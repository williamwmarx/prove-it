//! The module's exports and imports, as `lib.rs` describes them.

use prove_it_host::hooks::{self, HookResult};
use prove_it_host::outcome::{EventCall, get_event_call, get_outcome, get_settings};
use prove_it_host::value::HostValue;
use prove_it_host::{ABI_VERSION, check_on_thread};
use tla_values::transfer::EncodedStates;

use crate::encoding::{decode, encode};

#[link(wasm_import_module = "env")]
unsafe extern "C" {
    fn prove_it_report(kind: f64, a: f64, b: f64, c: f64, d: f64, e: f64);
    fn prove_it_print(pointer: *const u8, length: usize);
}

const RESULT: u8 = 0;
const TYPE_ERROR: u8 = 1;

/// A buffer of `length` bytes, for the loader to write a call's arguments into.
#[unsafe(no_mangle)]
pub extern "C" fn prove_it_alloc(length: usize) -> *mut u8 {
    Box::into_raw(vec![0u8; length].into_boxed_slice()).cast()
}

/// Frees a buffer `prove_it_alloc` or a call returned.
///
/// # Safety
///
/// The buffer is one of those, of that length, and not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn prove_it_free(pointer: *mut u8, length: usize) {
    drop(unsafe { Box::from_raw(std::ptr::slice_from_raw_parts_mut(pointer, length)) });
}

#[unsafe(no_mangle)]
pub extern "C" fn prove_it_abi_version() -> i32 {
    ABI_VERSION
}

// Runs a call on the arguments in a buffer from `prove_it_alloc`, which it frees, and returns
// the buffer of its result.
unsafe fn call(
    pointer: *mut u8,
    length: usize,
    body: impl FnOnce(Vec<HostValue>) -> HookResult,
) -> *mut u8 {
    let bytes = unsafe { Box::from_raw(std::ptr::slice_from_raw_parts_mut(pointer, length)) };
    let result = match decode(&bytes) {
        Ok(HostValue::Array(arguments)) => body(arguments),
        Ok(_) => Err("the arguments must be an array".into()),
        Err(error) => Err(error),
    };
    let mut out = vec![0; 4];
    match result {
        Ok(value) => {
            out.push(RESULT);
            encode(&value, &mut out);
        }
        Err(message) => {
            out.push(TYPE_ERROR);
            encode(&HostValue::text(&message), &mut out);
        }
    }
    let rest = (out.len() - 4) as u32;
    out[..4].copy_from_slice(&rest.to_le_bytes());
    Box::into_raw(out.into_boxed_slice()).cast()
}

fn get<const N: usize>(arguments: Vec<HostValue>) -> [HostValue; N] {
    let mut arguments = arguments;
    arguments.resize(N, HostValue::Undefined);
    arguments.try_into().unwrap_or_else(|_| unreachable!())
}

fn get_int32s(value: HostValue, what: &str) -> Result<Vec<i32>, String> {
    match value {
        HostValue::Int32s(words) => Ok(words),
        _ => Err(format!("{what} must be an Int32Array")),
    }
}

fn get_index(value: &HostValue, what: &str) -> Result<usize, String> {
    match *value {
        HostValue::Number(number)
            if number >= 0.0 && number.fract() == 0.0 && number <= u32::MAX as f64 =>
        {
            Ok(number as usize)
        }
        _ => Err(format!("{what} must be a whole number")),
    }
}

fn get_text(value: HostValue, what: &str) -> Result<Vec<u16>, String> {
    match value {
        HostValue::Text(units) => Ok(units),
        _ => Err(format!("{what} must be a string")),
    }
}

/// `check(ir, settings, stateLog)`, which calls the imports as the search reports.
///
/// # Safety
///
/// The arguments are a buffer from `prove_it_alloc` of that length.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn prove_it_check(pointer: *mut u8, length: usize) -> *mut u8 {
    unsafe {
        call(pointer, length, |arguments| {
            let [ir, settings, state_log] = get(arguments);
            let HostValue::Uint8s(ir) = ir else {
                return Err("check takes the engine IR as a Uint8Array".into());
            };
            let words = get_int32s(settings, "the settings")?;
            let state_log = get_text(state_log, "the state log")?;
            let mut settings = get_settings(&words, String::from_utf16_lossy(&state_log))?;
            settings.threads = 1;
            let outcome = check_on_thread(&ir, &settings, |event| match get_event_call(event) {
                EventCall::Report([kind, a, b, c, d, e]) => prove_it_report(kind, a, b, c, d, e),
                EventCall::Print(width, values) => {
                    let mut out = Vec::new();
                    let printed = HostValue::Array(vec![
                        HostValue::Number(width),
                        HostValue::Int32s(values.words),
                        HostValue::texts(&values.strings),
                    ]);
                    encode(&printed, &mut out);
                    prove_it_print(out.as_ptr(), out.len());
                }
            });
            Ok(get_outcome(&outcome))
        })
    }
}

/// `sanyText(root, source, fileName, known)`, as prove-it-host's `sany` describes it.
///
/// # Safety
///
/// As for `prove_it_check`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn prove_it_sany_text(pointer: *mut u8, length: usize) -> *mut u8 {
    unsafe {
        call(pointer, length, |arguments| {
            prove_it_host::sany::sany_text(&get::<4>(arguments))
        })
    }
}

/// `checkSources(args, known, machine)`, as prove-it-host's `check` describes it.
///
/// # Safety
///
/// As for `prove_it_check`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn prove_it_check_sources(pointer: *mut u8, length: usize) -> *mut u8 {
    unsafe {
        call(pointer, length, |arguments| {
            prove_it_host::check::check_sources(&get::<3>(arguments))
        })
    }
}

/// `decide(prover, text, timeLimitMs, stepLimit)`, as prove-it-host's `prover` describes it. There
/// is no cancel cell: the decision runs on the thread that would set it.
///
/// # Safety
///
/// As for `prove_it_check`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn prove_it_decide(pointer: *mut u8, length: usize) -> *mut u8 {
    unsafe {
        call(pointer, length, |arguments| {
            prove_it_host::prover::decide(&get::<4>(arguments), None)
        })
    }
}

/// `storePerform(name, args)`.
///
/// # Safety
///
/// As for `prove_it_check`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn prove_it_store_perform(pointer: *mut u8, length: usize) -> *mut u8 {
    unsafe {
        call(pointer, length, |arguments| {
            let [name, list] = get(arguments);
            let name = get_text(name, "storePerform takes an operation's name; it")?;
            let HostValue::Array(elements) = list else {
                return Err("storePerform takes its arguments as an array".into());
            };
            let arguments = elements
                .iter()
                .map(hooks::get_argument)
                .collect::<Result<_, _>>()?;
            hooks::store_perform(String::from_utf16_lossy(&name), arguments)
        })
    }
}

/// `storeDecode(words, strings, width, count, ids)`, which returns the ids rather than write them.
///
/// # Safety
///
/// As for `prove_it_check`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn prove_it_store_decode(pointer: *mut u8, length: usize) -> *mut u8 {
    unsafe {
        call(pointer, length, |arguments| {
            let [words, strings, width, count, ids] = get(arguments);
            let HostValue::Array(strings) = strings else {
                return Err("strings must be an array of strings".into());
            };
            let encoded = EncodedStates {
                words: get_int32s(words, "words")?,
                strings: strings
                    .into_iter()
                    .map(|text| get_text(text, "each of strings"))
                    .collect::<Result<_, _>>()?,
                count: get_index(&count, "count")? as u32,
            };
            let width = get_index(&width, "width")?;
            let ids = get_int32s(ids, "ids")?;
            hooks::store_decode(encoded, width, ids.len())
        })
    }
}

/// `storeEncode(states, width)`.
///
/// # Safety
///
/// As for `prove_it_check`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn prove_it_store_encode(pointer: *mut u8, length: usize) -> *mut u8 {
    unsafe {
        call(pointer, length, |arguments| {
            let [states, width] = get(arguments);
            hooks::store_encode(get_int32s(states, "states")?, get_index(&width, "width")?)
        })
    }
}

/// `storeFingerprints(states, width, order, parents, isReference, fingerprints)`, which returns
/// the fingerprints rather than write them.
///
/// # Safety
///
/// As for `prove_it_check`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn prove_it_store_fingerprints(pointer: *mut u8, length: usize) -> *mut u8 {
    unsafe {
        call(pointer, length, |arguments| {
            let [states, width, order, parents, is_reference, out] = get(arguments);
            let parents = match parents {
                HostValue::Undefined | HostValue::Null => None,
                parents => Some(get_int32s(parents, "parents")?),
            };
            let HostValue::BigInt64s(out) = out else {
                return Err("fingerprints must be a BigInt64Array".into());
            };
            hooks::store_fingerprints(
                get_int32s(states, "states")?,
                get_index(&width, "width")?,
                &get_int32s(order, "order")?,
                parents,
                is_reference == HostValue::Bool(true),
                out.len(),
            )
        })
    }
}

/// `storeResetFingerprints()`.
///
/// # Safety
///
/// As for `prove_it_check`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn prove_it_store_reset_fingerprints(
    pointer: *mut u8,
    length: usize,
) -> *mut u8 {
    unsafe {
        call(pointer, length, |_| {
            hooks::store_reset_fingerprints();
            Ok(HostValue::Undefined)
        })
    }
}

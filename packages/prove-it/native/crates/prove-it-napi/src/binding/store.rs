//! Test hooks into the native store, for `src/engine/native-store.ts`, which gives the store's
//! tests and the value oracle the TypeScript store's functions over this one. The process has one
//! store, which each call runs on a thread with a stack for deeply nested values. A call costs what an N-API
//! call costs, which tests don't mind; the engine never crosses per value.
//!
//! - `storePerform(name, args)` runs an operation as a store trace names it, with ids as numbers,
//!   texts as strings and lists as arrays or Int32Arrays, and returns its number, boolean or
//!   null, or the reason the store stopped as a string;
//! - `storeDecode(words, strings, width, count, ids)` interns states in `transfer.ts`'s encoding
//!   into `ids`, an Int32Array, as `fromValue` does, and returns null or the reason it stopped;
//! - `storeEncode(states, width)` writes states in that encoding, as `{ words, strings, count }`;
//! - `storeFingerprints(states, width, order, parents, isReference, fingerprints)` writes TLC's
//!   fingerprints of the states into a BigInt64Array, and `storeResetFingerprints()` forgets
//!   every value's.

use std::ffi::{CStr, CString, c_void};
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::ptr::null_mut;
use std::sync::mpsc::{Sender, channel};
use std::sync::{Mutex, PoisonError};

use tla_values::fingerprint::Fingerprints;
use tla_values::trace::{Answer, Argument, Failure, perform};
use tla_values::transfer::{DecodeError, EncodedStates, StateEncoder, decode_states};
use tla_values::{Id, Store, on_nesting_stack};

use super::{
    Thrown, export, guard, napi_callback_info, napi_create_object, napi_env, napi_get_cb_info,
    napi_get_typedarray_info, napi_is_typedarray, napi_status, napi_value, set_property, status,
};

const NAPI_NULL: i32 = 1;
const NAPI_NUMBER: i32 = 3;
pub(super) const NAPI_STRING: i32 = 4;
pub(super) const NAPI_INT32_ARRAY: i32 = 5;
pub(super) const NAPI_BIGINT64_ARRAY: i32 = 9;
const NAPI_UNDEFINED: i32 = 0;

napi_functions! {
    pub(super) fn napi_typeof(env: napi_env, value: napi_value, result: *mut i32) -> napi_status;
    fn napi_get_value_double(env: napi_env, value: napi_value, result: *mut f64) -> napi_status;
    fn napi_get_value_bool(env: napi_env, value: napi_value, result: *mut bool) -> napi_status;
    fn napi_get_value_string_utf16(
        env: napi_env,
        value: napi_value,
        buffer: *mut u16,
        size: usize,
        result: *mut usize,
    ) -> napi_status;
    fn napi_is_array(env: napi_env, value: napi_value, result: *mut bool) -> napi_status;
    fn napi_get_array_length(env: napi_env, value: napi_value, result: *mut u32) -> napi_status;
    fn napi_get_element(
        env: napi_env,
        object: napi_value,
        index: u32,
        result: *mut napi_value,
    ) -> napi_status;
    pub(super) fn napi_set_element(
        env: napi_env,
        object: napi_value,
        index: u32,
        value: napi_value,
    ) -> napi_status;
    fn napi_create_double(env: napi_env, value: f64, result: *mut napi_value) -> napi_status;
    fn napi_get_boolean(env: napi_env, value: bool, result: *mut napi_value) -> napi_status;
    fn napi_get_null(env: napi_env, result: *mut napi_value) -> napi_status;
    fn napi_create_string_utf16(
        env: napi_env,
        text: *const u16,
        length: usize,
        result: *mut napi_value,
    ) -> napi_status;
    pub(super) fn napi_create_array_with_length(
        env: napi_env,
        length: usize,
        result: *mut napi_value,
    ) -> napi_status;
    pub(super) fn napi_create_arraybuffer(
        env: napi_env,
        byte_length: usize,
        data: *mut *mut c_void,
        result: *mut napi_value,
    ) -> napi_status;
    pub(super) fn napi_create_typedarray(
        env: napi_env,
        kind: i32,
        length: usize,
        arraybuffer: napi_value,
        byte_offset: usize,
        result: *mut napi_value,
    ) -> napi_status;
}

type Job = Box<dyn FnOnce(&mut Store, &mut Fingerprints) + Send>;

// The thread that owns the store and runs every call's work on it, with a stack for deeply nested
// values. A thread spawned per call would map that stack each time.
static STORE_THREAD: Mutex<Option<Sender<Job>>> = Mutex::new(None);

fn start_store_thread() -> Sender<Job> {
    let (sender, jobs) = channel::<Job>();
    std::thread::spawn(move || {
        on_nesting_stack(move || {
            let (mut store, mut fingerprints) = (Store::new(), Fingerprints::new());
            for job in jobs {
                job(&mut store, &mut fingerprints);
            }
        })
    });
    sender
}

// Runs work on the store and its fingerprints, and returns what it returns, or its panic.
fn with_store<T: Send + 'static>(
    work: impl FnOnce(&mut Store, &mut Fingerprints) -> T + Send + 'static,
) -> T {
    let (reply, answer) = channel();
    let job: Job = Box::new(move |store, fingerprints| {
        let _ = reply.send(catch_unwind(AssertUnwindSafe(|| work(store, fingerprints))));
    });
    STORE_THREAD
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .get_or_insert_with(start_store_thread)
        .send(job)
        .expect("the store's thread takes work");
    answer
        .recv()
        .expect("the store's thread answers")
        .unwrap_or_else(|panic| resume_unwind(panic))
}

pub(super) fn wrong(message: String) -> Thrown {
    Thrown::WrongArgument(CString::new(message).unwrap_or_default())
}

pub(super) unsafe fn get_arguments<const N: usize>(
    env: napi_env,
    info: napi_callback_info,
) -> Result<[napi_value; N], Thrown> {
    let mut argc = N;
    let mut argv = [null_mut(); N];
    status(unsafe {
        napi_get_cb_info(
            env,
            info,
            &mut argc,
            argv.as_mut_ptr(),
            null_mut(),
            null_mut(),
        )
    })?;
    Ok(argv)
}

pub(super) unsafe fn type_of(env: napi_env, value: napi_value) -> Result<i32, Thrown> {
    let mut kind = 0;
    status(unsafe { napi_typeof(env, value, &mut kind) })?;
    Ok(kind)
}

pub(super) unsafe fn get_number(env: napi_env, value: napi_value) -> Result<f64, Thrown> {
    let mut number = 0.0;
    status(unsafe { napi_get_value_double(env, value, &mut number) })?;
    Ok(number)
}

unsafe fn get_index(env: napi_env, value: napi_value, what: &str) -> Result<usize, Thrown> {
    let number = unsafe { get_number(env, value) }?;
    if number >= 0.0 && number.fract() == 0.0 && number <= u32::MAX as f64 {
        Ok(number as usize)
    } else {
        Err(wrong(format!("{what} must be a whole number")))
    }
}

pub(super) unsafe fn get_text(env: napi_env, value: napi_value) -> Result<Vec<u16>, Thrown> {
    let mut length = 0;
    status(unsafe { napi_get_value_string_utf16(env, value, null_mut(), 0, &mut length) })?;
    let mut units = vec![0u16; length + 1];
    status(unsafe {
        napi_get_value_string_utf16(env, value, units.as_mut_ptr(), length + 1, &mut length)
    })?;
    units.truncate(length);
    Ok(units)
}

// The elements of an array, or None if the value isn't one.
unsafe fn get_elements(
    env: napi_env,
    value: napi_value,
) -> Result<Option<Vec<napi_value>>, Thrown> {
    let mut is_array = false;
    status(unsafe { napi_is_array(env, value, &mut is_array) })?;
    if !is_array {
        return Ok(None);
    }
    let mut length = 0;
    status(unsafe { napi_get_array_length(env, value, &mut length) })?;
    (0..length)
        .map(|index| {
            let mut element = null_mut();
            status(unsafe { napi_get_element(env, value, index, &mut element) })?;
            Ok(element)
        })
        .collect::<Result<Vec<_>, Thrown>>()
        .map(Some)
}

// A typed array's elements in place, if the value is one of that kind.
pub(super) unsafe fn get_typed<'a, T>(
    env: napi_env,
    value: napi_value,
    expected: i32,
) -> Result<Option<&'a mut [T]>, Thrown> {
    let mut is_typed_array = false;
    status(unsafe { napi_is_typedarray(env, value, &mut is_typed_array) })?;
    if !is_typed_array {
        return Ok(None);
    }
    let (mut kind, mut length, mut data) = (0, 0, null_mut());
    status(unsafe {
        napi_get_typedarray_info(
            env,
            value,
            &mut kind,
            &mut length,
            &mut data,
            null_mut(),
            null_mut(),
        )
    })?;
    if kind != expected {
        return Ok(None);
    }
    Ok(Some(if length == 0 {
        &mut []
    } else {
        unsafe { std::slice::from_raw_parts_mut(data.cast::<T>(), length) }
    }))
}

pub(super) unsafe fn get_int32s<'a>(
    env: napi_env,
    value: napi_value,
    what: &str,
) -> Result<&'a mut [i32], Thrown> {
    unsafe { get_typed(env, value, NAPI_INT32_ARRAY) }?
        .ok_or_else(|| wrong(format!("{what} must be an Int32Array")))
}

unsafe fn get_texts(env: napi_env, value: napi_value, what: &str) -> Result<Vec<Vec<u16>>, Thrown> {
    let elements = unsafe { get_elements(env, value) }?
        .ok_or_else(|| wrong(format!("{what} must be an array of strings")))?;
    elements
        .into_iter()
        .map(|element| unsafe { get_text(env, element) })
        .collect()
}

unsafe fn get_argument(env: napi_env, value: napi_value) -> Result<Argument, Thrown> {
    match unsafe { type_of(env, value) }? {
        NAPI_NUMBER => return Ok(Argument::Number(unsafe { get_number(env, value) }?)),
        NAPI_STRING => return Ok(Argument::Text(unsafe { get_text(env, value) }?)),
        _ => {}
    }
    if let Some(words) = unsafe { get_typed::<i32>(env, value, NAPI_INT32_ARRAY) }? {
        return Ok(Argument::Numbers(
            words.iter().map(|&word| f64::from(word)).collect(),
        ));
    }
    let elements = unsafe { get_elements(env, value) }?
        .ok_or_else(|| wrong("an argument must be a number, a string or an array".into()))?;
    let first = elements
        .first()
        .map(|&element| unsafe { type_of(env, element) })
        .transpose()?;
    if first == Some(NAPI_STRING) {
        let texts = elements
            .into_iter()
            .map(|element| unsafe { get_text(env, element) });
        return Ok(Argument::Texts(texts.collect::<Result<_, _>>()?));
    }
    let numbers = elements
        .into_iter()
        .map(|element| unsafe { get_number(env, element) });
    Ok(Argument::Numbers(numbers.collect::<Result<_, _>>()?))
}

pub(super) unsafe fn create_null(env: napi_env) -> Result<napi_value, Thrown> {
    let mut result = null_mut();
    status(unsafe { napi_get_null(env, &mut result) })?;
    Ok(result)
}

pub(super) unsafe fn create_number(env: napi_env, value: f64) -> Result<napi_value, Thrown> {
    let mut result = null_mut();
    status(unsafe { napi_create_double(env, value, &mut result) })?;
    Ok(result)
}

pub(super) unsafe fn create_text(env: napi_env, units: &[u16]) -> Result<napi_value, Thrown> {
    let mut result = null_mut();
    status(unsafe { napi_create_string_utf16(env, units.as_ptr(), units.len(), &mut result) })?;
    Ok(result)
}

unsafe fn create_bail(env: napi_env, reason: &str) -> Result<napi_value, Thrown> {
    unsafe { create_text(env, &reason.encode_utf16().collect::<Vec<u16>>()) }
}

pub(super) unsafe fn create_int32s(env: napi_env, words: &[i32]) -> Result<napi_value, Thrown> {
    let (mut data, mut buffer, mut result) = (null_mut(), null_mut(), null_mut());
    status(unsafe { napi_create_arraybuffer(env, size_of_val(words), &mut data, &mut buffer) })?;
    if !words.is_empty() {
        unsafe { std::slice::from_raw_parts_mut(data.cast::<i32>(), words.len()) }
            .copy_from_slice(words);
    }
    status(unsafe {
        napi_create_typedarray(env, NAPI_INT32_ARRAY, words.len(), buffer, 0, &mut result)
    })?;
    Ok(result)
}

// storePerform(name: string, args: unknown[]): number | boolean | null | string
unsafe extern "C" fn store_perform(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let [name, list] = get_arguments::<2>(env, info)?;
            if type_of(env, name)? != NAPI_STRING {
                return Err(wrong("storePerform takes an operation's name".into()));
            }
            let name = String::from_utf16_lossy(&get_text(env, name)?);
            let elements = get_elements(env, list)?
                .ok_or_else(|| wrong("storePerform takes its arguments as an array".into()))?;
            let arguments = elements
                .into_iter()
                .map(|element| get_argument(env, element))
                .collect::<Result<Vec<_>, _>>()?;
            match with_store(move |store, _| perform(store, &name, &arguments)) {
                Ok(Answer::Null) => create_null(env),
                Ok(Answer::Bool(value)) => {
                    let mut result = null_mut();
                    status(napi_get_boolean(env, value, &mut result))?;
                    Ok(result)
                }
                Ok(Answer::Number(value)) => create_number(env, value as f64),
                Err(Failure::Bail(bail)) => create_bail(env, bail.0),
                Err(Failure::Argument(message)) => Err(wrong(message)),
            }
        })
    }
}

// storeDecode(words: Int32Array, strings: string[], width: number, count: number,
// ids: Int32Array): null | string
unsafe extern "C" fn store_decode(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let [words, strings, width, count, ids] = get_arguments::<5>(env, info)?;
            let encoded = EncodedStates {
                words: get_int32s(env, words, "words")?.to_vec(),
                strings: get_texts(env, strings, "strings")?,
                count: get_index(env, count, "count")? as u32,
            };
            let width = get_index(env, width, "width")?;
            let ids = get_int32s(env, ids, "ids")?;
            if ids.len() < width * encoded.count as usize {
                return Err(wrong("ids must hold every value of every state".into()));
            }
            match with_store(move |store, _| decode_states(store, &encoded, width)) {
                Ok(decoded) => {
                    for (slot, id) in ids.iter_mut().zip(decoded) {
                        *slot = id as i32;
                    }
                    create_null(env)
                }
                Err(DecodeError::Bail(bail)) => create_bail(env, bail.0),
                Err(DecodeError::Malformed(error)) => Err(wrong(format!("storeDecode: {error}"))),
            }
        })
    }
}

// The states of a call, checked to be ids of the store's values.
fn get_states(store: &Store, words: &[i32], width: usize) -> Result<Vec<Id>, Thrown> {
    if width == 0 || !words.len().is_multiple_of(width) {
        return Err(wrong(
            "states must be whole states of a width above 0".into(),
        ));
    }
    words
        .iter()
        .map(|&word| match Id::try_from(word) {
            Ok(id) if (id as usize) < store.value_count() => Ok(id),
            _ => Err(wrong(format!("{word} is no value's id"))),
        })
        .collect()
}

// storeEncode(states: Int32Array, width: number): { words: Int32Array, strings: string[], count }
unsafe extern "C" fn store_encode(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let [states, width] = get_arguments::<2>(env, info)?;
            let words = get_int32s(env, states, "states")?;
            let width = get_index(env, width, "width")?;
            let words = words.to_vec();
            let encoded = with_store(move |store, _| {
                let words = &words;
                let states = get_states(store, words, width)?;
                let mut encoder = StateEncoder::new();
                for state in states.chunks_exact(width) {
                    encoder
                        .encode(store, state)
                        .map_err(|bail| wrong(bail.0.into()))?;
                }
                Ok(encoder.finish())
            })?;
            let mut strings = null_mut();
            status(napi_create_array_with_length(
                env,
                encoded.strings.len(),
                &mut strings,
            ))?;
            for (index, text) in encoded.strings.iter().enumerate() {
                status(napi_set_element(
                    env,
                    strings,
                    index as u32,
                    create_text(env, text)?,
                ))?;
            }
            let mut result = null_mut();
            status(napi_create_object(env, &mut result))?;
            set_property(env, result, c"words", create_int32s(env, &encoded.words)?)?;
            set_property(env, result, c"strings", strings)?;
            set_property(
                env,
                result,
                c"count",
                create_number(env, f64::from(encoded.count))?,
            )?;
            Ok(result)
        })
    }
}

// storeFingerprints(states: Int32Array, width: number, order: Int32Array,
// parents: Int32Array | undefined, isReference: boolean, fingerprints: BigInt64Array): undefined
unsafe extern "C" fn store_fingerprints(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let [states, width, order, parents, is_reference, out] = get_arguments::<6>(env, info)?;
            let words = get_int32s(env, states, "states")?;
            let width = get_index(env, width, "width")?;
            let order = get_int32s(env, order, "order")?
                .iter()
                .map(|&index| usize::try_from(index).ok().filter(|&index| index < width))
                .collect::<Option<Vec<usize>>>()
                .ok_or_else(|| wrong("order must hold positions inside a state".into()))?;
            let parents = match type_of(env, parents)? {
                NAPI_UNDEFINED | NAPI_NULL => None,
                _ => Some(get_int32s(env, parents, "parents")?.to_vec()),
            };
            let mut is_reference_value = false;
            status(napi_get_value_bool(
                env,
                is_reference,
                &mut is_reference_value,
            ))?;
            let out = get_typed::<i64>(env, out, NAPI_BIGINT64_ARRAY)?
                .ok_or_else(|| wrong("fingerprints must be a BigInt64Array".into()))?;
            let words = words.to_vec();
            let fingerprints = with_store(move |store, fingerprints| {
                let (words, parents) = (&words, parents.as_deref());
                let states = get_states(store, words, width)?;
                let count = states.len() / width;
                if parents.is_some_and(|parents| {
                    parents.len() < count || parents.iter().take(count).any(|&parent| parent < -1)
                }) {
                    return Err(wrong("parents must name a state or be -1".into()));
                }
                if is_reference_value {
                    fingerprints.get_states_reference(store, &states, width, &order)
                } else {
                    fingerprints.get_states(store, &states, width, &order, parents)
                }
                .map_err(|bail| wrong(bail.0.into()))
            })?;
            if out.len() < fingerprints.len() {
                return Err(wrong("fingerprints must have room for every state".into()));
            }
            for (slot, fingerprint) in out.iter_mut().zip(fingerprints) {
                *slot = fingerprint as i64;
            }
            Ok(null_mut())
        })
    }
}

// storeResetFingerprints(): undefined
unsafe extern "C" fn store_reset_fingerprints(
    env: napi_env,
    _info: napi_callback_info,
) -> napi_value {
    unsafe {
        guard(env, || {
            with_store(|_, fingerprints| fingerprints.reset());
            Ok(null_mut())
        })
    }
}

pub(super) unsafe fn export_hooks(env: napi_env, exports: napi_value) -> Result<(), Thrown> {
    let hooks: [(&CStr, super::napi_callback); 5] = [
        (c"storePerform", store_perform),
        (c"storeDecode", store_decode),
        (c"storeEncode", store_encode),
        (c"storeFingerprints", store_fingerprints),
        (c"storeResetFingerprints", store_reset_fingerprints),
    ];
    for (name, callback) in hooks {
        unsafe { export(env, exports, name, callback) }?;
    }
    Ok(())
}

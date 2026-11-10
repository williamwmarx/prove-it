//! Test hooks into the native store, for `src/engine/native-store.ts`, which gives the store's
//! tests and the value oracle the TypeScript store's functions over this one. The process has one
//! store, which each call runs on a thread with a stack for deeply nested values. A call costs what an
//! N-API call costs, which tests don't mind; the engine never crosses per value.
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
use std::ptr::null_mut;

use prove_it_host::hooks::{self, HookResult};
use prove_it_host::value::HostValue;
use tla_values::transfer::EncodedStates;

use super::{
    Thrown, export, guard, napi_callback_info, napi_create_object, napi_env, napi_get_cb_info,
    napi_get_typedarray_info, napi_is_typedarray, napi_status, napi_value, set_property, status,
};

const NAPI_NULL: i32 = 1;
const NAPI_NUMBER: i32 = 3;
pub(super) const NAPI_STRING: i32 = 4;
pub(super) const NAPI_INT32_ARRAY: i32 = 5;
const NAPI_UNDEFINED: i32 = 0;
const NAPI_UINT8_ARRAY: i32 = 1;
const NAPI_FLOAT64_ARRAY: i32 = 8;
const NAPI_BIGINT64_ARRAY: i32 = 9;

napi_functions! {
    fn napi_get_undefined(env: napi_env, result: *mut napi_value) -> napi_status;
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

// A value for `storePerform`'s arguments: a number, a string, an Int32Array or an array of them.
pub(super) unsafe fn get_host(env: napi_env, value: napi_value) -> Result<HostValue, Thrown> {
    match unsafe { type_of(env, value) }? {
        NAPI_NUMBER => return Ok(HostValue::Number(unsafe { get_number(env, value) }?)),
        NAPI_STRING => return Ok(HostValue::Text(unsafe { get_text(env, value) }?)),
        _ => {}
    }
    if let Some(words) = unsafe { get_typed::<i32>(env, value, NAPI_INT32_ARRAY) }? {
        return Ok(HostValue::Int32s(words.to_vec()));
    }
    match unsafe { get_elements(env, value) }? {
        Some(elements) => elements
            .into_iter()
            .map(|element| unsafe { get_host(env, element) })
            .collect::<Result<_, _>>()
            .map(HostValue::Array),
        None => Ok(HostValue::Undefined),
    }
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

/// The JavaScript value for what the engine hands its host.
pub(super) unsafe fn create_host(env: napi_env, value: &HostValue) -> Result<napi_value, Thrown> {
    let mut result = null_mut();
    unsafe {
        match value {
            HostValue::Undefined => status(napi_get_undefined(env, &mut result))?,
            HostValue::Null => return create_null(env),
            HostValue::Bool(value) => status(napi_get_boolean(env, *value, &mut result))?,
            HostValue::Number(value) => return create_number(env, *value),
            HostValue::Text(units) => return create_text(env, units),
            HostValue::Int32s(values) => return create_int32s(env, values),
            HostValue::Float64s(values) => return create_typed(env, NAPI_FLOAT64_ARRAY, values),
            HostValue::BigInt64s(values) => return create_typed(env, NAPI_BIGINT64_ARRAY, values),
            HostValue::Uint8s(values) => return create_typed(env, NAPI_UINT8_ARRAY, values),
            HostValue::Array(elements) => {
                status(napi_create_array_with_length(
                    env,
                    elements.len(),
                    &mut result,
                ))?;
                for (index, element) in elements.iter().enumerate() {
                    let element = create_host(env, element)?;
                    status(napi_set_element(env, result, index as u32, element))?;
                }
            }
            HostValue::Object(properties) => {
                status(napi_create_object(env, &mut result))?;
                for (name, property) in properties {
                    let name = CString::new(*name).unwrap_or_default();
                    set_property(env, result, &name, create_host(env, property)?)?;
                }
            }
        }
    }
    Ok(result)
}

pub(super) unsafe fn create_result(
    env: napi_env,
    result: HookResult,
) -> Result<napi_value, Thrown> {
    unsafe { create_host(env, &result.map_err(wrong)?) }
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
                .map(|element| hooks::get_argument(&get_host(env, element)?).map_err(wrong))
                .collect::<Result<Vec<_>, _>>()?;
            create_result(env, hooks::store_perform(name, arguments))
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
            match hooks::store_decode(encoded, width, ids.len()).map_err(wrong)? {
                HostValue::Int32s(decoded) => {
                    ids[..decoded.len()].copy_from_slice(&decoded);
                    create_null(env)
                }
                bail => create_host(env, &bail),
            }
        })
    }
}

// storeEncode(states: Int32Array, width: number): { words: Int32Array, strings: string[], count }
unsafe extern "C" fn store_encode(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let [states, width] = get_arguments::<2>(env, info)?;
            let words = get_int32s(env, states, "states")?.to_vec();
            let width = get_index(env, width, "width")?;
            create_result(env, hooks::store_encode(words, width))
        })
    }
}

// storeFingerprints(states: Int32Array, width: number, order: Int32Array,
// parents: Int32Array | undefined, isReference: boolean, fingerprints: BigInt64Array): undefined
unsafe extern "C" fn store_fingerprints(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let [states, width, order, parents, is_reference, out] = get_arguments::<6>(env, info)?;
            let words = get_int32s(env, states, "states")?.to_vec();
            let width = get_index(env, width, "width")?;
            let order = get_int32s(env, order, "order")?;
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
            let fingerprints = hooks::store_fingerprints(
                words,
                width,
                order,
                parents,
                is_reference_value,
                out.len(),
            )
            .map_err(wrong)?;
            if let HostValue::BigInt64s(fingerprints) = fingerprints {
                out[..fingerprints.len()].copy_from_slice(&fingerprints);
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
            hooks::store_reset_fingerprints();
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

//! The N-API binding, written by hand against Node-API version 8, which Node and Bun both load, so
//! the addon has no dependencies. Node or Bun defines the `napi_*` functions when it loads the
//! addon.

#![allow(non_camel_case_types)]

use std::ffi::{CStr, c_char, c_void};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::ptr::{null, null_mut};

use crate::{ABI_VERSION, Outcome, check};

type napi_env = *mut c_void;
type napi_value = *mut c_void;
type napi_callback_info = *mut c_void;
type napi_callback = unsafe extern "C" fn(napi_env, napi_callback_info) -> napi_value;
type napi_status = i32;

const NAPI_OK: napi_status = 0;
const NAPI_UINT8_ARRAY: i32 = 1;
const NAPI_VERSION: i32 = 8;

unsafe extern "C" {
    fn napi_create_function(
        env: napi_env,
        name: *const c_char,
        length: usize,
        callback: napi_callback,
        data: *mut c_void,
        result: *mut napi_value,
    ) -> napi_status;
    fn napi_set_named_property(
        env: napi_env,
        object: napi_value,
        name: *const c_char,
        value: napi_value,
    ) -> napi_status;
    fn napi_get_cb_info(
        env: napi_env,
        info: napi_callback_info,
        argc: *mut usize,
        argv: *mut napi_value,
        this_arg: *mut napi_value,
        data: *mut *mut c_void,
    ) -> napi_status;
    fn napi_is_typedarray(env: napi_env, value: napi_value, result: *mut bool) -> napi_status;
    fn napi_get_typedarray_info(
        env: napi_env,
        typedarray: napi_value,
        kind: *mut i32,
        length: *mut usize,
        data: *mut *mut c_void,
        arraybuffer: *mut napi_value,
        byte_offset: *mut usize,
    ) -> napi_status;
    fn napi_create_int32(env: napi_env, value: i32, result: *mut napi_value) -> napi_status;
    fn napi_create_object(env: napi_env, result: *mut napi_value) -> napi_status;
    fn napi_create_string_utf8(
        env: napi_env,
        text: *const c_char,
        length: usize,
        result: *mut napi_value,
    ) -> napi_status;
    fn napi_throw_error(env: napi_env, code: *const c_char, message: *const c_char) -> napi_status;
    fn napi_throw_type_error(
        env: napi_env,
        code: *const c_char,
        message: *const c_char,
    ) -> napi_status;
}

// Returns a JavaScript exception for a failed call or a panic, which the caller throws.
enum Thrown {
    Error(&'static CStr),
    TypeError(&'static CStr),
}

fn status(status: napi_status) -> Result<(), Thrown> {
    if status == NAPI_OK {
        Ok(())
    } else {
        Err(Thrown::Error(c"an N-API call failed"))
    }
}

// Runs a callback's body, and throws what it returns as an error, as a panic does.
unsafe fn guard(env: napi_env, body: impl FnOnce() -> Result<napi_value, Thrown>) -> napi_value {
    let thrown = match catch_unwind(AssertUnwindSafe(body)) {
        Ok(Ok(value)) => return value,
        Ok(Err(thrown)) => thrown,
        Err(_) => Thrown::Error(c"the native engine panicked"),
    };
    unsafe {
        match thrown {
            Thrown::Error(message) => napi_throw_error(env, null(), message.as_ptr()),
            Thrown::TypeError(message) => napi_throw_type_error(env, null(), message.as_ptr()),
        };
    }
    null_mut()
}

unsafe fn create_string(env: napi_env, text: &str) -> Result<napi_value, Thrown> {
    let mut result = null_mut();
    status(unsafe { napi_create_string_utf8(env, text.as_ptr().cast(), text.len(), &mut result) })?;
    Ok(result)
}

unsafe fn set_property(
    env: napi_env,
    object: napi_value,
    name: &CStr,
    value: napi_value,
) -> Result<(), Thrown> {
    status(unsafe { napi_set_named_property(env, object, name.as_ptr(), value) })
}

// abiVersion(): number
unsafe extern "C" fn abi_version(env: napi_env, _info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let mut result = null_mut();
            status(napi_create_int32(env, ABI_VERSION, &mut result))?;
            Ok(result)
        })
    }
}

// check(ir: Uint8Array): { status: "declined", reason: string }. It reads the IR in place.
unsafe extern "C" fn check_model(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let mut argc = 1;
            let mut ir = null_mut();
            status(napi_get_cb_info(
                env,
                info,
                &mut argc,
                &mut ir,
                null_mut(),
                null_mut(),
            ))?;
            let mut is_typed_array = false;
            if argc >= 1 {
                status(napi_is_typedarray(env, ir, &mut is_typed_array))?;
            }
            let not_bytes = Thrown::TypeError(c"check takes the engine IR as a Uint8Array");
            if !is_typed_array {
                return Err(not_bytes);
            }
            let (mut kind, mut length, mut data, mut offset) = (0, 0, null_mut(), 0);
            status(napi_get_typedarray_info(
                env,
                ir,
                &mut kind,
                &mut length,
                &mut data,
                null_mut(),
                &mut offset,
            ))?;
            if kind != NAPI_UINT8_ARRAY {
                return Err(not_bytes);
            }
            let bytes = if length == 0 {
                &[][..]
            } else {
                std::slice::from_raw_parts(data.cast::<u8>(), length)
            };
            let Outcome::Declined(reason) = check(bytes);
            let mut result = null_mut();
            status(napi_create_object(env, &mut result))?;
            set_property(env, result, c"status", create_string(env, "declined")?)?;
            set_property(env, result, c"reason", create_string(env, reason)?)?;
            Ok(result)
        })
    }
}

unsafe fn export(
    env: napi_env,
    exports: napi_value,
    name: &CStr,
    callback: napi_callback,
) -> Result<(), Thrown> {
    let mut function = null_mut();
    status(unsafe {
        napi_create_function(
            env,
            name.as_ptr(),
            name.count_bytes(),
            callback,
            null_mut(),
            &mut function,
        )
    })?;
    unsafe { set_property(env, exports, name, function) }
}

/// Node and Bun call this when they load the addon.
///
/// # Safety
///
/// Only Node or Bun calls it, with the environment and the exports object they made.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn napi_register_module_v1(env: napi_env, exports: napi_value) -> napi_value {
    unsafe {
        guard(env, || {
            export(env, exports, c"abiVersion", abi_version)?;
            export(env, exports, c"check", check_model)?;
            Ok(exports)
        })
    }
}

/// The Node-API version the addon is written against.
#[unsafe(no_mangle)]
pub extern "C" fn node_api_module_get_api_version_v1() -> i32 {
    NAPI_VERSION
}

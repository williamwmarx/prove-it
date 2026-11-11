//! The N-API binding, written by hand against Node-API version 8, which Node and Bun both load, so
//! the addon has no dependencies. Node or Bun defines the `napi_*` functions when it loads the
//! addon.

#![allow(non_camel_case_types)]

use std::ffi::{CStr, c_char, c_void};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::ptr::{null, null_mut};
use std::sync::atomic::AtomicI32;

use crate::ABI_VERSION;

// Declares N-API functions. Linux and macOS leave them to the loader, which finds them in the host
// process. Windows has no such lookup, and the host may be node.exe or bun.exe, so each is resolved
// in the host's executable the first time it is called, and the module's NAPI_NAMES lists them for
// the check as the addon loads.
macro_rules! napi_functions {
    ($($vis:vis fn $name:ident($($argument:ident: $type:ty),* $(,)?) -> $result:ty;)*) => {
        #[cfg(not(windows))]
        unsafe extern "C" {
            $($vis fn $name($($argument: $type),*) -> $result;)*
        }
        #[cfg(windows)]
        pub(super) const NAPI_NAMES: &[&str] = &[$(concat!(stringify!($name), "\0")),*];
        $(
            #[cfg(windows)]
            $vis unsafe fn $name($($argument: $type),*) -> $result {
                static ADDRESS: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
                let address = *ADDRESS
                    .get_or_init(|| crate::binding::get_host_function(concat!(stringify!($name), "\0")));
                // SAFETY: the host exports the function under its N-API name with this signature.
                let function = unsafe {
                    std::mem::transmute::<usize, unsafe extern "C" fn($($type),*) -> $result>(address)
                };
                unsafe { function($($argument),*) }
            }
        )*
    };
}

// The address of a function the host's executable exports, or null, given its name and a NUL.
#[cfg(windows)]
fn find_host_function(name: &str) -> *mut c_void {
    #[link(name = "kernel32")]
    unsafe extern "system" {
        fn GetModuleHandleW(name: *const u16) -> *mut c_void;
        fn GetProcAddress(module: *mut c_void, name: *const c_char) -> *mut c_void;
    }
    unsafe { GetProcAddress(GetModuleHandleW(null()), name.as_ptr().cast()) }
}

// The address of an N-API function, which the check as the addon loads found.
#[cfg(windows)]
fn get_host_function(name: &str) -> usize {
    let address = find_host_function(name);
    assert!(!address.is_null(), "the host doesn't export {name}");
    address as usize
}

// The first N-API function the addon calls that the host doesn't export, as an older Node or Bun
// may not, so the addon fails to load, naming it, and the TypeScript engine searches instead.
#[cfg(windows)]
fn find_missing_host_function() -> Option<&'static str> {
    NAPI_NAMES
        .iter()
        .chain(store::NAPI_NAMES)
        .chain(check::NAPI_NAMES)
        .find(|name| find_host_function(name).is_null())
        .map(|name| name.trim_end_matches('\0'))
}

mod check;
mod store;

type napi_env = *mut c_void;
type napi_value = *mut c_void;
type napi_callback_info = *mut c_void;
type napi_callback = unsafe extern "C" fn(napi_env, napi_callback_info) -> napi_value;
type napi_status = i32;

const NAPI_OK: napi_status = 0;
const NAPI_UINT8_ARRAY: i32 = 1;
const NAPI_VERSION: i32 = 8;

napi_functions! {
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
    // A TypeError whose message says which argument is wrong.
    WrongArgument(std::ffi::CString),
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
            Thrown::WrongArgument(message) => napi_throw_type_error(env, null(), message.as_ptr()),
        };
    }
    null_mut()
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

// The bytes of a Uint8Array, in place.
unsafe fn get_bytes<'a>(env: napi_env, value: napi_value) -> Result<&'a [u8], Thrown> {
    let mut is_typed_array = false;
    if !value.is_null() {
        status(unsafe { napi_is_typedarray(env, value, &mut is_typed_array) })?;
    }
    let not_bytes = Thrown::TypeError(c"check takes the engine IR as a Uint8Array");
    if !is_typed_array {
        return Err(not_bytes);
    }
    let (mut kind, mut length, mut data, mut offset) = (0, 0, null_mut(), 0);
    status(unsafe {
        napi_get_typedarray_info(
            env,
            value,
            &mut kind,
            &mut length,
            &mut data,
            null_mut(),
            &mut offset,
        )
    })?;
    if kind != NAPI_UINT8_ARRAY {
        return Err(not_bytes);
    }
    Ok(if length == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(data.cast::<u8>(), length) }
    })
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

// sanyText(root: string, source: string, fileName: string | undefined, version: string,
// rootExtendees: string[], known: [string, string | undefined][]): { kind, ... }, as
// prove-it-host's `sany` describes it.
unsafe extern "C" fn sany_text(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let arguments = store::get_arguments::<6>(env, info)?
                .into_iter()
                .map(|argument| store::get_host(env, argument))
                .collect::<Result<Vec<_>, _>>()?;
            store::create_result(env, prove_it_host::sany::sany_text(&arguments))
        })
    }
}

// sanyXml(root: string, source: string, fileName: string, flags: string, known: [string,
// string | undefined][]): { kind, ... }, as prove-it-host's `sany` describes it.
unsafe extern "C" fn sany_xml(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let arguments = store::get_arguments::<5>(env, info)?
                .into_iter()
                .map(|argument| store::get_host(env, argument))
                .collect::<Result<Vec<_>, _>>()?;
            store::create_result(env, prove_it_host::sany::sany_xml(&arguments))
        })
    }
}

// checkSources(args: string[], known: [string, string | undefined][], machine): { kind, ... }, as
// prove-it-host's `check` describes it.
unsafe extern "C" fn check_sources(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let arguments = store::get_arguments::<3>(env, info)?
                .into_iter()
                .map(|argument| store::get_host(env, argument))
                .collect::<Result<Vec<_>, _>>()?;
            store::create_result(env, prove_it_host::check::check_sources(&arguments))
        })
    }
}

/// The first element of a cancel cell, read in place.
struct CancelCell(*const AtomicI32);

// SAFETY: the cell is an `Int32Array` over a `SharedArrayBuffer`, which other threads set
// atomically, and the decision reads it with an atomic load only while `decide` runs, during which
// JavaScript keeps the array alive: the backend drops its `Limits`, and with them the `Cancel`,
// before `decide` returns.
unsafe impl Send for CancelCell {}
unsafe impl Sync for CancelCell {}

fn get_cancel(first: &mut i32) -> prove_it_host::prover::Cancel {
    // SAFETY: an i32 and an AtomicI32 have the same layout.
    let cell = CancelCell(unsafe { AtomicI32::from_ptr(first) });
    std::sync::Arc::new(move || {
        let cell = &cell;
        // SAFETY: as for CancelCell, the array outlives every read.
        unsafe { &*cell.0 }.load(std::sync::atomic::Ordering::Relaxed) != 0
    })
}

// decide(prover: string, text: string, timeLimitMs: number, stepLimit: number | undefined,
// cancel: Int32Array | undefined): { kind, ... }, as prove-it-host's `prover` describes it. The
// first element of `cancel`, over a SharedArrayBuffer, is read in place while the backend runs, so
// that another thread can cancel it.
unsafe extern "C" fn decide(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let [prover, text, time_limit, step_limit, cancel] =
                store::get_arguments::<5>(env, info)?;
            let arguments = [prover, text, time_limit, step_limit]
                .into_iter()
                .map(|argument| store::get_host(env, argument))
                .collect::<Result<Vec<_>, _>>()?;
            let cancel = match store::get_typed::<i32>(env, cancel, store::NAPI_INT32_ARRAY)? {
                Some([first, ..]) => Some(get_cancel(first)),
                _ => None,
            };
            store::create_result(env, prove_it_host::prover::decide(&arguments, cancel))
        })
    }
}

// prove(file: string, source: string, known: [key, value][]), as prove-it-host's `prove`
// describes it.
unsafe extern "C" fn prove(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let arguments = store::get_arguments::<3>(env, info)?
                .into_iter()
                .map(|argument| store::get_host(env, argument))
                .collect::<Result<Vec<_>, _>>()?;
            store::create_result(env, prove_it_host::prove::prove(&arguments))
        })
    }
}

/// Node and Bun call this when they load the addon.
///
/// # Safety
///
/// Only Node or Bun calls it, with the environment and the exports object they made.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn napi_register_module_v1(env: napi_env, exports: napi_value) -> napi_value {
    #[cfg(windows)]
    if let Some(name) = find_missing_host_function() {
        let message = std::ffi::CString::new(format!(
            "the host doesn't export {name}, which the native engine needs"
        ))
        .unwrap_or_default();
        unsafe { napi_throw_error(env, null(), message.as_ptr()) };
        return null_mut();
    }
    unsafe {
        guard(env, || {
            export(env, exports, c"abiVersion", abi_version)?;
            export(env, exports, c"check", check::check_model)?;
            export(env, exports, c"sanyText", sany_text)?;
            export(env, exports, c"sanyXml", sany_xml)?;
            export(env, exports, c"decide", decide)?;
            export(env, exports, c"prove", prove)?;
            export(env, exports, c"checkSources", check_sources)?;
            store::export_hooks(env, exports)?;
            Ok(exports)
        })
    }
}

/// The Node-API version the addon is written against.
#[unsafe(no_mangle)]
pub extern "C" fn node_api_module_get_api_version_v1() -> i32 {
    NAPI_VERSION
}

#[cfg(all(test, windows))]
mod tests {
    // A test executable exports no N-API functions, so the check names the first the addon needs.
    #[test]
    fn a_host_without_n_api_names_the_first_function_missing() {
        assert_eq!(
            super::find_missing_host_function(),
            Some("napi_create_function")
        );
    }
}

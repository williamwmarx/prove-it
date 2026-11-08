// A dependency-free N-API module, to measure the cost of crossing between JavaScript and Rust.
#![allow(non_camel_case_types)]
use std::ffi::c_void;
use std::os::raw::c_char;

type napi_env = *mut c_void;
type napi_value = *mut c_void;
type napi_callback_info = *mut c_void;
type napi_callback = unsafe extern "C" fn(napi_env, napi_callback_info) -> napi_value;

extern "C" {
    fn napi_create_function(env: napi_env, name: *const c_char, len: usize, cb: napi_callback, data: *mut c_void, result: *mut napi_value) -> i32;
    fn napi_set_named_property(env: napi_env, object: napi_value, name: *const c_char, value: napi_value) -> i32;
    fn napi_get_cb_info(env: napi_env, info: napi_callback_info, argc: *mut usize, argv: *mut napi_value, this_arg: *mut napi_value, data: *mut *mut c_void) -> i32;
    fn napi_get_value_int32(env: napi_env, value: napi_value, result: *mut i32) -> i32;
    fn napi_create_int32(env: napi_env, value: i32, result: *mut napi_value) -> i32;
    fn napi_get_typedarray_info(env: napi_env, typedarray: napi_value, ty: *mut i32, length: *mut usize, data: *mut *mut c_void, arraybuffer: *mut napi_value, byte_offset: *mut usize) -> i32;
    fn napi_get_undefined(env: napi_env, result: *mut napi_value) -> i32;
    fn napi_call_function(env: napi_env, recv: napi_value, func: napi_value, argc: usize, argv: *const napi_value, result: *mut napi_value) -> i32;
}

unsafe fn args<const N: usize>(env: napi_env, info: napi_callback_info) -> [napi_value; N] {
    let mut argc = N;
    let mut argv = [std::ptr::null_mut(); N];
    napi_get_cb_info(env, info, &mut argc, argv.as_mut_ptr(), std::ptr::null_mut(), std::ptr::null_mut());
    argv
}

unsafe fn int(env: napi_env, value: i32) -> napi_value {
    let mut result = std::ptr::null_mut();
    napi_create_int32(env, value, &mut result);
    result
}

unsafe extern "C" fn noop(env: napi_env, _info: napi_callback_info) -> napi_value {
    let mut result = std::ptr::null_mut();
    napi_get_undefined(env, &mut result);
    result
}

unsafe extern "C" fn add(env: napi_env, info: napi_callback_info) -> napi_value {
    let [a, b] = args::<2>(env, info);
    let (mut x, mut y) = (0, 0);
    napi_get_value_int32(env, a, &mut x);
    napi_get_value_int32(env, b, &mut y);
    int(env, x.wrapping_add(y))
}

// Sums an Int32Array in place, without copying it: the way a batch of ids crosses.
unsafe extern "C" fn sum(env: napi_env, info: napi_callback_info) -> napi_value {
    let [array] = args::<1>(env, info);
    let (mut ty, mut length, mut data, mut offset) = (0, 0usize, std::ptr::null_mut(), 0usize);
    let mut buffer = std::ptr::null_mut();
    napi_get_typedarray_info(env, array, &mut ty, &mut length, &mut data, &mut buffer, &mut offset);
    let slice = std::slice::from_raw_parts(data as *const i32, length);
    int(env, slice.iter().fold(0i32, |acc, v| acc.wrapping_add(*v)))
}

// Calls a JavaScript function n times from Rust: the cost of a callback, such as a question the
// engine would ask the interpreter.
unsafe extern "C" fn call_back(env: napi_env, info: napi_callback_info) -> napi_value {
    let [func, count] = args::<2>(env, info);
    let mut n = 0;
    napi_get_value_int32(env, count, &mut n);
    let mut undefined = std::ptr::null_mut();
    napi_get_undefined(env, &mut undefined);
    let mut total = 0i32;
    for i in 0..n {
        let arg = int(env, i);
        let mut result = std::ptr::null_mut();
        napi_call_function(env, undefined, func, 1, &arg, &mut result);
        let mut value = 0;
        napi_get_value_int32(env, result, &mut value);
        total = total.wrapping_add(value);
    }
    int(env, total)
}

unsafe fn export(env: napi_env, exports: napi_value, name: &str, cb: napi_callback) {
    let mut function = std::ptr::null_mut();
    let cname = std::ffi::CString::new(name).unwrap();
    napi_create_function(env, cname.as_ptr(), name.len(), cb, std::ptr::null_mut(), &mut function);
    napi_set_named_property(env, exports, cname.as_ptr(), function);
}

#[no_mangle]
pub unsafe extern "C" fn napi_register_module_v1(env: napi_env, exports: napi_value) -> napi_value {
    export(env, exports, "noop", noop);
    export(env, exports, "add", add);
    export(env, exports, "sum", sum);
    export(env, exports, "callBack", call_back);
    exports
}

// The same functions for bun:ffi, which calls C functions without N-API.
#[no_mangle]
pub extern "C" fn ffi_add(a: i32, b: i32) -> i32 { a.wrapping_add(b) }
#[no_mangle]
pub unsafe extern "C" fn ffi_sum(data: *const i32, length: usize) -> i32 {
    std::slice::from_raw_parts(data, length).iter().fold(0i32, |acc, v| acc.wrapping_add(*v))
}

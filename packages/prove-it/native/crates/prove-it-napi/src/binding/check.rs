//! `check(ir, settings, stateLog, report, print)`: searches the model the engine IR describes, on a
//! thread with a deep stack, and calls `report` and `print` on the calling thread as the search
//! reports. `prove_it_host::outcome` says what each takes and what `check` returns.

use std::ptr::null_mut;

use prove_it_host::check_on_thread;
use prove_it_host::outcome::{EventCall, get_event_call, get_outcome, get_settings};
use prove_it_host::value::HostValue;

use super::store::{
    NAPI_STRING, create_host, create_number, get_arguments, get_int32s, get_text, type_of, wrong,
};
use super::{Thrown, guard, napi_callback_info, napi_env, napi_status, napi_value, status};

napi_functions! {
    fn napi_call_function(
        env: napi_env,
        recv: napi_value,
        function: napi_value,
        argc: usize,
        argv: *const napi_value,
        result: *mut napi_value,
    ) -> napi_status;
}

// check(ir: Uint8Array, settings: Int32Array, stateLog: string, report: Function,
// print: Function)
pub(super) unsafe extern "C" fn check_model(env: napi_env, info: napi_callback_info) -> napi_value {
    unsafe {
        guard(env, || {
            let [ir, settings, state_log, report, print] = get_arguments::<5>(env, info)?;
            let bytes = super::get_bytes(env, ir)?;
            let words = get_int32s(env, settings, "the settings")?;
            if type_of(env, state_log)? != NAPI_STRING {
                return Err(wrong("the state log must be a string".into()));
            }
            let state_log = String::from_utf16_lossy(&get_text(env, state_log)?);
            let settings = get_settings(words, state_log).map_err(wrong)?;
            let undefined = create_host(env, &HostValue::Undefined)?;
            // A callback that throws leaves its exception pending, and the rest aren't called.
            let mut is_thrown = false;
            let outcome = check_on_thread(bytes, &settings, |event| {
                if is_thrown {
                    return;
                }
                let call = match get_event_call(event) {
                    EventCall::Report(numbers) => numbers
                        .iter()
                        .map(|&number| create_number(env, number))
                        .collect::<Result<Vec<_>, Thrown>>()
                        .map(|argv| (report, argv)),
                    EventCall::Print(width, values) => [
                        HostValue::Number(width),
                        HostValue::Int32s(values.words),
                        HostValue::texts(&values.strings),
                    ]
                    .iter()
                    .map(|argument| create_host(env, argument))
                    .collect::<Result<Vec<_>, Thrown>>()
                    .map(|argv| (print, argv)),
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
            create_host(env, &get_outcome(&outcome))
        })
    }
}

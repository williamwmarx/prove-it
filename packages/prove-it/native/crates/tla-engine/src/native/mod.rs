//! Native code from our own backend (native/design/native-backend.md). The `unsafe` the backend
//! needs lives in this module: [`memory`] maps, seals and frees the memory code runs from, `call`
//! runs it, and `helpers` are what it calls back. [`ir`] is what code is emitted from, `emit`
//! emits it, and [`x86_64`] encodes the instructions it's emitted as.
//!
//! N1 emits guards and invariants for x86-64 Linux only, behind `PROVE_IT_NATIVE_CODE`.
//! Everywhere else, and for anything it can't emit, the closures run as before.

#[cfg(target_arch = "x86_64")]
mod call;
#[cfg(target_arch = "x86_64")]
mod emit;
#[cfg(test)]
mod generated;
#[cfg(target_arch = "x86_64")]
mod helpers;
#[cfg_attr(not(any(test, target_arch = "x86_64")), allow(dead_code))]
pub(crate) mod ir;
pub mod memory;
#[cfg_attr(not(any(test, target_arch = "x86_64")), allow(dead_code))]
pub(crate) mod x86_64;

use crate::compile::predicate::{Predicate, Test};
use crate::machine::Eval;

/// PROVE_IT_NATIVE_CODE: whether guards and invariants run as native code.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum NativeCode {
    #[default]
    Off,
    On,
    /// Runs each predicate's native code and its closures, and panics where they differ.
    Verify,
}

/// A predicate's test: its native code where the setting asks for it and the platform runs it,
/// else its closures.
pub(crate) fn test(predicate: &Predicate, native_code: NativeCode) -> Test {
    compile(predicate, native_code).unwrap_or_else(|| predicate.build())
}

/// A state predicate's closure from its native code, where `test` would give native code.
pub(crate) fn eval(predicate: &Predicate, native_code: NativeCode) -> Option<Eval> {
    compile(predicate, native_code)
        .map(|test| crate::compile::eval(move |machine| test(machine).map(crate::compile::bool_id)))
}

#[cfg(target_arch = "x86_64")]
fn compile(predicate: &Predicate, native_code: NativeCode) -> Option<Test> {
    if native_code == NativeCode::Off {
        return None;
    }
    let function = ir::lower(predicate);
    let native = call::Native::new(
        &emit::function(&function),
        function.evals,
        native_code == NativeCode::Verify,
    )?;
    if native_code == NativeCode::On {
        return Some(Box::new(move |machine| native.run(machine)));
    }
    let closures = predicate.build();
    Some(Box::new(move |machine| {
        // The closures run first, and what the native code prints again is dropped.
        let expected = closures(machine);
        let printed = machine.output.len();
        let actual = native.run(machine);
        machine.output.truncate(printed);
        assert_eq!(actual, expected, "native code differs from its closures");
        expected
    }))
}

#[cfg(not(target_arch = "x86_64"))]
fn compile(_: &Predicate, _: NativeCode) -> Option<Test> {
    None
}

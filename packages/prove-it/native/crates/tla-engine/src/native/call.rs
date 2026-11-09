//! The one place a code address becomes a function and is called (native/design/native-backend.md
//! 6). Code is emitted as `extern "sysv64" fn(*mut Context) -> u32`, and reaches the machine only
//! through the context it's given: the bases it reads at fixed offsets, and the helpers it calls.

use std::any::Any;
use std::mem::offset_of;

use tla_values::store::Outcome;
use tla_values::{Bail, Id};

use super::memory::Code;
use crate::machine::{Eval, Machine};

/// The bases of the vectors emitted code indexes, at fixed offsets. A helper may move them, so
/// each refreshes them before it returns, and the code reloads a base after every call.
#[repr(C)]
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Bases {
    pub(crate) locals: *const Id,
    pub(crate) current: *const Id,
}

impl Bases {
    pub(crate) fn of(machine: &Machine<'_>) -> Bases {
        Bases {
            locals: machine.locals.as_ptr(),
            current: machine.cur.as_ptr(),
        }
    }
}

/// What emitted code is given: its first argument.
#[repr(C)]
pub(crate) struct Context {
    pub(crate) bases: Bases,
    // The machine, lent for the call; `Machine` has a lifetime, so it's held untyped.
    pub(crate) machine: *mut (),
    pub(crate) evals: *const [Eval],
    pub(crate) bail: Option<Bail>,
    // A panic in a helper, which can't unwind through emitted code, so it resumes past it.
    pub(crate) panic: Option<Box<dyn Any + Send>>,
    pub(crate) is_verified: bool,
}

pub(crate) const LOCALS: i32 = (offset_of!(Context, bases) + offset_of!(Bases, locals)) as i32;
pub(crate) const CURRENT: i32 = (offset_of!(Context, bases) + offset_of!(Bases, current)) as i32;

/// What emitted code returns.
pub(crate) const FAILS: u32 = 0;
pub(crate) const HOLDS: u32 = 1;
pub(crate) const BAILED: u32 = 2;

/// A predicate's native code, and the closures of the leaves it calls.
pub(crate) struct Native {
    code: Code,
    evals: Box<[Eval]>,
    is_verified: bool,
}

impl Native {
    /// None where executable memory isn't available.
    pub(crate) fn new(bytes: &[u8], evals: Vec<Eval>, is_verified: bool) -> Option<Native> {
        Code::new(bytes).map(|code| Native {
            code,
            evals: evals.into_boxed_slice(),
            is_verified,
        })
    }

    pub(crate) fn run(&self, machine: &mut Machine<'_>) -> Outcome<bool> {
        let mut context = Context {
            bases: Bases::of(machine),
            machine: (machine as *mut Machine<'_>).cast(),
            evals: &*self.evals,
            bail: None,
            panic: None,
            is_verified: self.is_verified,
        };
        // SAFETY: the code is what `emit::function` emitted for this signature, sealed in a
        // mapping this `Native` owns and keeps alive for the call. It reaches the machine only
        // through `context`, by the helpers, on this thread, while `machine` is borrowed here.
        let entry: extern "sysv64" fn(*mut Context) -> u32 =
            unsafe { std::mem::transmute(self.code.entry()) };
        let result = entry(&mut context);
        if let Some(panic) = context.panic {
            std::panic::resume_unwind(panic);
        }
        match result {
            FAILS => Ok(false),
            HOLDS => Ok(true),
            _ => Err(context.bail.expect("a bail's reason")),
        }
    }
}

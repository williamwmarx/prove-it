//! What emitted code calls (native/design/native-backend.md 6). Each helper turns its context back
//! into the machine under one invariant: the code is only ever called by `call.rs`, on the thread
//! that owns the machine, while `call.rs` holds the machine's only borrow. Each returns an id, or
//! [`BAILED`] with the reason in the context, and refreshes the bases before it returns. A panic
//! can't unwind through emitted code, so a helper catches it for `call.rs` to resume.

use std::panic::{self, AssertUnwindSafe};

use tla_values::store::{KIND_SET, Outcome};
use tla_values::{Bail, Id};

use super::call::{Bases, Context};
use crate::compile::predicate;
use crate::machine::{Eval, Machine};

/// What a helper returns where it bailed: no id is this large.
pub(crate) const BAILED: u64 = u64::MAX;

/// The reasons emitted code bails for itself, by their index.
const REASONS: [&str; 2] = ["variable not assigned", "expected a boolean"];
pub(crate) const UNASSIGNED: u32 = 0;
pub(crate) const NOT_BOOLEAN: u32 = 1;

fn with(context: *mut Context, run: impl FnOnce(&mut Machine<'_>, &[Eval]) -> Outcome<Id>) -> u64 {
    // SAFETY: by the invariant above, `context` is the live context `call.rs` made for this call,
    // its machine is the machine `call.rs` borrowed mutably for it, and its evals are its
    // `Native`'s, alive as long as the call.
    let (context, machine, evals) = unsafe {
        let context = &mut *context;
        let machine = &mut *context.machine.cast::<Machine<'_>>();
        let evals = &*context.evals;
        (context, machine, evals)
    };
    let bases = Bases::of(machine);
    let outcome = panic::catch_unwind(AssertUnwindSafe(|| {
        if context.is_verified {
            assert_eq!(context.bases, bases, "native code read stale bases");
        }
        run(machine, evals)
    }));
    context.bases = Bases::of(machine);
    match outcome {
        Ok(Ok(id)) => u64::from(id),
        Ok(Err(bail)) => {
            context.bail = Some(bail);
            BAILED
        }
        // The code takes its bail path, and `call.rs` resumes the panic once it has returned.
        Err(payload) => {
            context.panic = Some(payload);
            BAILED
        }
    }
}

/// `f[k]`, as `predicate::apply` applies it.
pub(crate) extern "sysv64" fn apply(context: *mut Context, function: Id, key: Id) -> u64 {
    with(context, |machine, _| {
        predicate::apply(machine, function, key)
    })
}

/// TLC's equality, as `predicate::equals` decides it: FALSE or TRUE.
pub(crate) extern "sysv64" fn equals(context: *mut Context, left: Id, right: Id) -> u64 {
    with(context, |machine, _| {
        predicate::equals(machine, left, right).map(|is_equal| machine.store.bool(is_equal))
    })
}

/// `e \in S`, failing on a non-set: FALSE or TRUE.
pub(crate) extern "sysv64" fn member(context: *mut Context, element: Id, set: Id) -> u64 {
    with(context, |machine, _| {
        if machine.store.kind_of(set) != KIND_SET {
            return Err(Bail("membership in a non-set"));
        }
        machine
            .store
            .is_member(element, set)
            .map(|is_member| machine.store.bool(is_member))
    })
}

/// A call of one of the closures the compiler built.
pub(crate) extern "sysv64" fn eval(context: *mut Context, index: u32) -> u64 {
    with(context, |machine, evals| evals[index as usize](machine))
}

/// Bails for one of [`REASONS`].
pub(crate) extern "sysv64" fn bail(context: *mut Context, reason: u32) -> u64 {
    with(context, |_, _| Err(Bail(REASONS[reason as usize])))
}

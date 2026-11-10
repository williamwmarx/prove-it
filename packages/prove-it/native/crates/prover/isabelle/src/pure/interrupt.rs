//! Isabelle interrupts a proof that runs out of time, wherever it is; this port checks for that at
//! the points where Isabelle's tactics and unifier spend their time (`pure/interrupt.ts`).
//!
//! The TypeScript hands its `Limits` to every closure that checks them. Here the limits of the
//! decision running on this thread are installed for its duration by `with_limits`, so that lazy
//! sequences and tactics, which outlive any borrow, can check them without carrying them.

use std::cell::Cell;

use prove_decide::Limits;

use crate::error::{Error, Exception, Res, isabelle_error};

thread_local! {
    /// The limits of the decision running on this thread, while `with_limits` runs it.
    static LIMITS: Cell<Option<*mut Limits<'static>>> = const { Cell::new(None) };
    /// The address of the stack where the decision started, for `check_stack`.
    static STACK_BASE: Cell<usize> = const { Cell::new(0) };
}

/// How much stack a decision may use before it gives up as JavaScript does on a stack overflow.
/// Decisions run on a thread with a 256 MB stack (design/prover.md 3.2), so this leaves ample room.
const STACK_BUDGET: usize = 64 << 20;

struct Installed {
    limits: Option<*mut Limits<'static>>,
    base: usize,
}

impl Drop for Installed {
    fn drop(&mut self) {
        LIMITS.with(|cell| cell.set(self.limits));
        STACK_BASE.with(|cell| cell.set(self.base));
    }
}

fn stack_address() -> usize {
    let marker = 0u8;
    std::hint::black_box(&marker) as *const u8 as usize
}

/// Runs a decision with `limits` installed for `check_interrupt`, and the current stack depth as
/// the base of `check_stack`.
pub fn with_limits<T>(limits: &mut Limits<'_>, run: impl FnOnce() -> T) -> T {
    let pointer = (limits as *mut Limits<'_>).cast::<Limits<'static>>();
    let _restore = Installed {
        limits: LIMITS.with(|cell| cell.replace(Some(pointer))),
        base: STACK_BASE.with(|cell| cell.replace(stack_address())),
    };
    run()
}

/// checkInterrupt: raises Interrupt past the step limit, past the deadline, or once the decision
/// is canceled. Each check is a step. Without installed limits (a unit test of the kernel), it
/// never interrupts.
pub fn check_interrupt() -> Res<()> {
    let Some(pointer) = LIMITS.with(Cell::get) else {
        return Ok(());
    };
    // SAFETY: `with_limits` installs the pointer from a live `&mut Limits` and removes it before
    // that borrow ends; nothing else touches the limits while the decision runs on this thread.
    let limits = unsafe { &mut *pointer };
    if limits.is_step_limit_reached() || limits.is_past_deadline() || limits.is_canceled() {
        return Err(isabelle_error(Exception::Interrupt, "Interrupt"));
    }
    Ok(())
}

/// Gives up with `Error::Stack` once the recursion has used more stack than a decision may, where
/// the TypeScript would overflow JavaScript's stack and answer unknown. Rust can't catch an
/// overflow, so the deep recursions call this instead.
pub fn check_stack() -> Res<()> {
    let base = STACK_BASE.with(Cell::get);
    if base != 0 && base.abs_diff(stack_address()) > STACK_BUDGET {
        return Err(Error::Stack);
    }
    Ok(())
}

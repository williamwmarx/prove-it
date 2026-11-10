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
    /// How deep the recursions that call `check_stack` are nested.
    static DEPTH: Cell<usize> = const { Cell::new(0) };
}

struct Installed {
    limits: Option<*mut Limits<'static>>,
}

impl Drop for Installed {
    fn drop(&mut self) {
        LIMITS.with(|cell| cell.set(self.limits));
    }
}

/// Runs a decision with `limits` installed for `check_interrupt`.
pub fn with_limits<T>(limits: &mut Limits<'_>, run: impl FnOnce() -> T) -> T {
    let pointer = (limits as *mut Limits<'_>).cast::<Limits<'static>>();
    let _restore = Installed {
        limits: LIMITS.with(|cell| cell.replace(Some(pointer))),
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

/// How deep the recursions that call `check_stack` may nest. A decision runs natively on a thread
/// with a stack sized for this; WebAssembly runs on the host's JavaScript stack, which is far
/// shallower, so its bound is lower (design/fallback.md, "WebAssembly's stack").
#[cfg(not(target_arch = "wasm32"))]
pub const MAXIMUM_DEPTH: usize = 20_000;
#[cfg(target_arch = "wasm32")]
pub const MAXIMUM_DEPTH: usize = 1_000;

/// One level of a recursion that `check_stack` admitted; dropping it leaves the level.
#[must_use = "the depth counts while the guard lives: bind it with `let _depth = check_stack()?;`"]
pub struct Depth(());

impl Drop for Depth {
    fn drop(&mut self) {
        DEPTH.with(|depth| depth.set(depth.get() - 1));
    }
}

/// Enters one level of a deep recursion, or gives up with `Error::Stack` past `MAXIMUM_DEPTH`,
/// where the TypeScript would overflow JavaScript's stack and answer unknown. Rust can't catch an
/// overflow, so the deep recursions call this on entry and keep the guard until they return:
/// `let _depth = check_stack()?;`.
pub fn check_stack() -> Res<Depth> {
    DEPTH.with(|depth| {
        if depth.get() >= MAXIMUM_DEPTH {
            return Err(Error::Stack);
        }
        depth.set(depth.get() + 1);
        Ok(Depth(()))
    })
}

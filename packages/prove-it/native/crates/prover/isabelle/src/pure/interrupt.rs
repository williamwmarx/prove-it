//! Isabelle interrupts a proof that runs out of time, wherever it is; this port checks for that at
//! the points where Isabelle's tactics and unifier spend their time (`pure/interrupt.ts`).
//!
//! The TypeScript hands its `Limits` to every closure that checks them. Here the limits of the
//! decision running on this thread are installed for its duration by `with_limits`, so that lazy
//! sequences and tactics, which outlive any borrow, can check them without carrying them.

use std::cell::{Cell, RefCell};

use prove_decide::Limits;

use crate::error::{Error, Exception, Res, isabelle_error};

thread_local! {
    /// The limits of the decision running on this thread, while `with_limits` runs it.
    static LIMITS: RefCell<Option<Limits>> = const { RefCell::new(None) };
    /// How deep the recursions that call `check_stack` are nested.
    static DEPTH: Cell<usize> = const { Cell::new(0) };
}

/// Puts back the limits that were installed before, when the decision ends however it ends, so
/// that no decision keeps its limits after it returns.
struct Installed(Option<Limits>);

impl Drop for Installed {
    fn drop(&mut self) {
        LIMITS.with(|cell| *cell.borrow_mut() = self.0.take());
    }
}

/// Runs a decision with `limits` installed for `check_interrupt`.
pub fn with_limits<T>(limits: &Limits, run: impl FnOnce() -> T) -> T {
    let _restore = Installed(LIMITS.with(|cell| cell.borrow_mut().replace(limits.clone())));
    run()
}

/// Runs a computation as the TypeScript runs one with `limits` undefined: the unifier checks no
/// interrupt (here, it checks limits that never interrupt, and counts its steps apart). The
/// computation must force every sequence it pulls before it returns.
pub fn without_limits<T>(run: impl FnOnce() -> T) -> T {
    with_limits(&Limits::new(f64::INFINITY, None, None), run)
}

/// checkInterrupt: raises Interrupt past the step limit, past the deadline, or once the decision
/// is canceled. Each check is a step. Without installed limits (a unit test of the kernel), it
/// never interrupts.
pub fn check_interrupt() -> Res<()> {
    let is_interrupted = LIMITS.with(|cell| {
        cell.borrow().as_ref().is_some_and(|limits| {
            limits.is_step_limit_reached() || limits.is_past_deadline() || limits.is_canceled()
        })
    });
    if is_interrupted {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interrupts_past_the_step_limit_only_while_installed() {
        let limits = Limits::new(f64::INFINITY, Some(2), None);
        with_limits(&limits, || {
            assert!(check_interrupt().is_ok());
            assert!(check_interrupt().is_ok());
            assert!(check_interrupt().is_err_and(|error| error.is(Exception::Interrupt)));
        });
        assert_eq!(limits.steps(), 3);
        assert!(check_interrupt().is_ok());
        assert_eq!(limits.steps(), 3);
    }

    #[test]
    fn gives_up_past_the_maximum_depth() {
        let guards = (0..MAXIMUM_DEPTH)
            .map(|_| check_stack())
            .collect::<Res<Vec<_>>>();
        assert!(guards.is_ok());
        assert!(matches!(check_stack(), Err(Error::Stack)));
        drop(guards);
        assert!(check_stack().is_ok());
    }
}

//! Prove It's native engine, loaded by `src/engine/native.ts` as an N-API addon. It decodes the
//! engine IR, compiles the model and searches it, or declines a model it can't search before
//! producing any state, so that the TypeScript engine checks it.

#[cfg(not(test))]
mod binding;

pub use tla_engine::search::{Reporter, SearchOutcome, Settings};
use tla_values::transfer::{EncodedStates, StateEncoder};
use tla_values::{Id, Store};

/// The version of the contract between the loader and the addon: the exports, their arguments
/// and the engine IR. The loader uses the TypeScript engine when it expects another.
<<<<<<< HEAD
pub const ABI_VERSION: i32 = 6;
=======
pub const ABI_VERSION: i32 = 5;
>>>>>>> origin/main

/// How deep the search thread's stack may grow: compiled closures recurse with the expressions
/// and the values they evaluate. It is reserved, not committed.
const SEARCH_STACK_BYTES: usize = if cfg!(debug_assertions) {
    1024 * 1024 * 1024
} else {
    256 * 1024 * 1024
};

/// Checks the model the engine IR describes, on this thread.
pub fn check(ir: &[u8], settings: &Settings, reporter: &mut dyn Reporter) -> SearchOutcome {
    match tla_ir::decode(ir) {
        Err(error) => SearchOutcome::Declined(format!("the engine IR doesn't decode: {error}")),
        Ok(ir) => tla_engine::search::search(&ir, settings, reporter),
    }
}

/// What a search reports as it runs, which the thread that called it relays to JavaScript.
#[derive(Debug, PartialEq)]
pub enum Event {
    InitialStatesStarted,
    InitialStatesProgress(u64),
    InitialStates(u64, u64),
    Progress(u64, u64, u64, u64),
    /// What Print or PrintT printed, as one state of `width` values.
    Print(EncodedStates, usize),
}

struct Relay(std::sync::mpsc::Sender<Event>);

impl Reporter for Relay {
    fn initial_states_started(&mut self) {
        let _ = self.0.send(Event::InitialStatesStarted);
    }

    fn initial_states_progress(&mut self, count: u64) {
        let _ = self.0.send(Event::InitialStatesProgress(count));
    }

    fn initial_states(&mut self, generated: u64, distinct: u64) {
        let _ = self.0.send(Event::InitialStates(generated, distinct));
    }

    fn progress(&mut self, generated: u64, distinct: u64, queued: u64, depth: u64) {
        let _ = self
            .0
            .send(Event::Progress(generated, distinct, queued, depth));
    }

    // The values go to JavaScript in `transfer.ts`'s encoding, as one state of their count, for
    // the interpreter's printer.
    fn print(&mut self, store: &Store, values: &[Id]) {
        let mut encoder = StateEncoder::new();
        encoder.encode(store, values);
        let _ = self.0.send(Event::Print(encoder.finish(), values.len()));
    }
}

/// Checks the model on a thread with a deep stack, handing each event to `on_event` on this
/// thread as it comes, in order.
pub fn check_on_thread(
    ir: &[u8],
    settings: &Settings,
    mut on_event: impl FnMut(Event),
) -> SearchOutcome {
    std::thread::scope(|scope| {
        let (sender, receiver) = std::sync::mpsc::channel();
        let search = std::thread::Builder::new()
            .stack_size(SEARCH_STACK_BYTES)
            .spawn_scoped(scope, move || check(ir, settings, &mut Relay(sender)))
            .expect("a thread for the search");
        for event in receiver {
            on_event(event);
        }
        search
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn declined(outcome: SearchOutcome) -> Option<String> {
        match outcome {
            SearchOutcome::Declined(reason) => Some(reason),
            _ => None,
        }
    }

    #[test]
    fn declines_what_isnt_an_ir() {
        let outcome = check_on_thread(&[1, 2, 3], &Settings::default(), |_| {});
        assert_eq!(
            declined(outcome),
            Some("the engine IR doesn't decode: at word 0: 3 bytes are no IR".into())
        );
    }

    #[test]
    fn checks_commit() {
        let commit = include_bytes!(
            "../../../../tests/conformance/ir/examples/specifications/transaction_commit/TCommit.ir"
        );
        let mut events = Vec::new();
        let outcome = check_on_thread(commit, &Settings::default(), |event| events.push(event));
        let SearchOutcome::Complete { counts, .. } = outcome else {
            panic!("TCommit didn't complete");
        };
        assert_eq!(events.first(), Some(&Event::InitialStatesStarted));
        assert_eq!(counts.initial_distinct, 1);
        assert!(counts.distinct > 1);
    }
}

//! Test hooks into the native store, for `src/engine/native-store.ts`, which gives the store's
//! tests and the value oracle the TypeScript store's functions over this one. The process has one
//! store, which each call runs on a thread with a stack for deeply nested values, or in place in
//! WebAssembly. A call costs what crossing into the engine costs, which tests don't mind; the
//! engine never crosses per value.
//!
//! - `storePerform(name, args)` runs an operation as a store trace names it, with ids as numbers,
//!   texts as strings and lists as arrays or Int32Arrays, and returns its number, boolean or
//!   null, or the reason the store stopped as a string;
//! - `storeDecode(words, strings, width, count, ids)` interns states in `transfer.ts`'s encoding
//!   into `ids`, an Int32Array, as `fromValue` does, and returns null or the reason it stopped;
//! - `storeEncode(states, width)` writes states in that encoding, as `{ words, strings, count }`;
//! - `storeFingerprints(states, width, order, parents, isReference, fingerprints)` writes TLC's
//!   fingerprints of the states into a BigInt64Array, and `storeResetFingerprints()` forgets
//!   every value's.
//!
//! Each hook here returns what the binding gives JavaScript, or the message of the TypeError it
//! throws for a wrong argument. Where a hook writes into an array JavaScript gave it, it returns
//! the array's new elements for the binding to copy.

use tla_values::trace::{Answer, Argument, Failure, perform};
use tla_values::transfer::{DecodeError, EncodedStates, StateEncoder, decode_states};
use tla_values::{Id, Store};

use crate::value::HostValue;

/// A hook's result, or the message of the TypeError the binding throws.
pub type HookResult = Result<HostValue, String>;

#[cfg(not(target_arch = "wasm32"))]
mod owner {
    use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
    use std::sync::mpsc::{Sender, channel};
    use std::sync::{Mutex, PoisonError};

    use tla_values::fingerprint::{Fingerprints, Polynomial};
    use tla_values::{Store, on_nesting_stack};

    type Job = Box<dyn FnOnce(&mut Store, &mut Fingerprints) + Send>;

    // The thread that owns the store and runs every call's work on it, with a stack for deeply
    // nested values. A thread spawned per call would map that stack each time.
    static STORE_THREAD: Mutex<Option<Sender<Job>>> = Mutex::new(None);

    fn start_store_thread() -> Sender<Job> {
        let (sender, jobs) = channel::<Job>();
        std::thread::spawn(move || {
            on_nesting_stack(move || {
                let (mut store, mut fingerprints) =
                    (Store::new(), Fingerprints::new(Polynomial::get(0)));
                for job in jobs {
                    job(&mut store, &mut fingerprints);
                }
            })
        });
        sender
    }

    /// Runs work on the store and its fingerprints, and returns what it returns, or its panic.
    pub fn with_store<T: Send + 'static>(
        work: impl FnOnce(&mut Store, &mut Fingerprints) -> T + Send + 'static,
    ) -> T {
        let (reply, answer) = channel();
        let job: Job = Box::new(move |store, fingerprints| {
            let _ = reply.send(catch_unwind(AssertUnwindSafe(|| work(store, fingerprints))));
        });
        STORE_THREAD
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get_or_insert_with(start_store_thread)
            .send(job)
            .expect("the store's thread takes work");
        answer
            .recv()
            .expect("the store's thread answers")
            .unwrap_or_else(|panic| resume_unwind(panic))
    }
}

#[cfg(target_arch = "wasm32")]
mod owner {
    use std::cell::RefCell;

    use tla_values::Store;
    use tla_values::fingerprint::{Fingerprints, Polynomial};

    thread_local! {
        static STORE: RefCell<(Store, Fingerprints)> =
            RefCell::new((Store::new(), Fingerprints::new(Polynomial::get(0))));
    }

    /// Runs work on the store and its fingerprints, in place: WebAssembly has one thread.
    pub fn with_store<T: Send + 'static>(
        work: impl FnOnce(&mut Store, &mut Fingerprints) -> T + Send + 'static,
    ) -> T {
        STORE.with(|owned| {
            let (store, fingerprints) = &mut *owned.borrow_mut();
            work(store, fingerprints)
        })
    }
}

use owner::with_store;

/// An argument of `storePerform` as JavaScript gives it: a number, a string, an Int32Array, or an
/// array of strings or of numbers.
pub fn get_argument(value: &HostValue) -> Result<Argument, String> {
    match value {
        HostValue::Number(number) => Ok(Argument::Number(*number)),
        HostValue::Text(text) => Ok(Argument::Text(text.clone())),
        HostValue::Int32s(words) => Ok(Argument::Numbers(
            words.iter().map(|&word| f64::from(word)).collect(),
        )),
        HostValue::Array(elements) => {
            if matches!(elements.first(), Some(HostValue::Text(_))) {
                return elements
                    .iter()
                    .map(|element| match element {
                        HostValue::Text(text) => Ok(text.clone()),
                        _ => Err("an argument's strings must all be strings".to_owned()),
                    })
                    .collect::<Result<_, _>>()
                    .map(Argument::Texts);
            }
            elements
                .iter()
                .map(|element| match element {
                    HostValue::Number(number) => Ok(*number),
                    _ => Err("an argument's numbers must all be numbers".to_owned()),
                })
                .collect::<Result<_, _>>()
                .map(Argument::Numbers)
        }
        _ => Err("an argument must be a number, a string or an array".into()),
    }
}

/// `storePerform(name, args)`.
pub fn store_perform(name: String, arguments: Vec<Argument>) -> HookResult {
    match with_store(move |store, _| perform(store, &name, &arguments)) {
        Ok(Answer::Null) => Ok(HostValue::Null),
        Ok(Answer::Bool(value)) => Ok(HostValue::Bool(value)),
        Ok(Answer::Number(value)) => Ok(HostValue::Number(value as f64)),
        Err(Failure::Bail(bail)) => Ok(HostValue::text(bail.0)),
        Err(Failure::Argument(message)) => Err(message),
    }
}

/// `storeDecode(words, strings, width, count, ids)`: the ids for `ids`, or the reason the store
/// stopped. `ids_length` is the length of `ids`.
pub fn store_decode(encoded: EncodedStates, width: usize, ids_length: usize) -> HookResult {
    if ids_length < width * encoded.count as usize {
        return Err("ids must hold every value of every state".into());
    }
    match with_store(move |store, _| decode_states(store, &encoded, width)) {
        Ok(decoded) => Ok(HostValue::Int32s(
            decoded.into_iter().map(|id| id as i32).collect(),
        )),
        Err(DecodeError::Bail(bail)) => Ok(HostValue::text(bail.0)),
        Err(DecodeError::Malformed(error)) => Err(format!("storeDecode: {error}")),
    }
}

/// The states of a call, checked to be ids of the store's values.
fn get_states(store: &Store, words: &[i32], width: usize) -> Result<Vec<Id>, String> {
    if width == 0 || !words.len().is_multiple_of(width) {
        return Err("states must be whole states of a width above 0".into());
    }
    words
        .iter()
        .map(|&word| match Id::try_from(word) {
            Ok(id) if (id as usize) < store.value_count() => Ok(id),
            _ => Err(format!("{word} is no value's id")),
        })
        .collect()
}

/// `storeEncode(states, width)`.
pub fn store_encode(words: Vec<i32>, width: usize) -> HookResult {
    let encoded = with_store(move |store, _| {
        let states = get_states(store, &words, width)?;
        let mut encoder = StateEncoder::new();
        for state in states.chunks_exact(width) {
            encoder
                .encode(store, state)
                .map_err(|bail| bail.0.to_owned())?;
        }
        Ok::<_, String>(encoder.finish())
    })?;
    Ok(HostValue::Object(vec![
        ("words", HostValue::Int32s(encoded.words)),
        ("strings", HostValue::texts(&encoded.strings)),
        ("count", HostValue::Number(f64::from(encoded.count))),
    ]))
}

/// `storeFingerprints(states, width, order, parents, isReference, fingerprints)`: the
/// fingerprints for `fingerprints`, whose length is `out_length`.
pub fn store_fingerprints(
    words: Vec<i32>,
    width: usize,
    order: &[i32],
    parents: Option<Vec<i32>>,
    is_reference: bool,
    out_length: usize,
) -> HookResult {
    let order = order
        .iter()
        .map(|&index| usize::try_from(index).ok().filter(|&index| index < width))
        .collect::<Option<Vec<usize>>>()
        .ok_or_else(|| "order must hold positions inside a state".to_owned())?;
    let fingerprints = with_store(move |store, fingerprints| {
        let parents = parents.as_deref();
        let states = get_states(store, &words, width)?;
        let count = states.len() / width;
        if parents.is_some_and(|parents| {
            parents.len() < count || parents.iter().take(count).any(|&parent| parent < -1)
        }) {
            return Err("parents must name a state or be -1".to_owned());
        }
        if is_reference {
            fingerprints.get_states_reference(store, &states, width, &order)
        } else {
            fingerprints.get_states(store, &states, width, &order, parents)
        }
        .map_err(|bail| bail.0.to_owned())
    })?;
    if out_length < fingerprints.len() {
        return Err("fingerprints must have room for every state".into());
    }
    Ok(HostValue::BigInt64s(
        fingerprints
            .into_iter()
            .map(|fingerprint| fingerprint as i64)
            .collect(),
    ))
}

/// `storeResetFingerprints()`.
pub fn store_reset_fingerprints() {
    with_store(|_, fingerprints| fingerprints.reset());
}

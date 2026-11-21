//! The values of Prove It's native engine: a hash-consed store of TLA+ values that hands out the
//! same ids as `src/engine/store.ts` for the same operations, TLC's order and the places where TLC
//! fails to compare, TLC's FP64 fingerprints of values and states, TLC's text of values, and
//! `src/transfer.ts`'s encoding of states.

pub mod fingerprint;
pub mod json;
pub mod print;
pub mod random;
pub mod store;
pub mod trace;
pub mod transfer;
pub mod written;

pub use store::{Bail, Id, Store};

/// The prefix of the names of TLC's named registers (`TLCGetSet.NAMED_REGISTER_PREFIX`).
pub const NAMED_REGISTER_PREFIX: &str = "s:";

/// The prefix of a key of TLCGet and TLCSet that names a Java system property, whose value
/// `System.getProperty` gives with the key as the default.
pub const JAVA_PROPERTY_PREFIX: &str = "-D";

/// The path `java.io.File` holds of a name on Unix (`UnixFileSystem.normalize`): without repeated
/// slashes or a final one.
pub fn java_file_path(path: &str) -> String {
    let mut normalized = String::with_capacity(path.len());
    for character in path.chars() {
        if character == '/' && normalized.ends_with('/') {
            continue;
        }
        normalized.push(character);
    }
    if normalized.len() > 1 && normalized.ends_with('/') {
        normalized.pop();
    }
    normalized
}

/// Whether `TLCGetSet.TLCGetStringValue` knows no such key, where it fails ("TLCGet(foo) was
/// undefined."): not one of the keys of its run, a named register or a system property.
pub fn is_unknown_tlc_get_key(key: &str) -> bool {
    !matches!(
        key,
        "diameter"
            | "generated"
            | "distinct"
            | "queue"
            | "duration"
            | "stats"
            | "config"
            | "revision"
            | "spec"
            | "level"
            | "action"
            | "all"
            | "all:named"
    ) && !key.starts_with(NAMED_REGISTER_PREFIX)
        && !key.starts_with(JAVA_PROPERTY_PREFIX)
}

/// Where the JVM and its libraries name the system properties they set themselves.
pub const JVM_PROPERTY_NAMESPACES: [&str; 16] = [
    "java.", "javax.", "jdk.", "sun.", "os.", "user.", "file.", "line.", "path.", "native.",
    "stdout.", "stderr.", "awt.", "http.", "https.", "ftp.",
];

/// Where TLC and the libraries it bundles name the system properties they read.
pub const TLC_PROPERTY_NAMESPACES: [&str; 9] = [
    "tlc2", "tla2", "pcal", "util", "org.", "com.", "net.", "io.", "lambda",
];

/// Whether TLCSet may set the system property of this name as the native checker follows it: one
/// with a name, that neither the JVM nor TLC reads, whose value TLC's run then doesn't depend on.
pub fn is_settable_property(name: &str) -> bool {
    !name.is_empty()
        && !JVM_PROPERTY_NAMESPACES
            .iter()
            .chain(&TLC_PROPERTY_NAMESPACES)
            .any(|namespace| name.starts_with(namespace))
}

/// TLCGlobals.setBound for a ValueVec built from its default empty capacity.
pub const SET_BOUND: usize = 1_000_000;
pub const SET_BOUND_EXCEEDED: Bail = Bail("constructed a set with too many elements");

/// Checks an emitted element before insertion, after computing it and before deduplication.
pub fn check_set_insertion(length: usize) -> Result<(), Bail> {
    if length >= SET_BOUND {
        Err(SET_BOUND_EXCEEDED)
    } else {
        Ok(())
    }
}

/// The stack the store's callers run it on. `compare`, `equals` and the transfer encoding follow
/// nested values by recursion, and a Rust stack overflow aborts the process rather than failing,
/// so they run on a thread whose stack holds values nested 100,000 deep, past where the TypeScript
/// store runs out of stack (between 10,000 and 30,000 in Bun). The stack is reserved, not
/// committed.
pub const NESTING_STACK_BYTES: usize = if cfg!(debug_assertions) {
    1024 * 1024 * 1024
} else {
    256 * 1024 * 1024
};

/// Runs work on a thread with a stack for deeply nested values, and returns what it returns.
pub fn on_nesting_stack<T: Send>(work: impl FnOnce() -> T + Send) -> T {
    // WebAssembly runs on one thread, whose stack the module sets as it links.
    #[cfg(target_arch = "wasm32")]
    return work();
    #[cfg(not(target_arch = "wasm32"))]
    let journal = written::current();
    #[cfg(not(target_arch = "wasm32"))]
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(NESTING_STACK_BYTES)
            .spawn_scoped(scope, move || written::enter(journal.as_ref(), work))
            .expect("a thread for nested values")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

#[cfg(test)]
mod tests {
    #[test]
    fn java_file_path_drops_repeated_and_final_slashes() {
        for (path, normalized) in [
            ("/", "/"),
            ("//", "/"),
            ("a//b/", "a/b"),
            ("dir//vars.chkpt", "dir/vars.chkpt"),
            ("", ""),
        ] {
            assert_eq!(super::java_file_path(path), normalized);
        }
    }
}

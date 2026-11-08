//! Prove It's native engine, loaded by `src/engine/native.ts` as an N-API addon. It decodes the
//! engine IR and compiles nothing yet, so `check` declines every model and the TypeScript engine
//! checks it.

#[cfg(not(test))]
mod binding;

/// The version of the contract between the loader and the addon: the exports, their arguments
/// and the engine IR. The loader uses the TypeScript engine when it expects another.
pub const ABI_VERSION: i32 = 1;

/// What a check found. Declining happens before any state is produced, so the TypeScript engine
/// starts from scratch.
#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Declined(String),
}

/// Checks the model the engine IR describes.
pub fn check(ir: &[u8]) -> Outcome {
    match tla_ir::decode(ir) {
        Err(error) => Outcome::Declined(format!("the engine IR doesn't decode: {error}")),
        Ok(_) => Outcome::Declined("the native engine compiles nothing yet".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn declines_what_isnt_an_ir() {
        assert_eq!(
            check(&[1, 2, 3]),
            Outcome::Declined("the engine IR doesn't decode: at word 0: 3 bytes are no IR".into())
        );
    }

    #[test]
    fn declines_every_model() {
        let commit = include_bytes!(
            "../../../../tests/conformance/ir/examples/specifications/transaction_commit/TCommit.ir"
        );
        assert_eq!(
            check(commit),
            Outcome::Declined("the native engine compiles nothing yet".into())
        );
    }
}

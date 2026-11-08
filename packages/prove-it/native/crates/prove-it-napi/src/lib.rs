//! Prove It's native engine, loaded by `src/engine/native.ts` as an N-API addon. It compiles
//! nothing yet, so `check` declines every model and the TypeScript engine checks it.

#[cfg(not(test))]
mod binding;

/// The version of the contract between the loader and the addon: the exports, their arguments
/// and the engine IR. The loader uses the TypeScript engine when it expects another.
pub const ABI_VERSION: i32 = 1;

/// What a check found. Declining happens before any state is produced, so the TypeScript engine
/// starts from scratch.
#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Declined(&'static str),
}

/// Checks the model the engine IR describes.
pub fn check(_ir: &[u8]) -> Outcome {
    Outcome::Declined("the native engine compiles nothing yet")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn declines_every_model() {
        assert_eq!(
            check(&[]),
            Outcome::Declined("the native engine compiles nothing yet")
        );
        assert_eq!(
            check(&[1, 2, 3]),
            Outcome::Declined("the native engine compiles nothing yet")
        );
    }
}

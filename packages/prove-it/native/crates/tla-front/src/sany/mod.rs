//! SANY's semantic graph and its XMLExporter (`tla2sany.semantic`, `tla2sany.xml`), ported from
//! `src/sany`: the nodes SANY builds for a specification, with their UIDs, levels and comments,
//! and the XML that tlapm and other tools read.
//!
//! Only TLC master's SANY is ported; TLC 1.7.4's is retired. What SANY prints (its errors and
//! warnings) is `report.rs`'s: the graph is built only for a specification SANY accepts, and a
//! throw of the TypeScript generator, or an error `report.rs` didn't report, is `NotYet`.

pub mod nodes;
pub mod selectors;

pub type Result<T> = std::result::Result<T, crate::errors::FrontError>;

/// The `NotYet` the port returns where the TypeScript throws.
pub fn not_yet<T>(reason: impl Into<String>) -> Result<T> {
    Err(crate::errors::FrontError::NotYet(reason.into()))
}

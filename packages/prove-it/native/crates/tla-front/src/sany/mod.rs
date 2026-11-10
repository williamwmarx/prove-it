//! SANY's semantic graph and its XMLExporter (`tla2sany.semantic`, `tla2sany.xml`), ported from
//! `src/sany`: the nodes SANY builds for a specification, with their UIDs, levels and comments,
//! and the XML that tlapm and other tools read.
//!
//! Only TLC master's SANY is ported; TLC 1.7.4's is retired. What SANY prints (its errors and
//! warnings) is `report.rs`'s: the graph is built only for a specification SANY accepts, and a
//! throw of the TypeScript generator, or an error `report.rs` didn't report, is `NotYet`.

pub mod export;
pub mod levels;
pub mod nodes;
pub mod selectors;
pub mod xml;

pub type Result<T> = std::result::Result<T, crate::errors::FrontError>;

/// The `NotYet` the port returns where the TypeScript throws.
pub fn not_yet<T>(reason: impl Into<String>) -> Result<T> {
    Err(crate::errors::FrontError::NotYet(reason.into()))
}

/// `SanySpecification`: the graph SANY builds for a specification, its root module, every module
/// in the order SANY analyzes them, the messages it reports, and the builtins of the
/// specification.
#[derive(Clone, Debug)]
pub struct SanySpecification {
    pub graph: nodes::Graph,
    pub root: nodes::NodeId,
    pub modules: Vec<nodes::NodeId>,
    pub messages: Vec<nodes::SanyMessage>,
    pub builtins: Vec<nodes::NodeId>,
}

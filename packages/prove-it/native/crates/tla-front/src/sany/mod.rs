//! SANY's semantic graph and its XMLExporter (`tla2sany.semantic`, `tla2sany.xml`), ported from
//! `src/sany`: the nodes SANY builds for a specification, with their UIDs, levels and comments,
//! and the XML that tlapm and other tools read.
//!
//! Only TLC master's SANY is ported; TLC 1.7.4's is retired. What SANY prints (its errors and
//! warnings) is `report.rs`'s: the graph is built only for a specification SANY accepts, and a
//! throw of the TypeScript generator, or an error `report.rs` didn't report, is `NotYet`.

pub mod builtins;
pub mod export;
pub mod generator;
pub mod levels;
pub mod messages;
pub mod nodes;
pub mod selectors;
pub mod source;
pub mod xml;

pub type Result<T> = std::result::Result<T, crate::errors::FrontError>;

/// What `Generator.endOpDefNode` throws when a module defines more operators than its RECURSIVE
/// statements declared, as `SANY.parse` prints it.
pub const GENERATOR_EXCEPTION: &str = "util.WrongInvocationException: Defined more recursive operators than were declared in RECURSIVE statements.";

/// The `NotYet` the port returns where the TypeScript throws.
pub fn not_yet<T>(reason: impl Into<String>) -> Result<T> {
    Err(crate::errors::FrontError::NotYet(reason.into()))
}

/// What starts the reason of a `NotYet` for a shape where linking would report otherwise than
/// SANY too, so SANY's report declines rather than taking linking's messages.
pub const UNLINKABLE: &str = "SANY's report of ";

/// The `NotYet` for a shape whose report neither the generator nor linking gives.
pub fn not_yet_unlinkable<T>(reason: &str) -> Result<T> {
    not_yet(format!("{UNLINKABLE}{reason}"))
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

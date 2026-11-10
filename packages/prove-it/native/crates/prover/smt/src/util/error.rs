//! The SMT solver's errors, `src/errors.ts`'s `Smt*Error` classes.

use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SmtError {
    /// `SmtCanceledError`: the limits stopped the work in the middle of a rewrite or a search.
    Canceled,
    /// `SmtUnsupportedError`: input outside the subset tlapm emits.
    Unsupported(String),
    /// `SmtInvariantError`: a bug in the port.
    Invariant(String),
    /// `SmtParseError`: malformed SMT-LIB.
    Parse(String),
}

impl fmt::Display for SmtError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtError::Canceled => formatter.write_str("the SMT solver was canceled"),
            SmtError::Unsupported(message)
            | SmtError::Invariant(message)
            | SmtError::Parse(message) => formatter.write_str(message),
        }
    }
}

impl std::error::Error for SmtError {}

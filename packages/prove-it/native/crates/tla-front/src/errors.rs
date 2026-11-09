//! The errors of `src/errors.ts` the front end raises, with the same messages.

/// Where a syntax error is, as `SyntaxFailure` in `errors.ts`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SyntaxFailure {
    pub reason: String,
    pub line: u32,
    pub column: u32,
    pub is_end: bool,
}

/// `TlaSyntaxError`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SyntaxError {
    pub message: String,
    pub failure: Option<SyntaxFailure>,
}

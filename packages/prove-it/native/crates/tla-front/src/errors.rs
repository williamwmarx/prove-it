//! The errors of `src/errors.ts` the front end raises, with the same messages.

/// Where a syntax error is, as `SyntaxFailure` in `errors.ts`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SyntaxFailure {
    pub reason: String,
    pub line: u32,
    pub column: u32,
    pub is_end: bool,
}

/// An error SANY reports at a location, such as "In module M" or a range in a module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SanyError {
    pub location: String,
    pub message: String,
}

/// The errors SANY reports for a spec, and the warnings it prints before them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SanyReport {
    pub errors: Vec<SanyError>,
    pub warnings: Vec<SanyError>,
    pub is_fatal: bool,
    pub parse_error: Option<String>,
}

/// `TlaSyntaxError`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SyntaxError {
    pub message: String,
    pub failure: Option<SyntaxFailure>,
    pub sany: Option<Box<SanyReport>>,
}

impl SyntaxError {
    /// `createSanyError` with errors alone.
    pub fn sany(errors: Vec<SanyError>) -> SyntaxError {
        SyntaxError {
            message: errors
                .iter()
                .map(|error| format!("{}\n\n{}", error.location, error.message))
                .collect::<Vec<_>>()
                .join("\n\n"),
            failure: None,
            sany: Some(Box::new(SanyReport {
                errors,
                warnings: Vec::new(),
                is_fatal: false,
                parse_error: None,
            })),
        }
    }
}

/// `formatRange`.
pub fn format_range(range: &crate::ast::SourceRange) -> String {
    format!(
        "line {}, col {} to line {}, col {} of module {}",
        range.start.line, range.start.column, range.end.line, range.end.column, range.module
    )
}

/// `describeRange`: where an expression is written, which TLC's messages print.
pub fn describe_range(expression: &crate::ast::Expression) -> String {
    let location = &expression.location;
    location.range.as_ref().map_or_else(
        || format!("line {}, column {}", location.line, location.column),
        format_range,
    )
}

/// What stops the front end: an error of `errors.ts` it raises as TypeScript does, or a construct
/// it doesn't cover yet.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrontError {
    /// `TlaSyntaxError`.
    Syntax(SyntaxError),
    /// `TlaEvaluationError`, which the front end raises for a literal TLC can't hold.
    Evaluation(String),
    /// `TlaConfigError`.
    Config(String),
    /// What the Rust front end doesn't cover yet.
    NotYet(String),
}

impl From<SyntaxError> for FrontError {
    fn from(error: SyntaxError) -> FrontError {
        FrontError::Syntax(error)
    }
}

impl SyntaxError {
    /// A `TlaSyntaxError` with a message alone.
    pub fn new(message: impl Into<String>) -> SyntaxError {
        SyntaxError {
            message: message.into(),
            failure: None,
            sany: None,
        }
    }
}

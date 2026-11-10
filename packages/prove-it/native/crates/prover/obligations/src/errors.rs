//! The errors of `src/errors.ts` the obligations throw: `TlaProofError` (with `TlapmBugError`, which
//! keeps its name), `TlaProverError` and `TlaUnsupportedError`.

use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ObligationError {
    /// `TlaProofError`: `failure` is tlapm's `Failure` text when it raised one, and `exception` the
    /// exception it prints, `Failure("…")` by default.
    Proof {
        message: String,
        failure: Option<String>,
        exception: String,
    },
    /// `TlaProverError`: a backend can't take an obligation.
    Prover(String),
    /// `TlaUnsupportedError`.
    Unsupported(String),
}

pub type Result<T> = std::result::Result<T, ObligationError>;

/// JSON.stringify of a string, as `TlaProofError` quotes its failure.
pub fn quote_json(text: &str) -> String {
    let mut quoted = String::with_capacity(text.len() + 2);
    quoted.push('"');
    for character in text.chars() {
        match character {
            '"' => quoted.push_str("\\\""),
            '\\' => quoted.push_str("\\\\"),
            '\n' => quoted.push_str("\\n"),
            '\r' => quoted.push_str("\\r"),
            '\t' => quoted.push_str("\\t"),
            '\u{8}' => quoted.push_str("\\b"),
            '\u{c}' => quoted.push_str("\\f"),
            control if (control as u32) < 0x20 => {
                quoted.push_str(&format!("\\u{:04x}", control as u32));
            }
            other => quoted.push(other),
        }
    }
    quoted.push('"');
    quoted
}

impl ObligationError {
    /// `new TlaProofError(message)`: the failure is the message.
    pub fn proof(message: impl Into<String>) -> Self {
        let message = message.into();
        Self::Proof {
            exception: format!("Failure({})", quote_json(&message)),
            failure: Some(message.clone()),
            message,
        }
    }

    /// `new TlaProofError(message, {failure})`.
    pub fn proof_failure(message: impl Into<String>, failure: impl Into<String>) -> Self {
        let failure = failure.into();
        Self::Proof {
            message: message.into(),
            exception: format!("Failure({})", quote_json(&failure)),
            failure: Some(failure),
        }
    }

    /// `new TlaProofError(message, {exception})`.
    pub fn proof_exception(message: impl Into<String>, exception: impl Into<String>) -> Self {
        Self::Proof {
            message: message.into(),
            failure: None,
            exception: exception.into(),
        }
    }

    /// `new TlapmBugError(exception)`; the default exception is `Assert_failure`.
    pub fn bug(exception: impl Into<String>) -> Self {
        Self::proof_exception("Oops, this seems to be a bug in TLAPM.", exception)
    }

    /// `new TlapmBugError()`.
    pub fn assert_failure() -> Self {
        Self::bug("Assert_failure")
    }

    pub fn prover(message: impl Into<String>) -> Self {
        Self::Prover(message.into())
    }

    pub fn unsupported(message: impl Into<String>) -> Self {
        Self::Unsupported(message.into())
    }

    pub fn message(&self) -> &str {
        match self {
            Self::Proof { message, .. } | Self::Prover(message) | Self::Unsupported(message) => {
                message
            }
        }
    }

    /// The error's `name`, as JavaScript reports it.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Proof { .. } => "TlaProofError",
            Self::Prover(_) => "TlaProverError",
            Self::Unsupported(_) => "TlaUnsupportedError",
        }
    }
}

impl fmt::Display for ObligationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.message())
    }
}

impl std::error::Error for ObligationError {}

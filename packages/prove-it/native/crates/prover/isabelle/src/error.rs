//! The exceptions the port raises, as `TlaIsabelleError` and the local exception classes of the
//! TypeScript define them. Isabelle's tactics raise and handle them as control flow, so every
//! function that can raise one returns a `Res`, and a handler matches on the variant it catches
//! and propagates the rest with `?`, as the TypeScript rethrows.

/// The exceptions Isabelle raises: ERROR for a rejected theory or a failed proof, TERM, TYPE and
/// THM for an ill-formed term, type or theorem, and Interrupt when the limits run out.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Exception {
    Error,
    Term,
    Type,
    Thm,
    Interrupt,
}

impl Exception {
    /// The name decideIsabelle reports as the statistic `stop`.
    pub fn name(self) -> &'static str {
        match self {
            Exception::Error => "ERROR",
            Exception::Term => "TERM",
            Exception::Type => "TYPE",
            Exception::Thm => "THM",
            Exception::Interrupt => "Interrupt",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// `TlaIsabelleError`.
    Isabelle(Exception, String),
    /// Where JavaScript would overflow its stack: the recursion went deeper than the port allows
    /// (`interrupt::check_stack`). decideIsabelle answers unknown, as for a stack overflow.
    Stack,
    /// pattern.ts's Unif, NotPattern and Match.
    Unif,
    NotPattern,
    Match,
    /// unify.ts's CantUnify and ChangeFail.
    CantUnify,
    ChangeFail,
    /// thm.ts's Compose.
    Compose,
    /// rewriter.ts's MatchFailure.
    MatchFailure,
    /// hypsubst.ts's NoMatch and EqVar.
    NoMatch,
    EqVar,
    /// blast.ts's Trans, with its message.
    Trans(String),
    /// blast's state.ts Backtrack, with the token of the choice point it returns to: `None` for
    /// PROVE, the end of the search. Tokens are numbers unique within a search, standing for the
    /// fresh objects the TypeScript compares by identity.
    Backtrack(Option<u64>),
}

pub type Res<T> = Result<T, Error>;

/// `new TlaIsabelleError(exception, message)`, ready to return with `Err`.
pub fn isabelle_error(exception: Exception, message: impl Into<String>) -> Error {
    Error::Isabelle(exception, message.into())
}

pub fn error_exn(message: impl Into<String>) -> Error {
    isabelle_error(Exception::Error, message)
}

pub fn term_exn(message: impl Into<String>) -> Error {
    isabelle_error(Exception::Term, message)
}

pub fn type_exn(message: impl Into<String>) -> Error {
    isabelle_error(Exception::Type, message)
}

pub fn thm_exn(message: impl Into<String>) -> Error {
    isabelle_error(Exception::Thm, message)
}

impl Error {
    /// `error instanceof TlaIsabelleError && error.exception === exception`.
    pub fn is(&self, exception: Exception) -> bool {
        matches!(self, Error::Isabelle(raised, _) if *raised == exception)
    }
}

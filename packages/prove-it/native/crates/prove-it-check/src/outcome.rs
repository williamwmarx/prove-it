//! What a check found, as the library's `check` reports it (`src/check-result.ts`), recorded as the
//! check prints it: the status, the counts, what the spec printed as TLC searched, and each
//! violation or error TLC reports with the states it prints after it.

use crate::plain::Variable;

#[derive(Default)]
pub struct Outcome {
    /// The status, where the check ends as the library reports it: none where TLC stops before it
    /// searches, such as at a spec SANY rejects, for which the library throws.
    pub status: Option<&'static str>,
    /// The counts of TLC's statistics, which are zero where TLC prints none, as at a violation by an
    /// initial state.
    pub counts: Counts,
    /// What the spec printed as TLC computed its constants, checked its assumptions and searched,
    /// and as it checked the postconditions after a search that completed, each print as a line.
    pub prints: Vec<String>,
    /// SANY's warnings, which the library's check prints before the prints where its caller
    /// didn't print SANY's report.
    pub sany_warnings: Vec<String>,
    pub violations: Vec<Reported>,
    /// TLC's messages as the check printed them, the library's progress events: each one's code,
    /// level and text, and how many of `prints` came before it.
    pub messages: Vec<Message>,
}

pub struct Message {
    pub code: u32,
    pub level: u8,
    pub text: String,
    pub prints_before: usize,
    /// The search's counts when TLC checks the temporal properties part way through it, which
    /// the message doesn't print.
    pub counts: Option<Counts>,
}

#[derive(Clone, Copy, Default)]
pub struct Counts {
    pub generated: u64,
    pub distinct: u64,
    pub queued: u64,
    pub depth: u64,
}

/// A violation or an error TLC reports: its message's code and text, and the behavior it prints
/// with it. A lasso's cycle starts at `loop_start`, which is the last state where it stutters.
pub struct Reported {
    pub code: u32,
    pub headline: String,
    pub states: Vec<ReportedState>,
    pub loop_start: Option<usize>,
}

/// A state of a behavior: TLC's label of the step to it, and its variables in TLC's order, or the
/// fields of the ALIAS TLC prints in their place.
pub struct ReportedState {
    pub label: String,
    pub variables: Vec<Variable>,
}

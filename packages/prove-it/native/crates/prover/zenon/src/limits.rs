//! When Zenon gives up: past the deadline, past the step limit, or once the cancel cell is set.
//! tlapm kills Zenon at its deadline whether Zenon is searching or printing the proof, so the
//! search, the checker and the printer each check the limits at every step.

use prove_decide::Limits;

/// Why the limits have stopped Zenon, if they have: `getStopReason`.
pub fn get_stop_reason(limits: &Limits) -> Option<&'static str> {
    if limits.is_step_limit_passed() {
        Some("step limit")
    } else if limits.is_past_deadline() {
        Some("time limit")
    } else if limits.is_canceled() {
        Some("aborted")
    } else {
        None
    }
}

/// Counts a step, and returns why the limits stop Zenon now, if they do: `getLimitFailure`.
pub fn get_limit_failure(limits: &Limits) -> Option<&'static str> {
    if limits.is_step_limit_reached() {
        Some("step limit")
    } else {
        get_stop_reason(limits)
    }
}

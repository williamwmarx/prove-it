// When Zenon gives up: past the deadline, a time from Date.now(), past the step limit, or once the
// signal aborts. tlapm kills Zenon at its deadline whether Zenon is searching or printing the proof,
// so the search, the checker and the printer each check the limits at every step.
import { isStepLimitReached, type Steps } from "../verdict";

export interface Limits {
  deadline: number;
  signal: AbortSignal | undefined;
  steps: Steps;
}

// Why the limits have stopped Zenon, if they have.
export const getStopReason = (limits: Limits) =>
  limits.steps.count > limits.steps.limit
    ? "step limit"
    : Date.now() > limits.deadline
      ? "time limit"
      : limits.signal?.aborted === true
        ? "aborted"
        : undefined;

// Counts a step, and returns why the limits stop Zenon now, if they do.
export const getLimitFailure = (limits: Limits) =>
  isStepLimitReached(limits.steps) ? "step limit" : getStopReason(limits);

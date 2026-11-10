// Isabelle interrupts a proof that runs out of time, wherever it is; this port checks for that at
// the points where Isabelle's tactics and unifier spend their time.

import { TlaIsabelleError } from "../../../errors";
import { isStepLimitReached, type Steps } from "../../verdict";

// When a proof gives up: past the deadline, a time from Date.now(), past the step limit, or once
// the signal aborts. Each check is a step.
export interface Limits {
  readonly deadline: number;
  readonly signal?: AbortSignal;
  readonly steps: Steps;
}

// tlapm reports no success for an interrupted proof.
export const checkInterrupt = (limits: Limits) => {
  if (
    isStepLimitReached(limits.steps) ||
    Date.now() > limits.deadline ||
    limits.signal?.aborted === true
  )
    throw new TlaIsabelleError("Interrupt", "Interrupt");
};

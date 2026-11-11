import type { CheckStatus, EvaluationFailure, InitialStateViolation, Violation } from "../check";
import { TlaEvaluationError, UNEXPECTED_EXCEPTION } from "../errors";
import { EXIT_STATUS, setExitCode } from "../exit-codes";
import { formatState } from "../values";
import { formatInnerMessage, MESSAGE_CODE } from "./messages";
import type { TlcVersion } from "./version";

// The message TLC reports a violation or an error with: its code and its text.
export interface Headline {
  code: number;
  text: string;
}

export const getInitialViolationHeadline = (
  status: InitialStateViolation["status"],
  name: string | undefined,
): Headline =>
  status === "invariant-violation"
    ? {
        code: MESSAGE_CODE.invariantViolatedInitial,
        text: `Invariant ${name} is violated by the initial state:`,
      }
    : {
        code: MESSAGE_CODE.propertyViolatedInitial,
        text: `Property ${name} is violated by the initial state:`,
      };

// TLC 1.7.4 doesn't name the properties, and later versions name none when they can't tell which.
const getTemporalHeadline = (names: string[], version: TlcVersion) =>
  version === "1.7.4" || names.length === 0
    ? "Temporal properties were violated.\n"
    : names.length === 1
      ? `Temporal property ${names[0]} was violated.\n`
      : `Temporal properties ${names.slice(0, -1).join(", ")}${names.length > 2 ? "," : ""} and ${names[names.length - 1]} were violated.\n`;

// TLC prints a violation by an initial state without the behavior or the statistics.
export const isInitialViolation = (status: CheckStatus, violation: Violation) =>
  violation.loopStart === undefined &&
  violation.trace.length === 1 &&
  (status === "invariant-violation" || status === "liveness-violation");

// The message TLC reports a violation with, but for the state of an initial one, which it prints in
// the same message.
export const getViolationHeadline = (
  status: CheckStatus,
  violation: Violation,
  isTool: boolean,
  version: TlcVersion,
): Headline | undefined => {
  const name = violation.name;
  const isInitial = isInitialViolation(status, violation);
  const temporal = {
    code: MESSAGE_CODE.temporalPropertyViolated,
    text: getTemporalHeadline(violation.properties ?? [name], version),
  };
  return {
    success: undefined,
    error: undefined,
    "assumption-violation": violation.message
      ? {
          code: MESSAGE_CODE.assumptionEvaluationError,
          text: formatInnerMessage(
            MESSAGE_CODE.assumptionEvaluationError,
            `Evaluating assumption ${name} failed.\n${violation.message}`,
            isTool,
          ),
        }
      : { code: MESSAGE_CODE.assumptionFalse, text: `Assumption ${name} is false.` },
    deadlock: { code: MESSAGE_CODE.deadlockReached, text: "Deadlock reached." },
    "invariant-violation": isInitial
      ? getInitialViolationHeadline("invariant-violation", name)
      : { code: MESSAGE_CODE.invariantViolatedBehavior, text: `Invariant ${name} is violated.` },
    "property-violation": temporal,
    "liveness-violation":
      violation.loopStart !== undefined
        ? temporal
        : isInitial
          ? getInitialViolationHeadline("liveness-violation", name)
          : {
              code: MESSAGE_CODE.actionPropertyViolatedBehavior,
              text: `Action property ${name} is violated.`,
            },
    "postcondition-violation": {
      code: violation.postcondition?.code ?? MESSAGE_CODE.general,
      text: violation.message ?? `Postcondition ${name} is false.`,
    },
  }[status];
};

// The message TLC reports a failure with: on an initial state, with the state, which TLC prints as
// it reports the error, so a state it can't print fails outside the checker, which TLC reports as
// an exception it did not expect.
export const getFailureHeadline = (failure: EvaluationFailure, isTool: boolean): Headline => {
  const message = isTool ? failure.toolMessage : failure.message;
  const initialState = failure.initialState;
  if (!initialState) return { code: failure.code, text: message };
  const state = (() => {
    try {
      return formatState(initialState);
    } catch (error) {
      if (!(error instanceof TlaEvaluationError)) throw error;
      throw setExitCode(
        new TlaEvaluationError(`${UNEXPECTED_EXCEPTION}${error.message}`),
        EXIT_STATUS.error,
      );
    }
  })();
  return {
    code: MESSAGE_CODE.initialState,
    text: `${message}\nWhile working on the initial state:\n${state}`,
  };
};

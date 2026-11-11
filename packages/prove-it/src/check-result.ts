// What check returns: each state of a behavior TLC reports, variable by variable, as TLC prints it
// and as plain data. The native check records it as it prints (prove-it-check's outcome.rs); the
// interpreter's result converts to it, until the interpreter goes.

import type {
  CheckProgress as SearchProgress,
  CheckResult as SearchResult,
  CheckStatus,
  TraceStep as SearchStep,
  Violation as SearchViolation,
} from "./check";
import type { NativeCheckOutcome } from "./engine/native";
import { TlaEvaluationError, UNEXPECTED_EVAL_EXCEPTION, UNEXPECTED_EXCEPTION } from "./errors";
import { prettyPrint } from "./pretty-print";
import {
  getFailureHeadline,
  getViolationHeadline,
  type Headline,
  isInitialViolation,
} from "./tlc/headlines";
import { formatInnerMessage, isEvalException, MESSAGE_CODE } from "./tlc/messages";
import type { TlcVersion } from "./tlc/version";
import { formatValue, toFiniteFunction, UNDEFINED_VARIABLE, type Value } from "./values";

// A value as plain data: a boolean, an integer or a string as itself; a function over 1..n, such as
// a sequence or a tuple, as an array; a record, or any function whose keys are all strings none of
// which starts with "@", as an object; and, tagged by a key that starts with "@", any other
// function as its pairs, a set as its elements, a model value as its name, and a set or function
// TLC keeps lazy, such as Nat, as TLC's text of it, as TLC's toString writes it before its pretty
// printer breaks the lines. Keys and elements are in TLC's order.
export type PlainValue =
  | boolean
  | number
  | string
  | PlainValue[]
  | PlainRecord
  | { "@function": [PlainValue, PlainValue][] }
  | { "@set": PlainValue[] }
  | { "@model": string }
  | { "@lazy": string };

interface PlainRecord {
  [field: string]: PlainValue;
}

// A variable of a state: TLC's text of its value, as TLC prints it in a trace, and the value as
// plain data, null where TLC prints null for a variable a successor leaves undefined, and wherever
// the data couldn't be exactly TLC's.
export interface TraceVariable {
  text: string;
  value: PlainValue | null;
}

export interface TraceStep {
  // "Initial predicate", or TLC's name, parameters and location for the action that took the step.
  label: string;
  // The variables in TLC's order, or the fields of the ALIAS TLC prints in their place.
  variables: Record<string, TraceVariable>;
}

// A violation or an error TLC reports: its message's code and text, and the behavior TLC prints
// with it. A lasso's cycle starts at the state at loopStart, the last one where it stutters.
export interface Violation {
  code: number;
  headline: string;
  states: TraceStep[];
  loopStart?: number;
}

// The counts are those TLC prints in its statistics, and zero where it prints none, as at a
// violation by an initial state or a false assumption.
export interface CheckResult {
  status: CheckStatus;
  // What TLC reports, in order: the violation or error the search stopped at, then what TLC reports
  // after it, such as a temporal property a deadlock violates or a postcondition that fails. With
  // -continue, each violation the search went on past comes first.
  violations: Violation[];
  generatedStates: number;
  distinctStates: number;
  queuedStates: number;
  depth: number;
}

// The points of the search at which TLC prints a message, a violation -continue goes on past
// among them.
export type CheckProgress =
  | Exclude<SearchProgress, { kind: "violation" }>
  | { kind: "violation"; status: CheckStatus; violation: Violation };

// The most elements, of sets, functions and sequences at any depth, that a variable's plain data
// holds; past it the value is null, while its text stays TLC's. It is TLC's own bound on the
// elements of a set it builds (TLCGlobals.setBound, 1000000 by default), so data the bound cuts
// off is of a value TLC itself would refuse to enumerate, such as an interval it prints as 1..n.
const MAXIMUM_PLAIN_ELEMENTS = 1_000_000;

interface Budget {
  remaining: number;
}

// Takes `count` elements from the budget, if it has them.
const isWithin = (budget: Budget, count: number) => {
  if (count > budget.remaining) return false;
  budget.remaining -= count;
  return true;
};

const isPlain = (value: PlainValue | null): value is PlainValue => value !== null;

// The values as plain data, or null where one can't be.
const toPlainValues = (values: Value[], budget: Budget) => {
  if (!isWithin(budget, values.length)) return null;
  const plain = values.map((value) => toPlain(value, budget));
  return plain.every(isPlain) ? plain : null;
};

const toPlainFunction = (domain: Value[], range: Value[], budget: Budget): PlainValue | null => {
  const keys = toPlainValues(domain, budget);
  const values = keys && toPlainValues(range, budget);
  if (keys === null || values === null) return null;
  const isSequence = domain.every((key, index) => key === index + 1);
  const isRecord =
    domain.length > 0 && domain.every((key) => typeof key === "string" && !key.startsWith("@"));
  if (isSequence) return values;
  if (isRecord) return Object.fromEntries(domain.map((key, index) => [String(key), values[index]]));
  return { "@function": keys.map((key, index) => [key, values[index]]) };
};

// A value as plain data, as prove-it-check's plain.rs writes the native one: null where TLC can't
// print the value, as a set it can't normalize, where its text wouldn't be TLC's, where the
// interpreter marks a variable a state leaves undefined, and past the budget.
const toPlain = (value: Value, budget: Budget): PlainValue | null => {
  if (typeof value !== "object") return value;
  if (value === UNDEFINED_VARIABLE) return null;
  if (value.kind === "ModelValue") return { "@model": value.name };
  if (value.kind === "MixedSet") return null;
  if (value.kind === "Set") {
    const elements = toPlainValues(value.elements, budget);
    return elements && { "@set": elements };
  }
  if (value.kind === "Interval") {
    const size = Math.max(0, value.high - value.low + 1);
    return isWithin(budget, size)
      ? { "@set": Array.from({ length: size }, (_, index) => value.low + index) }
      : null;
  }
  if (value.kind === "Function") return toPlainFunction(value.domain, value.range, budget);
  // A function TLC keeps lazy over a set it enumerates is the function it converts to, unless its
  // domain is past the budget.
  if (value.kind === "LazyFunction" && typeof value.domain === "object") {
    const domain = value.domain;
    const size =
      domain.kind === "Set"
        ? domain.elements.length
        : domain.kind === "Interval"
          ? Math.max(0, domain.high - domain.low + 1)
          : undefined;
    if (size !== undefined && size > budget.remaining) return null;
    if (size !== undefined) {
      const enumerated = toFiniteFunction(value);
      return toPlainFunction(enumerated.domain, enumerated.range, budget);
    }
  }
  // The interpreter writes a lazy function or set filter it has no source for as no TLC text.
  if ((value.kind === "LazyFunction" || value.kind === "FilteredSet") && !value.source) {
    return null;
  }
  return { "@lazy": formatValue(value) };
};

const toPlainValue = (value: Value) => toPlain(value, { remaining: MAXIMUM_PLAIN_ELEMENTS });

// A step as TLC prints it, or the error TLC raises printing it: TLC normalizes each value it prints,
// which fails for a set whose elements it can't compare.
const toTraceStep = (step: SearchStep): TraceStep | TlaEvaluationError => {
  try {
    return {
      label: step.label ?? step.action ?? "Initial predicate",
      variables: Object.fromEntries(
        Object.entries(step.state).map(([name, value]) => [
          name,
          { text: prettyPrint(formatValue(value)), value: toPlainValue(value) },
        ]),
      ),
    };
  } catch (error) {
    if (!(error instanceof TlaEvaluationError)) throw error;
    return error;
  }
};

// What TLC reports of a violation and its behavior: the violation with its states, or, where TLC
// fails to print a state, the states before it and then the exception TLC reports, after which it
// reports nothing more.
const toViolation = (
  headline: Headline,
  steps: SearchStep[],
  isTool: boolean,
  loopStart?: number,
): Violation[] => {
  const states = steps.map(toTraceStep);
  const failed = states.findIndex((state) => state instanceof TlaEvaluationError);
  const error = states[failed];
  const printed = states.slice(0, failed === -1 ? states.length : failed);
  return [
    {
      code: headline.code,
      headline: headline.text,
      states: printed.filter((state): state is TraceStep => !(state instanceof TlaEvaluationError)),
      ...(loopStart !== undefined && { loopStart }),
    },
    ...(error instanceof TlaEvaluationError
      ? [
          {
            code: MESSAGE_CODE.general,
            headline: formatInnerMessage(
              MESSAGE_CODE.general,
              `${isEvalException(error) ? UNEXPECTED_EVAL_EXCEPTION : UNEXPECTED_EXCEPTION}${error.message}`,
              isTool,
            ),
            states: [],
          },
        ]
      : []),
  ];
};

// What TLC reports, in order, of each violation: once TLC fails to print one, nothing after it.
const toReported = (reports: Violation[][]) =>
  reports.slice(0, reports.findIndex((report) => report.length > 1) + 1 || reports.length).flat();

// What the interpreter's violation reports, as TLC prints it: the violation, then a postcondition
// TLC checks after it, which fails.
const getReported = (
  status: CheckStatus,
  violation: SearchViolation,
  isTool: boolean,
  version: TlcVersion,
) => {
  const headline = getViolationHeadline(status, violation, isTool, version);
  const postcondition =
    violation.unwitnessed ??
    (status === "postcondition-violation" ? undefined : violation.postcondition);
  return [
    ...(headline
      ? [
          toViolation(
            headline,
            violation.trace,
            isTool,
            status === "property-violation" ? undefined : violation.loopStart,
          ),
        ]
      : []),
    ...(postcondition
      ? [toViolation({ code: postcondition.code, text: postcondition.message }, [], isTool)]
      : []),
  ];
};

// The interpreter's violation, as -continue reports it, and the exception TLC reports where it
// fails to print the violation's trace.
export const toContinuedViolation = (
  status: CheckStatus,
  violation: SearchViolation,
  isTool: boolean,
  version: TlcVersion,
) => toReported(getReported(status, violation, isTool, version).slice(0, 1));

// The interpreter's result, converted.
export const fromSearchResult = (
  result: SearchResult,
  continued: Violation[],
  isTool: boolean,
  version: TlcVersion,
): CheckResult => {
  const failure = result.failure;
  const violation = result.violation;
  const additional = result.additionalViolation;
  const reported = failure
    ? [
        toViolation(getFailureHeadline(failure, isTool), failure.trace, isTool),
        ...(failure.postcondition
          ? [
              toViolation(
                { code: failure.postcondition.code, text: failure.postcondition.message },
                [],
                isTool,
              ),
            ]
          : []),
      ]
    : violation
      ? [
          ...getReported(result.status, violation, isTool, version),
          ...(isInitialViolation(result.status, violation) || !additional
            ? []
            : getReported("property-violation", additional, isTool, version)),
        ]
      : [];
  const isWithoutStatistics =
    failure?.isWithoutStatistics ||
    result.status === "assumption-violation" ||
    (violation !== undefined && isInitialViolation(result.status, violation));
  return {
    status: result.status,
    violations: [...continued, ...toReported(reported)],
    generatedStates: isWithoutStatistics ? 0 : result.generatedStates,
    distinctStates: isWithoutStatistics ? 0 : result.distinctStates,
    queuedStates: isWithoutStatistics ? 0 : result.queuedStates,
    depth: isWithoutStatistics ? 0 : result.depth,
  };
};

// The native check's outcome, its plain data parsed.
export const fromNativeOutcome = (outcome: NativeCheckOutcome): CheckResult => ({
  status: outcome.status,
  violations: outcome.violations.map((violation) => ({
    code: violation.code,
    headline: violation.headline,
    states: violation.states.map((state) => ({
      label: state.label,
      variables: Object.fromEntries(
        state.variables.map((variable) => [
          variable[0],
          { text: variable[1], value: JSON.parse(variable[2]) },
        ]),
      ),
    })),
    ...(violation.loopStart !== undefined && { loopStart: violation.loopStart }),
  })),
  generatedStates: outcome.generatedStates,
  distinctStates: outcome.distinctStates,
  queuedStates: outcome.queuedStates,
  depth: outcome.depth,
});

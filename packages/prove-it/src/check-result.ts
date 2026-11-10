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
import { prettyPrint } from "./pretty-print";
import {
  getFailureHeadline,
  getViolationHeadline,
  type Headline,
  isInitialViolation,
} from "./tlc/headlines";
import type { TlcVersion } from "./tlc/version";
import { formatValue, toFiniteFunction, type Value } from "./values";

// A value as plain data: a boolean, an integer or a string as itself; a function over 1..n, such as
// a sequence or a tuple, as an array; a record, or any function whose keys are all strings none of
// which starts with "@", as an object; and, tagged by a key that starts with "@", any other
// function as its pairs, a set as its elements, a model value as its name, and a set or function
// TLC keeps lazy, such as Nat, as TLC's text of it. Keys and elements are in TLC's order.
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
// plain data, null where TLC prints null for a variable a successor leaves undefined.
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

const toPlainRecord = (entries: [string, PlainValue][]): PlainRecord => Object.fromEntries(entries);

const toPlainFunction = (domain: Value[], range: Value[]): PlainValue => {
  const isSequence = domain.every((key, index) => key === index + 1);
  const isRecord =
    domain.length > 0 && domain.every((key) => typeof key === "string" && !key.startsWith("@"));
  if (isSequence) return range.map(toPlainValue);
  if (isRecord) {
    return toPlainRecord(domain.map((key, index) => [String(key), toPlainValue(range[index])]));
  }
  return {
    "@function": domain.map((key, index) => [toPlainValue(key), toPlainValue(range[index])]),
  };
};

// A value as plain data, as prove-it-check's plain.rs writes the native one.
const toPlainValue = (value: Value): PlainValue => {
  if (typeof value !== "object") return value;
  if (value.kind === "ModelValue") return { "@model": value.name };
  if (value.kind === "Set") return { "@set": value.elements.map(toPlainValue) };
  if (value.kind === "Interval") {
    return {
      "@set": Array.from({ length: Math.max(0, value.high - value.low + 1) }, (_, index) =>
        toPlainValue(value.low + index),
      ),
    };
  }
  if (value.kind === "Function") return toPlainFunction(value.domain, value.range);
  // A function TLC keeps lazy over a set it enumerates is the function it converts to.
  if (
    value.kind === "LazyFunction" &&
    typeof value.domain === "object" &&
    (value.domain.kind === "Set" || value.domain.kind === "Interval")
  ) {
    const enumerated = toFiniteFunction(value);
    return toPlainFunction(enumerated.domain, enumerated.range);
  }
  return { "@lazy": formatValue(value) };
};

const toTraceStep = (step: SearchStep): TraceStep => ({
  label: step.label ?? step.action ?? "Initial predicate",
  variables: Object.fromEntries(
    Object.entries(step.state).map(([name, value]) => [
      name,
      { text: prettyPrint(formatValue(value)), value: toPlainValue(value) },
    ]),
  ),
});

const toViolation = (headline: Headline, steps: SearchStep[], loopStart?: number): Violation => ({
  code: headline.code,
  headline: headline.text,
  states: steps.map(toTraceStep),
  ...(loopStart !== undefined && { loopStart }),
});

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
            status === "property-violation" ? undefined : violation.loopStart,
          ),
        ]
      : []),
    ...(postcondition
      ? [toViolation({ code: postcondition.code, text: postcondition.message }, [])]
      : []),
  ];
};

// The interpreter's violation, as -continue reports it.
export const toContinuedViolation = (
  status: CheckStatus,
  violation: SearchViolation,
  isTool: boolean,
  version: TlcVersion,
) => getReported(status, violation, isTool, version)[0];

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
        toViolation(getFailureHeadline(failure, isTool), failure.trace),
        ...(failure.postcondition
          ? [
              toViolation(
                { code: failure.postcondition.code, text: failure.postcondition.message },
                [],
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
    violations: [...continued, ...reported],
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

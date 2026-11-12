// What check returns: each state of a behavior TLC reports, variable by variable, as TLC prints it
// and as plain data, as the native check records it as it prints (prove-it-check's outcome.rs).

import type { NativeCheckOutcome } from "./engine/native";

// How the check ends, as TLC reports it.
export type CheckStatus =
  | "success"
  | "assumption-violation"
  | "invariant-violation"
  | "property-violation"
  | "liveness-violation"
  | "postcondition-violation"
  | "deadlock"
  | "error";

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

// TLC's counts of the search so far.
export interface SearchStatistics extends Pick<
  CheckResult,
  "generatedStates" | "distinctStates" | "queuedStates" | "depth"
> {}

// The points of the search at which TLC prints a message, as the native check reports them once it
// ends (native-progress.ts).
export type CheckProgress =
  | { kind: "parsed" }
  | { kind: "constant-level-invariant"; name: string }
  | { kind: "state-level-property"; name: string }
  | { kind: "liveness-initializing"; isSymmetric: boolean; isConstrained: boolean }
  | { kind: "liveness-prepared"; branches: number }
  | { kind: "initial-states-started" }
  | { kind: "initial-states-progress"; count: number }
  | { kind: "initial-states-computed"; initialStates: { generated: number; distinct: number } }
  | { kind: "progress"; statistics: SearchStatistics }
  | {
      kind: "liveness-started";
      branches: number;
      // Whether TLC checks the complete state graph, and how many states its behavior graphs have,
      // summed over the branches.
      isComplete: boolean;
      states: number;
      statistics: SearchStatistics;
    }
  | { kind: "liveness-finished" }
  // A warning TLC prints as it evaluates the spec, with its message code.
  | { kind: "warning"; code: number; text: string }
  // A violation that the search goes on past with -continue.
  | { kind: "violation"; status: CheckStatus; violation: Violation }
  // A method of the class named after a module, which TLC reports as it loads the class.
  | {
      kind: "java-override";
      module: string;
      operator: string;
      signature: string;
      isMatched: boolean;
    };

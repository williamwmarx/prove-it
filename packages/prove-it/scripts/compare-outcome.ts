import type { ModelOutcome } from "./check-model";
import type { ExpectedResult } from "./record-tlc";

const EXIT_STATUSES: Record<string, string> = {
  "postcondition-violation": "assumption-violation",
};

// The fields of an outcome that two runs of a model must agree on.
export const OUTCOME_FIELDS = [
  "status",
  "violation",
  "generatedStates",
  "distinctStates",
  "depth",
  "traceLength",
  "error",
] as const;

const getExitStatus = (status: string) => EXIT_STATUSES[status] ?? status;

export const compareOutcome = (
  expected: ExpectedResult,
  actual: ModelOutcome,
): string | undefined => {
  if (expected.status === "error")
    return actual.status === "error" ? undefined : `expected an error, got ${actual.status}`;
  if (getExitStatus(actual.status) !== expected.status) {
    return `expected ${expected.status}, got ${actual.status}${actual.error ? ` (${actual.error})` : ""}`;
  }
  const fields = [
    "violation",
    "generatedStates",
    "distinctStates",
    "depth",
    "traceLength",
  ] as const;
  const differences = fields
    .filter((field) => expected[field] !== undefined && expected[field] !== actual[field])
    .map((field) => `${field}: expected ${expected[field]}, got ${actual[field]}`);
  return differences.length > 0 ? differences.join("; ") : undefined;
};

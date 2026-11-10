// A backend's answer to an obligation. tlapm frames an obligation as unsat when the backend
// proves it.
export type Verdict = "unsat" | "sat" | "unknown";

// What a backend reports about its search, the same in every port of it, so that two ports can be
// shown to make the same search and not only reach the same verdict.
export interface Statistics {
  [name: string]: number | string;
}

export interface Decision {
  verdict: Verdict;
  timeUsedMs: number;
  statistics: Statistics;
}

// The steps a backend has taken, each a point where it checks its limits. Past `limit` it gives up
// as it does at the time limit. Scripts set a limit and no time limit, so that what a backend
// decides doesn't depend on the machine; prove sets none.
export interface Steps {
  count: number;
  readonly limit: number;
}

export interface DecideOptions {
  timeLimitMs: number;
  signal?: AbortSignal;
  steps?: Steps;
  // Where the backend writes its statistics.
  statistics?: Statistics;
}

export const createSteps = (limit = Infinity): Steps => ({ count: 0, limit });

// Counts a step, and returns whether the budget is spent.
export const isStepLimitReached = (steps: Steps) => ++steps.count > steps.limit;

// The length and FNV-1a hash of a text's UTF-16 code units, to compare long outputs such as proofs.
export const getTextDigest = (text: string) => {
  const hash = Array.from({ length: text.length }, (_, index) => text.charCodeAt(index)).reduce(
    (state, unit) => Math.imul(state ^ unit, 0x01000193) >>> 0,
    0x811c9dc5,
  );
  return `${text.length}:${hash.toString(16).padStart(8, "0")}`;
};

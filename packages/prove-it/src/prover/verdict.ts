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

export interface DecideOptions {
  timeLimitMs: number;
  signal?: AbortSignal;
  // A cell over shared memory whose first element another thread sets to cancel the decision, as
  // the signal does where the decision can't see it: in a native backend, or a worker.
  cancel?: Int32Array;
}

// The length and FNV-1a hash of a text's UTF-16 code units, to compare long outputs such as proofs.
export const getTextDigest = (text: string) => {
  const hash = Array.from({ length: text.length }, (_, index) => text.charCodeAt(index)).reduce(
    (state, unit) => Math.imul(state ^ unit, 0x01000193) >>> 0,
    0x811c9dc5,
  );
  return `${text.length}:${hash.toString(16).padStart(8, "0")}`;
};

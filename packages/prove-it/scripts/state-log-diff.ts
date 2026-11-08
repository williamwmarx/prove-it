// Compares two state logs PROVE_IT_STATE_LOG wrote (src/engine/state-log.ts) and reports the
// first state where they differ, with both states and their parents decoded and printed.
// Usage: bun scripts/state-log-diff.ts <left log> <right log>

import { getStateLogDifference, readLogLines } from "./state-logs";

const difference = getStateLogDifference(
  readLogLines(process.argv[2]),
  readLogLines(process.argv[3]),
);
console.log(difference ?? "The logs agree on every state.");
if (difference) process.exitCode = 1;

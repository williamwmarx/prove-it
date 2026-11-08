// Compares two state logs PROVE_IT_STATE_LOG wrote (src/engine/state-log.ts) and reports the
// first state where they differ, with both states and their parents decoded and printed.
// Usage: bun scripts/state-log-diff.ts <left log> <right log>

import { readFileSync } from "node:fs";

import { getStateLogDifference } from "./state-logs";

const difference = getStateLogDifference(
  readFileSync(process.argv[2], "utf8"),
  readFileSync(process.argv[3], "utf8"),
);
console.log(difference ?? "The logs agree on every state.");
if (difference) process.exitCode = 1;

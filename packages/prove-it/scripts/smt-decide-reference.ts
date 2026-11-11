// Writes the table that prove-smt's `decide` is compared with (design/prover.md, 2.3): decideSmt's
// verdict and statistics on every script of tests/fixtures/smt, with no deadline and a fixed step
// limit, as the decider differential compares the two ports in miniature. prove-smt's
// tests/smt.rs replays it:
//   bun scripts/smt-decide-reference.ts
//
// Each line is `<fixture> <verdict> <statistics>`, the statistics as name=value in the order
// decideSmt writes them, or `<fixture> error=<name>: <message>` where it throws.
import { readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import { decideSmt } from "../src/prover/smt/solver/solver";
import { createSteps, type Statistics } from "../src/prover/verdict";

const STEP_LIMIT = 5_000_000;

const getDecision = (text: string) => {
  const statistics: Statistics = {};
  try {
    const verdict = decideSmt(text, {
      timeLimitMs: Number.POSITIVE_INFINITY,
      steps: createSteps(STEP_LIMIT),
      statistics,
    });
    const entries = Object.entries(statistics).map((entry) => `${entry[0]}=${entry[1]}`);
    return [verdict, ...entries].join(" ");
  } catch (error) {
    return error instanceof Error ? `error=${error.name}: ${error.message}` : `error=${error}`;
  }
};

const directory = join(import.meta.dir, "../tests/fixtures/smt");
const lines = readdirSync(directory)
  .filter((name) => name.endsWith(".smt"))
  .toSorted()
  .map((name) => `${name} ${getDecision(readFileSync(join(directory, name), "utf8"))}`);
writeFileSync(
  join(import.meta.dir, "../native/crates/prover/smt/tests/tables/decide.txt"),
  `${lines.join("\n")}\n`,
);

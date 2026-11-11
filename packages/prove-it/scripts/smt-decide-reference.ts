// Writes the table that prove-smt's `decide` is compared with (design/prover.md, 2.3): decideSmt's
// verdict and statistics on every script of tests/fixtures/smt, with no deadline and a fixed step
// limit, as the decider differential compares the two ports in miniature, and on every input of
// prove-smt's tests/inputs, the corpus inputs the ports once differed on, reduced, under a smaller
// one. prove-smt's tests/smt.rs replays both:
//   bun scripts/smt-decide-reference.ts
//
// Each line is `<fixture> <verdict> <statistics>`, the statistics as name=value in the order
// decideSmt writes them, or `<fixture> error=<name>: <message>` where it throws.
import { readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import { decideSmt } from "../src/prover/smt/solver/solver";
import { createSteps, type Statistics } from "../src/prover/verdict";

const STEP_LIMIT = 5_000_000;
const INPUT_STEP_LIMIT = 20_000;

const CRATE_DIRECTORY = join(import.meta.dir, "../native/crates/prover/smt/tests");
const TABLES_DIRECTORY = join(CRATE_DIRECTORY, "tables");

const getDecision = (text: string, stepLimit: number) => {
  const statistics: Statistics = {};
  try {
    const verdict = decideSmt(text, {
      timeLimitMs: Number.POSITIVE_INFINITY,
      steps: createSteps(stepLimit),
      statistics,
    });
    const entries = Object.entries(statistics).map((entry) => `${entry[0]}=${entry[1]}`);
    return [verdict, ...entries].join(" ");
  } catch (error) {
    return error instanceof Error ? `error=${error.name}: ${error.message}` : `error=${error}`;
  }
};

const writeTable = (directory: string, stepLimit: number, table: string) => {
  const lines = readdirSync(directory)
    .filter((name) => name.endsWith(".smt"))
    .toSorted()
    .map(
      (name) => `${name} ${getDecision(readFileSync(join(directory, name), "utf8"), stepLimit)}`,
    );
  writeFileSync(join(TABLES_DIRECTORY, table), `${lines.join("\n")}\n`);
};

writeTable(join(import.meta.dir, "../tests/fixtures/smt"), STEP_LIMIT, "decide.txt");
writeTable(join(CRATE_DIRECTORY, "inputs"), INPUT_STEP_LIMIT, "decide-inputs.txt");

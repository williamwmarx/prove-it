// Records what the TypeScript Zenon answers on the fixtures that tests/fixtures/zenon/decisions.txt
// lists, which the Rust port's tests compare with. Each line names a fixture under tests/fixtures
// and a step limit; this script rewrites the rest of the line with the statistics decideZenon
// reports under that step limit and no time limit, in its order: steps, nodesSearched,
// maxBranchFormulas, proofNodes, formulasCreated, stop and the proof's digest.

import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import { createSteps, type Statistics } from "../src/prover/verdict";
import { decideZenon } from "../src/prover/zenon/decide";

const FIXTURES = join(import.meta.dirname, "../tests/fixtures");
const DECISIONS = join(FIXTURES, "zenon/decisions.txt");

const lines = readFileSync(DECISIONS, "utf8")
  .split("\n")
  .filter((line) => line !== "")
  .map((line) => {
    const fields = line.split(" ");
    const path = fields[0];
    const stepLimit = Number(fields[1]);
    const statistics: Statistics = {};
    decideZenon(readFileSync(join(FIXTURES, path), "utf8"), {
      timeLimitMs: Infinity,
      steps: createSteps(stepLimit),
      statistics,
    });
    const values = Object.entries(statistics).map(
      (entry) =>
        `${entry[0]}=${typeof entry[1] === "string" ? JSON.stringify(entry[1]) : entry[1]}`,
    );
    return [path, stepLimit, ...values].join(" ");
  });
writeFileSync(DECISIONS, `${lines.join("\n")}\n`);

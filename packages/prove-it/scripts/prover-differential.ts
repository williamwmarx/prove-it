// Decides each input prover-inputs.ts wrote again, with its recorded step limit and no time limit,
// and compares the verdict and the statistics with the TypeScript backends' recorded ones. The
// answers must be the same, statistics included, which shows the same search was made.
//   --side ts (the default) decides with the TypeScript backends, which checks that the recording
//     reproduces; --side rust with the native ones.
//   --prover smt|z3|zenon|isabelle|ls4 and --filter text keep the inputs of one backend, or whose
//     digest contains the text. --jobs n runs n workers. --verbose lists every difference.
// An answer is "unstable" when the recording or the new decision stopped for a reason that is a
// property of the runtime rather than of the search, a full heap or stack, and isn't compared.

import { readFileSync } from "node:fs";
import { join } from "node:path";
import { isDeepStrictEqual } from "node:util";

import { TlaProverError } from "../src/errors";
import { decide } from "../src/prover/deciders";
import type { Statistics, Verdict } from "../src/prover/verdict";
import { CONFORMANCE_DIRECTORY, getOption, writeResults } from "./corpora";
import { runModuleWorkers } from "./module-workers";
import { printResults } from "./proof-records";
import { getInputPath, type InputRecord, readInputRecords } from "./prover-records";

type Outcome = "same" | "differs" | "unstable" | "crash";

interface Answer {
  verdict: Verdict;
  statistics: Statistics;
  error?: string;
}

interface Result {
  verdict: Outcome;
  prover: string;
  digest: string;
  expected?: Answer;
  actual?: Answer;
  crash?: string;
}

interface Batch {
  id: string;
  digests: string[];
}

const RESULTS_PATH = join(CONFORMANCE_DIRECTORY, ".prover-differential.json");

const BATCH_SIZE = 25;

const RUNTIME_STOPS = new Set(["heap", "stack"]);

const side = getOption("--side") ?? "ts";
const prover = getOption("--prover");
const filter = getOption("--filter");

const decideOnSide = (record: InputRecord, text: string): Answer => {
  if (side !== "ts") throw new Error(`no ${side} side`);
  try {
    const decision = decide(record.prover, text, { timeLimitMs: Infinity }, record.stepLimit);
    return { verdict: decision.verdict, statistics: decision.statistics };
  } catch (error) {
    if (!(error instanceof TlaProverError)) throw error;
    return { verdict: "unknown", statistics: {}, error: error.message };
  }
};

const isRuntimeStop = (answer: Answer) => RUNTIME_STOPS.has(String(answer.statistics.stop));

const getResult = (digest: string, record: InputRecord): Result => {
  const expected = {
    verdict: record.verdict,
    statistics: record.statistics,
    ...(record.error !== undefined && { error: record.error }),
  };
  const base = { prover: record.prover, digest, expected };
  const actual = (() => {
    try {
      return decideOnSide(record, readFileSync(getInputPath(record.prover, digest), "utf8"));
    } catch (error) {
      return String(error instanceof Error ? (error.stack ?? error.message) : error);
    }
  })();
  if (typeof actual === "string") return { ...base, verdict: "crash", crash: actual };
  const outcome: Outcome =
    isRuntimeStop(expected) || isRuntimeStop(actual)
      ? "unstable"
      : isDeepStrictEqual(actual, expected)
        ? "same"
        : "differs";
  return { ...base, verdict: outcome, ...(outcome !== "same" && { actual }) };
};

const records = readInputRecords();
const digests = Object.keys(records)
  .filter((digest) => prover === undefined || records[digest].prover === prover)
  .filter((digest) => filter === undefined || digest.includes(filter));
const batches: Batch[] = Array.from(
  { length: Math.ceil(digests.length / BATCH_SIZE) },
  (_, index) => ({
    id: `inputs ${index * BATCH_SIZE + 1}-${Math.min(digests.length, (index + 1) * BATCH_SIZE)}`,
    digests: digests.slice(index * BATCH_SIZE, (index + 1) * BATCH_SIZE),
  }),
);
const byBatch = await runModuleWorkers(
  batches,
  (batch) => batch.digests.reduce((total, digest) => total + records[digest].stepLimit, 0),
  async (batch) => batch.digests.map((digest) => getResult(digest, records[digest])),
  1,
);
const results = [...byBatch.values()].flat();
writeResults(RESULTS_PATH, results);
const missing = digests.length - results.length;
console.log(
  `${side} on ${results.length} of ${digests.length} inputs${missing > 0 ? `, ${missing} lost with their worker` : ""}`,
);
printResults(results, ["same", "differs", "unstable", "crash"], ["differs", "crash"], (result) =>
  result.verdict === "crash"
    ? `crash ${result.prover} ${result.digest}: ${result.crash}`
    : `${result.verdict} ${result.prover} ${result.digest}: expected ${JSON.stringify(result.expected)}, got ${JSON.stringify(result.actual)}`,
);
if (
  results.some((result) => result.verdict === "differs" || result.verdict === "crash") ||
  missing > 0
)
  process.exitCode = 1;

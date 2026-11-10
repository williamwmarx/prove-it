// Decides each input prover-inputs.ts wrote again, with its recorded step limit and no time limit,
// and compares the verdict and the statistics with the TypeScript backends' recorded ones. The
// answers must be the same, statistics included, which shows the same search was made.
//   --side ts (the default) decides with the TypeScript backends, which checks that the recording
//     reproduces; --side rust with the native ones.
//   --prover smt|z3|zenon|isabelle|ls4 and --filter text keep the inputs of one backend, or whose
//     key, prover/digest, contains the text. --jobs n runs n workers. --verbose lists every difference.
// "declined" counts the inputs the native backend doesn't decide yet, and isn't a failure.
// An answer is "unstable" when the recording or the new decision stopped for a reason that is a
// property of the runtime rather than of the search, a full heap or stack, and isn't compared.

import { readFileSync } from "node:fs";
import { join } from "node:path";
import { isDeepStrictEqual } from "node:util";

import { getNativeAddon } from "../src/engine/native";
import { TlaProverError } from "../src/errors";
import { decide } from "../src/prover/deciders";
import type { Statistics, Verdict } from "../src/prover/verdict";
import { CONFORMANCE_DIRECTORY, getOption, writeResults } from "./corpora";
import { runModuleWorkers } from "./module-workers";
import { printResults } from "./proof-records";
import {
  getInputPath,
  type InputRecord,
  readInputRecords,
  useTypeScriptBackends,
} from "./prover-records";

type Outcome = "same" | "differs" | "unstable" | "declined" | "crash";

interface Answer {
  verdict: Verdict;
  statistics: Statistics;
  error?: string;
}

interface Result {
  verdict: Outcome;
  prover: string;
  key: string;
  expected?: Answer;
  actual?: Answer;
  crash?: string;
  reason?: string;
}

interface Batch {
  id: string;
  keys: string[];
}

const RESULTS_PATH = join(CONFORMANCE_DIRECTORY, ".prover-differential.json");

const BATCH_SIZE = 25;

const RUNTIME_STOPS = new Set(["heap", "stack"]);

const side = getOption("--side") ?? "ts";
const prover = getOption("--prover");
const filter = getOption("--filter");

useTypeScriptBackends();

// The native backend's answer, which reads the input with no fallback, or why it declined.
const decideNatively = (record: InputRecord, text: string): Answer | string => {
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new Error(`no native engine: ${addon}`);
  const decision = addon.decide(record.prover, text, Infinity, record.stepLimit, undefined);
  if (decision.kind === "declined") return decision.reason;
  if (decision.kind === "error")
    return { verdict: "unknown", statistics: {}, error: decision.message };
  return { verdict: decision.verdict, statistics: decision.statistics };
};

const decideOnSide = (record: InputRecord, text: string): Answer | string => {
  if (side === "rust") return decideNatively(record, text);
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

const getResult = (key: string, record: InputRecord): Result => {
  const expected = {
    verdict: record.verdict,
    statistics: record.statistics,
    ...(record.error !== undefined && { error: record.error }),
  };
  const base = { prover: record.prover, key, expected };
  const actual = (() => {
    try {
      return decideOnSide(record, readFileSync(getInputPath(key), "utf8"));
    } catch (error) {
      return { crash: String(error instanceof Error ? (error.stack ?? error.message) : error) };
    }
  })();
  if (typeof actual === "string") return { ...base, verdict: "declined", reason: actual };
  if ("crash" in actual) return { ...base, verdict: "crash", crash: actual.crash };
  const outcome: Outcome =
    isRuntimeStop(expected) || isRuntimeStop(actual)
      ? "unstable"
      : isDeepStrictEqual(actual, expected)
        ? "same"
        : "differs";
  return { ...base, verdict: outcome, ...(outcome !== "same" && { actual }) };
};

const records = readInputRecords();
const keys = Object.keys(records)
  .filter((key) => prover === undefined || records[key].prover === prover)
  .filter((key) => filter === undefined || key.includes(filter));
const batches: Batch[] = Array.from(
  { length: Math.ceil(keys.length / BATCH_SIZE) },
  (_, index) => ({
    id: `inputs ${index * BATCH_SIZE + 1}-${Math.min(keys.length, (index + 1) * BATCH_SIZE)}`,
    keys: keys.slice(index * BATCH_SIZE, (index + 1) * BATCH_SIZE),
  }),
);
const byBatch = await runModuleWorkers(
  batches,
  (batch) => batch.keys.reduce((total, key) => total + (records[key].stepLimit ?? 0), 0),
  async (batch) => batch.keys.map((key) => getResult(key, records[key])),
  1,
);
const results = [...byBatch.values()].flat();
writeResults(RESULTS_PATH, results);
const missing = keys.length - results.length;
console.log(
  `${side} on ${results.length} of ${keys.length} inputs${missing > 0 ? `, ${missing} lost with their worker` : ""}`,
);
printResults(
  results,
  ["same", "differs", "unstable", "declined", "crash"],
  ["differs", "crash"],
  (result) =>
    result.verdict === "crash"
      ? `crash ${result.key}: ${result.crash}`
      : `${result.verdict} ${result.key}: expected ${JSON.stringify(result.expected)}, got ${JSON.stringify(result.actual)}`,
);
if (
  results.some((result) => result.verdict === "differs" || result.verdict === "crash") ||
  missing > 0
)
  process.exitCode = 1;

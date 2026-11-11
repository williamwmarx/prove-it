// Proves each recorded module with the TypeScript driver and with the Rust one, each decision
// replayed from prover-inputs.json, and compares what they report: every obligation's status, its
// prover or reason, and the counts of missing and omitted proofs, or the error. The replay makes
// both runs deterministic, so the answers must be the same. A text the record doesn't hold fails
// the module, as it shows a driver sent a backend what the TypeScript never did.
//   --filter text keeps the modules whose path contains the text. --jobs n runs n workers.
// Writes every result to .prover-driver-differential.json. Needs the native engine.

import { readFileSync } from "node:fs";
import { join } from "node:path";
import { isDeepStrictEqual } from "node:util";

import { TlaError, TlaProverError } from "../src/errors";
import { proveWith } from "../src/prover/prove";
import type { Decision } from "../src/prover/verdict";
import { CONFORMANCE_DIRECTORY, CORPORA_DIRECTORY, getOption, writeResults } from "./corpora";
import { runModuleWorkers } from "./module-workers";
import {
  getModuleLoader,
  getObligationCount,
  printResults,
  readProofRecords,
} from "./proof-records";
import { getInputKey, readInputRecords } from "./prover-records";
import { getDigest } from "./tlapm-digest";

interface Result {
  verdict: "same" | "differs" | "crash";
  module: string;
  typescript?: unknown;
  rust?: unknown;
  crash?: string;
}

const RESULTS_PATH = join(CONFORMANCE_DIRECTORY, ".prover-driver-differential.json");

const filter = getOption("--filter");
const records = readInputRecords();

// The recorded answer, as prove's decide gives it: a decision, or the TlaProverError the backend
// threw.
const replay = async (prover: string, text: string): Promise<Decision> => {
  const key = getInputKey(prover, getDigest(text));
  const record = records[key];
  if (record === undefined) throw new Error(`input ${key} isn't in prover-inputs.json`);
  if (record.error !== undefined) throw new TlaProverError(record.error);
  return { verdict: record.verdict, timeUsedMs: 0, statistics: record.statistics };
};

// What prove reports with the driver, or the error it throws.
const proveWithDriver = async (driver: string, path: string) => {
  process.env.PROVE_IT_PROVER_DRIVER = driver;
  return proveWith(
    { source: readFileSync(path, "utf8"), loadModule: getModuleLoader(path) },
    replay,
  ).catch((error: unknown) => {
    if (!(error instanceof TlaError)) throw error;
    return { error: error.name, message: error.message };
  });
};

const modules = readProofRecords().filter(
  (module) => filter === undefined || module.id.includes(filter),
);
const byModule = await runModuleWorkers(
  modules,
  getObligationCount,
  async (module): Promise<Result> => {
    const path = join(CORPORA_DIRECTORY, module.id);
    try {
      const typescript = await proveWithDriver("ts", path);
      const rust = await proveWithDriver("rust", path);
      return isDeepStrictEqual(rust, typescript)
        ? { verdict: "same", module: module.id }
        : { verdict: "differs", module: module.id, typescript, rust };
    } catch (error) {
      return {
        verdict: "crash",
        module: module.id,
        crash: String(error instanceof Error ? (error.stack ?? error.message) : error),
      };
    }
  },
  1,
);
const results = [...byModule.values()];
writeResults(RESULTS_PATH, results);
const missing = modules.length - results.length;
console.log(
  `${results.length} of ${modules.length} modules${missing > 0 ? `, ${missing} lost with their worker` : ""}`,
);
printResults(results, ["same", "differs", "crash"], ["differs", "crash"], (result) =>
  result.verdict === "crash"
    ? `crash ${result.module}: ${result.crash}`
    : `differs ${result.module}: see ${RESULTS_PATH}`,
);
if (results.some((result) => result.verdict !== "same") || missing > 0) process.exitCode = 1;

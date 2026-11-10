// Records the lp calls of the arithmetic theory on the SMT inputs of the decider corpus, one
// .lptrace file per input in .lp-traces, named by its digest (src/prover/smt/solver/lp-trace.ts),
// for the Rust port of lp to replay. Each input is decided with its recorded step limit and no time
// limit, as prover-differential.ts does, and the answer, statistics included, must be the recorded
// one, which shows that tracing left the search as it was.
//   --filter text keeps the inputs whose digest contains the text. --jobs n runs n workers.
//   --inputs directory traces the .smt files of a directory, such as tests/fixtures/smt, instead:
//     each is decided first without a trace, with the steps it takes within --time-limit
//     milliseconds (5000 by default) as its step limit, and its traced answer must be that one.
// Usage: bun scripts/run.ts lp-trace [--inputs directory] [--filter text] [--jobs n] [--verbose]

import { mkdirSync, readdirSync, readFileSync, statSync } from "node:fs";
import { join, resolve } from "node:path";
import { isDeepStrictEqual } from "node:util";

import { TlaProverError } from "../src/errors";
import { decide } from "../src/prover/deciders";
import type { Statistics, Verdict } from "../src/prover/verdict";
import { CONFORMANCE_DIRECTORY, getOption, writeResults } from "./corpora";
import { runModuleWorkers } from "./module-workers";
import { printResults } from "./proof-records";
import { getInputPath, readInputRecords, useTypeScriptBackends } from "./prover-records";
import { getDigest } from "./tlapm-digest";

interface Answer {
  verdict: Verdict;
  statistics: Statistics;
  error?: string;
}

interface TraceInput {
  id: string;
  prover: string;
  path: string;
  stepLimit?: number;
  expected?: Answer;
}

interface Result {
  verdict: "same" | "differs";
  id: string;
  digest: string;
  lines: number;
  bytes: number;
  expected: Answer;
  actual?: Answer;
}

const TRACES_DIRECTORY = join(CONFORMANCE_DIRECTORY, ".lp-traces");

const SMT_PROVERS = new Set(["smt", "z3"]);

const inputsDirectory = getOption("--inputs");
const filter = getOption("--filter");
const timeLimitMs = Number(getOption("--time-limit") ?? 5000);

useTypeScriptBackends();

const getAnswer = (
  prover: string,
  text: string,
  stepLimit: number | undefined,
  limitMs = Infinity,
): Answer => {
  try {
    const decision = decide(prover, text, { timeLimitMs: limitMs }, stepLimit);
    return { verdict: decision.verdict, statistics: decision.statistics };
  } catch (error) {
    if (!(error instanceof TlaProverError)) throw error;
    return { verdict: "unknown", statistics: {}, error: error.message };
  }
};

const getInputs = (): TraceInput[] => {
  if (inputsDirectory !== undefined)
    return readdirSync(inputsDirectory)
      .filter((name) => name.endsWith(".smt"))
      .map((name) => ({ id: name, prover: "smt", path: resolve(inputsDirectory, name) }));
  const records = readInputRecords();
  return Object.keys(records)
    .filter((key) => SMT_PROVERS.has(records[key].prover))
    .map((key) => ({
      id: key,
      prover: records[key].prover,
      path: getInputPath(key),
      stepLimit: records[key].stepLimit,
      expected: {
        verdict: records[key].verdict,
        statistics: records[key].statistics,
        ...(records[key].error !== undefined && { error: records[key].error }),
      },
    }));
};

const trace = async (input: TraceInput): Promise<Result> => {
  const text = readFileSync(input.path, "utf8");
  const stepLimit =
    input.stepLimit ??
    Number(getAnswer(input.prover, text, undefined, timeLimitMs).statistics.steps);
  const expected = input.expected ?? getAnswer(input.prover, text, stepLimit);
  process.env.PROVE_IT_LP_TRACE = TRACES_DIRECTORY;
  const actual = getAnswer(input.prover, text, stepLimit);
  delete process.env.PROVE_IT_LP_TRACE;
  const digest = getDigest(text);
  const tracePath = join(TRACES_DIRECTORY, `${digest}.lptrace`);
  const isSame = isDeepStrictEqual(actual, expected);
  return {
    verdict: isSame ? "same" : "differs",
    id: input.id,
    digest,
    lines: readFileSync(tracePath, "utf8").split("\n").length - 1,
    bytes: statSync(tracePath).size,
    expected,
    ...(!isSame && { actual }),
  };
};

const inputs = getInputs().filter((input) => filter === undefined || input.id.includes(filter));
const byInput = await runModuleWorkers(
  inputs,
  (input) => input.stepLimit ?? statSync(input.path).size,
  trace,
  1,
);
const results = [...byInput.values()];
mkdirSync(TRACES_DIRECTORY, { recursive: true });
writeResults(join(TRACES_DIRECTORY, "results.json"), results);
const missing = inputs.length - results.length;
const bytes = results.reduce((total, result) => total + result.bytes, 0);
const lines = results.reduce((total, result) => total + result.lines, 0);
console.log(
  `${results.length} of ${inputs.length} inputs traced in ${TRACES_DIRECTORY}: ${lines} lines, ${bytes} bytes${missing > 0 ? `, ${missing} lost with their worker` : ""}`,
);
printResults(
  results,
  ["same", "differs"],
  ["differs"],
  (result) =>
    `differs ${result.id}: expected ${JSON.stringify(result.expected)}, got ${JSON.stringify(result.actual)}`,
);
if (results.some((result) => result.verdict === "differs") || missing > 0) process.exitCode = 1;

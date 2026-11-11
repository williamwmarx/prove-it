// Runs Z3 5.3.3, the version the TypeScript SMT solver ports, on each smt and z3 input
// prover-inputs.ts wrote, as tlapm runs it, under the time limit prove sent the input with, and
// compares its verdict with the TypeScript's recorded one. The record shows the Rust port equals
// the TypeScript; this shows how far the TypeScript is from Z3. Citations are to tlapm at ff40755.
//   tlapm runs `z3 -smt2 -v:0 AUTO_CONFIG=false smt.MBQI=true "$file"` for both methods
//     (src/params.ml:221-231, the default solver by src/params.ml:274-276), with its output on
//     stdout only (src/backend/prep.ml:700), and counts the input proved when a line of the output
//     starts with "unsat" (src/backend/prep.ml:693, 721-729). The smt and z3 methods' time limit
//     is 5 s unless the proof names one (src/method.ml:10-13). The scheduler first looks at a
//     running prover after Params.wait, 3 s (src/params.ml:49, src/backend/prep.ml:745), then
//     moves its deadline to the method's time limit and kills it there (src/backend/prep.ml:
//     424-428, src/backend/schedule.ml:166-170), so it runs for the longer of the two. A method
//     with an rlimit budget has no time limit (src/backend/prep.ml:1489-1492), the budget being an
//     option in the text (src/backend/prep.ml:712-714).
//   Here Z3's own -T stops it at that time, which tlapm's kill gives too, and -st prints its
//     statistics, rlimit-count and quant-instantiations, after the verdict; neither changes the
//     search.
//   --z3 path names the binary, z3 on the PATH by default. The script fails unless it runs Z3
//     5.3.3, and records the binary's SHA-256 with the results.
//   --prover smt|z3 and --filter text keep the inputs of one prover, or whose key contains the
//     text. --jobs n runs n Z3s at once.
//   --retry scale runs Z3 again, with scale times the time limit, on each input of the last run
//     that the TypeScript proves and Z3 doesn't, to tell a time limit from a real divergence.
// Each run is kept in .z3-parity.jsonl as it ends, and a run that finds the journal goes on from
// it. The results are in .z3-parity.json.

import { spawn, spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { delimiter, join } from "node:path";

import { CONFORMANCE_DIRECTORY, getOption } from "./corpora";
import { appendJournal, readJournal, repairJournal } from "./journal";
import { printResults } from "./proof-records";
import {
  getInputPath,
  type InputRecord,
  readInputRecords,
  TIME_LIMITS_PATH,
} from "./prover-records";

// contradiction: one answers sat and the other unsat, which is a soundness bug on one side.
type Kind = "same" | "contradiction" | "ts-proves" | "z3-proves" | "mismatch" | "z3-error";

interface Z3Run {
  verdict: "unsat" | "sat" | "unknown" | "timeout" | "error";
  seconds: number;
  rlimit?: number;
  instances?: number;
  error?: string;
}

interface Result {
  verdict: Kind;
  key: string;
  // The time limit Z3 ran under, in seconds, null for none.
  timeLimit: number | null;
  ts: InputRecord;
  z3: Z3Run;
  retry?: Z3Run & { timeLimit: number | null };
}

interface Run extends Z3Run {
  key: string;
  timeLimit: number | null;
  sha256: string;
}

const RESULTS_PATH = join(CONFORMANCE_DIRECTORY, ".z3-parity.json");
const JOURNAL_PATH = join(CONFORMANCE_DIRECTORY, ".z3-parity.jsonl");

const VERSION = "5.3.3";

// Params.wait, the seconds tlapm's scheduler waits before it first looks at a prover's time limit.
const WAIT_SECONDS = 3;

const OPTIONS = ["-smt2", "-v:0", "AUTO_CONFIG=false", "smt.MBQI=true", "-st"];

const getBinaryPath = (name: string) =>
  name.includes("/")
    ? name
    : (process.env.PATH ?? "")
        .split(delimiter)
        .map((directory) => join(directory, name))
        .find((path) => existsSync(path));

const z3 = getOption("--z3") ?? "z3";
const z3Path = getBinaryPath(z3);
if (z3Path === undefined || !existsSync(z3Path))
  throw new Error(`Z3 ${VERSION} is required, and there is no ${z3}; name it with --z3 path`);
const version = spawnSync(z3Path, ["--version"], { encoding: "utf8" }).stdout?.trim() ?? "";
if (!version.startsWith(`Z3 version ${VERSION} `))
  throw new Error(`${z3Path} is "${version}", not Z3 ${VERSION}`);
const sha256 = createHash("sha256").update(readFileSync(z3Path)).digest("hex");

const getStatistic = (output: string, name: string) => {
  const match = new RegExp(`:${name}\\s+(\\d+)`).exec(output);
  return match === null ? undefined : Number(match[1]);
};

// tlapm's reading of the output: proved when a line starts with "unsat", else failed.
const getZ3Verdict = (output: string): Z3Run["verdict"] => {
  if (/^unsat/m.test(output)) return "unsat";
  if (/^\(error/m.test(output)) return "error";
  const first = output.split("\n")[0];
  return first === "sat" || first === "unknown" || first === "timeout" ? first : "error";
};

const runZ3 = (key: string, timeLimit: number | null) =>
  new Promise<Run>((resolve) => {
    const start = performance.now();
    const child = spawn(z3Path, [
      ...OPTIONS,
      ...(timeLimit === null ? [] : [`-T:${Math.ceil(Math.max(WAIT_SECONDS, timeLimit))}`]),
      getInputPath(key),
    ]);
    const chunks: Buffer[] = [];
    child.stdout.on("data", (chunk: Buffer) => chunks.push(chunk));
    child.stderr.on("data", (chunk: Buffer) => chunks.push(chunk));
    child.on("close", (code, signal) => {
      const output = Buffer.concat(chunks).toString("utf8");
      const verdict = getZ3Verdict(output);
      const isFailed = verdict === "error" || (code !== 0 && verdict !== "timeout");
      resolve({
        key,
        timeLimit,
        sha256,
        verdict: isFailed && verdict !== "unsat" ? "error" : verdict,
        seconds: Math.round(performance.now() - start) / 1000,
        rlimit: getStatistic(output, "rlimit-count"),
        instances: getStatistic(output, "quant-instantiations"),
        ...(isFailed && {
          error: `exit ${code ?? signal}: ${output
            .split("\n")
            .filter((line) => !line.startsWith(" :") && !line.startsWith("(:"))
            .join("\n")
            .slice(0, 2000)}`,
        }),
      });
    });
  });

const getKind = (ts: InputRecord, run: Z3Run): Kind => {
  if (run.verdict === "error") return "z3-error";
  const isZ3Proved = run.verdict === "unsat";
  if (
    (ts.verdict === "unsat" && run.verdict === "sat") ||
    (ts.verdict === "sat" && run.verdict === "unsat")
  )
    return "contradiction";
  if (ts.verdict === "unsat") return isZ3Proved ? "same" : "ts-proves";
  if (isZ3Proved) return "z3-proves";
  const z3Verdict = run.verdict === "timeout" ? "unknown" : run.verdict;
  return ts.error === undefined && ts.verdict === z3Verdict ? "same" : "mismatch";
};

// Runs Z3 on each key, jobs at once, journaling each run, and gives the runs by key.
const runAll = async (limits: Map<string, number | null>) => {
  repairJournal(JOURNAL_PATH);
  const runs = new Map(
    readJournal<Run>(JOURNAL_PATH)
      .filter((run) => run.sha256 === sha256 && limits.get(run.key) === run.timeLimit)
      .map((run) => [run.key, run]),
  );
  const queue = [...limits.keys()].filter((key) => !runs.has(key));
  const total = queue.length;
  await Promise.all(
    Array.from({ length: Number(getOption("--jobs") ?? 3) }, async () => {
      for (let key = queue.shift(); key !== undefined; key = queue.shift()) {
        const run = await runZ3(key, limits.get(key) ?? null);
        appendJournal(JOURNAL_PATH, run);
        runs.set(key, run);
        if ((total - queue.length) % 500 === 0) console.error(`${total - queue.length}/${total}`);
      }
    }),
  );
  return runs;
};

const getZ3Run = (run: Run): Z3Run => ({
  verdict: run.verdict,
  seconds: run.seconds,
  ...(run.rlimit !== undefined && { rlimit: run.rlimit }),
  ...(run.instances !== undefined && { instances: run.instances }),
  ...(run.error !== undefined && { error: run.error }),
});

const describe = (result: Result) =>
  `${result.verdict} ${result.key}: ts ${result.ts.verdict}, z3 ${result.z3.verdict} in ${result.z3.seconds} s${
    result.retry === undefined
      ? ""
      : `, ${result.retry.verdict} in ${result.retry.seconds} s of ${result.retry.timeLimit}`
  }${result.z3.error === undefined ? "" : ` (${result.z3.error})`}`;

const KINDS: Kind[] = ["same", "contradiction", "ts-proves", "z3-proves", "mismatch", "z3-error"];

const records = readInputRecords();
if (!existsSync(TIME_LIMITS_PATH)) throw new Error("Run prover-inputs first");
// The largest time limit prove sent each input with, which is the most time tlapm gives Z3 on it,
// or null where a method had none.
const timeLimits = new Map(
  Object.entries(
    JSON.parse(readFileSync(TIME_LIMITS_PATH, "utf8")) as Record<string, (number | null)[]>,
  ).map(([key, limits]) => [
    key,
    limits.includes(null) ? null : Math.max(...limits.map((limit) => limit ?? 0)),
  ]),
);

const writeOutput = (results: Result[]) =>
  writeFileSync(
    RESULTS_PATH,
    `${JSON.stringify({ z3: { path: z3Path, version, sha256 }, options: OPTIONS, results }, null, 2)}\n`,
  );

const retry = getOption("--retry");
if (retry === undefined) {
  const prover = getOption("--prover");
  const filter = getOption("--filter");
  const keys = Object.keys(records)
    .filter((key) => ["smt", "z3"].includes(records[key].prover))
    .filter((key) => prover === undefined || records[key].prover === prover)
    .filter((key) => filter === undefined || key.includes(filter));
  const missing = keys.filter((key) => !timeLimits.has(key));
  if (missing.length > 0) throw new Error(`no time limit for ${missing.join(", ")}`);
  const limits = new Map(keys.map((key) => [key, timeLimits.get(key) ?? null]));
  const runs = await runAll(limits);
  const results = keys.map((key): Result => {
    const run = getZ3Run(runs.get(key) as Run);
    return {
      verdict: getKind(records[key], run),
      key,
      timeLimit: limits.get(key) ?? null,
      ts: records[key],
      z3: run,
    };
  });
  writeOutput(results);
  printResults(
    results,
    KINDS,
    ["contradiction", "ts-proves", "z3-proves", "mismatch", "z3-error"],
    describe,
  );
} else {
  const audit: { z3: { sha256: string }; results: Result[] } = JSON.parse(
    readFileSync(RESULTS_PATH, "utf8"),
  );
  // A retry is only comparable with the run of the same binary.
  if (audit.z3.sha256 !== sha256)
    throw new Error(
      `the last run used the Z3 binary with SHA-256 ${audit.z3.sha256}, not ${sha256}: run the audit again with this binary first`,
    );
  const results = audit.results;
  const retried = results.filter((result) => result.verdict === "ts-proves");
  const limits = new Map(
    retried.map((result) => [
      result.key,
      result.timeLimit === null ? null : result.timeLimit * Number(retry),
    ]),
  );
  const runs = await runAll(limits);
  for (const result of retried)
    result.retry = {
      ...getZ3Run(runs.get(result.key) as Run),
      timeLimit: limits.get(result.key) ?? null,
    };
  writeOutput(results);
  const proved = retried.filter((result) => result.retry?.verdict === "unsat");
  console.log(
    `${retried.length} retried with ${retry} times the time limit: Z3 proves ${proved.length}`,
  );
  retried.forEach((result) => console.log(describe(result)));
}

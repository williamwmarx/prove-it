// Runs each conformance model with the engine on (PROVE_IT_ENGINE=debug) and off (PROVE_IT_ENGINE=0),
// checks both runs reach the same outcome, and tallies what the engine did with each model, weighted
// by the time TLC takes on it. --backend picks the engine's backend, and --compare-backends runs
// every backend, each checked against the engine off. With --state-logs, each model the engine
// completes runs again on 1 and on 4 threads, and the two state logs (PROVE_IT_STATE_LOG) must be
// identical.
// Usage: bun scripts/run.ts engine-coverage [--max-tlc-ms 20000] [--filter text] [--concurrency 3]
//        [--timeout-ms 600000] [--out path] [--backend ts | --compare-backends] [--state-logs]

import { spawn } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import type { ModelOutcome } from "./check-model";
import { compareOutcome, OUTCOME_FIELDS } from "./compare-outcome";
import {
  CONFORMANCE_DIRECTORY,
  type CorpusModel,
  EXPECTED_PATH,
  findModels,
  getOption,
  writeResults,
} from "./corpora";
import {
  classifyEngineLine,
  getBackendEnvironment,
  getBackends,
  getEngineLine,
} from "./engine-runs";
import type { ExpectedResult } from "./record-tlc";
import { getStateLogDifference, readLogLines } from "./state-logs";

interface Run {
  outcome: ModelOutcome | undefined;
  verdict: string;
  detail: string | undefined;
  engineLine: string | undefined;
  stderr: string;
  wallMilliseconds: number;
}

interface Coverage {
  id: string;
  tlcMilliseconds: number;
  expectedStatus: string;
  engine: string;
  reason: string | undefined;
  bucket: string;
  engineMilliseconds: number | undefined;
  isSame: boolean;
  differences: string[];
  // The run with the engine off, and with each backend.
  runs: Record<string, Run>;
  // With --state-logs, how many threads the run on 4 searched on.
  threads: number | undefined;
}

const maximumTlcMilliseconds = Number(getOption("--max-tlc-ms") ?? 20000);
const filter = getOption("--filter");
const concurrency = Number(getOption("--concurrency") ?? 3);
const timeoutMilliseconds = Number(getOption("--timeout-ms") ?? 600000);
const outPath = getOption("--out") ?? join(CONFORMANCE_DIRECTORY, ".engine-coverage.json");
const backends = getBackends();
const isLoggingStates = process.argv.includes("--state-logs");

// Names of the spec's own definitions and variables would split one missing feature into many rows.
const normalizeReason = (reason: string) =>
  reason
    .replace(/^(unsupported: the (?:name|operator|operator argument)) .+$/, "$1 <name>")
    .replace(/^the (\w+) .+ isn't defined$/, "the $1 <name> isn't defined")
    .replace(/\d+/g, "N");

const getEngineEnvironment = (backend: string) => ({
  ...getBackendEnvironment(backend),
  PROVE_IT_ENGINE: "debug",
});

const runModel = (model: CorpusModel, environment: NodeJS.ProcessEnv, expected: ExpectedResult) =>
  new Promise<Run>((resolve) => {
    const startedAt = performance.now();
    const child = spawn(
      process.execPath,
      [
        "--stack-size=8000",
        "--max-old-space-size=6144",
        join(import.meta.dirname, "check-model.js"),
        model.specPath,
        model.configPath,
      ],
      {
        stdio: ["ignore", "pipe", "pipe"],
        env: environment,
        timeout: timeoutMilliseconds,
        killSignal: "SIGKILL",
      },
    );
    const stdout: Buffer[] = [];
    const stderr: Buffer[] = [];
    child.stdout.on("data", (chunk: Buffer) => stdout.push(chunk));
    child.stderr.on("data", (chunk: Buffer) => stderr.push(chunk));
    child.on("close", (_code, signal) => {
      const output = Buffer.concat(stdout).toString("utf8");
      const errorOutput = Buffer.concat(stderr).toString("utf8");
      const outcome: ModelOutcome | undefined = output.startsWith("{")
        ? JSON.parse(output)
        : undefined;
      const detail = outcome
        ? compareOutcome(expected, outcome)
        : signal === "SIGKILL"
          ? `killed after ${timeoutMilliseconds} ms`
          : "the checker crashed";
      resolve({
        outcome,
        verdict: !outcome
          ? signal === "SIGKILL"
            ? "timeout"
            : "crash"
          : outcome.status === "unsupported"
            ? "unsupported"
            : detail
              ? "mismatch"
              : "match",
        detail: detail ?? outcome?.error,
        engineLine: getEngineLine(errorOutput),
        stderr: errorOutput.slice(0, 4000),
        wallMilliseconds: Math.round(performance.now() - startedAt),
      });
    });
  });

const expectedResults: ExpectedResult[] = JSON.parse(readFileSync(EXPECTED_PATH, "utf8"));
const expectedById = new Map(expectedResults.map((result) => [result.id, result]));

// The same models as bun run conformance with the same --max-tlc-ms, except that the large ones are
// left out altogether rather than run one at a time.
const models = findModels()
  .filter((model) => {
    const expected = expectedById.get(model.id);
    return (
      expected !== undefined &&
      expected.tlcMilliseconds <= maximumTlcMilliseconds &&
      (filter === undefined || model.id.includes(filter))
    );
  })
  .sort(
    (left, right) =>
      (expectedById.get(right.id)?.tlcMilliseconds ?? 0) -
      (expectedById.get(left.id)?.tlcMilliseconds ?? 0),
  );
const excluded = expectedResults.filter(
  (result) => result.tlcMilliseconds > maximumTlcMilliseconds,
);
console.log(
  `${models.length} models; excluded ${excluded.length} with TLC over ${maximumTlcMilliseconds} ms (${Math.round(excluded.reduce((sum, result) => sum + result.tlcMilliseconds, 0) / 1000)} s of TLC time)`,
);

// The state logs of the engine on 1 and on 4 threads, and how many threads the second searched on.
const compareThreads = async (model: CorpusModel, expected: ExpectedResult) => {
  const directory = mkdtempSync(join(tmpdir(), "prove-it-state-logs-"));
  const [serial, parallel] = ["1", "4"].map((threads) => join(directory, `${threads}.jsonl`));
  const environment = getEngineEnvironment(backends[0]);
  await runModel(
    model,
    { ...environment, PROVE_IT_WORKERS: "1", PROVE_IT_STATE_LOG: serial },
    expected,
  );
  const run = await runModel(
    model,
    { ...environment, PROVE_IT_WORKERS: "4", PROVE_IT_STATE_LOG: parallel },
    expected,
  );
  const difference =
    existsSync(serial) && existsSync(parallel)
      ? getStateLogDifference(readLogLines(serial), readLogLines(parallel))
      : "a run wrote no state log";
  rmSync(directory, { recursive: true, force: true });
  return {
    threads: Number(/ on (\d+) threads? /.exec(run.engineLine ?? "")?.[1] ?? 0),
    difference: difference?.split("\n")[0],
  };
};

const results: Coverage[] = [];

const work = async (queue: CorpusModel[]) => {
  for (let model = queue.shift(); model; model = queue.shift()) {
    const expected = expectedById.get(model.id);
    if (!expected) continue;
    const runs: Record<string, Run> = {};
    for (const backend of backends) {
      runs[backend] = await runModel(model, getEngineEnvironment(backend), expected);
    }
    const off = await runModel(model, { ...process.env, PROVE_IT_ENGINE: "0" }, expected);
    runs.off = off;
    const on = runs[backends[0]];
    const engine = classifyEngineLine(on.engineLine);
    // With one backend, the engine is on; with several, each is named.
    const differences = backends.flatMap((backend) => {
      const name = backends.length > 1 ? backend : "on";
      const run = runs[backend];
      return [
        ...(run.verdict === off.verdict
          ? []
          : [`verdict: ${name} ${run.verdict}, off ${off.verdict}`]),
        ...OUTCOME_FIELDS.filter((field) => run.outcome?.[field] !== off.outcome?.[field]).map(
          (field) => `${field}: ${name} ${run.outcome?.[field]}, off ${off.outcome?.[field]}`,
        ),
      ];
    });
    const threads =
      isLoggingStates && engine.engine === "completed"
        ? await compareThreads(model, expected)
        : undefined;
    if (threads?.difference) {
      differences.push(`state log on 1 and 4 threads: ${threads.difference}`);
    }
    const bucket =
      engine.reason === undefined
        ? engine.engine
        : `${engine.engine}: ${normalizeReason(engine.reason)}`;
    results.push({
      id: model.id,
      tlcMilliseconds: expected.tlcMilliseconds,
      expectedStatus: expected.status,
      engine: engine.engine,
      reason: engine.reason,
      bucket,
      engineMilliseconds: engine.engineMilliseconds,
      isSame: differences.length === 0,
      differences,
      runs,
      threads: threads?.threads,
    });
    console.log(
      `[${results.length}/${models.length}] ${differences.length === 0 ? "same" : "DIFFERENT"}  ${on.verdict.padEnd(11)} ${bucket.slice(0, 80).padEnd(80)} ${model.id}${differences.length === 0 ? "" : `  ${differences.join("; ")}`}`,
    );
  }
};

const queue = [...models];
await Promise.all(Array.from({ length: concurrency }, () => work(queue)));
results.sort((left, right) => (left.id < right.id ? -1 : 1));
writeResults(outPath, results);

const tally = (label: string, key: (result: Coverage) => string) =>
  [
    ...results
      .reduce((groups, result) => {
        const group = groups.get(key(result)) ?? { models: 0, tlcSeconds: 0, onSeconds: 0 };
        group.models++;
        group.tlcSeconds += result.tlcMilliseconds / 1000;
        group.onSeconds += result.runs[backends[0]].wallMilliseconds / 1000;
        return groups.set(key(result), group);
      }, new Map<string, { models: number; tlcSeconds: number; onSeconds: number }>())
      .entries(),
  ]
    .sort((left, right) => right[1].tlcSeconds - left[1].tlcSeconds)
    .map(([name, group]) => ({
      [label]: name,
      models: group.models,
      "tlc s": Number(group.tlcSeconds.toFixed(1)),
      "prove-it s": Number(group.onSeconds.toFixed(1)),
    }));

console.table(tally("engine", (result) => result.engine));
console.table(tally("bucket", (result) => result.bucket));

if (isLoggingStates) {
  const logged = results.filter((result) => result.threads !== undefined);
  console.log(
    `\nThe state logs on 1 and 4 threads were compared on ${logged.length} models, ${logged.filter((result) => (result.threads ?? 0) > 1).length} of which the workers took levels of.`,
  );
}

const different = results.filter((result) => !result.isSame);
console.log(
  different.length === 0
    ? "\nThe engine on and off reached the same outcome on every model."
    : `\n${different.length} models differ between the engine on and off:\n${different.map((result) => `  ${result.id}: ${result.differences.join("; ")}`).join("\n")}`,
);
console.log(`Wrote ${outPath}`);
// A model whose outcome depends on the engine fails the run, so CI can gate on it.
if (different.length > 0) process.exitCode = 1;

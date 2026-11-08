// Runs each conformance model with the engine on (PROVE_IT_ENGINE=debug) and off (PROVE_IT_ENGINE=0),
// checks both runs reach the same outcome, and tallies what the engine did with each model, weighted
// by the time TLC takes on it. --backend picks the engine's backend, and --compare-backends runs
// every backend, each checked against the engine off.
// Usage: bun scripts/run.ts engine-coverage [--max-tlc-ms 20000] [--filter text] [--concurrency 3]
//        [--timeout-ms 600000] [--out path] [--backend ts | --compare-backends]

import { spawn } from "node:child_process";
import { readFileSync } from "node:fs";
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
}

const maximumTlcMilliseconds = Number(getOption("--max-tlc-ms") ?? 20000);
const filter = getOption("--filter");
const concurrency = Number(getOption("--concurrency") ?? 3);
const timeoutMilliseconds = Number(getOption("--timeout-ms") ?? 600000);
const outPath = getOption("--out") ?? join(CONFORMANCE_DIRECTORY, ".engine-coverage.json");
const backends = getBackends();

// Names of the spec's own definitions and variables would split one missing feature into many rows.
const normalizeReason = (reason: string) =>
  reason
    .replace(/^(unsupported: the (?:name|operator|operator argument)) .+$/, "$1 <name>")
    .replace(/^the (\w+) .+ isn't defined$/, "the $1 <name> isn't defined")
    .replace(/\d+/g, "N");

const runModel = (model: CorpusModel, backend: string | undefined, expected: ExpectedResult) =>
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
        env: backend
          ? { ...getBackendEnvironment(backend), PROVE_IT_ENGINE: "debug" }
          : { ...process.env, PROVE_IT_ENGINE: "0" },
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

const results: Coverage[] = [];

const work = async (queue: CorpusModel[]) => {
  for (let model = queue.shift(); model; model = queue.shift()) {
    const expected = expectedById.get(model.id);
    if (!expected) continue;
    const runs: Record<string, Run> = {};
    for (const backend of backends) runs[backend] = await runModel(model, backend, expected);
    const off = await runModel(model, undefined, expected);
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

const different = results.filter((result) => !result.isSame);
console.log(
  different.length === 0
    ? "\nThe engine on and off reached the same outcome on every model."
    : `\n${different.length} models differ between the engine on and off:\n${different.map((result) => `  ${result.id}: ${result.differences.join("; ")}`).join("\n")}`,
);
console.log(`Wrote ${outPath}`);
// A model whose outcome depends on the engine fails the run, so CI can gate on it.
if (different.length > 0) process.exitCode = 1;

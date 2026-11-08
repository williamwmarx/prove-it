// Runs each conformance model with the engine on (PROVE_IT_ENGINE=debug) and off (PROVE_IT_ENGINE=0),
// checks both runs reach the same outcome, and tallies what the engine did with each model, weighted
// by the time TLC takes on it. --backend picks the engine's backend, and --compare-backends runs
// every backend, each checked against the engine off. With --state-logs, each model the engine
// completes runs again on 1 and on 4 threads, and the two state logs (PROVE_IT_STATE_LOG) must be
// identical; with --compare-backends too, each model both the TypeScript and the native engine
// complete runs again on each, with -nowarning and without, and their state logs must be
// identical.
//
// A model the TypeScript engine completes and the native engine doesn't is a coverage regression,
// which fails the run unless native/coverage-allowlist.json lists its reason, with the milestone
// that removes it.
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
  getNativeTier,
} from "./engine-runs";
import type { ExpectedResult } from "./record-tlc";
import { getStateLogDifference, readLogLines } from "./state-logs";

interface Run {
  outcome: ModelOutcome | undefined;
  verdict: string;
  detail: string | undefined;
  engineLine: string | undefined;
  // What the native engine did, when it ran.
  native: { tier: string; reason: string } | undefined;
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
  // With --state-logs and --compare-backends, whether the two engines' state logs were compared.
  isStateLogged: boolean;
}

interface AllowedRegression {
  reason: string;
  milestone: string;
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

const runModel = (
  model: CorpusModel,
  environment: NodeJS.ProcessEnv,
  expected: ExpectedResult,
  isWarningEnabled = false,
) =>
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
        ...(isWarningEnabled ? ["--warnings"] : []),
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
        native: getNativeTier(errorOutput),
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

// The state logs of the TypeScript and the native engine, with -nowarning and without, or the
// first difference.
const compareBackends = async (model: CorpusModel, expected: ExpectedResult) => {
  const directory = mkdtempSync(join(tmpdir(), "prove-it-state-logs-"));
  const differences: string[] = [];
  for (const isWarningEnabled of [false, true]) {
    const [typescript, native] = backends.map((backend) => join(directory, `${backend}.jsonl`));
    for (const [backend, path] of [
      ["ts", typescript],
      ["rust", native],
    ]) {
      await runModel(
        model,
        { ...getEngineEnvironment(backend), PROVE_IT_STATE_LOG: path },
        expected,
        isWarningEnabled,
      );
    }
    const difference =
      existsSync(typescript) && existsSync(native)
        ? getStateLogDifference(readLogLines(typescript), readLogLines(native))
        : "a run wrote no state log";
    if (difference) {
      differences.push(
        `state log of ts and rust${isWarningEnabled ? " with warnings" : ""}: ${difference.split("\n")[0]}`,
      );
    }
  }
  rmSync(directory, { recursive: true, force: true });
  return differences;
};

const allowlistPath = join(import.meta.dirname, "../native/coverage-allowlist.json");
const allowlist: AllowedRegression[] = existsSync(allowlistPath)
  ? JSON.parse(readFileSync(allowlistPath, "utf8"))
  : [];
const isAllowed = (reason: string) =>
  allowlist.some((allowed) => normalizeReason(reason).startsWith(allowed.reason));

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
    const isCompared = backends.length > 1;
    const threads =
      isLoggingStates && !isCompared && engine.engine === "completed"
        ? await compareThreads(model, expected)
        : undefined;
    if (threads?.difference) {
      differences.push(`state log on 1 and 4 threads: ${threads.difference}`);
    }
    // Both engines searched every state: completed, or found every state of a graph whose temporal
    // properties the interpreter checks.
    const isStateLogged =
      isLoggingStates &&
      isCompared &&
      (engine.engine === "completed" || (on.engineLine?.startsWith("found ") ?? false)) &&
      runs.rust?.native?.tier === "complete";
    if (isStateLogged) differences.push(...(await compareBackends(model, expected)));
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
      isStateLogged,
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

if (backends.includes("rust")) {
  const tiers = results.map((result) => ({
    result,
    native: result.runs.rust?.native,
    isCompleted: classifyEngineLine(result.runs.ts?.engineLine).engine === "completed",
  }));
  console.table(
    tally("native engine", (result) => {
      const native = result.runs.rust?.native;
      return native
        ? `${native.tier}${native.tier === "complete" ? "" : `: ${normalizeReason(native.reason)}`}`.slice(
            0,
            100,
          )
        : "not reached";
    }),
  );
  const regressions = tiers.filter((tier) => tier.isCompleted && tier.native?.tier !== "complete");
  const unallowed = regressions.filter((tier) => !isAllowed(tier.native?.reason ?? ""));
  console.log(
    `\nThe native engine completes ${tiers.filter((tier) => tier.native?.tier === "complete").length} models; of the ${tiers.filter((tier) => tier.isCompleted).length} the TypeScript engine completes, it doesn't complete ${regressions.length}, ${regressions.length - unallowed.length} of them for a reason the allowlist names.`,
  );
  const gained = tiers.filter((tier) => !tier.isCompleted && tier.native?.tier === "complete");
  if (gained.length > 0) {
    console.log(`Gained: ${gained.map((tier) => tier.result.id).join(", ")}`);
  }
  if (isLoggingStates) {
    console.log(
      `The state logs of the two engines were compared on ${results.filter((result) => result.isStateLogged).length} models.`,
    );
  }
  if (unallowed.length > 0) {
    console.log(
      `Coverage regressions the allowlist doesn't name:\n${unallowed.map((tier) => `  ${tier.result.id}: ${tier.native?.tier ?? "not reached"}: ${tier.native?.reason ?? ""}`).join("\n")}`,
    );
    process.exitCode = 1;
  }
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

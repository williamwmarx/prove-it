// Checks the native store (native/crates/tla-values) against the TypeScript engine on the corpus.
// Each model an engine-coverage run found the TypeScript engine completes runs again on one thread
// with PROVE_IT_STORE_TRACE and PROVE_IT_STATE_LOG, and native/tools/replay replays what they
// wrote: with --traces, every store operation on the Rust store, which must give the same ids,
// comparisons and reasons to stop; with --fingerprints (conformance:fp64), every state, whose TLC
// fingerprint the Rust store must compute as the engine did, from its parent and from scratch.
// The files of one model are deleted before the next starts, as the largest traces take gigabytes.
// Usage: bun scripts/run.ts native-replay --coverage <engine-coverage --out> [--traces]
//        [--fingerprints] [--filter text] [--concurrency 2] [--out path]

import { spawn, spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { findModels, getOption } from "./corpora";

interface Coverage {
  id: string;
  engine: string;
}

interface Replay {
  id: string;
  engineLine: string | undefined;
  traceBytes: number | undefined;
  trace: string | undefined;
  fingerprints: string | undefined;
  isExact: boolean;
}

const coveragePath = getOption("--coverage");
const filter = getOption("--filter");
const concurrency = Number(getOption("--concurrency") ?? 2);
const outPath = getOption("--out");
const isTracing = process.argv.includes("--traces");
const isFingerprinting = process.argv.includes("--fingerprints") || !isTracing;
if (coveragePath === undefined) {
  console.error("Pass --coverage, the results engine-coverage --out wrote");
  process.exit(2);
}

const NATIVE_DIRECTORY = join(import.meta.dirname, "../native");
const REPLAY = join(NATIVE_DIRECTORY, "target/release/replay");

const build = spawnSync("cargo", ["build", "--release", "--locked", "-p", "replay"], {
  cwd: NATIVE_DIRECTORY,
  stdio: "inherit",
});
if (build.status !== 0) process.exit(build.status ?? 1);

const coverage: Coverage[] = JSON.parse(readFileSync(coveragePath, "utf8"));
const completed = new Set(
  coverage.filter((entry) => entry.engine === "completed").map((entry) => entry.id),
);
const models = findModels().filter(
  (model) => completed.has(model.id) && (filter === undefined || model.id.includes(filter)),
);

const runProcess = (command: string, args: string[], environment?: NodeJS.ProcessEnv) =>
  new Promise<{ stdout: string; stderr: string; code: number | null }>((resolve) => {
    const child = spawn(command, args, { stdio: ["ignore", "pipe", "pipe"], env: environment });
    const stdout: Buffer[] = [];
    const stderr: Buffer[] = [];
    child.stdout.on("data", (chunk: Buffer) => stdout.push(chunk));
    child.stderr.on("data", (chunk: Buffer) => stderr.push(chunk));
    child.on("close", (code) =>
      resolve({
        stdout: Buffer.concat(stdout).toString("utf8"),
        stderr: Buffer.concat(stderr).toString("utf8"),
        code,
      }),
    );
  });

const replayModel = async (model: (typeof models)[number]): Promise<Replay> => {
  const directory = mkdtempSync(join(tmpdir(), "native-replay-"));
  const tracePath = join(directory, "trace.jsonl");
  const logPath = join(directory, "states.jsonl");
  const run = await runProcess(
    process.execPath,
    [
      "--stack-size=8000",
      "--max-old-space-size=6144",
      join(import.meta.dirname, "check-model.js"),
      model.specPath,
      model.configPath,
    ],
    {
      ...process.env,
      PROVE_IT_ENGINE: "debug",
      PROVE_IT_WORKERS: "1",
      ...(isTracing && { PROVE_IT_STORE_TRACE: tracePath }),
      ...(isFingerprinting && { PROVE_IT_STATE_LOG: logPath }),
    },
  );
  const engineLine = run.stderr
    .split("\n")
    .find((line) => line.startsWith("[engine] checked "))
    ?.slice("[engine] ".length);
  const replay = async (mode: string, path: string) => {
    const result = await runProcess(REPLAY, [mode, path]);
    return { text: (result.stdout + result.stderr).trim(), isExact: result.code === 0 };
  };
  const trace = isTracing ? await replay("store", tracePath) : undefined;
  const traceBytes = isTracing ? statSync(tracePath, { throwIfNoEntry: false })?.size : undefined;
  const fingerprints = isFingerprinting ? await replay("fingerprints", logPath) : undefined;
  rmSync(directory, { recursive: true, force: true });
  return {
    id: model.id,
    engineLine,
    traceBytes,
    trace: trace?.text,
    fingerprints: fingerprints?.text,
    isExact:
      engineLine !== undefined && (trace?.isExact ?? true) && (fingerprints?.isExact ?? true),
  };
};

const results: Replay[] = [];
const queue = [...models];
await Promise.all(
  Array.from({ length: concurrency }, async () => {
    for (let model = queue.shift(); model; model = queue.shift()) {
      const result = await replayModel(model);
      results.push(result);
      const detail = [result.trace, result.fingerprints]
        .filter((text) => text !== undefined)
        .map((text) => text.replace(/^\S+: /, ""))
        .join("; ");
      console.log(
        `${result.isExact ? "exact" : "DIFFERS"}  ${model.id}  ${result.engineLine ?? "the engine didn't complete"}  ${detail}`,
      );
    }
  }),
);

results.sort((left, right) => left.id.localeCompare(right.id));
if (outPath) writeFileSync(outPath, `${JSON.stringify(results, null, 2)}\n`);
const differing = results.filter((result) => !result.isExact);
const operations = results.reduce(
  (sum, result) => sum + Number(/replayed (\d+) operations/.exec(result.trace ?? "")?.[1] ?? 0),
  0,
);
const states = results.reduce(
  (sum, result) =>
    sum + Number(/fingerprinted (\d+) states/.exec(result.fingerprints ?? "")?.[1] ?? 0),
  0,
);
console.log(
  `\n${results.length} models: ${results.length - differing.length} exact, ${differing.length} not` +
    (isTracing ? `; ${operations} store operations replayed` : "") +
    (isFingerprinting ? `; ${states} states fingerprinted` : ""),
);
if (differing.length > 0) process.exitCode = 1;

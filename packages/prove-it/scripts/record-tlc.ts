// Records TLC's outcome on each corpus model in tests/conformance/expected.json, or with --stdout
// its full output, in the default and -tool modes and in TLC's own default, which writes the trace
// exploration files, in tests/conformance/tlc-stdout (see tlc-recordings.ts). --stdout records
// only the models expected.json lists with TLC under --max-tlc-ms, and only those it has no
// recording of yet.
// TLA2TOOLS_JAR must be tla2tools.jar as tlatools' `dist` target builds it, at
// /tmp/tlaplus/tlatools/org.lamport.tlatools/dist/tla2tools.jar, where the recordings were made,
// since TLCGet("config") prints where it is: TLC's classes compiled with -g, which Java's messages
// name variables by, and only the libraries `dist` folds in (javax.mail, jline, gson). A jar that
// folds in the rest of lib/, as CommunityModules.jar, loads its Java overrides of the community
// modules and records another TLC.
// Usage: TLA2TOOLS_JAR=path [TLC_COMMIT=commit] bun scripts/run.ts record-tlc [--stdout]
//        [--keep-unfinished] [--max-tlc-ms 20000] [--filter text] [--concurrency 2]

import { spawn } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, relative } from "node:path";

import {
  CORPORA_DIRECTORY,
  type CorpusModel,
  EXPECTED_PATH,
  findModels,
  getOption,
  linkLibraryModules,
} from "./corpora";
import {
  getRecordingPath,
  getTlcArguments,
  LIBRARY_OPTION,
  type OutputMode,
  readRecording,
  RECORDED_MODES,
  runTakingTraceFiles,
  TLC_COMMIT,
  TLC_STDOUT_DIRECTORY,
  type TlcRecording,
} from "./tlc-recordings";

export interface ExpectedResult {
  id: string;
  status: string;
  violation?: string;
  generatedStates?: number;
  distinctStates?: number;
  depth?: number;
  traceLength?: number;
  // TLC's estimate "based on the actual fingerprints", as check-model.ts's ModelOutcome has it.
  fingerprintProbability?: string;
  tlcMilliseconds: number;
}

interface ManifestModel {
  path: string;
  runtime: string;
  mode: string;
}

const MAXIMUM_RECORDED_RUNTIME_SECONDS = 60;

const isStdout = process.argv.includes("--stdout");
const maximumTlcMilliseconds = Number(getOption("--max-tlc-ms") ?? 20000);
const filter = getOption("--filter");
const concurrency = Number(getOption("--concurrency") ?? 2);

const jarPath = process.env.TLA2TOOLS_JAR;
if (!jarPath || !existsSync(jarPath)) {
  console.error("Set TLA2TOOLS_JAR to the path of tla2tools.jar");
  process.exit(1);
}

const getSeconds = (runtime: string) =>
  runtime.split(":").reduce((total, part) => total * 60 + Number(part), 0);

const isRecordable = (model: CorpusModel) => {
  if (!model.id.startsWith("examples/")) return true;
  const root = join(CORPORA_DIRECTORY, "examples");
  const manifestPath = join(dirname(model.specPath), "manifest.json");
  if (!existsSync(manifestPath)) return false;
  const manifest: { modules: { models: ManifestModel[] }[] } = JSON.parse(
    readFileSync(manifestPath, "utf8"),
  );
  const entry = manifest.modules
    .flatMap((module) => module.models)
    .find((candidate) => candidate.path === relative(root, model.configPath));
  return (
    entry !== undefined &&
    entry.mode === "exhaustive search" &&
    getSeconds(entry.runtime) <= MAXIMUM_RECORDED_RUNTIME_SECONDS
  );
};

const getStatus = (exitCode: number | null, output: string) => {
  if (exitCode === null) return "killed";
  if (exitCode === 0) return "success";
  if (exitCode === 10) return "assumption-violation";
  if (exitCode === 11) return "deadlock";
  if (exitCode === 12)
    return /Invariant \S+ is violated/.test(output) ? "invariant-violation" : "property-violation";
  if (exitCode === 13) return "liveness-violation";
  return "error";
};

const getFirstTraceLength = (output: string) => {
  const numbers = [...output.matchAll(/^State (\d+):/gm)].map((match) => Number(match[1]));
  const restart = numbers.indexOf(1, 1);
  return restart === -1 ? numbers.length : restart;
};

// TLC prints a line about JAVA_TOOL_OPTIONS and its kin when they're set, which would land in
// its output.
const getJavaEnvironment = () =>
  Object.fromEntries(
    Object.entries(process.env).filter(
      ([name]) => !["JAVA_TOOL_OPTIONS", "_JAVA_OPTIONS", "JDK_JAVA_OPTIONS"].includes(name),
    ),
  );

const spawnTlc = (model: CorpusModel, mode: OutputMode, metadataDirectory: string) =>
  spawn(
    "java",
    [
      "-XX:+UseParallelGC",
      "-Xmx768m",
      LIBRARY_OPTION,
      "-cp",
      jarPath,
      "tlc2.TLC",
      ...getTlcArguments(model, mode, metadataDirectory),
    ],
    { cwd: model.directory, env: getJavaEnvironment() },
  );

const getFingerprintProbability = (output: string) =>
  /based on the actual fingerprints: {2}val = (\S+)/.exec(output)?.[1];

const runTlc = (model: CorpusModel) =>
  new Promise<ExpectedResult>((resolve) => {
    const metadataDirectory = mkdtempSync(join(tmpdir(), "tla-ts-tlc-"));
    const startedAt = performance.now();
    const child = spawnTlc(model, "default", metadataDirectory);
    const chunks: Buffer[] = [];
    child.stdout.on("data", (chunk: Buffer) => chunks.push(chunk));
    child.stderr.on("data", (chunk: Buffer) => chunks.push(chunk));
    child.on("close", (exitCode) => {
      rmSync(metadataDirectory, { recursive: true, force: true });
      const output = Buffer.concat(chunks).toString("utf8");
      const status = getStatus(exitCode, output);
      const statistics = [
        ...output.matchAll(/(\d+) states generated, (\d+) distinct states found/g),
      ].at(-1);
      const depth = /The depth of the complete state graph search is (\d+)/.exec(output);
      const violation = /(?:Invariant|property) (\S+) is violated/.exec(output);
      const fingerprintProbability = getFingerprintProbability(output);
      resolve({
        id: model.id,
        status,
        ...(violation ? { violation: violation[1] } : {}),
        ...(status === "success" && statistics
          ? { generatedStates: Number(statistics[1]), distinctStates: Number(statistics[2]) }
          : {}),
        ...(status === "success" && depth ? { depth: Number(depth[1]) } : {}),
        ...(status === "success" && fingerprintProbability ? { fingerprintProbability } : {}),
        ...(status !== "success" && status !== "error"
          ? {
              traceLength: output.includes("is violated by the initial state")
                ? 1
                : getFirstTraceLength(output),
            }
          : {}),
        tlcMilliseconds: Math.round(performance.now() - startedAt),
      });
    });
  });

// A recording is only as good as the commit its key names, which a jar built without its git
// history doesn't print.
if (isStdout && process.env.TLC_COMMIT !== TLC_COMMIT) {
  console.error(`Build tla2tools.jar from ${TLC_COMMIT} and set TLC_COMMIT to it`);
  process.exit(1);
}

const runOutput = (model: CorpusModel, mode: OutputMode) =>
  new Promise<TlcRecording>((resolve) => {
    const metadataDirectory = mkdtempSync(join(tmpdir(), "prove-it-tlc-"));
    const child = spawnTlc(model, mode, metadataDirectory);
    const stdout: Buffer[] = [];
    const stderr: Buffer[] = [];
    child.stdout.on("data", (chunk: Buffer) => stdout.push(chunk));
    child.stderr.on("data", (chunk: Buffer) => stderr.push(chunk));
    child.on("close", (exitCode) => {
      rmSync(metadataDirectory, { recursive: true, force: true });
      resolve({
        id: model.id,
        mode,
        tlcCommit: TLC_COMMIT,
        exitCode: exitCode ?? -1,
        stdout: Buffer.concat(stdout).toString("utf8"),
        stderr: Buffer.concat(stderr).toString("utf8"),
      });
    });
  });

const recordOutput = async (model: CorpusModel, mode: OutputMode) => {
  const run =
    mode === "te"
      ? await runTakingTraceFiles(dirname(model.specPath), () => runOutput(model, mode))
      : { result: await runOutput(model, mode), files: {} };
  const recording =
    Object.keys(run.files).length === 0 ? run.result : { ...run.result, files: run.files };
  writeFileSync(getRecordingPath(model, mode), `${JSON.stringify(recording, null, 2)}\n`);
  return recording;
};

// The recordings run TLC as the outcomes do, so they give expected.json the fingerprint estimate of
// each model they agree with on the counts.
const addFingerprintProbabilities = (expectedResults: ExpectedResult[], models: CorpusModel[]) => {
  const expectedById = new Map(expectedResults.map((result) => [result.id, result]));
  for (const model of models) {
    const expected = expectedById.get(model.id);
    const recording = readRecording(model, "default");
    if (expected?.status !== "success" || !recording) continue;
    const statistics = [
      ...recording.stdout.matchAll(/(\d+) states generated, (\d+) distinct states found/g),
    ].at(-1);
    const fingerprintProbability = getFingerprintProbability(recording.stdout);
    if (
      statistics &&
      fingerprintProbability &&
      Number(statistics[1]) === expected.generatedStates &&
      Number(statistics[2]) === expected.distinctStates
    ) {
      expected.fingerprintProbability = fingerprintProbability;
    }
  }
  writeFileSync(EXPECTED_PATH, `${JSON.stringify(expectedResults, null, 2)}\n`);
};

const recordOutputs = async () => {
  const expectedResults: ExpectedResult[] = JSON.parse(readFileSync(EXPECTED_PATH, "utf8"));
  const expectedById = new Map(expectedResults.map((result) => [result.id, result]));
  const models = findModels().filter((model) => {
    const expected = expectedById.get(model.id);
    return (
      expected !== undefined &&
      expected.tlcMilliseconds <= maximumTlcMilliseconds &&
      (filter === undefined || model.id.includes(filter))
    );
  });
  const runs = models
    .flatMap((model) => RECORDED_MODES.map((mode) => ({ model, mode })))
    .filter((run) => !existsSync(getRecordingPath(run.model, run.mode)));
  mkdirSync(TLC_STDOUT_DIRECTORY, { recursive: true });
  const progress = { next: 0, done: 0 };
  const work = async () => {
    while (progress.next < runs.length) {
      const run = runs[progress.next++];
      const recording = await recordOutput(run.model, run.mode);
      progress.done++;
      console.log(
        `[${progress.done}/${runs.length}] exit ${String(recording.exitCode).padEnd(4)} ${run.mode.padEnd(8)} ${run.model.id}`,
      );
    }
  };
  await Promise.all(Array.from({ length: concurrency }, work));
  console.log(`Recorded ${runs.length} outputs in ${TLC_STDOUT_DIRECTORY}`);
  addFingerprintProbabilities(expectedResults, models);
};

// The recorder that made the first expected.json stopped TLC at 300 s and recorded an error, so an
// entry like that says only that TLC didn't finish in 300 s, which running TLC without a limit can't
// reproduce. --keep-unfinished carries those entries over without running TLC on their models.
const UNFINISHED_MILLISECONDS = 300000;

const getUnfinishedResults = () =>
  process.argv.includes("--keep-unfinished")
    ? (JSON.parse(readFileSync(EXPECTED_PATH, "utf8")) as ExpectedResult[]).filter(
        (result) => result.status === "error" && result.tlcMilliseconds >= UNFINISHED_MILLISECONDS,
      )
    : [];

const recordOutcomes = async () => {
  const unfinished = getUnfinishedResults();
  const unfinishedIds = new Set(unfinished.map((result) => result.id));
  const models = findModels().filter(
    (model) => isRecordable(model) && !unfinishedIds.has(model.id),
  );
  const results: ExpectedResult[] = [...unfinished];
  const queue = { next: 0 };
  const work = async () => {
    while (queue.next < models.length) {
      const model = models[queue.next++];
      const result = await runTlc(model);
      results.push(result);
      console.log(
        `[${results.length - unfinished.length}/${models.length}] ${result.status.padEnd(20)} ${model.id}`,
      );
    }
  };
  await Promise.all(Array.from({ length: concurrency }, work));
  results.sort((left, right) => (left.id < right.id ? -1 : 1));
  writeFileSync(EXPECTED_PATH, `${JSON.stringify(results, null, 2)}\n`);
  console.log(`Wrote ${results.length} TLC results to ${EXPECTED_PATH}`);
};

linkLibraryModules();
await (isStdout ? recordOutputs() : recordOutcomes());

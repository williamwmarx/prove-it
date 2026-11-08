// Compares the full output of Java TLC, of Prove It with its engine, and of Prove It with the engine
// off, on each corpus model, in TLC's default output and with -tool. TLC's output comes from the
// recordings record-tlc.ts --stdout makes (tlc-recordings.ts); Prove It runs as its CLI with the
// same command line. Each output is the exit code, stdout and stderr, normalised by
// normalize-output.ts. Every difference must be the one tests/conformance/known-differences.json
// lists for that model, mode and pair of checkers, or the run fails.
//
// --stop-at also runs the engine stopped by PROVE_IT_STOP_AT before a state picked at random
// from those it found, and its output must not differ from the engine's. --backend picks the
// engine's backend, and --compare-backends runs every one. --update rewrites
// known-differences.json from the run, keeping the reasons it gives.
// A run without a TLC recording fails the check, since nothing compared it with TLC. --timeout-ms
// stops a checker that runs longer, and without it nothing does.
// Usage: bun scripts/run.ts differential [--max-tlc-ms 20000] [--filter text] [--concurrency 3]
//        [--modes default,tool] [--stop-at] [--timeout-ms ms] [--update] [--out path]
//        [--backend ts | --compare-backends]

import { spawn } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import {
  CONFORMANCE_DIRECTORY,
  type CorpusModel,
  EXPECTED_PATH,
  findModels,
  getOption,
  linkLibraryModules,
  writeResults,
} from "./corpora";
import {
  classifyEngineLine,
  getBackendEnvironment,
  getBackends,
  getEngineLine,
} from "./engine-runs";
import { getLineDiff } from "./line-diff";
import { getTranscript } from "./normalize-output";
import type { ExpectedResult } from "./record-tlc";
import {
  getTlcArguments,
  LIBRARY_OPTION,
  OUTPUT_MODES,
  type OutputMode,
  readRecording,
} from "./tlc-recordings";

interface Output {
  // The exit code, stdout and stderr, normalised, as one text.
  transcript: string;
  engineLine: string | undefined;
}

interface KnownDifference {
  id: string;
  mode: OutputMode;
  // The two checkers, such as "tlc/ts" or "ts/interpreter".
  pair: string;
  reason: string;
  diff: string[];
}

interface Comparison {
  id: string;
  mode: OutputMode;
  pair: string;
  diff: string[];
  // Whether there is no diff or it is the one known-differences.json lists.
  isKnown: boolean;
}

export const KNOWN_DIFFERENCES_PATH = join(CONFORMANCE_DIRECTORY, "known-differences.json");

const CLI_PATH = join(import.meta.dirname, "../dist/cli.js");

const maximumTlcMilliseconds = Number(getOption("--max-tlc-ms") ?? 20000);
const filter = getOption("--filter");
const concurrency = Number(getOption("--concurrency") ?? 3);
const timeoutOption = getOption("--timeout-ms");
const timeoutMilliseconds = timeoutOption === undefined ? undefined : Number(timeoutOption);
const modes = (getOption("--modes")?.split(",") ?? OUTPUT_MODES).filter(
  (mode): mode is OutputMode => OUTPUT_MODES.some((known) => known === mode),
);
const isStopping = process.argv.includes("--stop-at");
const isUpdate = process.argv.includes("--update");
const outPath = getOption("--out") ?? join(CONFORMANCE_DIRECTORY, ".differential.json");
const backends = getBackends();

const runCli = (model: CorpusModel, mode: OutputMode, environment: NodeJS.ProcessEnv) =>
  new Promise<Output>((resolve) => {
    const metadataDirectory = mkdtempSync(join(tmpdir(), "prove-it-differential-"));
    const child = spawn(
      process.execPath,
      [CLI_PATH, LIBRARY_OPTION, "tlc2.TLC", ...getTlcArguments(model, mode, metadataDirectory)],
      {
        cwd: model.directory,
        env: environment,
        timeout: timeoutMilliseconds,
        killSignal: "SIGKILL",
      },
    );
    const stdout: Buffer[] = [];
    const stderr: Buffer[] = [];
    child.stdout.on("data", (chunk: Buffer) => stdout.push(chunk));
    child.stderr.on("data", (chunk: Buffer) => stderr.push(chunk));
    child.on("close", (exitCode, signal) => {
      rmSync(metadataDirectory, { recursive: true, force: true });
      const errorOutput = Buffer.concat(stderr).toString("utf8");
      resolve({
        transcript: getTranscript(
          signal === "SIGKILL" ? `killed after ${timeoutMilliseconds} ms` : String(exitCode),
          Buffer.concat(stdout).toString("utf8"),
          errorOutput,
        ),
        engineLine: getEngineLine(errorOutput),
      });
    });
  });

// A state from those the run found, the same for a model on every run.
const getStopState = (id: string, transcript: string) => {
  const distinct = [...transcript.matchAll(/(\d+) distinct states? found/g)].at(-1);
  if (!distinct || Number(distinct[1]) === 0) return undefined;
  const hash = [...id].reduce(
    (total, character) => Math.imul(total ^ character.charCodeAt(0), 0x01000193),
    0x811c9dc5,
  );
  return (hash >>> 0) % Number(distinct[1]);
};

const knownDifferences: KnownDifference[] = existsSync(KNOWN_DIFFERENCES_PATH)
  ? JSON.parse(readFileSync(KNOWN_DIFFERENCES_PATH, "utf8"))
  : [];
const getKey = (id: string, mode: string, pair: string) => `${id} ${mode} ${pair}`;
const knownByKey = new Map(
  knownDifferences.map((known) => [getKey(known.id, known.mode, known.pair), known]),
);

const expectedResults: ExpectedResult[] = JSON.parse(readFileSync(EXPECTED_PATH, "utf8"));
const expectedById = new Map(expectedResults.map((result) => [result.id, result]));
const isSelected = (expected: ExpectedResult) =>
  expected.tlcMilliseconds <= maximumTlcMilliseconds &&
  (filter === undefined || expected.id.includes(filter));
const models = findModels()
  .filter((model) => {
    const expected = expectedById.get(model.id);
    return expected !== undefined && isSelected(expected);
  })
  .sort(
    (left, right) =>
      (expectedById.get(right.id)?.tlcMilliseconds ?? 0) -
      (expectedById.get(left.id)?.tlcMilliseconds ?? 0),
  );

// A model expected.json selects that isn't in the fetched corpora is one the run didn't check.
const foundIds = new Set(models.map((model) => model.id));
const absent = expectedResults
  .filter((expected) => isSelected(expected) && !foundIds.has(expected.id))
  .map((expected) => expected.id);

// What the engine says when PROVE_IT_STOP_AT stops it.
const STOPPED_REASON = "stopped where PROVE_IT_STOP_AT asked";

const comparisons: Comparison[] = [];
const missing: string[] = [];
// The runs --stop-at couldn't stop, since the engine handed over before the first state it could.
const unforced: string[] = [];
const results: unknown[] = [];

const compare = (id: string, mode: OutputMode, pair: string, left: string, right: string) => {
  const diff = getLineDiff(left.split("\n"), right.split("\n"));
  const known = knownByKey.get(getKey(id, mode, pair));
  const comparison = {
    id,
    mode,
    pair,
    diff,
    isKnown: diff.length === 0 || JSON.stringify(diff) === JSON.stringify(known?.diff),
  };
  comparisons.push(comparison);
  return comparison;
};

const work = async (queue: { model: CorpusModel; mode: OutputMode }[], total: number) => {
  for (let run = queue.shift(); run; run = queue.shift()) {
    const model = run.model;
    const mode = run.mode;
    const recording = readRecording(model, mode);
    if (!recording) missing.push(`${model.id} ${mode}`);
    const tlc =
      recording && getTranscript(String(recording.exitCode), recording.stdout, recording.stderr);
    const interpreter = await runCli(model, mode, { ...process.env, PROVE_IT_ENGINE: "0" });
    const modelComparisons: Comparison[] = [];
    const outputs: Record<string, Output> = { interpreter };
    for (const backend of backends) {
      const engine = await runCli(model, mode, {
        ...getBackendEnvironment(backend),
        PROVE_IT_ENGINE: "debug",
      });
      outputs[backend] = engine;
      if (tlc)
        modelComparisons.push(compare(model.id, mode, `tlc/${backend}`, tlc, engine.transcript));
      modelComparisons.push(
        compare(
          model.id,
          mode,
          `${backend}/interpreter`,
          engine.transcript,
          interpreter.transcript,
        ),
      );
      // A stop needs a search to stop: an engine that skipped the spec would only run the
      // interpreter again.
      const isSearched = ["completed", "handed over"].includes(
        classifyEngineLine(engine.engineLine).engine,
      );
      // The final count includes states the engine never expanded when it handed over, so a stop
      // there wouldn't stop it: a run counts only when the engine says it stopped, and otherwise
      // the stop moves to half as far, down to the first state.
      let stopAt = isStopping && isSearched ? getStopState(model.id, engine.transcript) : undefined;
      let isForced = false;
      while (stopAt !== undefined && !isForced) {
        const stopped = await runCli(model, mode, {
          ...getBackendEnvironment(backend),
          PROVE_IT_ENGINE: "debug",
          PROVE_IT_STOP_AT: String(stopAt),
        });
        isForced = stopped.engineLine?.endsWith(STOPPED_REASON) ?? false;
        if (isForced) {
          outputs[`${backend} stopped at ${stopAt}`] = stopped;
          modelComparisons.push(
            compare(model.id, mode, `${backend}/stopped`, engine.transcript, stopped.transcript),
          );
        } else stopAt = stopAt > 0 ? Math.floor(stopAt / 2) : undefined;
      }
      if (isStopping && isSearched && !isForced) unforced.push(`${backend} ${mode} ${model.id}`);
    }
    results.push({ id: model.id, mode, tlc, outputs, comparisons: modelComparisons });
    const unknown = modelComparisons.filter((comparison) => !comparison.isKnown);
    const differing = modelComparisons.filter((comparison) => comparison.diff.length > 0);
    console.log(
      `[${results.length}/${total}] ${unknown.length > 0 ? "NEW" : differing.length > 0 ? "known" : "same"}  ${mode.padEnd(7)} ${model.id}${differing.length > 0 ? `  ${differing.map((comparison) => `${comparison.pair}: ${comparison.diff.length} lines`).join(", ")}` : ""}${recording ? "" : "  (no TLC recording)"}`,
    );
  }
};

linkLibraryModules();
const runs = models.flatMap((model) => modes.map((mode) => ({ model, mode })));
const total = runs.length;
await Promise.all(Array.from({ length: concurrency }, () => work(runs, total)));
writeResults(outPath, results);

// The pairs a run compares, so a known difference of a pair it didn't run isn't reported fixed.
const isCompared = (known: KnownDifference) =>
  comparisons.some(
    (comparison) =>
      comparison.id === known.id &&
      comparison.mode === known.mode &&
      comparison.pair === known.pair,
  );
const unknown = comparisons.filter((comparison) => !comparison.isKnown);
const fixed = knownDifferences.filter(
  (known) =>
    isCompared(known) &&
    comparisons.some(
      (comparison) =>
        comparison.id === known.id &&
        comparison.mode === known.mode &&
        comparison.pair === known.pair &&
        comparison.diff.length === 0,
    ),
);
const differing = comparisons.filter((comparison) => comparison.diff.length > 0);
const pairs = [...new Set(comparisons.map((comparison) => comparison.pair))];
console.table(
  pairs.map((pair) => ({
    pair,
    compared: comparisons.filter((comparison) => comparison.pair === pair).length,
    same: comparisons.filter(
      (comparison) => comparison.pair === pair && comparison.diff.length === 0,
    ).length,
    known: differing.filter((comparison) => comparison.pair === pair && comparison.isKnown).length,
    new: unknown.filter((comparison) => comparison.pair === pair).length,
  })),
);
if (missing.length > 0) {
  console.log(
    `\n${missing.length} runs have no TLC recording; record them with record-tlc.ts --stdout.`,
  );
  process.exitCode = 1;
}
if (unforced.length > 0) {
  console.log(`\n${unforced.length} runs the engine handed over before any stop could take it:`);
  for (const run of unforced.slice(0, 20)) console.log(`  ${run}`);
}
if (absent.length > 0) {
  console.log(
    `\n${absent.length} models aren't in the fetched corpora; fetch them with fetch-corpora.ts:`,
  );
  for (const id of absent.slice(0, 20)) console.log(`  ${id}`);
  process.exitCode = 1;
}
if (fixed.length > 0) {
  console.log(`\n${fixed.length} known differences are gone:`);
  for (const known of fixed) console.log(`  ${known.pair} ${known.mode} ${known.id}`);
}

if (isUpdate) {
  // Entries of runs this one didn't make stay as they are.
  const kept = knownDifferences.filter((known) => !isCompared(known));
  const recorded = differing.map((comparison) => ({
    id: comparison.id,
    mode: comparison.mode,
    pair: comparison.pair,
    reason: knownByKey.get(getKey(comparison.id, comparison.mode, comparison.pair))?.reason ?? "",
    diff: comparison.diff,
  }));
  const updated = [...kept, ...recorded].sort((left, right) =>
    getKey(left.id, left.mode, left.pair) < getKey(right.id, right.mode, right.pair) ? -1 : 1,
  );
  writeFileSync(KNOWN_DIFFERENCES_PATH, `${JSON.stringify(updated, null, 2)}\n`);
  console.log(`Wrote ${updated.length} known differences to ${KNOWN_DIFFERENCES_PATH}`);
} else if (unknown.length > 0) {
  console.log(`\n${unknown.length} differences known-differences.json doesn't list:`);
  for (const comparison of unknown) {
    console.log(`  ${comparison.pair} ${comparison.mode} ${comparison.id}`);
    for (const line of comparison.diff.slice(0, 10)) console.log(`    ${line}`);
  }
  process.exitCode = 1;
} else {
  console.log("\nEvery difference is one known-differences.json lists.");
}
console.log(`Wrote ${outPath}`);

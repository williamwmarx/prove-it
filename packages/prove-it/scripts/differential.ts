// Compares the full output of Java TLC, of Prove It with its engine, and of Prove It with the engine
// off, on each corpus model, in TLC's default output and with -tool. TLC's output comes from the
// recordings record-tlc.ts --stdout makes (tlc-recordings.ts); Prove It runs as its CLI with the
// same command line. Each output is the exit code, stdout and stderr, normalised by
// normalize-output.ts. Every difference must be the one tests/conformance/known-differences.json
// lists for that model, mode and pair of checkers, or the run fails.
//
// --stop-at also runs the engine stopped by PROVE_IT_STOP_AT before a state picked at random
// from those it found, and its output must not differ from the engine's. --backend picks the
// engine's backend, and --compare-backends runs every one: each is compared with TLC and the
// interpreter (tlc/rust, rust/interpreter), and each other with the first (ts/rust). --update rewrites
// known-differences.json from the run, keeping the reasons it gives.
// --native names the native prove-it binary (native/DESIGN.md 13), which then runs on each model
// too, with the front the first backend's run recorded, and is compared with TLC as tlc/native.
// That pair fails nothing yet: the run reports how many runs it matches and why the others differ.
// A run without a TLC recording fails the check, since nothing compared it with TLC. --timeout-ms
// stops a checker that runs longer, and without it nothing does.
// Usage: bun scripts/run.ts differential [--max-tlc-ms 20000] [--filter text] [--concurrency 3]
//        [--modes default,tool] [--stop-at] [--timeout-ms ms] [--update] [--out path]
//        [--backend ts | --compare-backends] [--native path]

import { spawn } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, join, resolve } from "node:path";

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
  stdout: string;
  stderr: string;
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
// Resolved here, since each checker runs from its model's directory.
const nativeOption = getOption("--native");
const nativeBinary = nativeOption && resolve(nativeOption);
// The native binary reads the IR the Rust engine reads, so the run on that backend records its
// front: the TypeScript engine skips models the Rust engine takes.
const frontBackend = backends.includes("rust") ? "rust" : backends[0];

// Runs a checker with TLC's command line for the model, from the model's directory.
const runChecker = (
  command: string,
  args: string[],
  model: CorpusModel,
  mode: OutputMode,
  environment: NodeJS.ProcessEnv,
) =>
  new Promise<Output>((resolve) => {
    const metadataDirectory = mkdtempSync(join(tmpdir(), "prove-it-differential-"));
    const child = spawn(
      command,
      [...args, LIBRARY_OPTION, "tlc2.TLC", ...getTlcArguments(model, mode, metadataDirectory)],
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
      const output = Buffer.concat(stdout).toString("utf8");
      const errorOutput = Buffer.concat(stderr).toString("utf8");
      resolve({
        transcript: getTranscript(
          signal === "SIGKILL" ? `killed after ${timeoutMilliseconds} ms` : String(exitCode),
          output,
          errorOutput,
        ),
        engineLine: getEngineLine(errorOutput),
        stdout: output,
        stderr: errorOutput,
      });
    });
  });

const runCli = (model: CorpusModel, mode: OutputMode, environment: NodeJS.ProcessEnv) =>
  runChecker(process.execPath, [CLI_PATH], model, mode, environment);

// What TLC prints between its banner and the first message of the search, which the front end
// computes: the native binary reads it, with the IR, as the front of the run until tla-front
// lands (native/DESIGN.md 13.5). A run whose engine never computed the initial states has none.
const getFront = (stdout: string) => {
  const isTool = stdout.startsWith("@!@!@STARTMSG");
  const banner = isTool ? "@!@!@ENDMSG 2187 @!@!@\n" : "\nRunning breadth-first search ";
  const bannerAt = stdout.indexOf(banner);
  const start = isTool
    ? bannerAt + banner.length
    : stdout.indexOf("\n", bannerAt + banner.length) + 1;
  // The front ends where TLC computes the initial states, or where it reports an assumption false.
  const ends = isTool
    ? ["@!@!@STARTMSG 2189:", "@!@!@STARTMSG 2104:"]
    : ["\nComputing initial states...\n", "\nError: Assumption "];
  const end = Math.min(
    ...ends.map((marker) => stdout.indexOf(marker)).filter((index) => index !== -1),
  );
  return bannerAt === -1 || end === Infinity
    ? undefined
    : stdout.slice(start, end + (isTool ? 0 : 1));
};

// Runs the native binary on a model, with the front the TypeScript CLI recorded for it.
const runNative = async (
  binary: string,
  model: CorpusModel,
  mode: OutputMode,
  recorded: Output,
  directory: string,
) => {
  const stem = basename(model.specPath, ".tla");
  const front = getFront(recorded.stdout);
  if (front !== undefined) writeFileSync(join(directory, `${stem}.front`), front);
  const native = await runChecker(binary, [], model, mode, {
    ...process.env,
    PROVE_IT_FRONT: directory,
  });
  rmSync(directory, { recursive: true, force: true });
  return native;
};

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
// The native binary's comparisons with TLC, which measure how much of TLC's output it prints and
// fail nothing yet: why it couldn't do a run, if it said.
const nativeComparisons: (Comparison & { reason: string | undefined })[] = [];
const missing: string[] = [];
// The runs --stop-at couldn't stop, since the engine handed over before the first state it could.
const unforced: string[] = [];
const results: unknown[] = [];

const getComparison = (
  id: string,
  mode: OutputMode,
  pair: string,
  left: string,
  right: string,
): Comparison => {
  const diff = getLineDiff(left.split("\n"), right.split("\n"));
  const known = knownByKey.get(getKey(id, mode, pair));
  return {
    id,
    mode,
    pair,
    diff,
    isKnown: diff.length === 0 || JSON.stringify(diff) === JSON.stringify(known?.diff),
  };
};

const compare = (id: string, mode: OutputMode, pair: string, left: string, right: string) => {
  const comparison = getComparison(id, mode, pair, left, right);
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
    const frontDirectory = nativeBinary && mkdtempSync(join(tmpdir(), "prove-it-front-"));
    for (const backend of backends) {
      const isFrontRecorded = frontDirectory && backend === frontBackend;
      const engine = await runCli(model, mode, {
        ...getBackendEnvironment(backend),
        PROVE_IT_ENGINE: "debug",
        ...(isFrontRecorded && {
          PROVE_IT_IR_DUMP: join(frontDirectory, `${basename(model.specPath, ".tla")}.ir`),
        }),
      });
      outputs[backend] = engine;
      const first = backends[0];
      if (backend !== first) {
        modelComparisons.push(
          compare(
            model.id,
            mode,
            `${first}/${backend}`,
            outputs[first].transcript,
            engine.transcript,
          ),
        );
      }
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
    if (nativeBinary && frontDirectory) {
      const native = await runNative(
        nativeBinary,
        model,
        mode,
        outputs[frontBackend],
        frontDirectory,
      );
      outputs.native = native;
      if (tlc) {
        const comparison = getComparison(model.id, mode, "tlc/native", tlc, native.transcript);
        nativeComparisons.push({
          ...comparison,
          // A run with no front never reached the engine in TypeScript: SANY, the configuration or
          // an assumption stopped it, which tla-front will report.
          reason: /^prove-it: not native yet: (.*)$/m
            .exec(native.stderr)?.[1]
            ?.replace(/^no recorded front of .*$/, "no recorded front"),
        });
      }
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
if (nativeBinary) {
  const same = nativeComparisons.filter((comparison) => comparison.diff.length === 0);
  console.log(
    `\nnative: ${same.length} of ${nativeComparisons.length} runs print what TLC prints.`,
  );
  const reasons = new Map<string, number>();
  for (const comparison of nativeComparisons) {
    if (comparison.diff.length === 0) continue;
    const reason = comparison.reason ?? (comparison.isKnown ? "known" : "differs");
    reasons.set(reason, (reasons.get(reason) ?? 0) + 1);
  }
  for (const [reason, count] of [...reasons].sort((left, right) => right[1] - left[1])) {
    console.log(`  ${String(count).padStart(5)}  ${reason}`);
  }
}
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

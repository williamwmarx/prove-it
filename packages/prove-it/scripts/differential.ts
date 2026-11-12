// Compares the full output of Java TLC, of Prove It with its engine, and of Prove It with the engine
// off, on each corpus model, in TLC's default output and with -tool. TLC's output comes from the
// recordings record-tlc.ts --stdout makes (tlc-recordings.ts); Prove It runs as its CLI with the
// same command line. Each output is the exit code, stdout and stderr, normalised by
// normalize-output.ts. Every difference must be the one tests/conformance/known-differences.json
// lists for that model, mode and pair of checkers, or the run fails.
//
// --stop-at also runs the engine stopped by PROVE_IT_STOP_AT before a state picked at random
// from those it found, and its output must not differ from the engine's. The engine, named rust in
// the pairs, is compared with TLC (tlc/rust), with the interpreter (rust/interpreter) and with
// itself stopped (rust/stopped). --update rewrites known-differences.json from the run, keeping
// the reasons it gives.
// --native names the native prove-it binary (native/DESIGN.md 13), which then runs on each model
// too, as it ships, with tla-front as its front end, and is compared with TLC as tlc/native. That
// pair fails nothing: the run reports how many runs it matches and why the others differ.
// --native-only runs the native binary alone, without the CLI's runs, so a pass over the
// whole corpus takes minutes, and fails if it prints something TLC doesn't that
// known-differences.json doesn't list for tlc/native; a run it declines as not native fails nothing.
// --modes te, with --native-only, compares it in TLC's own default, where TLC records the trace and
// writes the trace exploration files, which the transcripts hold, and runs each model with an ALIAS
// with -tool -dumpTrace tlc too, in the jar and the binary. TLC's binary trace file, the .bin,
// holds each string's token in the run that wrote it, which no other run reproduces, so the
// transcript holds what TLC's -loadTrace rebuilds from it, with the jar TLA2TOOLS_JAR names: TLC's
// file and the binary's are the same where TLC reads the same trace back from each. A truncated and
// a corrupted copy of each of the binary's must not read back to that trace, or the run fails.
// A run without a TLC recording fails the check, since nothing compared it with TLC. --timeout-ms
// stops a checker that runs longer, and without it nothing does.
// Usage: bun scripts/run.ts differential [--max-tlc-ms 20000] [--filter text] [--concurrency 3]
//        [--modes default,tool,te] [--stop-at] [--timeout-ms ms] [--update] [--out path]
//        [--native path [--native-only]]

import { spawn } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, delimiter, dirname, join, resolve } from "node:path";

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
  ENGINE_LABEL,
  getEngineEnvironment,
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
  RECORDED_MODES,
  runTakingTraceFiles,
} from "./tlc-recordings";

interface Output {
  // The exit code, stdout and stderr, normalised, as one text.
  transcript: string;
  // Whether a signal ended the process other than the timeout's, as when it overflows its stack.
  isAborted: boolean;
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
  (mode): mode is OutputMode => RECORDED_MODES.some((known) => known === mode),
);
const isStopping = process.argv.includes("--stop-at");
const isUpdate = process.argv.includes("--update");
const outPath = getOption("--out") ?? join(CONFORMANCE_DIRECTORY, ".differential.json");
// Resolved here, since each checker runs from its model's directory.
const nativeOption = getOption("--native");
const nativeBinary = nativeOption && resolve(nativeOption);
const isNativeOnly = process.argv.includes("--native-only");
if (isNativeOnly && !nativeBinary) throw new Error("--native-only needs --native");
if (modes.includes("te") && !isNativeOnly) throw new Error("--modes te needs --native-only");
const tlaToolsJar = process.env.TLA2TOOLS_JAR;
if (modes.includes("te") && (!tlaToolsJar || !existsSync(tlaToolsJar))) {
  throw new Error("--modes te needs TLA2TOOLS_JAR, the tla2tools.jar that reads each trace file");
}
// The runs whose damaged trace file TLC read back to the trace the whole file holds.
const undamaged: string[] = [];

// Runs a checker with TLC's command line for the model, from the model's directory.
const spawnChecker = (
  command: string,
  args: string[],
  model: CorpusModel,
  mode: OutputMode,
  environment: NodeJS.ProcessEnv,
) =>
  new Promise<{ status: string; isAborted: boolean; stdout: string; stderr: string }>((resolve) => {
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
      resolve({
        status: signal === "SIGKILL" ? `killed after ${timeoutMilliseconds} ms` : String(exitCode),
        isAborted: signal !== null && !child.killed,
        stdout: Buffer.concat(stdout).toString("utf8"),
        stderr: Buffer.concat(stderr).toString("utf8"),
      });
    });
  });

// Runs the jar's TLC from the directory, and returns its exit code, stdout and stderr, normalised.
const runJar = (directory: string, args: string[]) =>
  new Promise<string>((resolve) => {
    const child = spawn("java", ["-XX:+UseParallelGC", "-cp", tlaToolsJar ?? "", ...args], {
      cwd: directory,
      env: { ...process.env, JAVA_TOOL_OPTIONS: undefined },
    });
    const stdout: Buffer[] = [];
    const stderr: Buffer[] = [];
    child.stdout.on("data", (chunk: Buffer) => stdout.push(chunk));
    child.stderr.on("data", (chunk: Buffer) => stderr.push(chunk));
    child.on("close", (exitCode) =>
      resolve(
        getTranscript(
          String(exitCode),
          Buffer.concat(stdout).toString("utf8"),
          Buffer.concat(stderr).toString("utf8"),
        ),
      ),
    );
  });

// What TLC reads back from the trace file's bytes for the model, normalised: what its -loadTrace
// prints, the trace it rebuilds from the file and checks again, which compares only the spec's
// variables; then the fingerprint of the whole value the file holds (TLCExt's TLCFP), as TLC
// deserialises it, which a module of its own named _TLCTrace makes the trace module's reader
// reachable for, beside the spec, with its model values from its configuration, each through an
// instance of its own, so that a spec that defines PrintT, TLCFP or _TLCTraceDeserialize itself
// doesn't stand in for them. The value itself
// may be too large to print, as a SUBSET of 20 elements. A file TLC can't read prints why, twice.
const readTrace = async (model: CorpusModel, bytes: Buffer) => {
  const directory = mkdtempSync(join(tmpdir(), "prove-it-read-trace-"));
  const tracePath = join(directory, "trace.bin");
  writeFileSync(tracePath, bytes);
  const args = getTlcArguments(model, "default", join(directory, "states"));
  const configIndex = args.indexOf("-config");
  const loaded = await runJar(model.directory, [
    LIBRARY_OPTION,
    "tlc2.TLC",
    ...args.slice(0, configIndex),
    "-loadTrace",
    "tlc",
    tracePath,
    ...args.slice(configIndex),
  ]);
  writeFileSync(
    join(directory, "_TLCTrace.tla"),
    "---- MODULE _TLCTrace ----\n_TLCTraceDeserialize(file) == TRUE\n====\n",
  );
  writeFileSync(
    join(directory, "ProveItTraceValue.tla"),
    [
      "---- MODULE ProveItTraceValue ----",
      `EXTENDS ${basename(model.specPath, ".tla")}`,
      "ProveItTLC == INSTANCE TLC",
      "ProveItTLCExt == INSTANCE TLCExt",
      "ProveItTrace == INSTANCE _TLCTrace",
      `ASSUME ProveItTLC!PrintT(ProveItTLCExt!TLCFP(ProveItTrace!_TLCTraceDeserialize(${JSON.stringify(tracePath)}))) /\\ FALSE`,
      "====",
      "",
    ].join("\n"),
  );
  const value = await runJar(model.directory, [
    `${LIBRARY_OPTION}${delimiter}${dirname(model.specPath)}`,
    "tlc2.TLC",
    ...args.slice(0, -1),
    join(directory, "ProveItTraceValue.tla"),
  ]);
  rmSync(directory, { recursive: true, force: true });
  return `${loaded}\n--- the fingerprint of the value it holds\n${value}`;
};

// The -dumpTrace tlc file a checker writes for the model with -tool, which no recording holds:
// TLC words the message of an ALIAS that fails as -tool prints it, which the file holds.
const dumpWithTool = async (model: CorpusModel, command: string, args: string[]) => {
  const directory = mkdtempSync(join(tmpdir(), "prove-it-tool-dump-"));
  const dumpPath = join(directory, "trace.bin");
  const tlcArgs = getTlcArguments(model, "tool", join(directory, "states"));
  const configIndex = tlcArgs.indexOf("-config");
  await new Promise((resolve) =>
    spawn(
      command,
      [
        ...args,
        LIBRARY_OPTION,
        "tlc2.TLC",
        ...tlcArgs.slice(0, configIndex),
        "-dumpTrace",
        "tlc",
        dumpPath,
        ...tlcArgs.slice(configIndex),
      ],
      {
        cwd: model.directory,
        env: { ...process.env, JAVA_TOOL_OPTIONS: undefined },
        stdio: "ignore",
      },
    ).on("close", resolve),
  );
  const bytes = existsSync(dumpPath) ? readFileSync(dumpPath) : undefined;
  rmSync(directory, { recursive: true, force: true });
  return bytes;
};

// The models with an ALIAS whose -tool dump the binary writes and TLC reads back to something else,
// and those whose -tool dump the binary declines, which fail nothing but are reported.
const toolDumpDifferences: string[] = [];
const toolDumpDeclines: string[] = [];

// The -tool dumps of a model with an ALIAS, the jar's and the binary's, read back by TLC; the
// binary may decline, and writes no file then.
const compareToolDumps = async (model: CorpusModel) => {
  if (!/\bALIAS\b/.test(readFileSync(model.configPath, "utf8"))) return;
  const native = await dumpWithTool(model, nativeBinary ?? "", []);
  if (native === undefined) {
    toolDumpDeclines.push(model.id);
    return;
  }
  const tlc = await dumpWithTool(model, "java", ["-XX:+UseParallelGC", "-cp", tlaToolsJar ?? ""]);
  const isSame =
    tlc !== undefined && (await readTrace(model, tlc)) === (await readTrace(model, native));
  if (!isSame) toolDumpDifferences.push(model.id);
};

// The trace exploration files with each .bin, held in base64, as what TLC reads back from it. Where
// `isDamageChecked`, a truncated and a corrupted copy of each must read back to something else.
const readTraceFiles = async (
  model: CorpusModel,
  files: Record<string, string>,
  isDamageChecked: boolean,
) =>
  Object.fromEntries(
    await Promise.all(
      Object.entries(files).map(async ([name, text]) => {
        if (!name.endsWith(".bin")) return [name, text];
        const bytes = Buffer.from(text, "base64");
        const loaded = await readTrace(model, bytes);
        if (isDamageChecked) {
          const corrupted = Buffer.from(bytes);
          corrupted[Math.floor(corrupted.length / 2)] ^= 0x5a;
          for (const [damage, damaged] of [
            ["truncated", bytes.subarray(0, Math.floor(bytes.length / 2))],
            ["corrupted", corrupted],
          ] as const) {
            if ((await readTrace(model, damaged)) === loaded) {
              undamaged.push(`${model.id}: a ${damage} ${name}`);
            }
          }
        }
        return [name, `what TLC reads back from the file:\n${loaded}`];
      }),
    ),
  );

// A run in TLC's own default writes the trace exploration files, which its transcript holds.
const runChecker = async (
  command: string,
  args: string[],
  model: CorpusModel,
  mode: OutputMode,
  environment: NodeJS.ProcessEnv,
): Promise<Output> => {
  const run = () => spawnChecker(command, args, model, mode, environment);
  const checked =
    mode === "te"
      ? await runTakingTraceFiles(dirname(model.specPath), run)
      : { result: await run(), files: {} };
  const result = checked.result;
  const files = mode === "te" ? await readTraceFiles(model, checked.files, true) : checked.files;
  return {
    transcript: getTranscript(result.status, result.stdout, result.stderr, files),
    isAborted: result.isAborted,
    engineLine: getEngineLine(result.stderr),
    stdout: result.stdout,
    stderr: result.stderr,
  };
};

const runCli = (model: CorpusModel, mode: OutputMode, environment: NodeJS.ProcessEnv) =>
  runChecker(process.execPath, [CLI_PATH], model, mode, environment);

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
// The last line of a --native-only run: how many native runs differ unlisted and how many aborted.
const nativeSummary: { text?: string } = {};
const nativeComparisons: (Comparison & { reason: string | undefined; isAborted: boolean })[] = [];
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

// Compares the native binary's run with TLC's, why it couldn't do the run if it said.
const compareNative = (id: string, mode: OutputMode, tlc: string, native: Output) => {
  const comparison = getComparison(id, mode, "tlc/native", tlc, native.transcript);
  nativeComparisons.push({
    ...comparison,
    reason: /^prove-it: not native yet: (.*)$/m.exec(native.stderr)?.[1],
    isAborted: native.isAborted,
  });
};

const work = async (queue: { model: CorpusModel; mode: OutputMode }[], total: number) => {
  for (let run = queue.shift(); run; run = queue.shift()) {
    const model = run.model;
    const mode = run.mode;
    const recording = readRecording(model, mode);
    if (!recording) missing.push(`${model.id} ${mode}`);
    const tlc =
      recording &&
      getTranscript(
        String(recording.exitCode),
        recording.stdout,
        recording.stderr,
        mode === "te" && recording.files
          ? await readTraceFiles(model, recording.files, false)
          : recording.files,
      );
    if (nativeBinary && isNativeOnly) {
      const native = await runChecker(nativeBinary, [], model, mode, process.env);
      if (tlc) compareNative(model.id, mode, tlc, native);
      if (mode === "te") await compareToolDumps(model);
      results.push({ id: model.id, mode, tlc, outputs: { native } });
      const isSame = native.transcript === tlc;
      console.log(
        `[${results.length}/${total}] ${isSame ? "same" : "native"}  ${mode.padEnd(7)} ${model.id}`,
      );
      continue;
    }
    const interpreter = await runCli(model, mode, { ...process.env, PROVE_IT_ENGINE: "0" });
    const modelComparisons: Comparison[] = [];
    const outputs: Record<string, Output> = { interpreter };
    const engine = await runCli(model, mode, getEngineEnvironment());
    outputs[ENGINE_LABEL] = engine;
    if (tlc) {
      modelComparisons.push(compare(model.id, mode, `tlc/${ENGINE_LABEL}`, tlc, engine.transcript));
    }
    modelComparisons.push(
      compare(
        model.id,
        mode,
        `${ENGINE_LABEL}/interpreter`,
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
        ...getEngineEnvironment(),
        PROVE_IT_STOP_AT: String(stopAt),
      });
      isForced = stopped.engineLine?.endsWith(STOPPED_REASON) ?? false;
      if (isForced) {
        outputs[`${ENGINE_LABEL} stopped at ${stopAt}`] = stopped;
        modelComparisons.push(
          compare(model.id, mode, `${ENGINE_LABEL}/stopped`, engine.transcript, stopped.transcript),
        );
      } else stopAt = stopAt > 0 ? Math.floor(stopAt / 2) : undefined;
    }
    if (isStopping && isSearched && !isForced) unforced.push(`${ENGINE_LABEL} ${mode} ${model.id}`);
    if (nativeBinary) {
      const native = await runChecker(nativeBinary, [], model, mode, process.env);
      outputs.native = native;
      if (tlc) compareNative(model.id, mode, tlc, native);
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
    const reason = comparison.isAborted
      ? "aborted"
      : (comparison.reason ?? (comparison.isKnown ? "known" : "differs"));
    reasons.set(reason, (reasons.get(reason) ?? 0) + 1);
  }
  for (const [reason, count] of [...reasons].sort((left, right) => right[1] - left[1])) {
    console.log(`  ${String(count).padStart(5)}  ${reason}`);
  }
  // A run that aborted fails even where its model is a listed difference.
  const aborted = nativeComparisons.filter((comparison) => comparison.isAborted);
  const differing = nativeComparisons.filter(
    (comparison) => !comparison.isAborted && comparison.reason === undefined && !comparison.isKnown,
  );
  if (isNativeOnly) {
    for (const [failed, heading] of [
      [aborted, "native runs aborted"],
      [differing, "native runs print what TLC doesn't"],
    ] as const) {
      if (failed.length === 0) continue;
      console.log(`\n${failed.length} ${heading}:`);
      for (const comparison of failed) {
        console.log(`  ${comparison.mode} ${comparison.id}`);
        for (const line of comparison.diff.slice(0, 10)) console.log(`    ${line}`);
      }
    }
    if (toolDumpDifferences.length > 0) {
      console.log(
        `\n${toolDumpDifferences.length} -tool dumps of models with an ALIAS TLC reads back otherwise:`,
      );
      for (const id of toolDumpDifferences) console.log(`  ${id}`);
    }
    if (toolDumpDeclines.length > 0) {
      console.log(
        `\n${toolDumpDeclines.length} -tool dumps of models with an ALIAS the binary declines:`,
      );
      for (const id of toolDumpDeclines) console.log(`  ${id}`);
    }
    if (undamaged.length > 0) {
      console.log(`\n${undamaged.length} damaged trace files TLC read back to the same trace:`);
      for (const run of undamaged) console.log(`  ${run}`);
    }
    if (
      aborted.length > 0 ||
      differing.length > 0 ||
      undamaged.length > 0 ||
      toolDumpDifferences.length > 0
    ) {
      process.exitCode = 1;
    }
    nativeSummary.text = `${differing.length} native differences known-differences.json doesn't list, ${aborted.length} native runs aborted, ${undamaged.length} damaged trace files read back, and ${toolDumpDifferences.length} -tool dumps of an ALIAS read back otherwise.`;
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
} else if (nativeSummary.text !== undefined) {
  // --native-only compares no other pair, so its own tally ends the run.
  console.log(`\n${nativeSummary.text}`);
} else {
  console.log("\nEvery difference is one known-differences.json lists.");
}
console.log(`Wrote ${outPath}`);

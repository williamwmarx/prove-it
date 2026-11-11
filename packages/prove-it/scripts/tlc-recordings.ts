// TLC's full output on the corpus models, which record-tlc.ts --stdout records and differential.ts
// compares with Prove It's. Each recording is a file named by a hash of what TLC's output depends
// on: the commit TLC was built from, the output mode, the model, the files beside it, and the
// library modules, so a recording goes stale, and is recorded again, when any of them changes.

import { createHash } from "node:crypto";
import { existsSync, readdirSync, readFileSync, rmSync, statSync } from "node:fs";
import { join } from "node:path";

import {
  CONFORMANCE_DIRECTORY,
  type CorpusModel,
  getCorpora,
  LIBRARY_PATH,
  TLC_SEED,
} from "./corpora";

export interface TlcRecording {
  id: string;
  mode: OutputMode;
  tlcCommit: string;
  exitCode: number;
  stdout: string;
  stderr: string;
  // The trace exploration files the run wrote, by name: a .tla as its text, a .bin in base64.
  files?: Record<string, string>;
}

// "te" is TLC's own default, which records the trace for its trace exploration spec: at a
// counterexample TLC writes <Spec>_TTrace_<epoch>.bin, and for a trace of two states or more
// <Spec>_TTrace_<epoch>.tla, beside the spec. Only the native binary is compared in it.
export type OutputMode = "default" | "tool" | "te";

export const OUTPUT_MODES: OutputMode[] = ["default", "tool"];

export const RECORDED_MODES: OutputMode[] = [...OUTPUT_MODES, "te"];

// The tlaplus/tlaplus commit TLC is built from, as .depot/workflows/benchmark.yml pins it.
export const TLC_COMMIT = "d8fb231de4e4b5d02c1b2ed1ac759c086f694021";

export const TLC_STDOUT_DIRECTORY = join(CONFORMANCE_DIRECTORY, "tlc-stdout");

const TRACE_FILE = /_TTrace_\d+\.(tla|bin)$/;

const getTraceFileNames = (directory: string) =>
  readdirSync(directory).filter((name) => TRACE_FILE.test(name));

// TLC names the trace exploration files by the second its run started, so runs in one directory
// take turns, and each takes the files it wrote: those that weren't there when it started.
const directoryTurns = new Map<string, Promise<unknown>>();

export const runTakingTraceFiles = <T>(
  directory: string,
  run: () => Promise<T>,
): Promise<{ result: T; files: Record<string, string> }> => {
  const turn = (directoryTurns.get(directory) ?? Promise.resolve()).then(async () => {
    const existing = new Set(getTraceFileNames(directory));
    const result = await run();
    const files: Record<string, string> = {};
    for (const name of getTraceFileNames(directory).sort()) {
      if (existing.has(name)) continue;
      const path = join(directory, name);
      files[name] = name.endsWith(".bin")
        ? readFileSync(path).toString("base64")
        : readFileSync(path, "utf8");
      rmSync(path);
    }
    return { result, files };
  });
  directoryTurns.set(
    directory,
    turn.catch(() => undefined),
  );
  return turn;
};

// The command line after `java ... tlc2.TLC` that the recordings, and Prove It in the
// differential, run a model with.
export const getTlcArguments = (
  model: CorpusModel,
  mode: OutputMode,
  metadataDirectory: string,
) => [
  "-workers",
  "1",
  "-nowarning",
  "-seed",
  String(TLC_SEED),
  "-fp",
  "0",
  "-lncheck",
  "final",
  ...(mode === "te" ? [] : ["-noGenerateSpecTE"]),
  ...(mode === "tool" ? ["-tool"] : []),
  "-metadir",
  metadataDirectory,
  "-config",
  model.configPath,
  model.specPath,
];

export const LIBRARY_OPTION = `-DTLA-Library=${LIBRARY_PATH}`;

// The library modules come from the corpora tlapm and community, which their commits pin.
const LIBRARY_CORPORA = new Set(["tlapm", "community"]);

export const getRecordingPath = (model: CorpusModel, mode: OutputMode) => {
  const hash = createHash("sha256");
  hash.update(`${TLC_COMMIT}\n${mode}\n${model.id}\n`);
  for (const corpus of getCorpora()) {
    if (LIBRARY_CORPORA.has(corpus.name)) hash.update(`${corpus.name} ${corpus.commit}\n`);
  }
  for (const name of readdirSync(model.directory).sort()) {
    const path = join(model.directory, name);
    if (!statSync(path).isFile()) continue;
    hash.update(`${name}\n`);
    hash.update(readFileSync(path));
  }
  return join(TLC_STDOUT_DIRECTORY, `${hash.digest("hex").slice(0, 32)}.json`);
};

export const readRecording = (model: CorpusModel, mode: OutputMode): TlcRecording | undefined => {
  const path = getRecordingPath(model, mode);
  return existsSync(path) ? JSON.parse(readFileSync(path, "utf8")) : undefined;
};

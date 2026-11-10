// Compares what the TypeScript writes for each module of proofs.json with what obligations-dump
// (native/crates/prover/obligations) writes, one JSON line per module, for
// obligation-differential.ts. Modules are read where tlapm finds them, as proof-records.ts does:
// beside the module, then the corpora's library, then tlapm's standard library. Without --rust
// <dump>, it builds obligations-dump with cargo first.

import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { TlaProofError } from "../src/errors";
import { CORPORA_DIRECTORY, getLibraryModules, getOption } from "./corpora";
import type { ModuleProofRecord } from "./proof-records";

const NATIVE_DIRECTORY = join(import.meta.dirname, "../native");

export interface ErrorRecord {
  name: string;
  message: string;
  failure?: string;
  exception?: string;
}

export const describeError = (error: unknown): ErrorRecord => {
  if (error instanceof TlaProofError) {
    return {
      name: error.name,
      message: error.message,
      failure: error.failure,
      exception: error.exception,
    };
  }
  if (error instanceof Error) return { name: error.name, message: error.message };
  throw error;
};

const getRustBinary = () => {
  const given = getOption("--rust");
  if (given !== undefined) return given;
  const build = spawnSync(
    "cargo",
    [
      "build",
      "--release",
      "--locked",
      "--quiet",
      "-p",
      "prove-obligations",
      "--bin",
      "obligations-dump",
    ],
    { cwd: NATIVE_DIRECTORY, stdio: "inherit" },
  );
  if (build.status !== 0) process.exit(build.status ?? 1);
  return join(NATIVE_DIRECTORY, "target/release/obligations-dump");
};

// A module's record and the lines both sides write, for the caller to check further.
export interface ComparedModule {
  record: ModuleProofRecord;
  expected: string;
  actual: string;
}

export interface Comparison {
  records: ModuleProofRecord[];
  writeModule: (path: string) => string;
  // obligations-dump's flags.
  flags: string[];
  // Modules per run of the Rust side, so that its output stays small.
  batch: number;
  onModule?: (module: ComparedModule) => void;
}

// Writes each module with writeModule and with obligations-dump, prints where they differ, passes
// each module to onModule as it goes, keeping no line, and returns the records that differ.
export const compareModules = (comparison: Comparison) => {
  const rust = getRustBinary();
  // The library modules by name, and tlapm's own library, for the Rust side to read as readModule
  // does.
  const directory = mkdtempSync(join(tmpdir(), "obligations-dump-"));
  const libraryPath = join(directory, "library.json");
  writeFileSync(
    libraryPath,
    JSON.stringify({
      modules: Object.fromEntries(getLibraryModules()),
      standard: join(CORPORA_DIRECTORY, "tlapm/library"),
    }),
  );
  const runRust = (paths: string[]) => {
    const run = spawnSync(rust, ["--library", libraryPath, ...comparison.flags], {
      input: paths.join("\n"),
      maxBuffer: 2 ** 31 - 1,
      encoding: "utf8",
    });
    if (run.status !== 0) throw new Error(`obligations-dump failed: ${run.stderr}`);
    return run.stdout.split("\n");
  };
  const paths = comparison.records.map((record) => join(CORPORA_DIRECTORY, record.id));
  const rustLines: string[] = [];
  const differences = comparison.records.filter((record, index) => {
    if (index % comparison.batch === 0)
      rustLines.splice(0, Infinity, ...runRust(paths.slice(index, index + comparison.batch)));
    const actual = rustLines[index % comparison.batch] ?? "";
    // Frees the line once read.
    rustLines[index % comparison.batch] = "";
    const expected = comparison.writeModule(paths[index]);
    comparison.onModule?.({ record, expected, actual });
    if (expected === actual) return false;
    const start = Array.from(expected).findIndex(
      (_, position) => actual[position] !== expected[position],
    );
    console.log(`differs: ${record.id} at ${start}`);
    console.log(`  ts:   ${expected.slice(Math.max(0, start - 80), start + 120)}`);
    console.log(`  rust: ${actual.slice(Math.max(0, start - 80), start + 120)}`);
    return true;
  });
  rmSync(directory, { recursive: true, force: true });
  return differences;
};

// Compares the Rust obligations (native/crates/prover/obligations) with the TypeScript ones on every
// module of proofs.json, as text: each side writes one JSON line per module, with each obligation's
// id, location, kind, method and printed text, each module's summary, the warnings in order, and
// the error that stopped it, if any.
// Usage: bun scripts/obligation-differential.ts [--filter text] [--skip text] [--rust <dump>]
// Modules are read where tlapm finds them, as proof-records.ts does: beside the module, then the
// corpora's library, then tlapm's standard library. Without --rust, it builds obligations-dump with
// cargo first.

import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { TlaProofError } from "../src/errors";
import { formatSummary, getObligations } from "../src/obligations";
import type { Warn } from "../src/obligations/expression";
import { CORPORA_DIRECTORY, getLibraryModules, getOption } from "./corpora";
import { readModule, readProofRecords } from "./proof-records";

const NATIVE_DIRECTORY = join(import.meta.dirname, "../native");

// Modules per run of the Rust side, so its output stays small.
const BATCH = 50;

interface ErrorRecord {
  name: string;
  message: string;
  failure?: string;
  exception?: string;
}

const describeError = (error: unknown): ErrorRecord => {
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

const writeModule = (path: string) => {
  const warnings: [string, string][] = [];
  const onWarning: Warn = (warning) => warnings.push([warning.channel, warning.text]);
  const read = () => {
    try {
      return {
        results: getObligations(
          [{ file: path, source: readFileSync(path, "utf8") }],
          (name) => readModule(path, name),
          { onWarning },
        ),
      };
    } catch (error) {
      return { error: describeError(error) };
    }
  };
  const outcome = read();
  return JSON.stringify({
    results: (outcome.results ?? []).map((result) => ({
      name: result.name,
      summary: formatSummary(result),
      obligations: result.obligations.map((obligation) => ({
        id: obligation.id,
        location: obligation.location,
        kind:
          obligation.kind.kind === "Omitted"
            ? `Omitted ${obligation.kind.omission}`
            : obligation.kind.kind,
        method:
          obligation.method === undefined
            ? null
            : [
                obligation.method.name,
                obligation.method.tactic ?? null,
                obligation.method.timeout ?? null,
              ],
        text: obligation.text,
      })),
    })),
    warnings,
    error: outcome.error ?? null,
  });
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
const rust = getRustBinary();

// The library modules by name, and tlapm's own library, for the Rust side to read as readModule does.
const directory = mkdtempSync(join(tmpdir(), "obligation-differential-"));
const libraryPath = join(directory, "library.json");
writeFileSync(
  libraryPath,
  JSON.stringify({
    modules: Object.fromEntries(getLibraryModules()),
    standard: join(CORPORA_DIRECTORY, "tlapm/library"),
  }),
);

const runRust = (paths: string[]) => {
  const run = spawnSync(rust, ["--library", libraryPath], {
    input: paths.join("\n"),
    maxBuffer: 2 ** 31 - 1,
    encoding: "utf8",
  });
  if (run.status !== 0) throw new Error(`obligations-dump failed: ${run.stderr}`);
  return run.stdout.split("\n");
};

const records = readProofRecords();
const paths = records.map((record) => join(CORPORA_DIRECTORY, record.id));
const rustLines: string[] = [];
const differences = records.filter((record, index) => {
  if (index % BATCH === 0)
    rustLines.splice(0, Infinity, ...runRust(paths.slice(index, index + BATCH)));
  const actual = rustLines[index % BATCH];
  const expected = writeModule(paths[index]);
  if (expected === actual) return false;
  const start = Array.from(expected).findIndex(
    (_, position) => actual?.[position] !== expected[position],
  );
  console.log(`differs: ${record.id} at ${start}`);
  console.log(`  ts:   ${expected.slice(Math.max(0, start - 80), start + 120)}`);
  console.log(`  rust: ${actual?.slice(Math.max(0, start - 80), start + 120)}`);
  return true;
});
rmSync(directory, { recursive: true, force: true });
console.log(
  `obligations: ${records.length - differences.length} of ${records.length} modules match`,
);
process.exit(differences.length === 0 ? 0 : 1);

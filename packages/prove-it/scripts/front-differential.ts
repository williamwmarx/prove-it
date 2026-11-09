// Compares the Rust front end (native/crates/tla-front) with the TypeScript one on every module of
// the fetched corpora and the test fixtures, as text: each side writes one JSON line per module.
// Usage: bun scripts/front-differential.ts tokens [--fixtures] [--filter text] [--rust <front-dump>]
// --fixtures reads only the fixtures, so it runs without the corpora. Without --rust, it builds
// front-dump with cargo first.

import { spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { join, relative } from "node:path";

import { TlaSyntaxError } from "../src/errors";
import { tokenize } from "../src/lexer";
import { findModules, getOption, listFiles } from "./corpora";

const PACKAGE_DIRECTORY = join(import.meta.dirname, "..");
const NATIVE_DIRECTORY = join(PACKAGE_DIRECTORY, "native");

const describe = (error: unknown) => {
  if (!(error instanceof TlaSyntaxError)) throw error;
  return error.failure === undefined
    ? { error: error.message }
    : { error: error.message, failure: error.failure };
};

const MODES: Record<string, (source: string) => unknown> = {
  tokens: (source) => {
    try {
      return tokenize(source).map((token) => [
        token.kind,
        token.text,
        token.spelling ?? null,
        token.line,
        token.column,
        token.endColumn,
      ]);
    } catch (error) {
      return describe(error);
    }
  },
};

const mode = process.argv[2];
const write = MODES[mode];
if (write === undefined) {
  throw new Error(`front-differential takes a mode: ${Object.keys(MODES).join(", ")}`);
}
const filter = getOption("--filter");
const fixtures = listFiles(join(PACKAGE_DIRECTORY, "tests/fixtures"))
  .filter((path) => path.endsWith(".tla"))
  .sort()
  .map((path) => ({ id: relative(PACKAGE_DIRECTORY, path), path }));
const modules = [...fixtures, ...(process.argv.includes("--fixtures") ? [] : findModules())].filter(
  (module) => filter === undefined || module.id.includes(filter),
);

const getRustBinary = () => {
  const given = getOption("--rust");
  if (given !== undefined) return given;
  const build = spawnSync(
    "cargo",
    ["build", "--release", "--locked", "--quiet", "-p", "tla-front", "--bin", "front-dump"],
    { cwd: NATIVE_DIRECTORY, stdio: "inherit" },
  );
  if (build.status !== 0) process.exit(build.status ?? 1);
  return join(NATIVE_DIRECTORY, "target/release/front-dump");
};

const rust = spawnSync(getRustBinary(), [mode], {
  input: modules.map((module) => module.path).join("\n"),
  maxBuffer: 2 ** 31 - 1,
  encoding: "utf8",
});
if (rust.status !== 0) throw new Error(`front-dump failed: ${rust.stderr}`);
const rustLines = rust.stdout.split("\n");

const differences = modules.filter((module, index) => {
  const expected = JSON.stringify(write(readFileSync(module.path, "utf8")));
  const actual = rustLines[index];
  if (expected === actual) return false;
  const start = Array.from(expected).findIndex(
    (_, position) => actual?.[position] !== expected[position],
  );
  console.log(`differs: ${module.id} at ${start}`);
  console.log(`  ts:   ${expected.slice(Math.max(0, start - 80), start + 120)}`);
  console.log(`  rust: ${actual?.slice(Math.max(0, start - 80), start + 120)}`);
  return true;
});
console.log(`${mode}: ${modules.length - differences.length} of ${modules.length} modules match`);
if (differences.length > 0) process.exit(1);

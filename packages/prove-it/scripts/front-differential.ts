// Compares the Rust front end (native/crates/tla-front) with the TypeScript one on every module of
// the fetched corpora and the test fixtures, as text: each side writes one JSON line per module.
// Usage: bun scripts/front-differential.ts <mode> [--fixtures] [--filter text] [--mutate count]
//   [--rust <front-dump>]
// The modes are tokens, ast and sany-ast, and time, which compares how long each side takes to
// parse each module instead. --fixtures reads only the fixtures, so it runs without the corpora.
// --mutate adds four variants of each of the first count modules, with syntax inserted and text
// deleted at places a fixed seed picks, so the two sides' errors are compared too. Without --rust,
// it builds front-dump with cargo first.

import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, relative } from "node:path";

import { TlaSyntaxError } from "../src/errors";
import { tokenize } from "../src/lexer";
import { parseModule, parseSanyModule } from "../src/parser";
import { findModules, getOption, listFiles } from "./corpora";

const PACKAGE_DIRECTORY = join(import.meta.dirname, "..");
const NATIVE_DIRECTORY = join(PACKAGE_DIRECTORY, "native");
// Batches keep each side's output for a run of modules well under a string's largest size.
const BATCH = 50;
const TIMED_RUNS = 5;

const describe = (error: unknown) => {
  if (!(error instanceof TlaSyntaxError)) throw error;
  return { error: error.message, failure: error.failure, sany: error.sany };
};

// JSON with each object's keys in order, so the two sides needn't build objects alike.
const sortKeys = (_key: string, value: unknown) =>
  value === null || typeof value !== "object" || Array.isArray(value)
    ? value
    : Object.fromEntries(Object.entries(value).sort(([left], [right]) => (left < right ? -1 : 1)));

const writeResult = (read: (source: string) => unknown) => (source: string) => {
  try {
    return JSON.stringify(read(source), sortKeys);
  } catch (error) {
    return JSON.stringify(describe(error), sortKeys);
  }
};

const MODES: Record<string, (source: string) => string> = {
  tokens: writeResult((source) =>
    tokenize(source).map((token) => [
      token.kind,
      token.text,
      token.spelling ?? null,
      token.line,
      token.column,
      token.endColumn,
    ]),
  ),
  ast: writeResult(parseModule),
  "sany-ast": writeResult((source) => parseSanyModule(source)),
};

// What a mutation inserts: the syntax whose errors and corner cases the parser handles.
const SNIPPETS = [
  ...["/\\", "\\/", "LET", "IN", "==", "<1>", "<1>a.", "<2>", "BY", "PROOF", "OBVIOUS", "QED"],
  ...["(", ")", "[", "]", "{", "}", "<<", ">>", "!", "\\in", ":", "->", "|->", "EXCEPT", "@"],
  ...["'", "^+", "LAMBDA", "INSTANCE", "WITH", "<-", "ASSUME", "PROVE", "NEW", "CASE", "OTHER"],
  ...["[]", "~", "-", "SUBSET", "DOMAIN", "::", "x ::", "lab(a) ::", "!:", "!<<", "!1", "!@"],
  ...["\\X", "WF_v", "<<A>>_v", "[A]_v", "DEF", "HIDE", "USE", "ONLY", "TAKE", "PICK", "SUFFICES"],
  ...["RECURSIVE", "LOCAL", "THEOREM", "LEMMA", ",", "..", "\\cdot", "=>", "#", "%", "(+)", "-."],
  ...["\\A x :", "\\E x \\in S :", "CHOOSE x :", "IF", "THEN", "ELSE", "ENABLED", "UNCHANGED"],
  ...["<>", "~>", "----", "====", "---- MODULE Inner ----", '"', "\\*", "(*", "\n", "\n  ", "\t"],
];

// mulberry32, so every run makes the same variants.
const createRandom = (seed: number) => {
  const state = { value: seed };
  return (bound: number) => {
    state.value = (state.value + 0x6d2b79f5) | 0;
    const mixed = Math.imul(state.value ^ (state.value >>> 15), state.value | 1);
    const next = mixed ^ (mixed + Math.imul(mixed ^ (mixed >>> 7), mixed | 61));
    return Math.floor((((next ^ (next >>> 14)) >>> 0) / 2 ** 32) * bound);
  };
};

const mutate = (source: string, random: (bound: number) => number) =>
  Array.from({ length: 1 + random(3) }).reduce<string>((text) => {
    const index = random(text.length + 1);
    return random(10) < 4
      ? text.slice(0, index) + text.slice(index + 1 + random(30))
      : `${text.slice(0, index)} ${SNIPPETS[random(SNIPPETS.length)]} ${text.slice(index)}`;
  }, source);

const mode = process.argv[2];
if (mode !== "time" && MODES[mode] === undefined) {
  throw new Error(`front-differential takes a mode: ${[...Object.keys(MODES), "time"].join(", ")}`);
}
const filter = getOption("--filter");
const fixtures = listFiles(join(PACKAGE_DIRECTORY, "tests/fixtures"))
  .filter((path) => path.endsWith(".tla"))
  .sort()
  .map((path) => ({ id: relative(PACKAGE_DIRECTORY, path), path }));
const originals = [
  ...fixtures,
  ...(process.argv.includes("--fixtures") ? [] : findModules()),
].filter((module) => filter === undefined || module.id.includes(filter));
const mutationDirectory = mkdtempSync(join(tmpdir(), "front-differential-"));
const random = createRandom(7);
const mutations = originals
  .slice(0, Number(getOption("--mutate") ?? 0))
  .flatMap((module, index) => {
    const source = readFileSync(module.path, "utf8");
    return [0, 1, 2, 3].map((variant) => {
      const path = join(mutationDirectory, `${index}-${variant}.tla`);
      writeFileSync(path, mutate(source, random));
      return { id: `${module.id} (variant ${variant})`, path };
    });
  });
const modules = [...originals, ...mutations];

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
const rust = getRustBinary();

const runRust = (batch: typeof modules) => {
  const run = spawnSync(rust, [mode], {
    input: batch.map((module) => module.path).join("\n"),
    maxBuffer: 2 ** 31 - 1,
    encoding: "utf8",
  });
  if (run.status !== 0) throw new Error(`front-dump failed: ${run.stderr}`);
  return run.stdout.split("\n");
};

// The best of five parses of each module, tokens and AST, in milliseconds.
const time = () => {
  const rustTimes = runRust(modules).map(Number);
  const rows = modules.map((module, index) => {
    const source = readFileSync(module.path, "utf8");
    const best = Math.min(
      ...Array.from({ length: TIMED_RUNS }, () => {
        const start = performance.now();
        try {
          parseModule(source);
        } catch (error) {
          describe(error);
        }
        return performance.now() - start;
      }),
    );
    return { id: module.id, size: source.length, typescript: best, rust: rustTimes[index] };
  });
  const total = (key: "typescript" | "rust") => rows.reduce((sum, row) => sum + row[key], 0);
  rows
    .toSorted((left, right) => right.size - left.size)
    .slice(0, 10)
    .forEach((row) =>
      console.log(
        `${row.id} (${row.size} characters): TypeScript ${row.typescript.toFixed(2)} ms, Rust ${row.rust.toFixed(2)} ms`,
      ),
    );
  console.log(
    `all ${rows.length} modules: TypeScript ${total("typescript").toFixed(0)} ms, Rust ${total("rust").toFixed(0)} ms`,
  );
};

const compare = (write: (source: string) => string) => {
  const rustLines: string[] = [];
  const differences = modules.filter((module, index) => {
    if (index % BATCH === 0) {
      rustLines.splice(0, Infinity, ...runRust(modules.slice(index, index + BATCH)));
    }
    const expected = write(readFileSync(module.path, "utf8"));
    const actual = rustLines[index % BATCH];
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
  return differences.length === 0;
};

const isMatch = mode === "time" ? (time(), true) : compare(MODES[mode]);
rmSync(mutationDirectory, { recursive: true, force: true });
if (!isMatch) process.exit(1);

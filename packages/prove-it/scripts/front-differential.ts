// Compares the Rust front end (native/crates/tla-front) with the TypeScript one on every module of
// the fetched corpora and the test fixtures, as text: each side writes one JSON line per module.
// Usage: bun scripts/front-differential.ts <mode> [--fixtures] [--filter text] [--mutate count]
//   [--rust <front-dump>]
// The modes are tokens, ast, sany-ast, config (over the .cfg files), resolve, model, ir, and time, which
// compares how long each side takes to parse each module instead. resolve links each module as the
// root of a spec without a model, reading the modules it imports beside it and from the corpora's
// library, and compares the environment: each definition by key, with every name resolved, the
// builtins, the variables, and SANY's errors and warnings. A module the Rust front end doesn't
// link yet is counted, not compared. model does the same for each corpus model, a .cfg file and
// the spec beside it, with the model's constants and substitutions. ir lowers each module's
// environment to the engine IR, with every definition in it, and compares the bytes. --fixtures reads only the fixtures, so it runs without the corpora.
// --mutate adds four variants of each of the first count modules, with syntax inserted and text
// deleted at places a fixed seed picks, so the two sides' errors are compared too. Without --rust,
// it builds front-dump with cargo first.

import { spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, relative } from "node:path";

import type { Definition, Expression } from "../src/ast";
import { type ModelConfig, parseConfig } from "../src/config";
import { lowerToIr } from "../src/engine/ir";
import { createEnvironment } from "../src/environment";
import { TlaConfigError, TlaEvaluationError, TlaModuleError, TlaSyntaxError } from "../src/errors";
import type { Builtin } from "../src/evaluate";
import { tokenize } from "../src/lexer";
import { parseModule, parseSanyModule } from "../src/parser";
import { createTlcOrder } from "../src/tlc/order";
import { setStringOrder } from "../src/values";
import {
  CORPORA_DIRECTORY,
  getCorpora,
  getOption,
  LIBRARY_PATH,
  linkLibraryModules,
  listFiles,
} from "./corpora";

const PACKAGE_DIRECTORY = join(import.meta.dirname, "..");
const NATIVE_DIRECTORY = join(PACKAGE_DIRECTORY, "native");
// Batches keep each side's output for a run of modules well under a string's largest size.
const BATCH = 50;
const TIMED_RUNS = 5;

const describe = (error: unknown) => {
  if (
    error instanceof TlaConfigError ||
    error instanceof TlaEvaluationError ||
    error instanceof TlaModuleError
  ) {
    return { error: error.message };
  }
  if (!(error instanceof TlaSyntaxError)) throw error;
  return { error: error.message, failure: error.failure, sany: error.sany };
};

// JSON with each object's keys in order, so the two sides needn't build objects alike.
const sortKeys = (_key: string, value: unknown) =>
  value === null || typeof value !== "object" || Array.isArray(value)
    ? value
    : Object.fromEntries(Object.entries(value).sort(([left], [right]) => (left < right ? -1 : 1)));

const writeResult =
  (read: (source: string, path: string, spec: string) => unknown) =>
  (source: string, path = "", spec = "") => {
    try {
      return JSON.stringify(read(source, path, spec), sortKeys);
    } catch (error) {
      return JSON.stringify(describe(error), sortKeys);
    }
  };

const getBuiltinFlags = (builtin: Builtin) =>
  (builtin.isStateLevel ? 1 : 0) | (builtin.isLevelConstant ? 2 : 0) | (builtin.isLazy ? 4 : 0);

// The spec whose root module is the file, linked with the model's configuration, or without a
// model, and what linking prints.
const linkSpec = (source: string, path: string, config?: ModelConfig) => {
  const loadModule = (name: string) =>
    [dirname(path), LIBRARY_PATH]
      .map((directory) => join(directory, `${name}.tla`))
      .filter((file) => existsSync(file))
      .map((file) => readFileSync(file, "utf8"))[0];
  const printed: string[] = [];
  const specification = createEnvironment(config ?? parseConfig(""), {
    source,
    loadModule,
    order: createTlcOrder(source, loadModule),
    print: (text) => printed.push(text),
    files: { readFile: () => undefined, writeFile: () => {} },
    isUnconfigured: config === undefined,
    isSanyAccepted: true,
  });
  return { specification, printed };
};

// The environment of a spec, as canonical JSON.
const readEnvironment = (source: string, path: string, config?: ModelConfig) => {
  const linked = linkSpec(source, path, config);
  const specification = linked.specification;
  const printed = linked.printed;
  const environment = specification.environment;
  const keys = new Map<Definition, string>();
  return {
    definitions: [...environment.definitions].map(([key, definition]) => {
      const first = keys.get(definition);
      if (first === undefined) keys.set(definition, key);
      return [key, first === undefined ? definition : { same: first }];
    }),
    builtins: [...environment.builtins].map(([key, builtin]) => [
      key,
      builtin.name,
      builtin.arity,
      getBuiltinFlags(builtin),
    ]),
    substituted: [...environment.definitions]
      .filter((entry) => environment.substitutedDefinitions.has(entry[1]))
      .map((entry) => entry[0]),
    facts: { words: environment.facts.words, rows: [...environment.facts.rows] },
    assigned: [...environment.constants.keys()],
    substitutions: [...environment.substitutions],
    variables: environment.variables,
    variableIndex: [...environment.variableIndex],
    constants: specification.rootConstants.map((constant) => constant.name),
    printed,
  };
};

// The IR of a model whose Init and Next are a placeholder and whose configuration names each
// definition of the environment, by key, as an invariant, so it holds every definition. No text is
// ranked, so the texts follow their first use.
const lowerDefinitions = (source: string, path: string) => {
  const environment = linkSpec(source, path).specification.environment;
  const root: Expression = { kind: "Number", value: 0, location: { line: 0, column: 0 } };
  setStringOrder([]);
  const outcome = lowerToIr({
    config: { ...parseConfig(""), invariants: [...environment.definitions.keys()] },
    environment,
    spec: { init: root, next: root },
    traceActions: [],
    isWarningEnabled: true,
    tlcOrder: [],
    properties: { invariants: [], invariantNames: [], actionProperties: [], initialPredicates: [] },
    symmetry: undefined,
    isRecordingGraph: false,
    version: undefined,
    atoms: [],
    liveFormula: undefined,
    liveProperties: [],
  });
  return "ir" in outcome ? { ir: Buffer.from(outcome.ir).toString("hex") } : outcome;
};

const MODES: Record<string, (source: string, path: string, spec: string) => string> = {
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
  resolve: writeResult((source, path) => readEnvironment(source, path)),
  ir: writeResult(lowerDefinitions),
  model: writeResult((source, _path, spec) =>
    readEnvironment(readFileSync(spec, "utf8"), spec, parseConfig(source)),
  ),
  config: (source) =>
    `{"master":${writeResult((text) => parseConfig(text, "master"))(source)},"v174":${writeResult((text) => parseConfig(text, "1.7.4"))(source)}}`,
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
  ...["CONSTANTS", "INIT", "INVARIANT", "CHECK_DEADLOCK", "TYPE", "ALIAS", "<-[M]", "= [M]", "*)"],
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
const extension = mode === "config" || mode === "model" ? ".cfg" : ".tla";
// A model is a configuration and the spec of the same name beside it.
const getSpec = (path: string) => {
  const spec = path.replace(/\.cfg$/, ".tla");
  return mode === "model" && existsSync(spec) ? spec : undefined;
};
const findFiles = (root: string, paths: string[], prefix: string) =>
  paths
    .flatMap((path) => (existsSync(join(root, path)) ? listFiles(join(root, path)) : []))
    .filter((path) => path.endsWith(extension))
    .sort()
    .filter((path) => mode !== "model" || getSpec(path) !== undefined)
    .map((path) => ({ id: `${prefix}${relative(root, path)}`, path, spec: getSpec(path) }));
const corpora = process.argv.includes("--fixtures")
  ? []
  : getCorpora().flatMap((corpus) =>
      findFiles(join(CORPORA_DIRECTORY, corpus.name), corpus.paths, `${corpus.name}/`),
    );
const originals = [...findFiles(PACKAGE_DIRECTORY, ["tests/fixtures"], ""), ...corpora].filter(
  (module) => filter === undefined || module.id.includes(filter),
);
const mutationDirectory = mkdtempSync(join(tmpdir(), "front-differential-"));
const random = createRandom(7);
const mutations = originals
  .slice(0, Number(getOption("--mutate") ?? 0))
  .flatMap((module, index) => {
    const source = readFileSync(module.path, "utf8");
    return [0, 1, 2, 3].map((variant) => {
      const path = join(mutationDirectory, `${index}-${variant}.tla`);
      writeFileSync(path, mutate(source, random));
      return { id: `${module.id} (variant ${variant})`, path, spec: module.spec };
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

const isLinked = mode === "resolve" || mode === "model" || mode === "ir";
if (isLinked) linkLibraryModules();

const runRust = (batch: typeof modules) => {
  const run = spawnSync(rust, isLinked ? [mode, "--library", LIBRARY_PATH] : [mode], {
    input: batch
      .map((module) => (module.spec ? `${module.path}\t${module.spec}` : module.path))
      .join("\n"),
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

const compare = (write: (source: string, path: string, spec: string) => string) => {
  const rustLines: string[] = [];
  const unported = new Map<string, number>();
  const differences = modules.filter((module, index) => {
    if (index % BATCH === 0) {
      rustLines.splice(0, Infinity, ...runRust(modules.slice(index, index + BATCH)));
    }
    const actual = rustLines[index % BATCH];
    const notYet = actual?.startsWith('{"notYet":') ? JSON.parse(actual).notYet : undefined;
    if (notYet !== undefined) {
      unported.set(notYet, (unported.get(notYet) ?? 0) + 1);
      return false;
    }
    const expected = write(readFileSync(module.path, "utf8"), module.path, module.spec ?? "");
    if (expected === actual) return false;
    const start = Array.from(expected).findIndex(
      (_, position) => actual?.[position] !== expected[position],
    );
    console.log(`differs: ${module.id} at ${start}`);
    console.log(`  ts:   ${expected.slice(Math.max(0, start - 80), start + 120)}`);
    console.log(`  rust: ${actual?.slice(Math.max(0, start - 80), start + 120)}`);
    return true;
  });
  const unportedCount = [...unported.values()].reduce((sum, count) => sum + count, 0);
  unported.forEach((count, reason) => console.log(`not linked yet: ${count} with ${reason}`));
  console.log(
    `${mode}: ${modules.length - differences.length - unportedCount} of ${modules.length} modules match${unportedCount > 0 ? `, ${unportedCount} not compared yet` : ""}`,
  );
  return differences.length === 0;
};

const isMatch = mode === "time" ? (time(), true) : compare(MODES[mode]);
rmSync(mutationDirectory, { recursive: true, force: true });
if (!isMatch) process.exit(1);

// Compares the Rust front end (native/crates/tla-front) with the TypeScript one on every module of
// the fetched corpora and the test fixtures, as text: each side writes one JSON line per module.
// Usage: bun scripts/front-differential.ts <mode> [--fixtures] [--filter text] [--mutate count]
//   [--rust <front-dump>]
// The modes are tokens, ast, sany-ast, tlapm-ast (the parse in tlapm's mode, whose failures carry
// the reason and position tlapm prints), config (over the .cfg files), resolve, model, ir, order,
// model-ir, pcal, sany-parse-error, and time, which
// compares how long each side takes to parse each module instead. resolve links each module as the
// root of a spec without a model, reading the modules it imports beside it and from the corpora's
// library, and compares the environment: each definition by key, with every name resolved, the
// builtins, the variables, and SANY's errors and warnings. A module the Rust front end doesn't
// link yet is counted, not compared. model does the same for each corpus model, a .cfg file and
// the spec beside it, with the model's constants and substitutions. ir lowers each module's
// environment to the engine IR, with every definition in it, and compares the bytes. order compares
// TLC's string order of each model and the root module's orders of declarations and definitions.
// model-ir lowers each model's environment as ir does, with its constants' values and the texts
// ranked in TLC's string order. pcal validates each module with a PlusCal algorithm against the
// checksums of its translation, as SANY does under TLC master and 1.7.4, and compares the
// results, what the translator logs and the exception it throws. sany-parse-error compares
// SANY's report of a module its lexer or parser rejects, for TLC master and 1.7.4, and TLC
// 1.7.4's lexical error. --fixtures reads only the
// fixtures, so it runs without the corpora. --mutate adds four variants of each of the first count modules, with syntax inserted and text
// deleted at places a fixed seed picks, so the two sides' errors are compared too. Without --rust,
// it builds front-dump with cargo first.

import { spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, relative } from "node:path";

import type { Definition, Expression } from "../src/ast";
import { getIrStartup, lowerConstantSpec, lowerUnsearchedSpec } from "../src/check";
import { type ModelConfig, parseConfig } from "../src/config";
import { lowerToIr } from "../src/engine/ir";
import { createEnvironment } from "../src/environment";
import {
  isStackOverflow,
  PcalBugError,
  PcalRuntimeError,
  STACK_OVERFLOW_MESSAGE,
  TlaConfigError,
  TlaEvaluationError,
  TlaModuleError,
  TlaSyntaxError,
} from "../src/errors";
import { type Builtin, describeRange } from "../src/evaluate";
import { tokenize } from "../src/lexer";
import { getLevel } from "../src/liveness";
import { createLivenessChecker } from "../src/liveness-checker";
import { parseModule, parseSanyModule, parseTlapmModule } from "../src/parser";
import { createPcalParams } from "../src/pcal/ast";
import { createPcalSession } from "../src/pcal/parse";
import { validatePcalModule } from "../src/pcal/validate";
import { getSany174LexicalError } from "../src/sany/lexer";
import { getSanyParseError } from "../src/sany/parse-error";
import { getSanyReport } from "../src/sany/report";
import { createSearch, getProperties, getSpecification } from "../src/search";
import { getNextSubstitution } from "../src/spec-description";
import { withUnexpectedException } from "../src/tlc/messages";
import { createTlcOrder } from "../src/tlc/order";
import type { TlcVersion } from "../src/tlc/version";
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
  // TLC overflows its stack where the TypeScript front end does.
  if (isStackOverflow(error)) return { error: STACK_OVERFLOW_MESSAGE };
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
  (builtin.isStateLevel ? 1 : 0) |
  (builtin.isLevelConstant ? 2 : 0) |
  (builtin.isLazy ? 4 : 0) |
  (builtin.isNaturalsGeq ? 16 : 0) |
  (builtin.isNaturalsMethod ? 32 : 0);

// The spec whose root module is the file, linked with the model's configuration, or without a
// model, and what linking prints.
const createLoader = (path: string) => (name: string) =>
  [dirname(path), LIBRARY_PATH]
    .map((directory) => join(directory, `${name}.tla`))
    .filter((file) => existsSync(file))
    .map((file) => readFileSync(file, "utf8"))[0];

// What SANY prints, with each file described by its module's name and origin, as front-dump
// describes it, and with the modules TLC adds to the root module's EXTENDS.
const writeSanyText = (path: string, rootExtendees: string[] | undefined) => {
  const report = getSanyReport(path, createLoader(path), {
    describeFile: (name, origin) =>
      `${name}|${{ file: "File", "root file": "RootFile", standard: "Standard" }[origin]}`,
    rootExtendees,
  });
  return JSON.stringify({ text: report.text, isFailed: report.isFailed });
};

// TLC's orders of a model: its string order, the root module's variables and constants, and the
// root module's definitions in the order TLC computes them.
const readOrders = (source: string, _path: string, spec: string) => {
  const config = parseConfig(source);
  const order = createTlcOrder(readFileSync(spec, "utf8"), createLoader(spec));
  return {
    strings: order.getStringOrder(config),
    variables: order.getDeclarationOrder("variable"),
    constants: order.getDeclarationOrder("constant"),
    definitions: order.createDefinitionOrder()(undefined),
  };
};

const linkSpec = (source: string, path: string, config?: ModelConfig, isSanyAccepted = true) => {
  const loadModule = createLoader(path);
  const printed: string[] = [];
  const specification = createEnvironment(config ?? parseConfig(""), {
    source,
    loadModule,
    order: createTlcOrder(source, loadModule),
    print: (text) => printed.push(text),
    files: { readFile: () => undefined, writeFile: () => {} },
    isUnconfigured: config === undefined,
    isSanyAccepted,
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
    assumptions: specification.assumptions
      .filter((assumption) => !assumption.isAxiom)
      .map((assumption) => describeRange(assumption.expression)),
    levels: [...environment.definitions]
      .filter(
        (entry) =>
          keys.get(entry[1]) === entry[0] &&
          entry[1].kind === "Operator" &&
          entry[1].params.length === 0,
      )
      .map((entry) => [entry[0], getLevel(entry[1].body, undefined, environment)]),
    startup: config
      ? specification.startupDefinitions.map((definition) => keys.get(definition))
      : [],
  };
};

// The IR of a model whose Init and Next are a placeholder and whose configuration names each
// definition of the environment, by key, as an invariant, so it holds every definition. No text is
// ranked, so the texts follow their first use.
const lowerDefinitions = (source: string, path: string) => {
  setStringOrder([]);
  return lowerEnvironment(undefined, linkSpec(source, path).specification);
};

// The IR of a model's environment, with the texts ranked in TLC's string order as check.ts ranks
// them before it links the spec.
const lowerModel = (source: string, _path: string, spec: string) => {
  const config = parseConfig(source);
  const specSource = readFileSync(spec, "utf8");
  const loadModule = createLoader(spec);
  const order = createTlcOrder(specSource, loadModule);
  setStringOrder(order.getStringOrder(config));
  const specification = createEnvironment(config, {
    source: specSource,
    loadModule,
    order,
    print: () => {},
    files: { readFile: () => undefined, writeFile: () => {} },
    isSanyAccepted: true,
  });
  return lowerEnvironment(config, specification);
};

// A model as check.ts lowers it, without TLC's actions, which the engine splits.
const lowerFullModel = (source: string, _path: string, spec: string) => {
  const config = parseConfig(source);
  const specSource = readFileSync(spec, "utf8");
  const loadModule = createLoader(spec);
  const order = createTlcOrder(specSource, loadModule);
  setStringOrder(order.getStringOrder(config));
  const linked = createEnvironment(config, {
    source: specSource,
    loadModule,
    // TLC loads the class named after a module from the spec's directory, as the CLI does.
    loadClass: (name) => {
      const classPath = join(dirname(spec), `${name}.class`);
      return existsSync(classPath) ? readFileSync(classPath) : undefined;
    },
    order,
    print: () => {},
    files: { readFile: () => undefined, writeFile: () => {} },
    isSanyAccepted: true,
  });
  // createSearch checks the configuration, as check.ts does first, so its error comes first, and
  // gives no search for a spec without variables, whose IR check.ts lowers with FALSE for Init and
  // Next. Its checks evaluate the invariants, which ranks the strings TLC computes at startup,
  // which this mode leaves out, so it runs after the model is lowered.
  const lowered = (() => {
    try {
      return { outcome: lowerLinkedModel(config, linked, order) };
    } catch (error) {
      return { error };
    }
  })();
  createSearch(config, linked.environment, () => [], undefined);
  if ("error" in lowered) throw lowered.error;
  return lowered.outcome;
};

const lowerLinkedModel = (
  config: ModelConfig,
  linked: ReturnType<typeof createEnvironment>,
  order: ReturnType<typeof createTlcOrder>,
) => {
  const environment = linked.environment;
  const specification = getSpecification(config, environment);
  const search = getProperties(config, environment, () => {});
  if (environment.variables.length === 0) {
    const constant = lowerConstantSpec(config, linked, undefined);
    return "ir" in constant ? { ir: Buffer.from(constant.ir).toString("hex") } : constant;
  }
  if (!specification.init) return { reason: "no Init" };
  const variableOrder = order.getDeclarationOrder("variable");
  const getPosition = (index: number) => {
    const position = variableOrder.indexOf(environment.variables[index]);
    return position === -1 ? environment.variables.length : position;
  };
  const tlcOrder = environment.variables
    .map((_, index) => index)
    .sort((left, right) => getPosition(left) - getPosition(right));
  if (!specification.next) {
    const unsearched = lowerUnsearchedSpec(
      config,
      linked,
      { init: specification.init, next: undefined, scope: specification.scope },
      tlcOrder,
      search,
      undefined,
    );
    return "ir" in unsearched ? { ir: Buffer.from(unsearched.ir).toString("hex") } : unsearched;
  }
  // The checker's formula and atoms, which need no graph before it checks. check.ts builds it
  // inside withUnexpectedException, as TLC reports a RuntimeException it raises.
  const liveness = withUnexpectedException(() =>
    createLivenessChecker(search.liveness, specification.temporals, environment, {
      getFingerprint: () => 0,
      getSuccessors: () => [],
    }),
  );
  const outcome = lowerToIr({
    config,
    environment,
    spec: { init: specification.init!, next: specification.next!, scope: specification.scope },
    traceActions: [],
    isWarningEnabled: true,
    tlcOrder,
    properties: search,
    isRecordingGraph: liveness !== undefined,
    version: undefined,
    // Without TLC's actions, which ENABLED's split into.
    atoms: (liveness?.atoms ?? []).map((atom) => ({ atom, actions: undefined })),
    liveFormula: liveness?.formula,
    liveProperties: liveness?.properties ?? [],
    startup: getIrStartup(config, linked),
    nextSubstitution: getNextSubstitution(config, environment, linked.instanceActions),
    instanceActions: linked.instanceActions,
    getSpecification: undefined,
  });
  return "ir" in outcome ? { ir: Buffer.from(outcome.ir).toString("hex") } : outcome;
};

const lowerEnvironment = (
  config: ModelConfig | undefined,
  specification: ReturnType<typeof createEnvironment>,
) => {
  const environment = specification.environment;
  const root: Expression = { kind: "Number", value: 0, location: { line: 0, column: 0 } };
  const outcome = lowerToIr({
    config: { ...parseConfig(""), invariants: [...environment.definitions.keys()] },
    environment,
    spec: { init: root, next: root },
    traceActions: [],
    isWarningEnabled: true,
    tlcOrder: [],
    properties: { invariants: [], actionProperties: [], initialPredicates: [] },
    isRecordingGraph: false,
    version: undefined,
    atoms: [],
    liveFormula: undefined,
    liveProperties: [],
    startup: {
      substitutes: [],
      definitions: [],
      // Without a configuration, TLC computes no definition at startup.
      normalized: config ? getIrStartup(config, specification).normalized : new Set(),
      predicates: [],
      symmetry: undefined,
      assumptions: [],
    },
    nextSubstitution: undefined,
    instanceActions: specification.instanceActions,
    getSpecification: undefined,
  });
  return "ir" in outcome ? { ir: Buffer.from(outcome.ir).toString("hex") } : outcome;
};

// SANY's validation of the module's PlusCal algorithm in a session of its own: the results, what
// it logs, and the message of the Java exception it throws.
const readPcal = (source: string, version: TlcVersion) => {
  const log: string[] = [];
  const session = createPcalSession(createPcalParams(), (line) => log.push(line));
  try {
    const results = validatePcalModule(session, source.split(/\r\n|\r|\n/), version);
    return { results: [...results].sort(), log };
  } catch (error) {
    if (!(error instanceof PcalRuntimeError || error instanceof PcalBugError)) throw error;
    return { fatal: error.message, log };
  }
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
  "tlapm-ast": writeResult(parseTlapmModule),
  resolve: writeResult((source, path) => readEnvironment(source, path)),
  // Whether linking with SANY's level checks passes, or its error.
  levels: writeResult((source, path) => {
    linkSpec(source, path, undefined, false);
    return { isLevelChecked: true };
  }),
  ir: writeResult(lowerDefinitions),
  "model-ir": writeResult(lowerModel),
  "model-full": writeResult(lowerFullModel),
  order: writeResult(readOrders),
  spec: writeResult((source, _path, spec) => {
    const config = parseConfig(source);
    const environment = linkSpec(readFileSync(spec, "utf8"), spec, config).specification
      .environment;
    const specification = getSpecification(config, environment);
    const describe = (expression: Expression) => [
      expression.kind === "Identifier" ? expression.name : null,
      describeRange(expression),
    ];
    const names: string[] = [];
    for (let scope = specification.scope; scope; scope = scope.parent) names.push(scope.name);
    const init = specification.init;
    return {
      init: init ? (init.kind === "And" ? init.operands : [init]).map(describe) : null,
      next: specification.next ? describe(specification.next) : null,
      scope: names,
      temporals: specification.temporals.map((temporal) => describeRange(temporal.expression)),
    };
  }),
  properties: writeResult((source, _path, spec) => {
    const config = parseConfig(source);
    const environment = linkSpec(readFileSync(spec, "utf8"), spec, config).specification
      .environment;
    const stateLevel: string[] = [];
    const properties = getProperties(config, environment, (progress) => {
      if (progress.kind === "state-level-property") stateLevel.push(progress.name);
    });
    const describe = (property: { name: string; expression: Expression; scope: unknown }) => [
      property.name,
      describeRange(property.expression),
      property.scope !== undefined,
    ];
    return {
      invariants: properties.invariants.map(describe),
      actionProperties: properties.actionProperties.map((property) => [
        property.name,
        describeRange(property.action),
        describeRange(property.subscript),
        property.scope !== undefined,
      ]),
      initialPredicates: properties.initialPredicates.map(describe),
      liveness: properties.liveness.map(describe),
      stateLevel,
    };
  }),
  "sany-text": (_source, path) => writeSanyText(path, undefined),
  // SANY's report where TLC records the trace for its trace exploration spec, TLC's default.
  "sany-text-trace": (_source, path) => writeSanyText(path, ["_TLCTrace"]),
  model: writeResult((source, _path, spec) =>
    readEnvironment(readFileSync(spec, "utf8"), spec, parseConfig(source)),
  ),
  "sany-parse-error": (source) =>
    JSON.stringify({
      master: getSanyParseError(source, "master") ?? null,
      v174: getSanyParseError(source, "1.7.4") ?? null,
      lexical174: getSany174LexicalError(source) ?? null,
    }),
  pcal: (source) =>
    JSON.stringify(
      { master: readPcal(source, "master"), v174: readPcal(source, "1.7.4") },
      sortKeys,
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
const isModel = ["model", "order", "model-ir", "model-full", "spec", "properties"].includes(mode);
const extension = mode === "config" || isModel ? ".cfg" : ".tla";
// A model is a configuration and the spec of the same name beside it.
const getSpec = (path: string) => {
  const spec = path.replace(/\.cfg$/, ".tla");
  return isModel && existsSync(spec) ? spec : undefined;
};
const findFiles = (root: string, paths: string[], prefix: string) =>
  paths
    .flatMap((path) => (existsSync(join(root, path)) ? listFiles(join(root, path)) : []))
    .filter((path) => path.endsWith(extension))
    .sort()
    .filter((path) => !isModel || getSpec(path) !== undefined)
    .map((path) => ({ id: `${prefix}${relative(root, path)}`, path, spec: getSpec(path) }));
const corpora = process.argv.includes("--fixtures")
  ? []
  : getCorpora().flatMap((corpus) =>
      findFiles(join(CORPORA_DIRECTORY, corpus.name), corpus.paths, `${corpus.name}/`),
    );
// pcal compares only the modules with a PlusCal algorithm, so --mutate varies them.
const originals = [...findFiles(PACKAGE_DIRECTORY, ["tests/fixtures"], ""), ...corpora]
  .filter((module) => filter === undefined || module.id.includes(filter))
  .filter(
    (module) => mode !== "pcal" || /--algorithm|--fair/.test(readFileSync(module.path, "utf8")),
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

const isLinked = [
  "resolve",
  "model",
  "ir",
  "order",
  "model-ir",
  "model-full",
  "spec",
  "properties",
  "sany-text",
  "sany-text-trace",
  "levels",
].includes(mode);
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
  // A text TLC's strings hold but UTF-8 can't, which the TypeScript IR declines and Rust can't make.
  const surrogates: string[] = [];
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
    if (expected === '{"reason":"a text with a lone surrogate"}') {
      surrogates.push(module.id);
      return false;
    }
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
  surrogates.forEach((id) =>
    console.log(`no TypeScript IR: ${id} has a text with a lone surrogate`),
  );
  const uncompared = unportedCount + surrogates.length;
  console.log(
    `${mode}: ${modules.length - differences.length - uncompared} of ${modules.length} modules match${uncompared > 0 ? `, ${uncompared} not compared yet` : ""}`,
  );
  return differences.length === 0;
};

const isMatch = mode === "time" ? (time(), true) : compare(MODES[mode]);
rmSync(mutationDirectory, { recursive: true, force: true });
if (!isMatch) process.exit(1);

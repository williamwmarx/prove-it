// The expression differential of native M4 (native/DESIGN.md 11): every invariant, property,
// constraint, action constraint, initial predicate and VIEW of a model, compiled by the TypeScript
// engine's compiler and by native/crates/tla-engine, and evaluated on the first states of the
// TypeScript engine's state log, decoded into each store. Both must compile each root, or refuse
// it for the same reason, and give each state the same value, by its TLC fingerprint, or stop for
// the same reason. A root the native compiler declines, as it declines the builtins the
// TypeScript engine bridges to the interpreter, is counted, not compared.
//
// Each model an engine-coverage run found the TypeScript engine searching runs again on one
// thread with PROVE_IT_IR_DUMP and PROVE_IT_STATE_LOG. Then this script with --evaluate and
// `native/tools/replay expressions` each write a line per root, then a line per state and root, and
// the lines are compared as they stream. The files of one model are deleted before the next.
// PROVE_IT_MEMO=off and PROVE_IT_EPOCH_CHECK=1 reach the native side as they are set.
//
// --record writes the fixtures of tests/conformance/expressions, which cargo test compares the
// native side with: in each directory, a spec whose states.cfg makes states.jsonl and whose
// roots.cfg names the expressions, the IR of roots.cfg as model.ir, and the TypeScript side's
// lines as expected.txt.
// Usage: bun scripts/run.ts native-expressions --coverage <engine-coverage --out> [--states 1000]
//        [--filter text] [--concurrency 2] [--out path]
//        bun scripts/run.ts native-expressions --record

import { type ChildProcess, spawn, spawnSync } from "node:child_process";
import {
  closeSync,
  existsSync,
  mkdtempSync,
  openSync,
  readdirSync,
  readFileSync,
  readSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { createInterface } from "node:readline";

import type { Expression } from "../src/ast";
import { parseConfig } from "../src/config";
import {
  type Compiled,
  DISTINCT_SLOT,
  LEVEL_SLOT,
  LOC,
  NEXT_LEVEL_SLOT,
  nextEpoch,
  resetCompileState,
  ROOT_CONTEXT,
  setCurrent,
  setNext,
} from "../src/engine/compile";
import { createEngineCompiler, toEngineProperties } from "../src/engine/context";
import { fromValue } from "../src/engine/convert";
import { getStateFingerprints, resetFingerprints } from "../src/engine/fingerprint";
import { Bailout, int, resetStore } from "../src/engine/store";
import { createEnvironment } from "../src/environment";
import { evaluateStartupDefinitions, getDefinition } from "../src/evaluate";
import { createSearch } from "../src/search";
import { createTlcOrder } from "../src/tlc/order";
import { createStateDecoder } from "../src/transfer";
import { setStringOrder } from "../src/values";
import { CONFORMANCE_DIRECTORY, findModels, getLibraryModules, getOption } from "./corpora";

const LOCATION = { line: 0, column: 0 };

// The first lines of a file, read only as far as they go.
const readFirstLines = (path: string, count: number) => {
  const descriptor = openSync(path, "r");
  const buffer = Buffer.alloc(1 << 20);
  const chunks: Buffer[] = [];
  let newlines = 0;
  for (
    let read = readSync(descriptor, buffer);
    read > 0 && newlines < count;
    read = readSync(descriptor, buffer)
  ) {
    const chunk = Buffer.from(buffer.subarray(0, read));
    for (const byte of chunk) if (byte === 10) newlines++;
    chunks.push(chunk);
  }
  closeSync(descriptor);
  return Buffer.concat(chunks).toString("utf8").split("\n").slice(0, count);
};

// Why an evaluation stopped. TLA+ recursion deep enough to overflow the TypeScript stack is where
// the native engine stops at its limit, before it overflows its own.
const describeError = (error: unknown) => {
  if (error instanceof Bailout) return `bail ${error.message}`;
  if (error instanceof RangeError && error.message === "Maximum call stack size exceeded")
    return "bail recursion too deep";
  throw error;
};

// The TypeScript side: the lines native/tools/replay writes, from the TypeScript compiler.
const evaluate = (specPath: string, configPath: string, logPath: string, limit: number) => {
  const directory = dirname(specPath);
  const libraryModules = getLibraryModules();
  const loadModule = (name: string) => {
    const modulePath = join(directory, `${name}.tla`);
    const libraryPath = libraryModules.get(name);
    return existsSync(modulePath)
      ? readFileSync(modulePath, "utf8")
      : libraryPath && readFileSync(libraryPath, "utf8");
  };
  const source = readFileSync(specPath, "utf8");
  const config = parseConfig(readFileSync(configPath, "utf8"));
  const order = createTlcOrder(source, loadModule);
  setStringOrder(order.getStringOrder(config));
  const specification = createEnvironment(config, {
    source,
    loadModule,
    order,
    print: () => {},
    files: {
      readFile: (path) => {
        const filePath = join(directory, path);
        return existsSync(filePath) ? readFileSync(filePath, "utf8") : undefined;
      },
      writeFile: undefined,
    },
    isWarningEnabled: false,
    version: undefined,
  });
  const environment = specification.environment;
  // TLC computes the constant definitions when it starts, and the engine reads the values of those
  // with effects in their place, as check() does.
  evaluateStartupDefinitions(specification.startupDefinitions, environment);
  const search = createSearch(config, environment, () => order.getDeclarationOrder("variable"));
  const properties = search && toEngineProperties(search.properties);
  if (!search || !properties) throw new Error("the model has no engine properties");
  resetStore();
  resetCompileState();
  resetFingerprints();
  const compiler = createEngineCompiler(environment);
  const named = (
    kind: string,
    name: string,
    isAction = false,
  ): [string, boolean, () => Compiled] => [
    `${kind} ${name}`,
    isAction,
    () => {
      if (!getDefinition(name, environment)) throw new Bailout(`the ${kind} ${name} isn't defined`);
      return compiler.compile({ kind: "Identifier", name, location: LOCATION }, ROOT_CONTEXT);
    },
  ];
  const expression = (label: string, isAction: boolean, root: Expression) =>
    [label, isAction, () => compiler.compile(root, ROOT_CONTEXT)] as [
      string,
      boolean,
      () => Compiled,
    ];
  const roots = [
    ...config.invariants.map((name) => named("invariant", name)),
    ...properties.invariants.map((root, index) => expression(`property ${index}`, false, root)),
    ...config.constraints.map((name) => named("constraint", name)),
    ...config.actionConstraints.map((name) => named("action constraint", name, true)),
    ...properties.actionProperties.flatMap((property, index) => [
      expression(`action property ${index}`, true, property.action),
      expression(`action property ${index} subscript`, true, {
        kind: "Unchanged",
        expression: property.subscript,
        location: property.subscript.location,
      }),
    ]),
    ...properties.initialPredicates.map((root, index) =>
      expression(`initial predicate ${index}`, false, root),
    ),
    ...(config.view === undefined ? [] : [named("view", config.view)]),
  ];
  const lines: string[] = [];
  const flush = () => {
    if (lines.length > 0) process.stdout.write(`${lines.join("\n")}\n`);
    lines.length = 0;
  };
  const compiled = roots.map(([label, isAction, compile], index) => {
    try {
      const value = compile();
      lines.push(`root ${index} ${label}: ok`);
      return { isAction, value };
    } catch (error) {
      lines.push(`root ${index} ${label}: ${describeError(error)}`);
      return undefined;
    }
  });
  const width = environment.variables.length;
  const decode = createStateDecoder(width);
  const unassigned = new Int32Array(width).fill(-1);
  const states: Int32Array[] = [];
  const levels: number[] = [];
  const setLevels = (level: number, count: number) => {
    LOC[LEVEL_SLOT] = int(level);
    LOC[NEXT_LEVEL_SLOT] = int(level + 1);
    LOC[DISTINCT_SLOT] = int(count + 1);
  };
  const logLines = readFirstLines(logPath, limit + 1).slice(1);
  for (const [count, line] of logLines.entries()) {
    if (line === "") break;
    const [, parent, , , words, strings] = JSON.parse(line) as [
      number,
      number,
      number,
      string,
      number[],
      string[],
    ];
    const state = Int32Array.from(
      decode({ words: Int32Array.from(words), strings, count: 1 })[0].map(fromValue),
    );
    const level = parent < 0 ? 1 : levels[parent] + 1;
    states.push(state);
    levels.push(level);
    for (const [root, entry] of compiled.entries()) {
      if (!entry) continue;
      if (entry.isAction) {
        if (parent < 0) {
          lines.push(`${count} ${root} -`);
          continue;
        }
        setCurrent(states[parent], nextEpoch());
        setNext(state);
        setLevels(levels[parent], count);
      } else {
        setCurrent(state, nextEpoch());
        setNext(unassigned);
        setLevels(level, count);
      }
      try {
        const id = entry.value.evaluate();
        const fingerprint = getStateFingerprints(Int32Array.of(id), 1, 1, [0])[0];
        lines.push(
          `${count} ${root} fp ${BigInt.asUintN(64, fingerprint).toString(16).padStart(16, "0")}`,
        );
      } catch (error) {
        lines.push(`${count} ${root} ${describeError(error)}`);
      }
    }
    if (lines.length > 4096) flush();
  }
  flush();
};

interface Comparison {
  id: string;
  engineLine: string | undefined;
  roots: number;
  compared: number;
  declined: string[];
  evaluations: number;
  difference: string | undefined;
}

const PACKAGE_DIRECTORY = join(import.meta.dirname, "..");
const NATIVE_DIRECTORY = join(PACKAGE_DIRECTORY, "native");
const REPLAY = join(NATIVE_DIRECTORY, "target/release/replay");

const runProcess = (command: string, args: string[], environment?: NodeJS.ProcessEnv) =>
  new Promise<{ stderr: string; code: number | null }>((resolve) => {
    const child = spawn(command, args, { stdio: ["ignore", "ignore", "pipe"], env: environment });
    const stderr: Buffer[] = [];
    child.stderr.on("data", (chunk: Buffer) => stderr.push(chunk));
    child.on("close", (code) => resolve({ stderr: Buffer.concat(stderr).toString("utf8"), code }));
  });

// The lines a child writes, one at a time, and whether and how it ended.
const readChild = (child: ChildProcess) => {
  const iterator = createInterface({ input: child.stdout! })[Symbol.asyncIterator]();
  const stderr: Buffer[] = [];
  child.stderr!.on("data", (chunk: Buffer) => stderr.push(chunk));
  const ended = new Promise<number | null>((resolve) => child.on("close", resolve));
  return {
    next: async () => {
      const result = await iterator.next();
      return result.done ? undefined : (result.value as string);
    },
    ended,
    stderr: () => Buffer.concat(stderr).toString("utf8").trim(),
  };
};

const checkModel = (specPath: string, configPath: string, environment: NodeJS.ProcessEnv) =>
  runProcess(
    process.execPath,
    [
      "--stack-size=8000",
      "--max-old-space-size=6144",
      join(import.meta.dirname, "check-model.js"),
      specPath,
      configPath,
    ],
    { ...process.env, PROVE_IT_ENGINE: "debug", PROVE_IT_WORKERS: "1", ...environment },
  );

const compareModel = async (
  model: { id: string; specPath: string; configPath: string },
  states: number,
): Promise<Comparison> => {
  const directory = mkdtempSync(join(tmpdir(), "native-expressions-"));
  const irPath = join(directory, "model.ir");
  const logPath = join(directory, "states.jsonl");
  const comparison: Comparison = {
    id: model.id,
    engineLine: undefined,
    roots: 0,
    compared: 0,
    declined: [],
    evaluations: 0,
    difference: undefined,
  };
  try {
    const run = await checkModel(model.specPath, model.configPath, {
      PROVE_IT_IR_DUMP: irPath,
      PROVE_IT_STATE_LOG: logPath,
    });
    comparison.engineLine = run.stderr
      .split("\n")
      .find((line) => /^\[engine\] (checked|handed over|found)/.test(line))
      ?.slice("[engine] ".length);
    // The engine never reached the model, or declined it before its IR.
    if (!existsSync(irPath)) return comparison;
    // A search that stopped before it wrote a log still has roots to compile.
    if (!existsSync(logPath)) writeFileSync(logPath, "{}\n");
    const typescript = readChild(
      spawn(
        process.execPath,
        [
          "--stack-size=8000",
          "--max-old-space-size=6144",
          process.argv[1],
          "--evaluate",
          model.specPath,
          model.configPath,
          logPath,
          String(states),
        ],
        { stdio: ["ignore", "pipe", "pipe"], env: { ...process.env, PROVE_IT_ENGINE: "1" } },
      ),
    );
    const native = readChild(
      spawn(REPLAY, ["expressions", irPath, logPath, String(states)], {
        stdio: ["ignore", "pipe", "pipe"],
      }),
    );
    const declined = new Set<string>();
    for (;;) {
      const expected = await typescript.next();
      if (expected === undefined) {
        const extra = await native.next();
        if (extra !== undefined) comparison.difference = `native has more: ${extra}`;
        break;
      }
      const root = /^root (\d+) (.*?): (.*)$/.exec(expected);
      if (!root && declined.has(expected.split(" ")[1])) continue;
      const actual = await native.next();
      if (actual === undefined) {
        comparison.difference = `native ended before: ${expected}`;
        break;
      }
      if (root) {
        comparison.roots++;
        const nativeRoot = /^root (\d+) (.*?): (.*)$/.exec(actual);
        if (nativeRoot?.[3].startsWith("declined ")) {
          declined.add(root[1]);
          comparison.declined.push(`${root[2]}: ${nativeRoot[3].slice("declined ".length)}`);
          continue;
        }
        if (actual !== expected) {
          comparison.difference = `TypeScript ${expected}, native ${actual}`;
          break;
        }
        if (root[3] === "ok") comparison.compared++;
        continue;
      }
      comparison.evaluations++;
      if (actual !== expected) {
        comparison.difference = `TypeScript ${expected}, native ${actual}`;
        break;
      }
    }
    const [typescriptCode, nativeCode] = await Promise.all([typescript.ended, native.ended]);
    if (comparison.difference === undefined && typescriptCode !== 0)
      comparison.difference = `the TypeScript side failed: ${typescript.stderr()}`;
    if (comparison.difference === undefined && nativeCode !== 0)
      comparison.difference = `the native side failed: ${native.stderr()}`;
    return comparison;
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
};

const recordFixtures = async () => {
  const fixtures = join(CONFORMANCE_DIRECTORY, "expressions");
  for (const name of readdirSync(fixtures).sort()) {
    const directory = join(fixtures, name);
    const specPath = join(directory, `${name}.tla`);
    const logPath = join(directory, "states.jsonl");
    const irPath = join(directory, "model.ir");
    await checkModel(specPath, join(directory, "states.cfg"), { PROVE_IT_STATE_LOG: logPath });
    await checkModel(specPath, join(directory, "roots.cfg"), { PROVE_IT_IR_DUMP: irPath });
    const evaluated = spawnSync(
      process.execPath,
      [
        "--stack-size=8000",
        process.argv[1],
        "--evaluate",
        specPath,
        join(directory, "roots.cfg"),
        logPath,
        "1000",
      ],
      { encoding: "utf8", env: { ...process.env, PROVE_IT_ENGINE: "1" } },
    );
    if (evaluated.status !== 0 || !existsSync(irPath)) {
      console.error(`${name}: ${evaluated.stderr}`);
      process.exit(1);
    }
    writeFileSync(join(directory, "expected.txt"), evaluated.stdout);
    const lines = evaluated.stdout.split("\n").filter((line) => line !== "");
    console.log(
      `${name}: ${lines.filter((line) => line.startsWith("root ")).length} roots, ${lines.filter((line) => !line.startsWith("root ")).length} values`,
    );
  }
};

if (process.argv[2] === "--evaluate") {
  const [specPath, configPath, logPath, limit] = process.argv.slice(3);
  evaluate(specPath, configPath, logPath, Number(limit));
} else if (process.argv.includes("--record")) {
  await recordFixtures();
} else {
  const coveragePath = getOption("--coverage");
  const filter = getOption("--filter");
  const states = Number(getOption("--states") ?? 1000);
  const concurrency = Number(getOption("--concurrency") ?? 2);
  const outPath = getOption("--out");
  if (coveragePath === undefined) {
    console.error("Pass --coverage, the results engine-coverage --out wrote");
    process.exit(2);
  }
  const build = spawnSync("cargo", ["build", "--release", "--locked", "-p", "replay"], {
    cwd: NATIVE_DIRECTORY,
    stdio: "inherit",
  });
  if (build.status !== 0) process.exit(build.status ?? 1);
  const coverage: { id: string; engine: string }[] = JSON.parse(readFileSync(coveragePath, "utf8"));
  const searched = new Set(
    coverage
      .filter((entry) => entry.engine === "completed" || entry.engine === "handed over")
      .map((entry) => entry.id),
  );
  const models = findModels().filter(
    (model) => searched.has(model.id) && (filter === undefined || model.id.includes(filter)),
  );
  const results: Comparison[] = [];
  const queue = [...models];
  await Promise.all(
    Array.from({ length: concurrency }, async () => {
      for (let model = queue.shift(); model; model = queue.shift()) {
        const result = await compareModel(model, states);
        results.push(result);
        console.log(
          `${result.difference === undefined ? "same" : "DIFFERS"}  ${model.id}  ${result.compared}/${result.roots} roots compared, ${result.declined.length} declined, ${result.evaluations} evaluations${result.difference === undefined ? "" : `: ${result.difference}`}`,
        );
      }
    }),
  );
  results.sort((left, right) => left.id.localeCompare(right.id));
  if (outPath) writeFileSync(outPath, `${JSON.stringify(results, null, 2)}\n`);
  const differing = results.filter((result) => result.difference !== undefined);
  const sum = (count: (result: Comparison) => number) =>
    results.reduce((total, result) => total + count(result), 0);
  const reasons = new Map<string, number>();
  for (const result of results) {
    for (const reason of result.declined) {
      const why = reason.slice(reason.indexOf(": ") + 2);
      reasons.set(why, (reasons.get(why) ?? 0) + 1);
    }
  }
  console.log(
    `\n${results.length} models: ${results.length - differing.length} the same, ${differing.length} not; ` +
      `${sum((result) => result.compared)} of ${sum((result) => result.roots)} roots compared, ` +
      `${sum((result) => result.declined.length)} declined; ${sum((result) => result.evaluations)} evaluations`,
  );
  for (const [reason, count] of [...reasons].sort((left, right) => right[1] - left[1]))
    console.log(`  declined ${count}: ${reason}`);
  if (differing.length > 0) process.exitCode = 1;
}

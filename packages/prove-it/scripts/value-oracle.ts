// The value oracle (native/DESIGN.md 6.8): seeded batches of generated values and operations on
// them, answered by TLC's own Value classes (native/oracle/ValueOracle.java), the TypeScript store
// (src/engine/store.ts, src/engine/fingerprint.ts), the interpreter's fingerprints
// (src/tlc/fingerprint.ts), and the native store (src/engine/native-store.ts). The operations are
// building a value, compare, equals, membership and fingerprint.
//
// The native store must answer as the TypeScript store does, with the same ids and the same
// reasons to stop. Against TLC, a store may stop where TLC doesn't (the engine then hands the step
// to the interpreter, which costs time but not parity), but where TLC fails the store must stop,
// and where both answer, the answers must agree. A batch interns its spec's strings and model
// names first, in a random order, as TLC interns a spec's, and then the strings a spec would build,
// which TLC ranks by when it builds them and the stores by their text, so it builds them in the
// order of their text.
// Usage: TLA2TOOLS_JAR=... PROVE_IT_ENGINE_ADDON=... bun scripts/run.ts value-oracle
//        [--operations 100000] [--seed 1]

import { spawnSync } from "node:child_process";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { getStateFingerprints, resetFingerprints } from "../src/engine/fingerprint";
import { nativeStore } from "../src/engine/native-store";
import {
  Bailout,
  compare,
  equals,
  FALSE,
  functionOf,
  int,
  isMember,
  model,
  resetStore,
  setOf,
  str,
  TRUE,
  tupleOf,
} from "../src/engine/store";
import { getTlcFingerprint } from "../src/tlc/fingerprint";
import {
  createEnumeratedSet,
  createFunction,
  createModelValue,
  createRecord,
  createTuple,
  setStringOrder,
  type Value,
} from "../src/values";
import { getOption } from "./corpora";

type Tree =
  | { kind: "bool"; value: boolean }
  | { kind: "int"; value: number }
  | { kind: "string" | "model"; text: string }
  | { kind: "set" | "tuple"; elements: Tree[] }
  | { kind: "record"; fields: [string, Tree][] }
  | { kind: "function"; pairs: [Tree, Tree][] };

// An answer: a number, a boolean or a fingerprint as text, or why it failed.
interface Answer {
  value?: string;
  failure?: string;
}

const operationCount = Number(getOption("--operations") ?? 100000);
const seed = Number(getOption("--seed") ?? 1);
const jar = process.env.TLA2TOOLS_JAR;
if (!jar || !process.env.PROVE_IT_ENGINE_ADDON) {
  console.error("Set TLA2TOOLS_JAR to tla2tools.jar and PROVE_IT_ENGINE_ADDON to the addon");
  process.exit(2);
}

const classes = mkdtempSync(join(tmpdir(), "value-oracle-"));
const compiled = spawnSync(
  "javac",
  ["-cp", jar, "-d", classes, join(import.meta.dirname, "../native/oracle/ValueOracle.java")],
  { stdio: "inherit" },
);
if (compiled.status !== 0) process.exit(compiled.status ?? 1);

const random = { state: seed >>> 0 || 1 };
const next = (bound: number) => {
  random.state ^= random.state << 13;
  random.state ^= random.state >>> 17;
  random.state ^= random.state << 5;
  random.state >>>= 0;
  return random.state % bound;
};
const pick = <Item>(items: readonly Item[]) => items[next(items.length)];

// The traps of 6.8: ranked and unranked strings, wide characters, typed and untyped model values,
// the ends of the integers, records against functions over strings, tuples against functions over
// 1..n, the empty function, and sets of sets.
const RANKED = ["a", "b", "c", "type", "msg"];
const UNRANKED = ["zz", "abc", "é", "xā", "ā", "αβ", "ÿ"];
const MODELS = ["m1", "m2", "p", "A_x", "A_y", "B_z"];
const INTS = [0, 1, 2, 3, -1, -7, 255, 256, 4096, 4097, -2147483648, 2147483647];

const generate = (depth: number): Tree => {
  const choice = next(depth === 0 ? 5 : 11);
  if (choice === 0) return { kind: "bool", value: next(2) === 1 };
  if (choice === 1) return { kind: "int", value: next(3) === 0 ? pick(INTS) : next(6) };
  if (choice === 2) return { kind: "string", text: pick([...RANKED, ...UNRANKED]) };
  if (choice === 3) return { kind: "model", text: pick(MODELS) };
  if (choice === 4) return { kind: "int", value: next(4) };
  const length = next(4);
  if (choice <= 6) {
    // Mostly one kind of element, as a spec's sets are.
    const kind = next(3);
    const elements = Array.from({ length }, () =>
      kind === 0 ? { kind: "int" as const, value: next(5) } : generate(kind === 1 ? 0 : depth - 1),
    );
    return { kind: "set", elements };
  }
  if (choice === 7) {
    return { kind: "tuple", elements: Array.from({ length }, () => generate(depth - 1)) };
  }
  const names = RANKED.slice(0, 1 + next(3));
  if (choice === 8) {
    return { kind: "record", fields: names.map((name) => [name, generate(depth - 1)]) };
  }
  // Keys from 1, which make a tuple of a function, or from 0, which don't.
  const low = next(2);
  const keys: Tree[] =
    choice === 9
      ? names.map((text) => ({ kind: "string", text }))
      : Array.from({ length: 1 + next(3) }, (_, index) => ({ kind: "int", value: low + index }));
  return { kind: "function", pairs: keys.map((key) => [key, generate(depth - 1)]) };
};

const encodeText = (text: string) =>
  Array.from(text, (_, index) => text.charCodeAt(index).toString(16).padStart(4, "0"))
    .join("")
    .slice(0, text.length * 4);

const toTokens = (tree: Tree): string[] => {
  switch (tree.kind) {
    case "bool":
      return [tree.value ? "T" : "F"];
    case "int":
      return [`i${tree.value}`];
    case "string":
      return [`s${encodeText(tree.text)}`];
    case "model":
      return [`m${encodeText(tree.text)}`];
    case "set":
      return [`S${tree.elements.length}`, ...tree.elements.flatMap(toTokens)];
    case "tuple":
      return [`U${tree.elements.length}`, ...tree.elements.flatMap(toTokens)];
    case "record":
      return [
        `R${tree.fields.length}`,
        ...tree.fields.flatMap(([name, field]) => [`s${encodeText(name)}`, ...toTokens(field)]),
      ];
    case "function":
      return [
        `f${tree.pairs.length}`,
        ...tree.pairs.flatMap(([key, value]) => [...toTokens(key), ...toTokens(value)]),
      ];
  }
};

const toValue = (tree: Tree): Value => {
  switch (tree.kind) {
    case "bool":
    case "int":
      return tree.value;
    case "string":
      return tree.text;
    case "model":
      return createModelValue(tree.text);
    case "set":
      // As the interpreter builds a set enumeration, which TLC sorts only when it must.
      return createEnumeratedSet(tree.elements.map(toValue));
    case "tuple":
      return createTuple(tree.elements.map(toValue));
    case "record":
      return createRecord(tree.fields.map(([name, field]) => [name, toValue(field)]));
    case "function":
      return createFunction(tree.pairs.map(([key, value]) => [toValue(key), toValue(value)]));
  }
};

interface StoreFunctions {
  int: (value: number) => number;
  str: (text: string) => number;
  model: (name: string) => number;
  setOf: (elements: number[]) => number;
  tupleOf: (elements: ArrayLike<number>, length: number) => number;
  functionOf: (keys: number[], values: number[]) => number;
  compare: (left: number, right: number) => number;
  equals: (left: number, right: number) => boolean;
  isMember: (element: number, set: number) => boolean;
}

// A tree built as convert.ts's fromValue builds a value: its parts first, a function's keys
// before its values.
const build = (store: StoreFunctions, tree: Tree): number => {
  switch (tree.kind) {
    case "bool":
      return tree.value ? TRUE : FALSE;
    case "int":
      return store.int(tree.value);
    case "string":
      return store.str(tree.text);
    case "model":
      return store.model(tree.text);
    case "set":
      return store.setOf(tree.elements.map((element) => build(store, element)));
    case "tuple": {
      const elements = tree.elements.map((element) => build(store, element));
      return store.tupleOf(elements, elements.length);
    }
    case "record": {
      const keys = tree.fields.map(([name]) => store.str(name));
      return store.functionOf(
        keys,
        tree.fields.map(([, field]) => build(store, field)),
      );
    }
    case "function": {
      const keys = tree.pairs.map(([key]) => build(store, key));
      return store.functionOf(
        keys,
        tree.pairs.map(([, value]) => build(store, value)),
      );
    }
  }
};

const answer = (operation: () => unknown): Answer => {
  try {
    const result = operation();
    return { value: typeof result === "number" ? String(Math.sign(result)) : String(result) };
  } catch (error) {
    if (error instanceof Bailout) return { failure: error.message };
    return { failure: error instanceof Error ? `${error.name}: ${error.message}` : String(error) };
  }
};

const localStore: StoreFunctions = {
  int,
  str,
  model,
  setOf,
  tupleOf,
  functionOf,
  compare,
  equals,
  isMember,
};

const tally = {
  operations: 0,
  // Whether the native store answered exactly as the TypeScript store, ids and reasons included.
  nativeDiffers: 0,
  // The stores against TLC.
  agree: 0,
  bothFail: 0,
  storeStopsAlone: 0,
  storeMissesFailure: 0,
  answersDiffer: 0,
  interpreterDiffers: 0,
};
const examples: string[] = [];
// The operations of each outcome, by name.
const breakdown: Record<string, number> = {};
const report = (kind: keyof typeof tally, text: string) => {
  tally[kind]++;
  const name = `${kind} on ${text.split(" ")[0]}`;
  breakdown[name] = (breakdown[name] ?? 0) + 1;
  if (examples.length < 20) examples.push(`${kind}: ${text}`);
};

const fingerprintOf = (
  fingerprint: (states: Int32Array, count: number, width: number, order: number[]) => BigInt64Array,
  id: number,
) => String(fingerprint(Int32Array.of(id), 1, 1, [0])[0]);

const runBatch = (operations: number) => {
  const shuffled = [...RANKED, ...MODELS].sort(() => next(3) - 1);
  setStringOrder(shuffled);
  resetStore();
  resetFingerprints();
  nativeStore.resetStore();
  nativeStore.resetFingerprints();
  const trees: Tree[] = [];
  const localIds: (number | undefined)[] = [];
  const nativeIds: (number | undefined)[] = [];
  const requests = [
    `strings ${[...shuffled, ...[...UNRANKED].sort()].map((text) => `s${encodeText(text)}`).join(" ")}`,
  ];
  // Each request with the stores' answers, to compare with TLC's once it has answered them all.
  const asked: { text: string; local: Answer; native: Answer; interpreter?: Answer }[] = [];
  const ask = (text: string, local: Answer, native: Answer, interpreter?: Answer) => {
    requests.push(text);
    asked.push({ text, local, native, interpreter });
  };
  const values = Math.max(2, Math.floor(operations / 8));
  for (let index = 0; index < values; index++) {
    const tree = generate(3);
    trees.push(tree);
    const local = answer(() => build(localStore, tree));
    const native = answer(() => build(nativeStore, tree));
    // The ids themselves, which the native store must hand out as the TypeScript store does.
    const localId = local.failure === undefined ? build(localStore, tree) : undefined;
    const nativeId = native.failure === undefined ? build(nativeStore, tree) : undefined;
    localIds.push(localId);
    nativeIds.push(nativeId);
    ask(
      `value ${toTokens(tree).join(" ")}`,
      localId === undefined ? local : { value: String(localId) },
      nativeId === undefined ? native : { value: String(nativeId) },
    );
  }
  while (asked.length < operations) {
    const left = next(values);
    const right = next(values);
    const kind = next(4);
    const leftId = localIds[left];
    const rightId = localIds[right];
    const nativeLeft = nativeIds[left];
    const nativeRight = nativeIds[right];
    // A value a store couldn't build is no operand, but its build was an operation.
    if (leftId === undefined || rightId === undefined) continue;
    if (nativeLeft === undefined || nativeRight === undefined) continue;
    if (kind === 0) {
      ask(
        `compare ${left} ${right}`,
        answer(() => compare(leftId, rightId)),
        answer(() => nativeStore.compare(nativeLeft, nativeRight)),
      );
    } else if (kind === 1) {
      ask(
        `equals ${left} ${right}`,
        answer(() => equals(leftId, rightId)),
        answer(() => nativeStore.equals(nativeLeft, nativeRight)),
      );
    } else if (kind === 2 && trees[right].kind === "set") {
      ask(
        `member ${left} ${right}`,
        answer(() => isMember(leftId, rightId)),
        answer(() => nativeStore.isMember(nativeLeft, nativeRight)),
      );
    } else {
      ask(
        `fingerprint ${left}`,
        { value: fingerprintOf(getStateFingerprints, leftId) },
        { value: fingerprintOf(nativeStore.getStateFingerprints, nativeLeft) },
        answer(() => String(BigInt.asIntN(64, getTlcFingerprint([toValue(trees[left])])))),
      );
    }
  }
  const oracle = spawnSync("java", ["-cp", `${jar}:${classes}`, "ValueOracle"], {
    input: `${requests.join("\n")}\n`,
    encoding: "utf8",
    maxBuffer: 1 << 30,
  });
  const lines = oracle.stdout.split("\n");
  const tokens = lines[0].split(" ").slice(1).map(Number);
  if (tokens.some((token, index) => token !== index + 1)) {
    throw new Error(`TLC interned the strings as ${lines[0]}, not from 1 in order`);
  }
  // A request with the values it names, as TLC's tokens.
  const describe = (text: string) =>
    text.startsWith("value ")
      ? text
      : `${text} on ${text
          .split(" ")
          .slice(1)
          .map((index) => toTokens(trees[Number(index)]).join(" "))
          .join(" and ")}`;
  asked.forEach((request, index) => {
    const line = lines[index + 1];
    const tlc: Answer = line.startsWith("!") ? { failure: line.slice(1) } : { value: line };
    const isBuild = request.text.startsWith("value ");
    tally.operations++;
    if (JSON.stringify(request.local) !== JSON.stringify(request.native)) {
      report(
        "nativeDiffers",
        `${describe(request.text)}: ${JSON.stringify(request.local)} ${JSON.stringify(request.native)}`,
      );
    }
    if (request.interpreter && request.interpreter.value !== tlc.value) {
      report(
        "interpreterDiffers",
        `${describe(request.text)}: ${JSON.stringify(request.interpreter)}, TLC ${line}`,
      );
    }
    const store = request.native;
    const value = isBuild && store.failure === undefined ? "ok" : store.value;
    const name = request.text.split(" ")[0];
    const count = (outcome: string) => {
      breakdown[`${outcome} on ${name}`] = (breakdown[`${outcome} on ${name}`] ?? 0) + 1;
    };
    if (store.failure !== undefined && tlc.failure !== undefined) {
      tally.bothFail++;
      count("bothFail");
    } else if (store.failure !== undefined) {
      tally.storeStopsAlone++;
      count("storeStopsAlone");
    } else if (tlc.failure !== undefined) {
      report(
        "storeMissesFailure",
        `${describe(request.text)}: ${JSON.stringify(store)}, TLC ${line}`,
      );
    } else if (value === tlc.value) {
      tally.agree++;
      count("agree");
    } else
      report("answersDiffer", `${describe(request.text)}: ${JSON.stringify(store)}, TLC ${line}`);
  });
};

const BATCH = 5000;
for (let done = 0; done < operationCount; done += BATCH)
  runBatch(Math.min(BATCH, operationCount - done));
console.log(examples.join("\n"));
console.log(Object.fromEntries(Object.entries(breakdown).sort()));
console.log(
  [
    `${tally.operations} operations on generated values, seed ${seed}:`,
    `the native store answered ${tally.operations - tally.nativeDiffers} as the TypeScript store does, ${tally.nativeDiffers} otherwise;`,
    `against TLC, ${tally.agree} agree, ${tally.bothFail} fail in both, ${tally.storeStopsAlone} stop the store alone,`,
    `${tally.storeMissesFailure} fail in TLC alone, ${tally.answersDiffer} answer otherwise;`,
    `the interpreter's fingerprint differs from TLC's ${tally.interpreterDiffers} times.`,
  ].join("\n"),
);
const disagreements =
  tally.nativeDiffers + tally.storeMissesFailure + tally.answersDiffer + tally.interpreterDiffers;
console.log(disagreements === 0 ? "No disagreements." : `${disagreements} disagreements.`);
if (disagreements > 0) process.exitCode = 1;

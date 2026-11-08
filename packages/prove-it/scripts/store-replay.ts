// Replays a trace PROVE_IT_STORE_TRACE wrote on the TypeScript store, and reports the first
// operation whose result differs from the one the trace recorded: an id, a comparison, or a reason
// to stop. A trace replays exactly when it holds every operation that made an id, so this checks
// the trace as much as the store, and is the reference for replaying it on another store.
// Usage: bun scripts/store-replay.ts <trace>

import { readFileSync } from "node:fs";

import {
  appendTuple,
  apply,
  applyField,
  Bailout,
  compare,
  concatTuples,
  createRecordShape,
  difference,
  domainOf,
  equals,
  except,
  exceptAt,
  findKey,
  functionOf,
  functionOfSorted,
  functionOverSet,
  int,
  intersection,
  isMember,
  isSubset,
  model,
  recordOf,
  resetStore,
  setOf,
  setOfRange,
  setOfSorted,
  setOfSortedRange,
  sliceTuple,
  str,
  tupleOf,
  tupleOfRange,
  union,
  withElement,
} from "../src/engine/store";
import { rankString, setStringOrder } from "../src/values";

interface Mismatch {
  line: number;
  operation: string;
  expected: unknown;
  actual: unknown;
}

const getIds = (values: unknown) => (Array.isArray(values) ? values.map(Number) : []);

const OPERATIONS: Record<string, (args: unknown[]) => unknown> = {
  resetStore: (args) => {
    setStringOrder(Array.isArray(args[0]) ? args[0].map(String) : []);
    return resetStore();
  },
  rankStrings: (args) => {
    for (const text of Array.isArray(args[0]) ? args[0] : []) rankString(String(text));
    return null;
  },
  int: (args) => int(Number(args[0])),
  str: (args) => str(String(args[0])),
  model: (args) => model(String(args[0])),
  compare: (args) => compare(Number(args[0]), Number(args[1])),
  equals: (args) => equals(Number(args[0]), Number(args[1])),
  setOf: (args) => setOf(getIds(args[0])),
  setOfRange: (args) => setOfRange(Int32Array.from(getIds(args[0])), 0, getIds(args[0]).length),
  setOfSorted: (args) => setOfSorted(getIds(args[0]), getIds(args[0]).length),
  setOfSortedRange: (args) =>
    setOfSortedRange(Int32Array.from(getIds(args[0])), 0, getIds(args[0]).length),
  isMember: (args) => isMember(Number(args[0]), Number(args[1])),
  union: (args) => union(Number(args[0]), Number(args[1])),
  intersection: (args) => intersection(Number(args[0]), Number(args[1])),
  difference: (args) => difference(Number(args[0]), Number(args[1])),
  isSubset: (args) => isSubset(Number(args[0]), Number(args[1])),
  withElement: (args) => withElement(Number(args[0]), Number(args[1])),
  tupleOf: (args) => tupleOf(getIds(args[0]), getIds(args[0]).length),
  tupleOfRange: (args) => tupleOfRange(Int32Array.from(getIds(args[0])), 0, getIds(args[0]).length),
  recordOf: (args) => recordOf(createRecordShape(getIds(args[0])), getIds(args[1])),
  functionOfSorted: (args) =>
    functionOfSorted(getIds(args[0]), getIds(args[1]), getIds(args[0]).length),
  functionOverSet: (args) => functionOverSet(Number(args[0]), Int32Array.from(getIds(args[1])), 0),
  functionOf: (args) => functionOf(getIds(args[0]), getIds(args[1])),
  findKey: (args) => findKey(Number(args[0]), Number(args[1])),
  apply: (args) => apply(Number(args[0]), Number(args[1])),
  except: (args) => except(Number(args[0]), Number(args[1]), Number(args[2])),
  exceptAt: (args) =>
    exceptAt(Number(args[0]), getIds(args[1]), getIds(args[2]), getIds(args[1]).length),
  applyField: (args) => applyField(Number(args[0]), Number(args[1]), { position: 0 }),
  domainOf: (args) => domainOf(Number(args[0])),
  sliceTuple: (args) => sliceTuple(Number(args[0]), Number(args[1]), Number(args[2])),
  concatTuples: (args) => concatTuples(Number(args[0]), Number(args[1])),
  appendTuple: (args) => appendTuple(Number(args[0]), Number(args[1])),
};

const runOperation = (operation: string, args: unknown[]) => {
  try {
    return OPERATIONS[operation](args) ?? null;
  } catch (error) {
    if (error instanceof Bailout) return { bail: error.message };
    throw error;
  }
};

export const replayStoreTrace = (trace: string): Mismatch | undefined => {
  const lines = trace.split("\n").filter((line) => line !== "");
  for (const [index, line] of lines.entries()) {
    const record: [string, unknown[], unknown] = JSON.parse(line);
    const actual = runOperation(record[0], record[1]);
    if (JSON.stringify(actual) !== JSON.stringify(record[2])) {
      return { line: index + 1, operation: record[0], expected: record[2], actual };
    }
  }
  return undefined;
};

if (process.argv[1] === import.meta.filename) {
  const mismatch = replayStoreTrace(readFileSync(process.argv[2], "utf8"));
  console.log(
    mismatch
      ? `line ${mismatch.line}: ${mismatch.operation} gave ${JSON.stringify(mismatch.actual)}, the trace ${JSON.stringify(mismatch.expected)}`
      : "The store replayed the trace exactly.",
  );
  if (mismatch) process.exitCode = 1;
}

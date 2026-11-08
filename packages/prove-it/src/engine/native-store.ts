// The native store (native/crates/tla-values) behind the functions of store.ts and fingerprint.ts,
// for tests and the value oracle, which run the same cases on both. Each call crosses into the
// addon, which costs what an N-API call costs; nothing in the engine calls this. TLC's order of
// strings stays in values.ts, as it does for the TypeScript store: a reset hands the native store
// the order then, and each operation first hands it the strings ranked since, as a store trace
// records them.

import { EngineInvariantError } from "../errors";
import { createStateEncoder } from "../transfer";
import { getRankedStringCount, getStringOrder, type Value } from "../values";
import { getNativeAddon } from "./native";
import { bail, type RecordShape } from "./store";

const getHooks = () => {
  const addon = getNativeAddon();
  if (typeof addon === "string") {
    throw new EngineInvariantError(`the native store needs the addon: ${addon}`);
  }
  return addon;
};

const ranking = { count: 0 };

const rankNewStrings = () => {
  const count = getRankedStringCount();
  if (count <= ranking.count) return;
  getHooks().storePerform("rankStrings", [getStringOrder().slice(ranking.count)]);
  ranking.count = count;
};

const perform = (name: string, args: unknown[]) => {
  rankNewStrings();
  const result = getHooks().storePerform(name, args);
  return typeof result === "string" ? bail(result) : result;
};

const performNumber = (name: string, args: unknown[]) => {
  const result = perform(name, args);
  if (typeof result !== "number") {
    throw new EngineInvariantError(`the native store's ${name} gave ${String(result)}`);
  }
  return result;
};

const performBoolean = (name: string, args: unknown[]) => {
  const result = perform(name, args);
  if (typeof result !== "boolean") {
    throw new EngineInvariantError(`the native store's ${name} gave ${String(result)}`);
  }
  return result;
};

const getWords = (words: ArrayLike<number>, start: number, length: number) =>
  Array.from({ length }, (_, index) => words[start + index]);

const resetStore = () => {
  ranking.count = getRankedStringCount();
  getHooks().storePerform("resetStore", [getStringOrder()]);
};

const getStateFingerprints = (
  states: Int32Array,
  count: number,
  width: number,
  order: number[],
  parents?: Int32Array,
  isReference = false,
) => {
  const fingerprints = new BigInt64Array(count);
  getHooks().storeFingerprints(
    states.subarray(0, count * width),
    width,
    Int32Array.from(order),
    parents,
    isReference,
    fingerprints,
  );
  return fingerprints;
};

// The functions of store.ts and fingerprint.ts that the native store implements, by the same names
// and with the same arguments.
export const nativeStore = {
  resetStore,
  getValueCount: () => performNumber("getValueCount", []),
  int: (value: number) => performNumber("int", [value]),
  str: (text: string) => performNumber("str", [text]),
  model: (name: string) => performNumber("model", [name]),
  compare: (left: number, right: number) => performNumber("compare", [left, right]),
  equals: (left: number, right: number) => performBoolean("equals", [left, right]),
  setOf: (elements: number[]) => performNumber("setOf", [elements]),
  setOfRange: (words: Int32Array, start: number, length: number) =>
    performNumber("setOfRange", [getWords(words, start, length)]),
  setOfSorted: (elements: ArrayLike<number>, length: number) =>
    performNumber("setOfSorted", [getWords(elements, 0, length)]),
  setOfSortedRange: (words: Int32Array, start: number, length: number) =>
    performNumber("setOfSortedRange", [getWords(words, start, length)]),
  isMember: (element: number, set: number) => performBoolean("isMember", [element, set]),
  union: (left: number, right: number) => performNumber("union", [left, right]),
  intersection: (left: number, right: number) => performNumber("intersection", [left, right]),
  difference: (left: number, right: number) => performNumber("difference", [left, right]),
  isSubset: (left: number, right: number) => performBoolean("isSubset", [left, right]),
  withElement: (set: number, element: number) => performNumber("withElement", [set, element]),
  tupleOf: (elements: ArrayLike<number>, length: number) =>
    performNumber("tupleOf", [getWords(elements, 0, length)]),
  tupleOfRange: (words: Int32Array, start: number, length: number) =>
    performNumber("tupleOfRange", [getWords(words, start, length)]),
  // The native store hashes a shape's keys itself.
  createRecordShape: (keys: number[]): RecordShape => ({ keys: Int32Array.from(keys), prefix: 0 }),
  recordOf: (shape: RecordShape, values: ArrayLike<number>) =>
    performNumber("recordOf", [shape.keys, getWords(values, 0, shape.keys.length)]),
  functionOfSorted: (domain: ArrayLike<number>, range: ArrayLike<number>, size: number) =>
    performNumber("functionOfSorted", [getWords(domain, 0, size), getWords(range, 0, size)]),
  functionOf: (keys: number[], values: number[]) => performNumber("functionOf", [keys, values]),
  findKey: (fn: number, key: number) => performNumber("findKey", [fn, key]),
  apply: (fn: number, key: number) => performNumber("apply", [fn, key]),
  except: (fn: number, key: number, value: number) => performNumber("except", [fn, key, value]),
  exceptAt: (fn: number, positions: number[], values: number[], count: number) =>
    performNumber("exceptAt", [fn, positions.slice(0, count), values.slice(0, count)]),
  domainOf: (fn: number) => performNumber("domainOf", [fn]),
  sliceTuple: (tuple: number, from: number, to: number) =>
    performNumber("sliceTuple", [tuple, from, to]),
  concatTuples: (left: number, right: number) => performNumber("concatTuples", [left, right]),
  appendTuple: (tuple: number, element: number) => performNumber("appendTuple", [tuple, element]),
  // convert.ts's fromValue, through transfer.ts's encoding.
  fromValue: (value: Value) => {
    rankNewStrings();
    const encoder = createStateEncoder();
    if (!encoder.encode([value])) bail(`a value the engine can't hold`);
    const encoded = encoder.finish();
    const ids = new Int32Array(1);
    const reason = getHooks().storeDecode(encoded.words, encoded.strings, 1, 1, ids);
    return reason === null ? ids[0] : bail(reason);
  },
  // The states in transfer.ts's encoding, as the engine's state log writes them.
  encodeStates: (states: Int32Array, count: number, width: number) =>
    getHooks().storeEncode(states.subarray(0, count * width), width),
  getStateFingerprints: (
    states: Int32Array,
    count: number,
    width: number,
    order: number[],
    parents?: Int32Array,
  ) => getStateFingerprints(states, count, width, order, parents),
  getStateFingerprintsReference: (
    states: Int32Array,
    count: number,
    width: number,
    order: number[],
  ) => getStateFingerprints(states, count, width, order, undefined, true),
  resetFingerprints: () => getHooks().storeResetFingerprints(),
};

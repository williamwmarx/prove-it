// A hash-consed store of TLA+ values. Every finite value the engine builds is interned once and
// named by a small integer, its id, so equal values have equal ids. A state is then a short vector
// of ids, equality is an integer comparison, and any pure computation can be cached by the ids of
// what it reads.
//
// Composite values keep their elements in TLC's order, so enumerating a set visits elements in the
// order TLC does and the engine generates successors in TLC's order.

import { findStringRank, getStringRank } from "../values";
import { getEnvironmentFlag } from "./settings";

export const KIND_BOOL = 0;
export const KIND_INT = 1;
export const KIND_STRING = 2;
export const KIND_MODEL = 3;
export const KIND_SET = 4;
// A function whose domain isn't 1..n, records included. Its heap block holds the domain in TLC's
// order, then the range.
export const KIND_FUNCTION = 5;
// A function with domain 1..n, the empty function included. Its heap block holds the range.
export const KIND_TUPLE = 6;

// Thrown wherever the engine meets something it doesn't handle or that TLC reports as an error.
// The checker then hands the whole check to the reference interpreter, which reproduces TLC's
// behavior, messages included.
export class Bailout extends Error {
  // Where the search stood when the engine stopped, so the interpreter can go on from there.
  checkpoint: unknown;

  constructor(reason: string) {
    super(reason);
    this.name = "Bailout";
  }
}

export const bail = (reason: string): never => {
  throw new Bailout(reason);
};

const INITIAL_CAPACITY = 1 << 12;

let kinds: Uint8Array = new Uint8Array(INITIAL_CAPACITY);
// For an integer its value, for a string or model value the index of its text, and for a composite
// value the offset of its block in the heap.
let payloads: Int32Array = new Int32Array(INITIAL_CAPACITY);
// For a composite value its size: the number of elements, pairs, or components.
let sizes: Int32Array = new Int32Array(INITIAL_CAPACITY);
let hashes: Int32Array = new Int32Array(INITIAL_CAPACITY);
let count = 0;

export let heap: Int32Array = new Int32Array(1 << 16);
let heapTop = 0;

let table = new Int32Array(INITIAL_CAPACITY * 2).fill(-1);
let tableMask = table.length - 1;

const texts: string[] = [];
// TLC orders strings by when it interned them. The rank of a string the spec doesn't mention is -1,
// and TLC orders those after the others, by their text.
const textRanks: number[] = [];
// Whether each text is a string's or a model value's.
const textKinds: number[] = [];
const stringIds = new Map<string, number>();
const modelIds = new Map<string, number>();

const SMALL_INT_MIN = -256;
const SMALL_INT_MAX = 4096;
const smallInts = new Int32Array(SMALL_INT_MAX - SMALL_INT_MIN + 1);

export const FALSE = 0;
export const TRUE = 1;
export let EMPTY_SET = 2;
export let EMPTY_TUPLE = 3;

// Bumped on every reset, so caches keyed by ids can tell they are stale.
export let generation = 0;

const mix = (hash: number) => {
  const first = Math.imul(hash ^ (hash >>> 16), 0x7feb352d);
  const second = Math.imul(first ^ (first >>> 15), 0x846ca68b);
  return second ^ (second >>> 16);
};

const growValues = () => {
  const capacity = kinds.length * 2;
  const nextKinds = new Uint8Array(capacity);
  nextKinds.set(kinds);
  kinds = nextKinds;
  const nextPayloads = new Int32Array(capacity);
  nextPayloads.set(payloads);
  payloads = nextPayloads;
  const nextSizes = new Int32Array(capacity);
  nextSizes.set(sizes);
  sizes = nextSizes;
  const nextHashes = new Int32Array(capacity);
  nextHashes.set(hashes);
  hashes = nextHashes;
};

const growTable = () => {
  const next = new Int32Array(table.length * 2).fill(-1);
  const mask = next.length - 1;
  for (let id = 0; id < count; id++) {
    let slot = hashes[id] & mask;
    while (next[slot] !== -1) slot = (slot + 1) & mask;
    next[slot] = id;
  }
  table = next;
  tableMask = mask;
};

const ensureHeap = (extra: number) => {
  if (heapTop + extra <= heap.length) return;
  let capacity = heap.length * 2;
  while (heapTop + extra > capacity) capacity *= 2;
  const next = new Int32Array(capacity);
  next.set(heap.subarray(0, heapTop));
  heap = next;
};

const allocate = (kind: number, payload: number, size: number, hash: number, slot: number) => {
  if (count === kinds.length) growValues();
  const id = count++;
  kinds[id] = kind;
  payloads[id] = payload;
  sizes[id] = size;
  hashes[id] = hash;
  table[slot] = id;
  if (count * 2 > table.length) growTable();
  return id;
};

// Interns a scalar: a boolean, an integer, a string, or a model value, by its payload.
const internScalar = (kind: number, payload: number) => {
  const hash = mix(Math.imul(kind + 1, 0x9e3779b1) ^ payload);
  if (shared) return internShared(kind, payload, EMPTY_WORDS, 0, 0, hash);
  for (let slot = hash & tableMask; ; slot = (slot + 1) & tableMask) {
    const id = table[slot];
    if (id === -1) return allocate(kind, payload, 0, hash, slot);
    if (hashes[id] === hash && kinds[id] === kind && payloads[id] === payload && sizes[id] === 0) {
      return id;
    }
  }
};

// Interns a composite value whose block is words[0..length).
const internBlock = (kind: number, words: ArrayLike<number>, length: number, size: number) => {
  let hash = Math.imul(kind + 7, 0x9e3779b1) ^ size;
  for (let index = 0; index < length; index++) hash = Math.imul(hash ^ words[index], 0x01000193);
  hash = mix(hash);
  if (shared) return internShared(kind, 0, words, length, size, hash);
  for (let slot = hash & tableMask; ; slot = (slot + 1) & tableMask) {
    const id = table[slot];
    if (id === -1) {
      ensureHeap(length);
      const offset = heapTop;
      for (let index = 0; index < length; index++) heap[offset + index] = words[index];
      heapTop += length;
      return allocate(kind, offset, size, hash, slot);
    }
    if (hashes[id] !== hash || kinds[id] !== kind || sizes[id] !== size) continue;
    const offset = payloads[id];
    let isEqual = true;
    for (let index = 0; index < length; index++) {
      if (heap[offset + index] !== words[index]) {
        isEqual = false;
        break;
      }
    }
    if (isEqual) return id;
  }
};

export const resetStore = () => {
  generation++;
  resetDomains();
  if (shared) {
    shared = undefined;
    kinds = new Uint8Array(INITIAL_CAPACITY);
    payloads = new Int32Array(INITIAL_CAPACITY);
    sizes = new Int32Array(INITIAL_CAPACITY);
    hashes = new Int32Array(INITIAL_CAPACITY);
    heap = new Int32Array(1 << 16);
  }
  textKinds.length = 0;
  count = 0;
  heapTop = 0;
  table.fill(-1);
  texts.length = 0;
  textRanks.length = 0;
  stringIds.clear();
  modelIds.clear();
  internScalar(KIND_BOOL, 0);
  internScalar(KIND_BOOL, 1);
  EMPTY_SET = internBlock(KIND_SET, [], 0, 0);
  EMPTY_TUPLE = internBlock(KIND_TUPLE, [], 0, 0);
  for (let value = SMALL_INT_MIN; value <= SMALL_INT_MAX; value++) {
    smallInts[value - SMALL_INT_MIN] = internScalar(KIND_INT, value);
  }
};

export const getValueCount = () => (shared ? Atomics.load(shared.counters, COUNT) : count);

export const kindOf = (id: number) => kinds[id];
export const sizeOf = (id: number) => sizes[id];
export const offsetOf = (id: number) => payloads[id];
export const hashOf = (id: number) => hashes[id];
export const intOf = (id: number) => payloads[id];
export const textOf = (id: number) => texts[payloads[id]];

export const bool = (value: boolean) => (value ? TRUE : FALSE);

export const int = (value: number) => {
  if (value >= SMALL_INT_MIN && value <= SMALL_INT_MAX) return smallInts[value - SMALL_INT_MIN];
  if (value > 2147483647 || value < -2147483648 || !Number.isInteger(value)) {
    return bail("integer overflow");
  }
  return internScalar(KIND_INT, value);
};

const internText = (text: string, kind: number) => {
  // Workers share ids, so they share the texts behind them: once workers run, a new text would get
  // a different index in each.
  if (shared?.isTextFrozen) bail("a string built while workers run");
  const index = texts.length;
  texts.push(text);
  textRanks.push(-1);
  textKinds.push(kind);
  return index;
};

export const str = (text: string) => {
  const known = stringIds.get(text);
  if (known !== undefined) return known;
  // A string the spec mentions has a rank already. One it builds keeps whatever rank it has now.
  const index = internText(text, KIND_STRING);
  textRanks[index] = peekRank(text);
  const id = internScalar(KIND_STRING, index);
  stringIds.set(text, id);
  return id;
};

const peekRank = (text: string) => findStringRank(text) ?? -1;

export const model = (name: string) => {
  const known = modelIds.get(name);
  if (known !== undefined) return known;
  // Typed model values, such as A_a, change how TLC compares values. The engine leaves them to the
  // reference interpreter.
  const index = internText(name, KIND_MODEL);
  textRanks[index] = getStringRank(name);
  const id = internScalar(KIND_MODEL, index);
  modelIds.set(name, id);
  return id;
};

export const isModelId = (id: number) => kinds[id] === KIND_MODEL;

// A model value named like A_x is typed: TLC compares it only with model values of its type or
// untyped ones, and fails on anything else. Returns the type's character code, or 0 if untyped.
const getModelType = (id: number) => {
  const name = texts[payloads[id]];
  return name.length > 2 && name[1] === "_" ? name.charCodeAt(0) : 0;
};

const checkModelTypes = (left: number, right: number) => {
  const leftType = getModelType(left);
  const rightType = getModelType(right);
  if (leftType !== 0 && rightType !== 0 && leftType !== rightType) {
    bail("differently typed model values");
  }
};

// TLC's Value#compareTo. Two values TLC can't compare make the engine bail out.
export const compare = (left: number, right: number): number => {
  if (left === right) return 0;
  const leftKind = kinds[left];
  const rightKind = kinds[right];
  if (leftKind === rightKind) {
    switch (leftKind) {
      case KIND_INT:
        return payloads[left] < payloads[right] ? -1 : 1;
      case KIND_STRING:
        return compareTexts(payloads[left], payloads[right]);
      case KIND_BOOL:
        return left < right ? -1 : 1;
      case KIND_MODEL:
        checkModelTypes(left, right);
        return textRanks[payloads[left]] - textRanks[payloads[right]];
      case KIND_SET:
        return compareSets(left, right);
      default:
        return compareFunctions(left, right);
    }
  }
  if (leftKind === KIND_MODEL) return getModelType(left) === 0 ? -1 : bail("typed model value");
  if (rightKind === KIND_MODEL) return getModelType(right) === 0 ? 1 : bail("typed model value");
  if (isFunctionKind(leftKind) && isFunctionKind(rightKind)) return compareFunctions(left, right);
  return bail("values TLC can't compare");
};

const compareTexts = (left: number, right: number) => {
  const leftRank = textRanks[left];
  const rightRank = textRanks[right];
  if (leftRank !== -1 && rightRank !== -1) return leftRank - rightRank;
  if (leftRank !== -1) return -1;
  if (rightRank !== -1) return 1;
  return texts[left] < texts[right] ? -1 : 1;
};

const compareSets = (left: number, right: number) => {
  const size = sizes[left];
  if (size !== sizes[right]) return size - sizes[right];
  const leftOffset = payloads[left];
  const rightOffset = payloads[right];
  for (let index = 0; index < size; index++) {
    const comparison = compare(heap[leftOffset + index], heap[rightOffset + index]);
    if (comparison !== 0) return comparison;
  }
  return 0;
};

export const isFunctionKind = (kind: number) => kind === KIND_FUNCTION || kind === KIND_TUPLE;

const isRecordId = (id: number) => {
  if (kinds[id] !== KIND_FUNCTION) return false;
  const offset = payloads[id];
  for (let index = 0; index < sizes[id]; index++) {
    if (kinds[heap[offset + index]] !== KIND_STRING) return false;
  }
  return true;
};

const compareFunctions = (left: number, right: number) => {
  const size = sizes[left];
  const rightSize = sizes[right];
  if (size !== rightSize) {
    // TLC compares a record only with a record, which may fail before the sizes decide.
    if (size > 0 && rightSize > 0 && isRecordId(left) !== isRecordId(right)) {
      return bail("record compared with a function");
    }
    return size - rightSize;
  }
  for (let index = 0; index < size; index++) {
    const comparison = compare(getKey(left, index), getKey(right, index));
    if (comparison !== 0) return comparison;
  }
  for (let index = 0; index < size; index++) {
    const comparison = compare(getRangeValue(left, index), getRangeValue(right, index));
    if (comparison !== 0) return comparison;
  }
  return 0;
};

// TLC's equality. Values of kinds TLC can't compare, other than model values, make the engine bail
// out, as TLC fails there.
export const equals = (left: number, right: number) => {
  if (left === right) return true;
  const leftKind = kinds[left];
  const rightKind = kinds[right];
  if (leftKind === rightKind) {
    if (leftKind === KIND_MODEL) checkModelTypes(left, right);
    return false;
  }
  if (leftKind === KIND_MODEL) return getModelType(left) === 0 ? false : bail("typed model value");
  if (rightKind === KIND_MODEL)
    return getModelType(right) === 0 ? false : bail("typed model value");
  if (isFunctionKind(leftKind) && isFunctionKind(rightKind)) return false;
  return bail("equality of values TLC can't compare");
};

// --- sets ---

// The set of the given elements, in any order and with duplicates.
export const setOf = (elements: number[]) => {
  const length = elements.length;
  if (length === 0) return EMPTY_SET;
  if (length === 1) return internBlock(KIND_SET, elements, 1, 1);
  let isSorted = true;
  for (let index = 1; index < length; index++) {
    if (compare(elements[index - 1], elements[index]) >= 0) {
      isSorted = false;
      break;
    }
  }
  if (isSorted) return internBlock(KIND_SET, elements, length, length);
  const sorted = elements.slice().sort(compare);
  let unique = 1;
  for (let index = 1; index < length; index++) {
    if (sorted[index] !== sorted[unique - 1]) sorted[unique++] = sorted[index];
  }
  return internBlock(KIND_SET, sorted, unique, unique);
};

// The set of elements already in TLC's order without duplicates.
export const setOfSorted = (elements: ArrayLike<number>, length: number) =>
  internBlock(KIND_SET, elements, length, length);

export const elementAt = (set: number, index: number) => heap[payloads[set] + index];

export const setElements = (set: number) => {
  const offset = payloads[set];
  return Array.from(heap.subarray(offset, offset + sizes[set]));
};

// Sets with more elements than this get a hash index for membership.
const INDEXED_SIZE = 16;
const memberIndexes = new Map<number, Set<number>>();

export const isMember = (element: number, set: number): boolean => {
  const size = sizes[set];
  const offset = payloads[set];
  if (size <= INDEXED_SIZE) {
    for (let index = 0; index < size; index++) if (heap[offset + index] === element) return true;
  } else {
    let index = memberIndexes.get(set);
    if (index === undefined) {
      index = new Set(heap.subarray(offset, offset + size));
      memberIndexes.set(set, index);
    }
    if (index.has(element)) return true;
  }
  // TLC compares the element with those of the set, which fails for values it can't compare.
  if (size > 0) checkComparable(element, heap[offset]);
  return false;
};

const checkComparable = (left: number, right: number) => {
  const leftKind = kinds[left];
  const rightKind = kinds[right];
  if (leftKind === rightKind) {
    if (leftKind === KIND_MODEL) checkModelTypes(left, right);
    return;
  }
  if (leftKind === KIND_MODEL || rightKind === KIND_MODEL) {
    if (getModelType(leftKind === KIND_MODEL ? left : right) !== 0) bail("typed model value");
    return;
  }
  if (isFunctionKind(leftKind) && isFunctionKind(rightKind)) return;
  bail("membership of a value TLC can't compare");
};

const mergeScratch: number[] = [];

export const union = (left: number, right: number) => {
  const leftSize = sizes[left];
  const rightSize = sizes[right];
  if (leftSize === 0) return right;
  if (rightSize === 0 || left === right) return left;
  const leftOffset = payloads[left];
  const rightOffset = payloads[right];
  const merged = mergeScratch;
  merged.length = 0;
  let leftIndex = 0;
  let rightIndex = 0;
  while (leftIndex < leftSize && rightIndex < rightSize) {
    const leftElement = heap[leftOffset + leftIndex];
    const rightElement = heap[rightOffset + rightIndex];
    if (leftElement === rightElement) {
      merged.push(leftElement);
      leftIndex++;
      rightIndex++;
      continue;
    }
    if (compare(leftElement, rightElement) < 0) {
      merged.push(leftElement);
      leftIndex++;
    } else {
      merged.push(rightElement);
      rightIndex++;
    }
  }
  while (leftIndex < leftSize) merged.push(heap[leftOffset + leftIndex++]);
  while (rightIndex < rightSize) merged.push(heap[rightOffset + rightIndex++]);
  if (merged.length === leftSize) return left;
  if (merged.length === rightSize) return right;
  return internBlock(KIND_SET, merged, merged.length, merged.length);
};

export const intersection = (left: number, right: number) => {
  const leftSize = sizes[left];
  const rightSize = sizes[right];
  if (leftSize === 0 || left === right) return left;
  if (rightSize === 0) return right;
  const leftOffset = payloads[left];
  const rightOffset = payloads[right];
  const merged = mergeScratch;
  merged.length = 0;
  let leftIndex = 0;
  let rightIndex = 0;
  while (leftIndex < leftSize && rightIndex < rightSize) {
    const leftElement = heap[leftOffset + leftIndex];
    const rightElement = heap[rightOffset + rightIndex];
    if (leftElement === rightElement) {
      merged.push(leftElement);
      leftIndex++;
      rightIndex++;
    } else if (compare(leftElement, rightElement) < 0) {
      leftIndex++;
    } else {
      rightIndex++;
    }
  }
  if (merged.length === leftSize) return left;
  return internBlock(KIND_SET, merged, merged.length, merged.length);
};

export const difference = (left: number, right: number) => {
  const leftSize = sizes[left];
  const rightSize = sizes[right];
  if (leftSize === 0 || rightSize === 0) return left;
  if (left === right) return EMPTY_SET;
  const leftOffset = payloads[left];
  const rightOffset = payloads[right];
  const merged = mergeScratch;
  merged.length = 0;
  let leftIndex = 0;
  let rightIndex = 0;
  while (leftIndex < leftSize && rightIndex < rightSize) {
    const leftElement = heap[leftOffset + leftIndex];
    const rightElement = heap[rightOffset + rightIndex];
    if (leftElement === rightElement) {
      leftIndex++;
      rightIndex++;
    } else if (compare(leftElement, rightElement) < 0) {
      merged.push(leftElement);
      leftIndex++;
    } else {
      rightIndex++;
    }
  }
  while (leftIndex < leftSize) merged.push(heap[leftOffset + leftIndex++]);
  if (merged.length === leftSize) return left;
  return internBlock(KIND_SET, merged, merged.length, merged.length);
};

export const isSubset = (left: number, right: number) => {
  if (left === right) return true;
  const leftSize = sizes[left];
  if (leftSize > sizes[right]) {
    // TLC still compares the elements, which may fail.
    for (let index = 0; index < leftSize; index++) {
      if (!isMember(heap[payloads[left] + index], right)) return false;
    }
    return false;
  }
  for (let index = 0; index < leftSize; index++) {
    if (!isMember(heap[payloads[left] + index], right)) return false;
  }
  return true;
};

export const withElement = (set: number, element: number) => {
  const size = sizes[set];
  const offset = payloads[set];
  const merged = mergeScratch;
  merged.length = 0;
  let isInserted = false;
  for (let index = 0; index < size; index++) {
    const current = heap[offset + index];
    if (current === element) return set;
    if (!isInserted && compare(element, current) < 0) {
      merged.push(element);
      isInserted = true;
    }
    merged.push(current);
  }
  if (!isInserted) merged.push(element);
  return internBlock(KIND_SET, merged, merged.length, merged.length);
};

// --- functions, records, and tuples ---

export const tupleOf = (elements: ArrayLike<number>, length: number) =>
  length === 0 ? EMPTY_TUPLE : internBlock(KIND_TUPLE, elements, length, length);

const pairScratch: number[] = [];

// The function with the given domain in TLC's order and the range in the same order. A domain of
// 1..n makes a tuple.
export const functionOfSorted = (
  domain: ArrayLike<number>,
  range: ArrayLike<number>,
  size: number,
) => {
  if (size === 0) return EMPTY_TUPLE;
  let isTuple = true;
  for (let index = 0; index < size; index++) {
    const key = domain[index];
    if (kinds[key] !== KIND_INT || payloads[key] !== index + 1) {
      isTuple = false;
      break;
    }
  }
  if (isTuple) return internBlock(KIND_TUPLE, range, size, size);
  const words = pairScratch;
  words.length = 2 * size;
  for (let index = 0; index < size; index++) {
    words[index] = domain[index];
    words[size + index] = range[index];
  }
  return internBlock(KIND_FUNCTION, words, 2 * size, size);
};

// The function of the given pairs, keys in any order but without duplicates.
export const functionOf = (keys: number[], values: number[]) => {
  const size = keys.length;
  let isSorted = true;
  for (let index = 1; index < size; index++) {
    if (compare(keys[index - 1], keys[index]) >= 0) {
      isSorted = false;
      break;
    }
  }
  if (isSorted) return functionOfSorted(keys, values, size);
  const order = keys
    .map((_, index) => index)
    .sort((left, right) => compare(keys[left], keys[right]));
  return functionOfSorted(
    order.map((index) => keys[index]),
    order.map((index) => values[index]),
    size,
  );
};

export const getKey = (fn: number, index: number) =>
  kinds[fn] === KIND_TUPLE ? int(index + 1) : heap[payloads[fn] + index];

export const getRangeValue = (fn: number, index: number) =>
  kinds[fn] === KIND_TUPLE ? heap[payloads[fn] + index] : heap[payloads[fn] + sizes[fn] + index];

// The position of a key in the domain of a function, or -1.
export const findKey = (fn: number, key: number) => {
  const size = sizes[fn];
  if (kinds[fn] === KIND_TUPLE) {
    if (kinds[key] !== KIND_INT) return -1;
    const position = payloads[key] - 1;
    return position >= 0 && position < size ? position : -1;
  }
  const offset = payloads[fn];
  // A domain of consecutive integers, such as 0..n, finds its key by subtraction.
  if (size > 0 && kinds[key] === KIND_INT) {
    const first = heap[offset];
    const last = heap[offset + size - 1];
    if (kinds[first] === KIND_INT && kinds[last] === KIND_INT) {
      const low = payloads[first];
      if (payloads[last] - low === size - 1) {
        const position = payloads[key] - low;
        return position >= 0 && position < size ? position : -1;
      }
    }
  }
  if (size <= INDEXED_SIZE) {
    for (let index = 0; index < size; index++) if (heap[offset + index] === key) return index;
    return -1;
  }
  let low = 0;
  let high = size - 1;
  while (low <= high) {
    const middle = (low + high) >> 1;
    const current = heap[offset + middle];
    if (current === key) return middle;
    if (compare(current, key) < 0) low = middle + 1;
    else high = middle - 1;
  }
  return -1;
};

// Whether each function's domain is a run of consecutive integers, such as 0..n, found once per
// function: 0 not yet known, 1 a run starting at domainLows[id], 2 anything else.
let domainKinds = new Uint8Array(0);
let domainLows = new Int32Array(0);

const classifyDomain = (fn: number) => {
  if (fn >= domainKinds.length) {
    const capacity = Math.max(1024, (fn + 1) * 2);
    const nextKinds = new Uint8Array(capacity);
    nextKinds.set(domainKinds);
    domainKinds = nextKinds;
    const nextLows = new Int32Array(capacity);
    nextLows.set(domainLows);
    domainLows = nextLows;
  }
  const size = sizes[fn];
  const offset = payloads[fn];
  const first = heap[offset];
  const last = heap[offset + size - 1];
  const isRun =
    size > 0 &&
    kinds[first] === KIND_INT &&
    kinds[last] === KIND_INT &&
    payloads[last] - payloads[first] === size - 1;
  domainKinds[fn] = isRun ? 1 : 2;
  if (isRun) domainLows[fn] = payloads[first];
  return domainKinds[fn];
};

export const resetDomains = () => {
  domainKinds = new Uint8Array(0);
  domainLows = new Int32Array(0);
};

export const apply = (fn: number, key: number) => {
  const kind = kinds[fn];
  if (kind === KIND_FUNCTION && kinds[key] === KIND_INT) {
    const domainKind =
      fn < domainKinds.length && domainKinds[fn] !== 0 ? domainKinds[fn] : classifyDomain(fn);
    if (domainKind === 1) {
      const position = payloads[key] - domainLows[fn];
      const size = sizes[fn];
      if (position >= 0 && position < size) return heap[payloads[fn] + size + position];
      return bail("applied a function outside its domain");
    }
  } else if (kind === KIND_TUPLE && kinds[key] === KIND_INT) {
    const position = payloads[key] - 1;
    if (position >= 0 && position < sizes[fn]) return heap[payloads[fn] + position];
    return bail("applied a function outside its domain");
  }
  if (kind !== KIND_FUNCTION && kind !== KIND_TUPLE) return bail("applied a non-function");
  const position = findKey(fn, key);
  if (position === -1) return bail("applied a function outside its domain");
  return kind === KIND_TUPLE
    ? heap[payloads[fn] + position]
    : heap[payloads[fn] + sizes[fn] + position];
};

const exceptScratch: number[] = [];

// [fn EXCEPT ![key] = value].
export const except = (fn: number, key: number, value: number) => {
  const kind = kinds[fn];
  if (kind !== KIND_FUNCTION && kind !== KIND_TUPLE) return bail("EXCEPT on a non-function");
  const position = findKey(fn, key);
  // TLC leaves a function alone when EXCEPT names a key outside its domain, but a tuple fails to
  // fingerprint later, so the engine leaves both to the reference interpreter.
  if (position === -1) return bail("EXCEPT outside the domain");
  const size = sizes[fn];
  const offset = payloads[fn];
  const length = kind === KIND_TUPLE ? size : 2 * size;
  const valueOffset = kind === KIND_TUPLE ? position : size + position;
  if (heap[offset + valueOffset] === value) return fn;
  const words = exceptScratch;
  words.length = length;
  for (let index = 0; index < length; index++) words[index] = heap[offset + index];
  words[valueOffset] = value;
  return internBlock(kind, words, length, size);
};

// [fn EXCEPT ![k1] = v1, ..., ![kn] = vn], given the position of each key in fn, interned once.
export const exceptAt = (fn: number, positions: number[], values: number[], count: number) => {
  const kind = kinds[fn];
  const size = sizes[fn];
  const offset = payloads[fn];
  const valueStart = kind === KIND_TUPLE ? 0 : size;
  let isChanged = false;
  for (let index = 0; index < count; index++) {
    if (heap[offset + valueStart + positions[index]] !== values[index]) {
      isChanged = true;
      break;
    }
  }
  if (!isChanged) return fn;
  const length = valueStart + size;
  const words = exceptScratch;
  words.length = length;
  for (let index = 0; index < length; index++) words[index] = heap[offset + index];
  for (let index = 0; index < count; index++) words[valueStart + positions[index]] = values[index];
  return internBlock(kind, words, length, size);
};

export const domainOf = (fn: number) => {
  const size = sizes[fn];
  const keys: number[] = new Array(size);
  for (let index = 0; index < size; index++) keys[index] = getKey(fn, index);
  return setOfSorted(keys, size);
};

export const tupleElements = (tuple: number) => {
  const offset = payloads[tuple];
  return Array.from(heap.subarray(offset, offset + sizes[tuple]));
};

// --- shared mode ---
//
// With workers, the store lives in SharedArrayBuffers that grow in place, so every thread sees the
// same ids. The intern table is split into segments, each with its own lock and its own region of
// a shared arena, so threads rarely contend and a segment grows without stopping the others. A
// value is written before its id is published under the lock, so any thread that learns an id can
// read the value.

const SEGMENT_BITS = 10;
const SEGMENTS = 1 << SEGMENT_BITS;
const INITIAL_SEGMENT_SLOTS = 64;
const COUNT = 0;
const HEAP_TOP = 1;
const ARENA_TOP = 2;
const EMPTY_WORDS: number[] = [];

export interface SharedStore {
  kinds: SharedArrayBuffer;
  payloads: SharedArrayBuffer;
  sizes: SharedArrayBuffer;
  hashes: SharedArrayBuffer;
  heap: SharedArrayBuffer;
  counters: SharedArrayBuffer;
  directory: SharedArrayBuffer;
  locks: SharedArrayBuffer;
  arena: SharedArrayBuffer;
  texts: string[];
  textRanks: number[];
  textKinds: number[];
  smallInts: Int32Array;
  emptySet: number;
  emptyTuple: number;
}

interface SharedViews {
  buffers: SharedStore;
  counters: Int32Array;
  directory: Int32Array;
  locks: Int32Array;
  arena: Int32Array;
  isTextFrozen: boolean;
}

let shared: SharedViews | undefined;

const MAXIMUM_SHARED_BYTES = 1 << 30;

// Append-only arrays get their whole capacity up front: the system commits a page only once it is
// written, and a view of fixed length runs faster than one that tracks a growing buffer.
const createGrowable = (bytes: number) =>
  getEnvironmentFlag("PROVE_IT_GROWABLE")
    ? new SharedArrayBuffer(bytes, { maxByteLength: MAXIMUM_SHARED_BYTES })
    : new SharedArrayBuffer(Math.max(bytes, MAXIMUM_SHARED_BYTES));

const growShared = (buffer: SharedArrayBuffer, bytes: number) => {
  if (!buffer.growable) {
    if (buffer.byteLength < bytes) bail("the shared store is full");
    return;
  }
  while (buffer.byteLength < bytes) {
    const target = Math.min(MAXIMUM_SHARED_BYTES, Math.max(bytes, buffer.byteLength * 2));
    if (target < bytes) bail("the shared store is full");
    try {
      buffer.grow(target);
    } catch {
      // Another thread grew it first, perhaps past what this one asked for.
    }
  }
};

const lockSegment = (locks: Int32Array, segment: number) => {
  while (Atomics.compareExchange(locks, segment, 0, 1) !== 0) {
    // Spin: a segment is held only while one value is looked up or added.
  }
};

const isEntry = (
  id: number,
  kind: number,
  payload: number,
  words: ArrayLike<number>,
  length: number,
  size: number,
  hash: number,
) => {
  if (hashes[id] !== hash || kinds[id] !== kind || sizes[id] !== size) return false;
  if (length === 0) return size !== 0 || payloads[id] === payload;
  const offset = payloads[id];
  for (let index = 0; index < length; index++)
    if (heap[offset + index] !== words[index]) return false;
  return true;
};

// Puts an id in its segment's table, the segment locked, growing the segment when half full.
const insertInSegment = (views: SharedViews, segment: number, id: number, hash: number) => {
  const directory = views.directory;
  const offset = directory[segment * 3];
  const mask = directory[segment * 3 + 1];
  let slot = hash & mask;
  while (views.arena[offset + slot] !== 0) slot = (slot + 1) & mask;
  views.arena[offset + slot] = id + 1;
  const used = ++directory[segment * 3 + 2];
  if (used * 2 <= mask + 1) return;
  const capacity = (mask + 1) * 2;
  const nextOffset = Atomics.add(views.counters, ARENA_TOP, capacity);
  growShared(views.buffers.arena, (nextOffset + capacity) * 4);
  const arena = views.arena;
  const nextMask = capacity - 1;
  for (let index = 0; index <= mask; index++) {
    const stored = arena[offset + index];
    if (stored === 0) continue;
    let target = hashes[stored - 1] & nextMask;
    while (arena[nextOffset + target] !== 0) target = (target + 1) & nextMask;
    arena[nextOffset + target] = stored;
  }
  directory[segment * 3] = nextOffset;
  directory[segment * 3 + 1] = nextMask;
};

const internShared = (
  kind: number,
  payload: number,
  words: ArrayLike<number>,
  length: number,
  size: number,
  hash: number,
) => {
  const views = shared!;
  const segment = hash >>> (32 - SEGMENT_BITS);
  lockSegment(views.locks, segment);
  const directory = views.directory;
  const offset = directory[segment * 3];
  const mask = directory[segment * 3 + 1];
  const arena = views.arena;
  for (let slot = hash & mask; ; slot = (slot + 1) & mask) {
    const stored = arena[offset + slot];
    if (stored === 0) break;
    if (isEntry(stored - 1, kind, payload, words, length, size, hash)) {
      Atomics.store(views.locks, segment, 0);
      return stored - 1;
    }
  }
  const counters = views.counters;
  const id = Atomics.add(counters, COUNT, 1);
  growShared(views.buffers.kinds, id + 1);
  growShared(views.buffers.payloads, (id + 1) * 4);
  growShared(views.buffers.sizes, (id + 1) * 4);
  growShared(views.buffers.hashes, (id + 1) * 4);
  let valuePayload = payload;
  if (length > 0) {
    valuePayload = Atomics.add(counters, HEAP_TOP, length);
    growShared(views.buffers.heap, (valuePayload + length) * 4);
    for (let index = 0; index < length; index++) heap[valuePayload + index] = words[index];
  }
  kinds[id] = kind;
  payloads[id] = valuePayload;
  sizes[id] = size;
  hashes[id] = hash;
  insertInSegment(views, segment, id, hash);
  Atomics.store(views.locks, segment, 0);
  return id;
};

const attachViews = (buffers: SharedStore): SharedViews => {
  kinds = new Uint8Array(buffers.kinds);
  payloads = new Int32Array(buffers.payloads);
  sizes = new Int32Array(buffers.sizes);
  hashes = new Int32Array(buffers.hashes);
  heap = new Int32Array(buffers.heap);
  return {
    buffers,
    counters: new Int32Array(buffers.counters),
    directory: new Int32Array(buffers.directory),
    locks: new Int32Array(buffers.locks),
    arena: new Int32Array(buffers.arena),
    isTextFrozen: false,
  };
};

// Moves the store into shared memory, keeping every id, so workers can join a search under way.
export const shareStore = (): SharedStore => {
  if (shared) return shared.buffers;
  const buffers: SharedStore = {
    kinds: createGrowable(Math.max(count, 1024)),
    payloads: createGrowable(Math.max(count, 1024) * 4),
    sizes: createGrowable(Math.max(count, 1024) * 4),
    hashes: createGrowable(Math.max(count, 1024) * 4),
    heap: createGrowable(Math.max(heapTop, 1024) * 4),
    counters: new SharedArrayBuffer(16),
    directory: new SharedArrayBuffer(SEGMENTS * 3 * 4),
    locks: new SharedArrayBuffer(SEGMENTS * 4),
    arena: createGrowable(SEGMENTS * INITIAL_SEGMENT_SLOTS * 4),
    texts,
    textRanks,
    textKinds,
    smallInts,
    emptySet: EMPTY_SET,
    emptyTuple: EMPTY_TUPLE,
  };
  new Uint8Array(buffers.kinds).set(kinds.subarray(0, count));
  new Int32Array(buffers.payloads).set(payloads.subarray(0, count));
  new Int32Array(buffers.sizes).set(sizes.subarray(0, count));
  new Int32Array(buffers.hashes).set(hashes.subarray(0, count));
  new Int32Array(buffers.heap).set(heap.subarray(0, heapTop));
  const counters = new Int32Array(buffers.counters);
  counters[COUNT] = count;
  counters[HEAP_TOP] = heapTop;
  counters[ARENA_TOP] = SEGMENTS * INITIAL_SEGMENT_SLOTS;
  const directory = new Int32Array(buffers.directory);
  for (let segment = 0; segment < SEGMENTS; segment++) {
    directory[segment * 3] = segment * INITIAL_SEGMENT_SLOTS;
    directory[segment * 3 + 1] = INITIAL_SEGMENT_SLOTS - 1;
  }
  const previousCount = count;
  const views = attachViews(buffers);
  for (let id = 0; id < previousCount; id++) {
    insertInSegment(views, hashes[id] >>> (32 - SEGMENT_BITS), id, hashes[id]);
  }
  shared = views;
  return buffers;
};

// Attaches a worker to the store a coordinator shared.
export const attachSharedStore = (buffers: SharedStore) => {
  generation++;
  shared = attachViews(buffers);
  shared.isTextFrozen = true;
  texts.length = 0;
  textRanks.length = 0;
  stringIds.clear();
  modelIds.clear();
  buffers.texts.forEach((text, index) => {
    texts.push(text);
    textRanks.push(buffers.textRanks[index]);
  });
  smallInts.set(buffers.smallInts);
  EMPTY_SET = buffers.emptySet;
  EMPTY_TUPLE = buffers.emptyTuple;
  // The ids of the texts, found again through the shared table.
  buffers.textKinds.forEach((kind, index) => {
    const id = internScalar(kind, index);
    (kind === KIND_STRING ? stringIds : modelIds).set(texts[index], id);
  });
};

// Stops new texts, once workers have the coordinator's list.
export const freezeTexts = () => {
  if (shared) shared.isTextFrozen = true;
};

// The store starts with the values every check has, once every declaration above exists.
resetStore();

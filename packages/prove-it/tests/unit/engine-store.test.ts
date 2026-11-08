// EXCEPT and record constructors look values up in place rather than through internBlock, so they
// must hash and compare exactly as it does: the same value has one id whichever path built it.

import { afterAll, beforeEach, describe, expect, it } from "bun:test";

import {
  appendTuple,
  concatTuples,
  createRecordShape,
  except,
  exceptAt,
  functionOf,
  functionOfSorted,
  getValueCount,
  int,
  recordOf,
  resetStore,
  setOf,
  setOfRange,
  setOfSorted,
  shareStore,
  sliceTuple,
  str,
  tupleOf,
} from "../../src/engine/store";

const ints = (values: number[]) => values.map(int);

// Workers share the store, which interns through a separate table.
describe.each(["local", "shared"])("the engine's %s store", (mode) => {
  beforeEach(() => {
    resetStore();
    if (mode === "shared") shareStore();
  });

  afterAll(() => resetStore());

  it("gives an EXCEPT result the id of the same tuple built directly", () => {
    const tuple = tupleOf(ints([1, 2, 3]), 3);
    const built = except(tuple, int(2), int(7));
    expect(tupleOf(ints([1, 7, 3]), 3)).toBe(built);
    const direct = tupleOf(ints([1, 2, 9]), 3);
    expect(except(tuple, int(3), int(9))).toBe(direct);
  });

  it("gives an EXCEPT result the id of the same function built directly", () => {
    // A domain that is a run of integers, and one of strings.
    for (const domain of [ints([0, 1, 2]), [str("a"), str("b"), str("c")]]) {
      const fn = functionOfSorted(domain, ints([5, 6, 7]), 3);
      const first = except(fn, domain[0], int(8));
      expect(functionOfSorted(domain, ints([8, 6, 7]), 3)).toBe(first);
      const direct = functionOfSorted(domain, ints([5, 6, 9]), 3);
      expect(except(fn, domain[2], int(9))).toBe(direct);
      // Updates out of order, and a key updated twice.
      expect(exceptAt(fn, [2, 1, 0, 1], ints([1, 4, 2, 3]), 4)).toBe(
        functionOfSorted(domain, ints([2, 3, 1]), 3),
      );
      expect(exceptAt(fn, [1, 1], ints([4, 6]), 2)).toBe(fn);
    }
  });

  it("gives a record the id of the same function built directly", () => {
    const keys = [str("x"), str("y")];
    const shape = createRecordShape(keys);
    const record = recordOf(shape, ints([1, 2]));
    expect(functionOfSorted(keys, ints([1, 2]), 2)).toBe(record);
    const direct = functionOfSorted(keys, ints([3, 4]), 2);
    expect(recordOf(shape, ints([3, 4]))).toBe(direct);
    expect(except(record, keys[1], int(4))).toBe(recordOf(shape, ints([1, 4])));
  });

  it("finds values again after the table and the heap grow", () => {
    const keys = [str("k")];
    const shape = createRecordShape(keys);
    const records = Array.from({ length: 20000 }, (_, index) => recordOf(shape, [int(index)]));
    const tuples = records.map((record) => except(tupleOf([record, record], 2), int(2), int(0)));
    const count = getValueCount();
    records.forEach((record, index) => {
      expect(functionOfSorted(keys, [int(index)], 1)).toBe(record);
      expect(tupleOf([record, int(0)], 2)).toBe(tuples[index]);
    });
    expect(getValueCount()).toBe(count);
  });

  it("sorts a set's elements and drops duplicates, short or long", () => {
    for (const length of [3, 16, 17, 100]) {
      const sorted = ints(Array.from({ length }, (_, index) => index));
      // Each element twice, in an order far from sorted.
      const shuffled = [...sorted, ...sorted].map((_, index) => sorted[(index * 37) % length]);
      expect(setOf(shuffled)).toBe(setOfSorted(sorted, length));
      // The elements from an offset, as the engine gathers them on its stack.
      const stack = Int32Array.from([int(-1), ...shuffled]);
      expect(setOfRange(stack, 1, shuffled.length)).toBe(setOfSorted(sorted, length));
    }
  });

  it("sorts a function's keys with their values", () => {
    const keys = [str("c"), str("a"), str("b")];
    expect(functionOf(keys, ints([3, 1, 2]))).toBe(
      functionOfSorted([str("a"), str("b"), str("c")], ints([1, 2, 3]), 3),
    );
    expect(functionOf(ints([3, 1, 2]), ints([7, 5, 6]))).toBe(tupleOf(ints([5, 6, 7]), 3));
  });

  it("builds a sequence's tail, append and concatenation as the tuple of their elements", () => {
    const tuple = tupleOf(ints([1, 2, 3]), 3);
    expect(sliceTuple(tuple, 1, 3)).toBe(tupleOf(ints([2, 3]), 2));
    expect(sliceTuple(tuple, 1, 1)).toBe(tupleOf([], 0));
    expect(appendTuple(tuple, int(4))).toBe(tupleOf(ints([1, 2, 3, 4]), 4));
    expect(concatTuples(tuple, tuple)).toBe(tupleOf(ints([1, 2, 3, 1, 2, 3]), 6));
    expect(concatTuples(tupleOf([], 0), tuple)).toBe(tuple);
  });
});

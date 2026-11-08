// EXCEPT and record constructors look values up in place rather than through internBlock, so they
// must hash and compare exactly as it does: the same value has one id whichever path built it.
// The native store (native/crates/tla-values) runs the same cases where the addon is built, with
// PROVE_IT_ENGINE_ADDON naming it, and must stop where the TypeScript store does, for the same
// reasons.

import { afterAll, beforeEach, describe, expect, it } from "bun:test";

import { fromValue, toValue } from "../../src/engine/convert";
import { nativeStore } from "../../src/engine/native-store";
import {
  appendTuple,
  Bailout,
  compare,
  concatTuples,
  createRecordShape,
  equals,
  except,
  exceptAt,
  functionOf,
  functionOfSorted,
  getValueCount,
  int,
  isMember,
  model,
  recordOf,
  resetStore,
  setOf,
  setOfRange,
  setOfSorted,
  shareStore,
  sliceTuple,
  str,
  TRUE,
  tupleOf,
} from "../../src/engine/store";
import { createStateEncoder } from "../../src/transfer";
import {
  createFunction,
  createModelValue,
  createRecord,
  createSet,
  createTuple,
  getStringRank,
  setStringOrder,
  type Value,
} from "../../src/values";

const localStore = {
  appendTuple,
  compare,
  concatTuples,
  createRecordShape,
  equals,
  except,
  exceptAt,
  functionOf,
  functionOfSorted,
  getValueCount,
  int,
  isMember,
  model,
  recordOf,
  resetStore,
  setOf,
  setOfRange,
  setOfSorted,
  sliceTuple,
  str,
  tupleOf,
};

const ADDON = process.env.PROVE_IT_ENGINE_ADDON;

// Workers share the store, which interns through a separate table.
const STORES: [string, typeof localStore][] = [
  ["local", localStore],
  ["shared", localStore],
  ...(ADDON === undefined ? [] : [["native", nativeStore] satisfies [string, typeof localStore]]),
];

describe.each(STORES)("the engine's %s store", (mode, store) => {
  const ints = (values: number[]) => values.map(store.int);

  beforeEach(() => {
    setStringOrder([]);
    store.resetStore();
    if (mode === "shared") shareStore();
  });

  afterAll(() => store.resetStore());

  it("gives an EXCEPT result the id of the same tuple built directly", () => {
    const tuple = store.tupleOf(ints([1, 2, 3]), 3);
    const built = store.except(tuple, store.int(2), store.int(7));
    expect(store.tupleOf(ints([1, 7, 3]), 3)).toBe(built);
    const direct = store.tupleOf(ints([1, 2, 9]), 3);
    expect(store.except(tuple, store.int(3), store.int(9))).toBe(direct);
  });

  it("gives an EXCEPT result the id of the same function built directly", () => {
    // A domain that is a run of integers, and one of strings.
    for (const domain of [ints([0, 1, 2]), [store.str("a"), store.str("b"), store.str("c")]]) {
      const fn = store.functionOfSorted(domain, ints([5, 6, 7]), 3);
      const first = store.except(fn, domain[0], store.int(8));
      expect(store.functionOfSorted(domain, ints([8, 6, 7]), 3)).toBe(first);
      const direct = store.functionOfSorted(domain, ints([5, 6, 9]), 3);
      expect(store.except(fn, domain[2], store.int(9))).toBe(direct);
      // Updates out of order, and a key updated twice.
      expect(store.exceptAt(fn, [2, 1, 0, 1], ints([1, 4, 2, 3]), 4)).toBe(
        store.functionOfSorted(domain, ints([2, 3, 1]), 3),
      );
      expect(store.exceptAt(fn, [1, 1], ints([4, 6]), 2)).toBe(fn);
    }
  });

  it("gives a record the id of the same function built directly", () => {
    const keys = [store.str("x"), store.str("y")];
    const shape = store.createRecordShape(keys);
    const record = store.recordOf(shape, ints([1, 2]));
    expect(store.functionOfSorted(keys, ints([1, 2]), 2)).toBe(record);
    const direct = store.functionOfSorted(keys, ints([3, 4]), 2);
    expect(store.recordOf(shape, ints([3, 4]))).toBe(direct);
    expect(store.except(record, keys[1], store.int(4))).toBe(store.recordOf(shape, ints([1, 4])));
  });

  it("ranks a model's name in TLC's order of strings, before the texts ranked after it", () => {
    store.model("m");
    expect(getStringRank("a")).toBeGreaterThan(getStringRank("m"));
  });

  // Some 80,000 calls, each of which crosses into the addon for the native store.
  it("finds values again after the table and the heap grow", () => {
    const keys = [store.str("k")];
    const shape = store.createRecordShape(keys);
    const records = Array.from({ length: 20000 }, (_, index) =>
      store.recordOf(shape, [store.int(index)]),
    );
    const tuples = records.map((record) =>
      store.except(store.tupleOf([record, record], 2), store.int(2), store.int(0)),
    );
    const count = store.getValueCount();
    records.forEach((record, index) => {
      expect(store.functionOfSorted(keys, [store.int(index)], 1)).toBe(record);
      expect(store.tupleOf([record, store.int(0)], 2)).toBe(tuples[index]);
    });
    expect(store.getValueCount()).toBe(count);
  }, 60_000);

  it("sorts a set's elements and drops duplicates, short or long", () => {
    for (const length of [3, 16, 17, 100]) {
      const sorted = ints(Array.from({ length }, (_, index) => index));
      // Each element twice, in an order far from sorted.
      const shuffled = [...sorted, ...sorted].map((_, index) => sorted[(index * 37) % length]);
      expect(store.setOf(shuffled)).toBe(store.setOfSorted(sorted, length));
      // The elements from an offset, as the engine gathers them on its stack.
      const stack = Int32Array.from([store.int(-1), ...shuffled]);
      expect(store.setOfRange(stack, 1, shuffled.length)).toBe(store.setOfSorted(sorted, length));
    }
  });

  it("sorts a function's keys with their values", () => {
    const keys = [store.str("c"), store.str("a"), store.str("b")];
    expect(store.functionOf(keys, ints([3, 1, 2]))).toBe(
      store.functionOfSorted([store.str("a"), store.str("b"), store.str("c")], ints([1, 2, 3]), 3),
    );
    expect(store.functionOf(ints([3, 1, 2]), ints([7, 5, 6]))).toBe(
      store.tupleOf(ints([5, 6, 7]), 3),
    );
  });

  it("builds a sequence's tail, append and concatenation as the tuple of their elements", () => {
    const tuple = store.tupleOf(ints([1, 2, 3]), 3);
    expect(store.sliceTuple(tuple, 1, 3)).toBe(store.tupleOf(ints([2, 3]), 2));
    expect(store.sliceTuple(tuple, 1, 1)).toBe(store.tupleOf([], 0));
    expect(store.appendTuple(tuple, store.int(4))).toBe(store.tupleOf(ints([1, 2, 3, 4]), 4));
    expect(store.concatTuples(tuple, tuple)).toBe(store.tupleOf(ints([1, 2, 3, 1, 2, 3]), 6));
    expect(store.concatTuples(store.tupleOf([], 0), tuple)).toBe(tuple);
  });

  it("orders strings by TLC's rank, ranked before unranked, and unranked by their text", () => {
    setStringOrder(["b", "a"]);
    store.resetStore();
    const [ranked, other, built, last] = ["a", "b", "zz", "c"].map(store.str);
    expect(Math.sign(store.compare(ranked, other))).toBe(1);
    expect(Math.sign(store.compare(other, built))).toBe(-1);
    expect(Math.sign(store.compare(last, built))).toBe(-1);
    expect(store.setOf([built, last, ranked, other])).toBe(
      store.setOfSorted([other, ranked, last, built], 4),
    );
  });

  it("stops where TLC fails to compare, for the TypeScript store's reasons", () => {
    const record = store.recordOf(store.createRecordShape([store.str("a")]), [store.int(1)]);
    const fn = store.functionOfSorted([store.int(0), store.int(1)], ints([1, 2]), 2);
    const typed = store.model("A_x");
    // Model values come first in a set, by rank, so the first element fails where the last doesn't.
    const models = store.setOf([store.model("B_y"), store.model("m")]);
    const cases: [() => unknown, string][] = [
      [() => store.compare(record, fn), "record compared with a function"],
      [() => store.equals(fn, record), "record compared with a function"],
      [() => store.compare(store.int(1), store.str("a")), "values TLC can't compare"],
      [() => store.equals(store.int(1), store.str("a")), "equality of values TLC can't compare"],
      [() => store.compare(typed, store.int(1)), "typed model value"],
      [() => store.equals(typed, store.model("B_y")), "differently typed model values"],
      [() => store.isMember(store.str("a"), store.setOf(ints([1, 2]))), "values TLC can't compare"],
      [() => store.setOf([store.int(1), store.str("a")]), "values TLC can't compare"],
      [() => store.isMember(typed, models), "differently typed model values"],
      [() => store.except(fn, store.int(5), store.int(0)), "EXCEPT outside the domain"],
      [() => store.int(2 ** 31), "integer overflow"],
    ];
    for (const [operation, reason] of cases) expect(operation).toThrow(new Bailout(reason));
    // An untyped model value is less than any other value.
    expect(store.setOf([store.int(1), store.model("m")])).toBe(
      store.setOfSorted([store.model("m"), store.int(1)], 2),
    );
  });

  // Cases the value oracle found: TLC's SetEnumValue.member binary-searches the set with the
  // element's compareTo, and fails where that fails.
  it("stops a membership where TLC's search of the set fails to compare", () => {
    const record = (values: number[]) =>
      store.recordOf(
        store.createRecordShape(values.map((_, index) => store.str("abc"[index]))),
        values.map(store.int),
      );
    const tuples = store.setOf([1, 2].map((value) => store.tupleOf([store.int(value)], 1)));
    const nested = store.setOf([store.tupleOf([record([1])], 1)]);
    const long = store.setOf(
      Array.from({ length: 40 }, (_, index) => store.tupleOf([store.int(index)], 1)),
    );
    const fn = store.functionOfSorted(ints([0, 1]), ints([5, 5]), 2);
    const cases: [() => unknown, string][] = [
      [() => store.isMember(record([0]), tuples), "values TLC can't compare"],
      [() => store.isMember(record([0, 1]), tuples), "record compared with a function"],
      [
        () => store.isMember(store.tupleOf([store.int(1)], 1), store.setOf([record([1])])),
        "values TLC can't compare",
      ],
      [
        () => store.isMember(store.tupleOf([store.tupleOf(ints([2]), 1)], 1), nested),
        "values TLC can't compare",
      ],
      [() => store.isMember(record([0]), long), "values TLC can't compare"],
      [() => store.isMember(record([0]), store.setOf([fn])), "record compared with a function"],
    ];
    for (const [operation, reason] of cases) expect(operation).toThrow(new Bailout(reason));
  });

  it("answers a miss among records of several sizes, which TLC compares without failing", () => {
    const kind = store.str("kind");
    const from = store.str("from");
    const messages = store.setOf([
      store.recordOf(store.createRecordShape([kind]), [store.str("abort")]),
      ...[1, 2, 3].map((participant) =>
        store.recordOf(store.createRecordShape([from, kind]), [
          store.model(`p${participant}`),
          store.str("prepared"),
        ]),
      ),
    ]);
    const commit = store.recordOf(store.createRecordShape([kind]), [store.str("commit")]);
    expect(store.isMember(commit, messages)).toBe(false);
    // Asked again, of a set of the same structure, and with a member whose field TLC can't compare.
    expect(store.isMember(commit, store.setOf([commit]))).toBe(true);
    const typed = store.recordOf(store.createRecordShape([kind]), [store.model("A_x")]);
    expect(() => store.isMember(typed, messages)).toThrow(new Bailout("typed model value"));
  });

  it("stops a membership TLC's search passes but its equals of a set enumeration fails", () => {
    // A_x ranks before m, so TRUE's search ends past m without comparing it with A_x. TLC checks a
    // set it hasn't normalized with each element's equals, which fails on A_x.
    const set = store.setOf([store.model("A_x"), store.model("m")]);
    expect(() => store.isMember(TRUE, set)).toThrow(new Bailout("typed model value"));
    expect(store.isMember(store.model("p"), set)).toBe(false);
  });
});

describe.if(ADDON !== undefined)("the native store's transfer encoding", () => {
  it("writes the words transfer.ts writes for the interpreter's values of the same ids", () => {
    setStringOrder(["b", "m"]);
    resetStore();
    nativeStore.resetStore();
    const values: Value[] = [
      createRecord([
        ["b", 1],
        ["a", createTuple([true, "\ud800"])],
      ]),
      createFunction([
        [0, createModelValue("m")],
        [-5, createSet([3, 1, 2])],
      ]),
      createTuple([]),
      createSet([createTuple([2, 3]), createTuple([1])]),
      -2147483648,
      "b",
    ];
    const expected = createStateEncoder();
    expected.encode(values.map((value) => toValue(fromValue(value))));
    const ids = Int32Array.from(values.map(nativeStore.fromValue));
    const encoded = nativeStore.encodeStates(ids, 1, values.length);
    expect({ ...encoded, words: [...encoded.words] }).toEqual({
      ...expected.finish(),
      words: [...expected.finish().words],
    });
  });
});

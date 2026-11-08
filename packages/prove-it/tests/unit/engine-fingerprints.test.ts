// The engine fingerprints most states from their parent's fingerprint, and an initial state from
// the one before it. These tests check it against the interpreter's fingerprints of the same values,
// and against the engine fingerprinting every state from scratch on whole searches. The native
// store's fingerprints (native/crates/tla-values) run the same cases on its own values where the
// addon is built, with PROVE_IT_ENGINE_ADDON naming it.

import { afterEach, describe, expect, it, spyOn } from "bun:test";

import { check } from "../../src";
import { fromValue } from "../../src/engine/convert";
import {
  getStateFingerprints,
  getStateFingerprintsReference,
  resetFingerprints,
} from "../../src/engine/fingerprint";
import { nativeStore } from "../../src/engine/native-store";
import { resetStore } from "../../src/engine/store";
import { getTlcFingerprint } from "../../src/tlc/fingerprint";
import {
  createModelValue,
  createRecord,
  createSet,
  createTuple,
  type Value,
} from "../../src/values";

const settings = {
  engine: process.env.PROVE_IT_ENGINE,
  fingerprint: process.env.PROVE_IT_FINGERPRINT,
};

afterEach(() => {
  for (const [name, setting] of [
    ["PROVE_IT_ENGINE", settings.engine],
    ["PROVE_IT_FINGERPRINT", settings.fingerprint],
  ] as const) {
    if (setting === undefined) delete process.env[name];
    else process.env[name] = setting;
  }
});

const localStore = {
  fromValue,
  getStateFingerprints,
  getStateFingerprintsReference,
  resetFingerprints,
  resetStore,
};

const STORES: [string, typeof localStore][] = [
  ["the TypeScript store", localStore],
  ...(process.env.PROVE_IT_ENGINE_ADDON === undefined
    ? []
    : [["the native store", nativeStore] satisfies [string, typeof localStore]]),
];

describe.each(STORES)("the fingerprints of %s's states", (_, store) => {
  it("match TLC's whichever parent each state names", () => {
    // A search resets the store before it interns values, as this test does, and the fingerprints
    // of values along with it, whose ids they are by.
    store.resetStore();
    store.resetFingerprints();
    // Several values share a length, so that many changes from a parent keep the lengths.
    const values: Value[] = [
      true,
      false,
      0,
      7,
      -2147483648,
      "a",
      "b",
      "long string ".repeat(30),
      createModelValue("m1"),
      createModelValue("m2"),
      createSet([]),
      createSet([1]),
      createSet([2]),
      createSet([1, 2, 3]),
      createRecord([
        ["type", "req"],
        ["n", 1],
      ]),
      createRecord([
        ["type", "ack"],
        ["n", 2],
      ]),
      createTuple([createSet([1, 2]), "a"]),
    ];
    const ids = values.map(store.fromValue);
    let seed = 12345;
    const random = (bound: number) => {
      seed = (Math.imul(seed, 1103515245) + 12345) >>> 0;
      return (seed >>> 8) % bound;
    };
    const width = 5;
    const count = 3000;
    const rows: number[][] = [];
    const parents = new Int32Array(count);
    for (let state = 0; state < count; state++) {
      const parent = state < 3 ? -1 : random(state + 1) - 1;
      parents[state] = parent;
      const row =
        parent >= 0 ? [...rows[parent]] : Array.from({ length: width }, () => random(ids.length));
      for (let change = random(3); change > 0; change--) row[random(width)] = random(ids.length);
      rows.push(row);
    }
    const states = Int32Array.from(rows.flatMap((row) => row.map((index) => ids[index])));
    const order = [3, 0, 4, 1, 2];
    const expected = rows.map((row) =>
      BigInt.asIntN(64, getTlcFingerprint(order.map((position) => values[row[position]]))),
    );
    expect([...store.getStateFingerprints(states, count, width, order, parents)]).toEqual(expected);
    expect([...store.getStateFingerprintsReference(states, count, width, order)]).toEqual(expected);
    expect([...store.getStateFingerprints(states, count, width, order)]).toEqual(expected);
  });

  it("match TLC's for initial states, each from the one before it", () => {
    store.resetStore();
    store.resetFingerprints();
    // The first two values of each kind share a length, so most states keep the lengths of the one
    // before them, and the third doesn't.
    const kinds: Value[][] = [
      [1, 2, "long string"],
      ["a", "b", "cc"],
      [createSet([1]), createSet([2]), createSet([1, 2])],
      [true, false, createModelValue("m1")],
    ];
    const ids = kinds.map((values) => values.map(store.fromValue));
    const rows: number[][] = [];
    // Odometer order, as TLC enumerates an initial predicate's states.
    for (let first = 0; first < 3; first++)
      for (let second = 0; second < 3; second++)
        for (let third = 0; third < 3; third++)
          for (let fourth = 0; fourth < 3; fourth++) rows.push([first, second, third, fourth]);
    const width = kinds.length;
    const states = Int32Array.from(
      rows.flatMap((row) => row.map((index, kind) => ids[kind][index])),
    );
    const order = [2, 0, 3, 1];
    const expected = rows.map((row) =>
      BigInt.asIntN(64, getTlcFingerprint(order.map((kind) => kinds[kind][row[kind]]))),
    );
    const parents = new Int32Array(rows.length).fill(-1);
    expect([...store.getStateFingerprints(states, rows.length, width, order, parents)]).toEqual(
      expected,
    );
  });
});

describe("the fingerprints of the engine's states", () => {
  it("report the same collision probability as the interpreter for many initial states", async () => {
    // Enough initial states that TLC reports the probability from the actual fingerprints, with
    // strings of two lengths among them.
    const source = [
      "---- MODULE M ----",
      "EXTENDS Naturals",
      "VARIABLES x, y, z",
      'Init == x \\in 1..120 /\\ y \\in {"a", "bb", "c"} /\\ z \\in 1..250',
      "Next == UNCHANGED <<x, y, z>>",
      "====",
    ].join("\n");
    const config = "INIT Init\nNEXT Next";
    delete process.env.PROVE_IT_ENGINE;
    const result = await check({ source, config, onPrint: () => {} });
    process.env.PROVE_IT_ENGINE = "0";
    const reference = await check({ source, config, onPrint: () => {} });
    expect(result.fingerprintDistance).toBeDefined();
    expect(result).toEqual(reference);
  });

  // Each search is large enough for the summary to ask for the fingerprints, and the check
  // setting hands the search over if any differs from the reference.
  it.each([
    [
      "sets that grow and records that change in place",
      [
        "EXTENDS Naturals",
        "VARIABLES s, r, n",
        'Init == s = {} /\\ r = [a |-> 0, b |-> "x"] /\\ n = 0',
        "Next == \\/ \\E e \\in 1..11 : s' = s \\cup {e} /\\ UNCHANGED <<r, n>>",
        "        \\/ n < 7 /\\ n' = n + 1 /\\ r' = [r EXCEPT !.a = n] /\\ UNCHANGED s",
        '        \\/ r\' = [r EXCEPT !.b = IF r.b = "x" THEN "yy" ELSE "x"] /\\ UNCHANGED <<s, n>>',
      ].join("\n"),
      "INIT Init\nNEXT Next",
    ],
    [
      "symmetry",
      [
        "EXTENDS Naturals, TLC",
        "CONSTANT P",
        "VARIABLES x, z",
        "Init == x = [p \\in P |-> 0] /\\ z = 0",
        "Next == \\/ \\E p \\in P : x' = [x EXCEPT ![p] = (x[p] + 1) % 21] /\\ UNCHANGED z",
        "        \\/ z' = (z + 1) % 31 /\\ UNCHANGED x",
        "Sym == Permutations(P)",
      ].join("\n"),
      "CONSTANT P = {p1, p2, p3}\nINIT Init\nNEXT Next\nSYMMETRY Sym",
    ],
    [
      "a VIEW",
      [
        "EXTENDS Naturals",
        "VARIABLES a, b",
        "Init == a = 0 /\\ b = 0",
        "Next == \\/ a' = (a + 1) % 300 /\\ UNCHANGED b",
        "        \\/ b' = (b + 1) % 300 /\\ UNCHANGED a",
        "        \\/ a' = (a + b) % 300 /\\ UNCHANGED b",
        "View == <<a, b % 200>>",
      ].join("\n"),
      "INIT Init\nNEXT Next\nVIEW View",
    ],
  ])("match the reference on a search with %s", async (_, body, config) => {
    process.env.PROVE_IT_ENGINE = "debug";
    process.env.PROVE_IT_FINGERPRINT = "check";
    const lines: string[] = [];
    const spy = spyOn(console, "error").mockImplementation((message: unknown) => {
      if (typeof message === "string" && message.startsWith("[engine] ")) lines.push(message);
    });
    try {
      const result = await check({ source: `---- MODULE M ----\n${body}\n====`, config });
      expect(result.status).toBe("success");
      expect(result.fingerprintDistance).toBeDefined();
      expect(lines.some((line) => line.startsWith("[engine] checked"))).toBe(true);
      expect(lines.filter((line) => line.includes("handed over"))).toEqual([]);
    } finally {
      spy.mockRestore();
    }
  });
});

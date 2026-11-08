// The engine fingerprints most states from their parent's fingerprint. These tests check it against
// the interpreter's fingerprints of the same values, and against the engine fingerprinting every
// state from scratch on whole searches.

import { afterEach, describe, expect, it, spyOn } from "bun:test";

import { check } from "../../src";
import { fromValue } from "../../src/engine/convert";
import { getStateFingerprints, getStateFingerprintsReference } from "../../src/engine/fingerprint";
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

describe("the fingerprints of the engine's states", () => {
  it("match TLC's whichever parent each state names", () => {
    // A search resets the store before it interns values, as this test does.
    resetStore();
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
    const ids = values.map(fromValue);
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
    expect([...getStateFingerprints(states, count, width, order, parents)]).toEqual(expected);
    expect([...getStateFingerprintsReference(states, count, width, order)]).toEqual(expected);
    expect([...getStateFingerprints(states, count, width, order)]).toEqual(expected);
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

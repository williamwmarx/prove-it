// The sets TLC keeps lazy, which the native engine enumerates in TLC's order: where an action
// assigns a variable from one (the order the set streams in, duplicates and all) and where it
// quantifies over one (the order of the enumerated set). Each must give the TypeScript engine's
// state log, whose order is the interpreter's, and the interpreter's result.

import { afterEach, describe, expect, it } from "bun:test";

import {
  ADDON,
  compareStateLogs,
  compareWithInterpreter,
  COMPLETE,
  restoreSettings,
  run,
  toModule,
} from "./native-runs";

afterEach(restoreSettings);

const CONFIG = "INIT Init\nNEXT Next";

// Sets of each lazy kind, over normalized and lazy components.
const LAZY_SETS = [
  "SUBSET {1, 2, 3}",
  "SUBSET (SUBSET {1, 2})",
  "[{1, 2} -> {3, 4, 5}]",
  "[SUBSET {1} -> {TRUE, FALSE}]",
  "[{1, 2} -> SUBSET {3}]",
  "[{} -> {1}]",
  "[{1} -> {}]",
  '[a : {1, 2}, b : {"x", "y"}]',
  '[b : SUBSET {1}, a : {"x"}]',
  "[a : {1}, b : {}]",
  "{1, 2} \\X {3, 4} \\X {5}",
  "(SUBSET {1, 2}) \\X {0}",
  "{s \\in SUBSET {1, 2, 3} : 2 \\in s}",
  "{f \\in [{1, 2} -> {3, 4}] : f[1] = 3}",
  "(SUBSET {1, 2}) \\ {{1}}",
  "(SUBSET {1, 2}) \\ SUBSET {2}",
  "(SUBSET {1, 2}) \\cap SUBSET {2, 3}",
  "{{1}, {4}} \\cap SUBSET {1, 2}",
  "(SUBSET {1, 2}) \\cup {{5}}",
  "{{5}, {}} \\cup SUBSET {1, 2}",
  "(SUBSET {1, 2}) \\cup SUBSET {2, 3}",
  "[{1} -> {3, 4}] \\cup [{1} -> {4, 5}]",
  "[{1, 2} -> {3} \\cup {4}]",
  "[{1} -> (SUBSET {1}) \\cup SUBSET {2}]",
  "((SUBSET {1}) \\cup SUBSET {2}) \\X {0}",
  "[a : (SUBSET {1}) \\cup SUBSET {2}]",
  "{s \\in (SUBSET {1}) \\cup SUBSET {2} : TRUE}",
  "IF y = 0 THEN SUBSET {1, 2} ELSE [{1} -> {2, 3}]",
  "SUBSET {} ",
];

// UNIONs TLC keeps lazy: of sets it keeps lazy, of intervals, of a set map, and over a lazy set.
const UNION_SETS = [
  "UNION {SUBSET {1, 2}, {{7}}, SUBSET {3}}",
  "UNION {[{1} -> {3, 4}], [{2} -> {5}]}",
  "UNION {1..2, {5}, 2..3}",
  "UNION {[1..n -> 1..n] : n \\in 0..2}",
  "UNION SUBSET {1, 2}",
  "UNION {s \\in SUBSET {1, 2, 3} : 2 \\in s}",
  "UNION ((SUBSET {1}) \\cup {{4}, {1}})",
  "UNION {SUBSET {1}}",
  "{{1}, {3}} \\cap UNION {SUBSET {1}, SUBSET {2}}",
  "IF y = 0 THEN UNION {1..2, {7}} ELSE {}",
];

describe.if(ADDON !== undefined)("the native engine's lazy sets", () => {
  for (const [index, set] of LAZY_SETS.entries()) {
    it(`enumerates ${set} in TLC's order`, async () => {
      // x' \in S takes the streamed order, which generates an element twice where a union
      // streams it from both its sets; \E and a walked \A take the enumerated order.
      const body = [
        "EXTENDS Naturals",
        "VARIABLES x, y",
        `S == ${set}`,
        "Init == x = 0 /\\ y = 0",
        "Next == \\/ x' \\in S /\\ y' = 1",
        "        \\/ \\E e \\in S : x' = e /\\ y' = 2",
        `        \\/ (${set}) # {} /\\ \\A e \\in S : x' = <<${index}>> /\\ y' = 3`,
        "        \\/ UNCHANGED <<x, y>>",
      ];
      for (const isWarningEnabled of [false, true]) {
        expect(await compareStateLogs(body, CONFIG, isWarningEnabled)).toContainEqual(
          expect.stringMatching(COMPLETE),
        );
      }
      expect(await compareWithInterpreter(body, CONFIG)).toContainEqual(
        expect.stringMatching(COMPLETE),
      );
    });
  }

  // TLC streams the sets of a UNION it keeps lazy in turn (UnionValue.Enumerator), which the
  // TypeScript engine refuses: each must give the interpreter's result.
  for (const [index, set] of UNION_SETS.entries()) {
    it(`enumerates ${set} in TLC's order`, async () => {
      const body = [
        "EXTENDS Naturals",
        "VARIABLES x, y",
        `S == ${set}`,
        "Init == x = 0 /\\ y = 0",
        "Next == \\/ x' \\in S /\\ y' = 1",
        "        \\/ \\E e \\in S : x' = e /\\ y' = 2",
        `        \\/ (${set}) # {} /\\ \\A e \\in S : x' = <<${index}>> /\\ y' = 3`,
        "        \\/ UNCHANGED <<x, y>>",
      ];
      expect(await compareWithInterpreter(body, CONFIG)).toContainEqual(
        expect.stringMatching(COMPLETE),
      );
    });
  }

  it("streams each set of a UNION in turn, as TLC counts it", async () => {
    const body = [
      "VARIABLE x",
      "Init == x \\in UNION {SUBSET {1, 2}, SUBSET {2, 3}}",
      "Next == UNCHANGED x",
    ];
    const native = await run(
      { source: toModule(body), config: CONFIG },
      { PROVE_IT_ENGINE: "debug", PROVE_IT_ENGINE_BACKEND: "rust" },
    );
    expect(native.lines).toContainEqual(expect.stringMatching(COMPLETE));
    // {} and {2} come up from both sets: 8 initial states and 6 steps.
    expect([native.result.generatedStates, native.result.distinctStates]).toEqual([14, 6]);
    await compareWithInterpreter(body, CONFIG);
  });

  it("streams an element of both sets of a union twice, as TLC counts it", async () => {
    const body = [
      "VARIABLE x",
      "Init == x \\in (SUBSET {1, 2}) \\cup SUBSET {2, 3}",
      "Next == UNCHANGED x",
    ];
    const native = await run(
      { source: toModule(body), config: CONFIG },
      { PROVE_IT_ENGINE: "debug", PROVE_IT_ENGINE_BACKEND: "rust" },
    );
    expect(native.lines).toContainEqual(expect.stringMatching(COMPLETE));
    // {} and {2} come up from both sets.
    expect([native.result.generatedStates, native.result.distinctStates]).toEqual([14, 6]);
    await compareWithInterpreter(body, CONFIG);
  });

  it("stops where TLC can't enumerate a set, and the interpreter reports it", async () => {
    for (const set of ["[{1} -> Nat]", "SUBSET Nat", "{1} \\X STRING", "{s \\in SUBSET {1} : s}"]) {
      const body = [
        "EXTENDS Naturals",
        "VARIABLE x",
        `Init == x \\in ${set}`,
        "Next == UNCHANGED x",
      ];
      expect(await compareWithInterpreter(body, CONFIG)).toContainEqual(
        expect.stringMatching(/^\[engine\] native: stopped: /),
      );
    }
  });

  it("leaves a set it has no order for, as the TypeScript engine does", async () => {
    // TLC streams the union in the UNION, duplicates and all, which neither engine follows once it
    // holds the union as an id, nor where a bound name may hold it.
    for (const set of [
      "UNION {(SUBSET {1}) \\cup SUBSET {2}}",
      "UNION {s : s \\in {(SUBSET {1}) \\cup SUBSET {2}}}",
      "UNION {[{1} -> s] : s \\in {(SUBSET {1}) \\cup SUBSET {2}}}",
      "UNION {IF s = {} THEN {} ELSE s : s \\in {(SUBSET {1}) \\cup SUBSET {2}}}",
    ]) {
      const body = ["VARIABLE x", `Init == x \\in ${set}`, "Next == UNCHANGED x"];
      const lines = await compareWithInterpreter(body, CONFIG);
      expect(lines).toEqual([
        expect.stringMatching(/^\[engine\] native: ir: /),
        expect.stringMatching(/^\[engine\] native: declined: unsupported: enumerating a set TLC /),
        expect.stringMatching(/^\[engine\] handed over after \d+ ms: unsupported: enumerating /),
      ]);
    }
  });

  it("leaves a UNION of a variable the initial predicate assigned", async () => {
    // TLC fingerprints a state only once the initial predicate has assigned it.
    const body = [
      "VARIABLES s, x",
      "Init == s = (SUBSET {1}) \\cup SUBSET {2} /\\ x \\in UNION {s}",
      "Next == UNCHANGED <<s, x>>",
    ];
    expect(await compareWithInterpreter(body, CONFIG)).toContainEqual(
      expect.stringMatching(/^\[engine\] native: declined: unsupported: enumerating a set TLC /),
    );
    // An alias an invariant compiled first, outside the initial predicate, as well.
    const aliased = [
      "VARIABLES s, x",
      "Alias == s",
      "Same == Alias = Alias",
      "Init == s = (SUBSET {1}) \\cup SUBSET {2} /\\ x \\in UNION {Alias}",
      "Next == UNCHANGED <<s, x>>",
    ];
    expect(await compareWithInterpreter(aliased, `${CONFIG}\nINVARIANT Same`)).toContainEqual(
      expect.stringMatching(/^\[engine\] native: declined: unsupported: enumerating a set TLC /),
    );
  });
});

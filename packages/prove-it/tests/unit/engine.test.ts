// The engine hands a model to the interpreter where it can't go on, and the interpreter's answer is
// the same either way, so these tests check that the engine itself finished the search: a wrong
// value in the engine shows up as a hand-over, not as a wrong answer.

import { afterEach, describe, expect, it, spyOn } from "bun:test";

import { check } from "../../src";

const setting = process.env.PROVE_IT_ENGINE;

afterEach(() => {
  if (setting === undefined) delete process.env.PROVE_IT_ENGINE;
  else process.env.PROVE_IT_ENGINE = setting;
});

const checkInEngine = async (body: string, config: string) => {
  process.env.PROVE_IT_ENGINE = "debug";
  const lines: string[] = [];
  const spy = spyOn(console, "error").mockImplementation((message: unknown) => {
    if (typeof message === "string" && message.startsWith("[engine] ")) lines.push(message);
  });
  try {
    const result = await check({ source: `---- MODULE M ----\n${body}\n====`, config });
    return { result, lines };
  } finally {
    spy.mockRestore();
  }
};

const FOLD = [
  "MapThenFoldSet(op(_, _), base, f(_), choose(_), S) ==",
  "  LET it[s \\in SUBSET S] ==",
  "        IF s = {} THEN base ELSE LET x == choose(s) IN op(f(x), it[s \\ {x}])",
  "  IN it[S]",
  "FoldFunction(op(_, _), base, fun) ==",
  "  MapThenFoldSet(op, base, LAMBDA i : fun[i], LAMBDA s : CHOOSE x \\in s : TRUE, DOMAIN fun)",
].join("\n");

describe("the engine", () => {
  it("builds a record again while a field of it recurses into the same record", async () => {
    // Three variables make the recursive call too wide to cache, so each field reads it afresh.
    const { result, lines } = await checkInEngine(
      [
        "EXTENDS Naturals, Sequences",
        FOLD,
        "VARIABLES m, a, b",
        "R(n, d) == [num |-> n, den |-> d]",
        "Zero == R(0, 1)",
        "Add(p, q) == IF p = Zero THEN q ELSE",
        "  LET l == IF p.den > q.den THEN p.den ELSE q.den",
        "      qq == R(q.num * (l \\div q.den), l)",
        "      pp == R(p.num * (l \\div p.den), l)",
        "  IN R(qq.num + pp.num, l)",
        "Init == a = 0 /\\ b = 0 /\\ m = <<R(1, 2), R(1, 4)>>",
        "Next == UNCHANGED <<m, a, b>>",
        "Inv == FoldFunction(Add, Zero, m) = R(3, 4)",
      ].join("\n"),
      "INIT Init\nNEXT Next\nINVARIANT Inv",
    );
    expect(result.status).toBe("success");
    expect(lines).toEqual([expect.stringMatching(/^\[engine\] checked 1 states/)]);
  });

  it("keeps the names a recursive function binds apart in each call", async () => {
    const { result, lines } = await checkInEngine(
      [
        "EXTENDS Sequences",
        "VARIABLE v",
        "Perms(S) == LET p[s \\in SUBSET S] ==",
        "  IF s = {} THEN {<<>>}",
        "  ELSE LET q == [x \\in s |-> {Append(t, x) : t \\in p[s \\ {x}]}] IN UNION {q[x] : x \\in s}",
        "  IN p[S]",
        "Init == v = <<>>",
        "Next == \\E t \\in Perms({1, 2, 3}) : v' = t",
      ].join("\n"),
      "INIT Init\nNEXT Next",
    );
    expect(result.distinctStates).toBe(7);
    expect(lines).toEqual([expect.stringMatching(/^\[engine\] checked 7 states/)]);
  });

  it("walks the body of a LET's function that an action applies", async () => {
    const { result, lines } = await checkInEngine(
      [
        "EXTENDS Integers",
        "VARIABLES m, x",
        "Init == m \\in [{1, 2} -> -1..2] /\\ x = -5",
        "Safe(b) == LET f[c \\in 0..2] == c = 0 \\/ \\A i \\in {1, 2} : m[i] >= c IN f[b]",
        "Next == \\E b \\in 0..2 : Safe(b) /\\ x' = b /\\ UNCHANGED m",
      ].join("\n"),
      "INIT Init\nNEXT Next",
    );
    expect([result.generatedStates, result.distinctStates]).toEqual([93, 37]);
    expect(lines).toEqual([expect.stringMatching(/^\[engine\] checked 37 states/)]);
  });

  it("reads Nat as the set the model substitutes for it", async () => {
    const { result, lines } = await checkInEngine(
      "EXTENDS Integers\nVARIABLE x\nInit == x = 0\nNext == UNCHANGED x\nInv == -1 \\in Nat",
      "CONSTANT Nat <- Int\nINIT Init\nNEXT Next\nINVARIANT Inv",
    );
    expect(result.status).toBe("success");
    expect(lines).toEqual([expect.stringMatching(/^\[engine\] checked 1 states/)]);
  });
});

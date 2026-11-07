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

  it("finds the same states with continuations shared or steps in functions of their own", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLES x, y, z",
      "Init == x = 0 /\\ y = 0 /\\ z = 0",
      "Next == /\\ \\/ x' = (x + 1) % 3 \\/ x' = x",
      "        /\\ IF x = 1 THEN y' = (y + 1) % 4 ELSE y' \\in {y, 0}",
      "        /\\ CASE y = 2 -> z' = (z + 2) % 5 [] y = 3 -> UNCHANGED z [] OTHER -> z' \\in {z, 1}",
      "        /\\ x' + y' + z' < 8",
    ].join("\n");
    const codegen = process.env.PROVE_IT_CODEGEN;
    try {
      const config = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE";
      const inline = await checkInEngine(body, config);
      for (const setting of ["share", "hoist"]) {
        process.env.PROVE_IT_CODEGEN = setting;
        const other = await checkInEngine(body, config);
        expect([other.result.generatedStates, other.result.distinctStates]).toEqual([
          inline.result.generatedStates,
          inline.result.distinctStates,
        ]);
        expect(other.lines).toEqual([expect.stringMatching(/^\[engine\] checked/)]);
      }
    } finally {
      if (codegen === undefined) delete process.env.PROVE_IT_CODEGEN;
      else process.env.PROVE_IT_CODEGEN = codegen;
    }
  });

  it("builds a record of many variables again for each state it expands", async () => {
    // Self(r) reads seven variables, too many for a memo table, so the engine keeps it only while
    // one state is current: a value kept from another state would find other successors.
    const { result, lines } = await checkInEngine(
      [
        "EXTENDS Naturals",
        "VARIABLES a, b, c, d, e, f, g",
        "P == {1, 2}",
        "Init == /\\ a = [p \\in P |-> 0] /\\ b = [p \\in P |-> 0] /\\ c = [p \\in P |-> 0]",
        "        /\\ d = [p \\in P |-> 0] /\\ e = [p \\in P |-> 0] /\\ f = [p \\in P |-> 0]",
        "        /\\ g = [p \\in P |-> 0]",
        "Self(r) == [a |-> a[r], b |-> b[r], c |-> c[r], d |-> d[r], e |-> e[r], f |-> f[r], g |-> g[r]]",
        "Step(r, s) == /\\ s.a < 3",
        "              /\\ a' = [a EXCEPT ![r] = s.a + 1]",
        "              /\\ b' = [b EXCEPT ![r] = (s.b + s.a) % 2]",
        "              /\\ c' = [c EXCEPT ![r] = s.b]",
        "              /\\ d' = [d EXCEPT ![r] = s.c]",
        "              /\\ e' = [e EXCEPT ![r] = s.d]",
        "              /\\ f' = [f EXCEPT ![r] = s.e]",
        "              /\\ g' = [g EXCEPT ![r] = (s.f + s.g + r) % 3]",
        "Next == \\E r \\in P : Step(r, Self(r))",
      ].join("\n"),
      "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
    );
    expect([result.generatedStates, result.distinctStates]).toEqual([25, 16]);
    expect(lines).toEqual([expect.stringMatching(/^\[engine\] checked 16 states/)]);
  });

  it("checks a constraint or invariant again only on steps that change what it reads", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLES x, y",
      "Init == x = 0 /\\ y = 0",
      "Next == \\/ x' = x + 1 /\\ UNCHANGED y",
      "        \\/ y' = y + 1 /\\ UNCHANGED x",
      "BoundX == x <= 3",
      "BoundY == y <= 2",
      "Sum == x + y <= 6",
      "SmallX == x < 3",
    ].join("\n");
    const bounded = await checkInEngine(
      body,
      "INIT Init\nNEXT Next\nCONSTRAINT BoundX BoundY\nINVARIANT Sum\nCHECK_DEADLOCK FALSE",
    );
    expect([bounded.result.generatedStates, bounded.result.distinctStates]).toEqual([25, 12]);
    expect(bounded.lines).toEqual([expect.stringMatching(/^\[engine\] checked 12 states/)]);
    const violated = await checkInEngine(
      body,
      "INIT Init\nNEXT Next\nCONSTRAINT BoundY\nINVARIANT SmallX\nCHECK_DEADLOCK FALSE",
    );
    expect(violated.result.status).not.toBe("success");
    expect(violated.lines).toEqual([expect.stringMatching(/an invariant violated$/)]);
  });

  it("settles mutually recursive operators together, whichever compiles first", async () => {
    // Q compiles first and R inside it, while Q's footprint is still growing: R reads x' through
    // Q, so W2, too wide for a memo table, can't be kept while the state is current.
    const { result, lines } = await checkInEngine(
      [
        "EXTENDS Naturals",
        "VARIABLES a, b, c, d, e, f, g, h, x",
        "RECURSIVE Q(_), R(_)",
        "Q(n) == IF n = 0 THEN x' ELSE R(n - 1)",
        "R(n) == Q(n) + b + c + d + e + f + g + h",
        "W2 == R(1)",
        "Init == /\\ a = 0 /\\ x = 0",
        "        /\\ b = 0 /\\ c = 0 /\\ d = 0 /\\ e = 0 /\\ f = 0 /\\ g = 0 /\\ h = 0",
        "Next == /\\ a < 3",
        "        /\\ \\E v \\in {1, 3} :",
        "             /\\ x' = v",
        "             /\\ Q(2) >= 0",
        "             /\\ a' = a + W2",
        "             /\\ UNCHANGED <<b, c, d, e, f, g, h>>",
      ].join("\n"),
      "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
    );
    expect([result.generatedStates, result.distinctStates]).toEqual([7, 7]);
    expect(lines).toEqual([expect.stringMatching(/^\[engine\] checked 7 states/)]);
    // The same for a memo table: R's key reads a, which only Q reads.
    const narrow = await checkInEngine(
      [
        "EXTENDS Naturals",
        "VARIABLES a, b",
        "RECURSIVE Q(_), R(_)",
        "Q(n) == IF n = 0 THEN a ELSE R(n - 1)",
        "R(n) == IF n = 0 THEN b ELSE Q(n - 1)",
        "Init == a = 0 /\\ b = 0",
        "Next == a < 3 /\\ a' = Q(2) + 1 /\\ b' = b",
      ].join("\n"),
      "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
    );
    expect([narrow.result.generatedStates, narrow.result.distinctStates]).toEqual([4, 4]);
    expect(narrow.lines).toEqual([expect.stringMatching(/^\[engine\] checked 4 states/)]);
  });

  it("checks a predicate on a mutually recursive operator on every step that changes what it reads", async () => {
    // A compiles first, and B inside it: Inv2 reads a through A, though only A names it.
    const body = [
      "EXTENDS Naturals",
      "VARIABLES a, b, c, d, e, f, g, h, i",
      "Init == a = 0 /\\ b = 0 /\\ c = 0 /\\ d = 0 /\\ e = 0 /\\ f = 0 /\\ g = 0 /\\ h = 0 /\\ i = 0",
      "Next == \\/ a' = (a + 1) % 6 /\\ UNCHANGED <<b, c, d, e, f, g, h, i>>",
      "        \\/ i' = 1 - i /\\ UNCHANGED <<a, b, c, d, e, f, g, h>>",
      "RECURSIVE A(_), B(_)",
      "A(n) == IF n = 0 THEN a ELSE B(n - 1)",
      "B(n) == IF n = 0 THEN b + c + d + e + f + g + h ELSE A(n - 1)",
      "Inv1 == A(2) >= 0",
      "Inv2 == B(1) < 3",
    ].join("\n");
    const violated = await checkInEngine(body, "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2");
    expect(violated.result.status).not.toBe("success");
    expect(violated.lines).toEqual([expect.stringMatching(/an invariant violated$/)]);
    const constrained = await checkInEngine(
      body,
      "INIT Init\nNEXT Next\nINVARIANT Inv1\nCONSTRAINT Inv2",
    );
    expect([constrained.result.generatedStates, constrained.result.distinctStates]).toEqual([
      13, 6,
    ]);
    expect(constrained.lines).toEqual([expect.stringMatching(/^\[engine\] checked 6 states/)]);
    // A definition compiled while R's footprint still grows reads what R comes to read.
    const definition = await checkInEngine(
      [
        "EXTENDS Naturals",
        "VARIABLES a, b",
        "Init == a = 0 /\\ b = 0",
        "Next == \\/ a' = (a + 1) % 6 /\\ UNCHANGED b",
        "        \\/ b' = 1 - b /\\ UNCHANGED a",
        "RECURSIVE R(_)",
        "Dd == R(0)",
        "R(n) == IF n = 0 THEN a ELSE Dd + 0",
        "Inv1 == R(1) >= 0",
        "Inv2 == Dd < 3",
      ].join("\n"),
      "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2",
    );
    expect(definition.result.status).not.toBe("success");
    expect(definition.lines).toEqual([expect.stringMatching(/an invariant violated$/)]);
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

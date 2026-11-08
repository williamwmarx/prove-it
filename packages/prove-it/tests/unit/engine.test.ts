// The engine hands a model to the interpreter where it can't go on, and the interpreter's answer is
// the same either way, so these tests check that the engine itself finished the search: a wrong
// value in the engine shows up as a hand-over, not as a wrong answer.

import { afterEach, describe, expect, it, spyOn } from "bun:test";

import { check, formatValue } from "../../src";
import { getMemoStatistics, nextEpoch } from "../../src/engine/compile";
import { EpochCache, MemoTable } from "../../src/engine/memo";
import { getEngineThreads } from "../../src/engine/settings";

const setting = process.env.PROVE_IT_ENGINE;
const threads = process.env.PROVE_IT_WORKERS;

afterEach(() => {
  if (setting === undefined) delete process.env.PROVE_IT_ENGINE;
  else process.env.PROVE_IT_ENGINE = setting;
  if (threads === undefined) delete process.env.PROVE_IT_WORKERS;
  else process.env.PROVE_IT_WORKERS = threads;
});

describe("the engine between checks", () => {
  it("keeps only the current check's memo tables", async () => {
    const options = {
      source: [
        "---- MODULE M ----",
        "EXTENDS Naturals, FiniteSets",
        "VARIABLE x",
        "RECURSIVE Sum(_)",
        "Sum(n) == IF n = 0 THEN 0 ELSE n + Sum(n - 1)",
        "Init == x = 0",
        "Next == x' = (x + 1) % 20",
        "Inv == Sum(x) >= 0 /\\ Cardinality({y \\in 0..x : y % 2 = 0}) >= 0",
        "====",
      ].join("\n"),
      config: "INIT Init\nNEXT Next\nINVARIANT Inv",
      onPrint: () => {},
    };
    await check(options);
    const tables = getMemoStatistics().length;
    expect(tables).toBeGreaterThan(0);
    await check(options);
    expect(getMemoStatistics().length).toBe(tables);
  });
});

describe("the engine's threads", () => {
  it("searches on one thread unless PROVE_IT_WORKERS asks for more", () => {
    delete process.env.PROVE_IT_WORKERS;
    expect(getEngineThreads()).toBe(1);
    process.env.PROVE_IT_WORKERS = "3";
    expect(getEngineThreads()).toBe(3);
    process.env.PROVE_IT_WORKERS = "0";
    expect(getEngineThreads()).toBe(1);
  });
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

  it("forgets the sets it tested membership in once a check is done", async () => {
    // The second check builds its sets afresh, and one of them gets the id of the first's S.
    const spec = (low: number, high: number) =>
      [
        "EXTENDS Naturals",
        "VARIABLE x",
        `S == {x + i : i \\in ${low}..${high}}`,
        "Init == x = 0",
        "Next == x' = (x + 1) % 2",
        "Inv == 5 \\in S",
      ].join("\n");
    const config = "INIT Init\nNEXT Next\nINVARIANT Inv";
    const first = await checkInEngine(spec(0, 20), config);
    expect(first.result.status).toBe("success");
    expect(first.lines).toEqual([expect.stringMatching(/^\[engine\] checked 2 states/)]);
    const second = await checkInEngine(spec(10, 30), config);
    expect(second.result.status).not.toBe("success");
    expect(second.lines).toEqual([
      expect.stringMatching(/an invariant violated in an initial state$/),
    ]);
  });

  it("checks each conjunct of an invariant on the steps that change what it reads", async () => {
    // Each step changes one of x and y, so the conjunct on y fails on a step that leaves x as it was.
    const body = [
      "EXTENDS Naturals",
      "VARIABLES x, y",
      "Init == x = 0 /\\ y = 0",
      "Next == \\/ x < 2 /\\ x' = x + 1 /\\ UNCHANGED y",
      "        \\/ y < 3 /\\ y' = y + 1 /\\ UNCHANGED x",
      "Bounded == y \\in 0..2",
      "TypeOK == x \\in 0..2 /\\ Bounded",
    ].join("\n");
    const violated = await checkInEngine(body, "INIT Init\nNEXT Next\nINVARIANT TypeOK");
    expect(violated.result.status).toBe("invariant-violation");
    expect(violated.lines).toEqual([expect.stringMatching(/an invariant violated$/)]);
    const constrained = await checkInEngine(
      body,
      "INIT Init\nNEXT Next\nCONSTRAINT TypeOK\nCHECK_DEADLOCK FALSE",
    );
    expect([constrained.result.generatedStates, constrained.result.distinctStates]).toEqual([
      16, 9,
    ]);
    expect(constrained.lines).toEqual([expect.stringMatching(/^\[engine\] checked 9 states/)]);
  });

  it("checks in each initial state the invariants the initial predicate doesn't assert", async () => {
    // The initial predicate is an inductive invariant, as with SPECIFICATION ISpec.
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "TypeOK == x \\in 0..4",
      "Inv == TypeOK /\\ x # 1",
      "Small == x < 3",
      "Next == x' = x",
    ].join("\n");
    const implied = await checkInEngine(body, "INIT Inv\nNEXT Next\nINVARIANT TypeOK Inv");
    expect([implied.result.status, implied.result.distinctStates]).toEqual(["success", 4]);
    expect(implied.lines).toEqual([expect.stringMatching(/^\[engine\] checked 4 states/)]);
    const violated = await checkInEngine(body, "INIT Inv\nNEXT Next\nINVARIANT Inv Small");
    expect(violated.result.status).toBe("invariant-violation");
    expect(violated.lines).toEqual([
      expect.stringMatching(/an invariant violated in an initial state$/),
    ]);
  });

  it("compiles a recursive operator apart for its primed calls", async () => {
    // S(1) compiles unprimed first; (S(1))' reads x'.
    const { result, lines } = await checkInEngine(
      [
        "EXTENDS Naturals",
        "VARIABLES x, y",
        "RECURSIVE S(_)",
        "S(n) == IF n = 0 THEN x ELSE S(n - 1)",
        "Init == x = 0 /\\ y = 0",
        "Next == x < 5 /\\ S(1) >= 0 /\\ x' = x + 1 /\\ (S(1))' # 2 /\\ y' = y",
      ].join("\n"),
      "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
    );
    expect([result.generatedStates, result.distinctStates]).toEqual([2, 2]);
    expect(lines).toEqual([expect.stringMatching(/^\[engine\] checked 2 states/)]);
    // The invariant compiles Rec(1) unprimed before Next does (Rec(1))'.
    const invariantFirst = await checkInEngine(
      [
        "EXTENDS Naturals",
        "VARIABLES x, y",
        "RECURSIVE Rec(_)",
        "Rec(n) == IF n = 0 THEN x ELSE Rec(n - 1)",
        "Init == x = 0 /\\ y = 0",
        "Next == \\/ x < 3 /\\ x' = x + 1 /\\ y' = (Rec(1))'",
        "        \\/ y > 0 /\\ y' = y - 1 /\\ x' = x",
        "Inv == Rec(1) >= 0",
      ].join("\n"),
      "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
    );
    expect([
      invariantFirst.result.generatedStates,
      invariantFirst.result.distinctStates,
      invariantFirst.result.depth,
    ]).toEqual([13, 10, 7]);
    expect(invariantFirst.lines).toEqual([expect.stringMatching(/^\[engine\] checked 10 states/)]);
  });

  it("reads the next state in a function a LET defines when it is primed", async () => {
    // (f[1])' is x', so y' = x' and the states cycle through (0, 0), (1, 1) and (2, 2).
    const primed = await checkInEngine(
      [
        "EXTENDS Naturals",
        "VARIABLES x, y",
        "Init == x = 0 /\\ y = 0",
        "Next == x' = (x + 1) % 3 /\\ y' = LET f[i \\in {1}] == x IN (f[1])'",
      ].join("\n"),
      "INIT Init\nNEXT Next",
    );
    expect([primed.result.generatedStates, primed.result.distinctStates]).toEqual([4, 3]);
    expect(primed.lines).toEqual([expect.stringMatching(/^\[engine\] checked 3 states/)]);
    // UNCHANGED f[1] compares x' with x, and the unprimed f[1] is compiled first.
    const unchanged = await checkInEngine(
      [
        "EXTENDS Naturals",
        "VARIABLES x, y",
        "Init == x = 0 /\\ y = 0",
        "Next == LET f[i \\in {1, 2}] == x + i IN",
        "          /\\ f[1] < 3 /\\ y' = (y + 1) % 2",
        "          /\\ x' \\in {x, x + 1} /\\ UNCHANGED f[1]",
      ].join("\n"),
      "INIT Init\nNEXT Next",
    );
    expect([unchanged.result.generatedStates, unchanged.result.distinctStates]).toEqual([3, 2]);
    expect(unchanged.lines).toEqual([expect.stringMatching(/^\[engine\] checked 2 states/)]);
  });

  it("prints the records of a trace it recovers through its states as TLC sorts them", async () => {
    // Done names status before Next names row, so TLC sorts status first when it fingerprints the
    // states it recovers for the trace, though the constructor writes row first.
    const { result, lines } = await checkInEngine(
      [
        "EXTENDS Naturals",
        "VARIABLES ev, x, y",
        'Done == {i \\in DOMAIN ev : ev[i].status = "done"}',
        'Init == ev = 0 /\\ x = "" /\\ y = 0',
        "Next == \\/ y = 0 /\\ ev' = [row |-> 0, status |-> 0] /\\ y' = 1 /\\ x' = x",
        "        \\/ y = 1 /\\ \\E k \\in DOMAIN ev : x' = k /\\ y' = 2 /\\ ev' = ev",
        "        \\/ y = 2 /\\ x' = \"end\" /\\ y' = 3 /\\ ev' = ev",
        "Inv == y < 3",
      ].join("\n"),
      "INIT Init\nNEXT Next\nINVARIANT Inv",
    );
    expect(result.status).toBe("invariant-violation");
    expect(lines).toEqual([expect.stringMatching(/an invariant violated$/)]);
    expect((result.violation?.trace ?? []).map((step) => formatValue(step.state.ev))).toEqual([
      "0",
      "[status |-> 0, row |-> 0]",
      "[status |-> 0, row |-> 0]",
      "[status |-> 0, row |-> 0]",
    ]);
  });

  it("never issues an epoch again, so a cached value can't outlive its state", () => {
    // A search holds the epoch of the state it expands while its successors take new ones.
    let previous = nextEpoch();
    for (let count = 0; count < 0x40000000; count++) {
      const epoch = nextEpoch();
      if (epoch <= previous) throw new Error(`epoch ${epoch} after ${previous}`);
      previous = epoch;
    }
    // Nor does a cache take an epoch past 2^32 for another.
    const cache = new EpochCache();
    const entry = EpochCache.entry(7, 0, 0, 0);
    cache.set(2 ** 32 + 5, entry, 7, 0, 0, 0, 111);
    expect(cache.get(2 ** 32 + 5, entry, 7, 0, 0, 0)).toBe(111);
    expect(cache.get(5, entry, 7, 0, 0, 0)).toBe(-1);
  });

  it("keeps every entry of a memo table of one key, its keys dense or sparse", () => {
    // Ids 0 to 1999 fit the table's array; ids a million apart make it a hash table.
    for (const stride of [1, 1_000_000]) {
      const table = new MemoTable(1);
      for (let key = 0; key < 1999; key++) table.set1(key * stride, key + 7);
      table.setN(Int32Array.of(1999 * stride), 0, 99);
      for (let key = 0; key < 2000; key++) {
        expect(table.getN(Int32Array.of(key * stride), 0)).toBe(key === 1999 ? 99 : key + 7);
      }
      expect(table.get1(2000 * stride)).toBe(-1);
      expect(table.get1(-1)).toBe(-1);
      expect(table.size).toBe(2000);
    }
  });

  it("compiles what an initial state's shortcut evaluates while generated code runs", async () => {
    // Each initial state the \\A reaches with every variable assigned evaluates its body.
    const many = await checkInEngine(
      [
        "EXTENDS Naturals",
        "VARIABLES x, y",
        "Init == /\\ y \\in 0..5000",
        "        /\\ \\A w \\in {1, 2} : /\\ x = 0",
        "                             /\\ \\E k \\in {1, 2} : k = w",
        "Next == x < 1 /\\ x' = x + 1 /\\ y' = y",
      ].join("\n"),
      "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
    );
    expect([many.result.generatedStates, many.result.distinctStates]).toEqual([10002, 10002]);
    expect(many.lines).toEqual([expect.stringMatching(/^\[engine\] checked 10002 states/)]);
    // The invariant binds nearly as many names as the engine has room for before Init runs.
    const pad = Array.from({ length: 4040 }, (_, k) => `(\\A i${k} \\in {1} : i${k} = 1)`);
    const nest = Array.from({ length: 40 }, (_, j) => `\\A k${j} \\in {1} : `).join("");
    const crowded = await checkInEngine(
      [
        "EXTENDS Naturals",
        "VARIABLES x, y",
        `Pad == ${pad.join(" /\\ ")}`,
        `Init == \\A w \\in {1} : x = 0 /\\ y = w /\\ ${nest}k0 = 1`,
        "Next == x < 2 /\\ x' = x + 1 /\\ y' = y",
      ].join("\n"),
      "INIT Init\nNEXT Next\nINVARIANT Pad\nCHECK_DEADLOCK FALSE",
    );
    expect([crowded.result.generatedStates, crowded.result.distinctStates]).toEqual([3, 3]);
    expect(crowded.lines).toEqual([expect.stringMatching(/^\[engine\] checked 3 states/)]);
  });

  it("hands over an equality that TLC fails on, as TLC compares elements up to the first that differ", async () => {
    // TLC fails to compare a record with a function that isn't one, or the elements of two sets of
    // one size, where they first differ, by kinds it can't compare.
    const failing = [
      ["[a |-> x] = (1 :> 2)", "record compared with a function"],
      ['{x + 1} = {"a"}', "equality of values TLC can't compare"],
      ['<<x, 1>> = <<x, "a">>', "equality of values TLC can't compare"],
      ['[a |-> 1, b |-> x] = [a |-> 1, b |-> "s"]', "equality of values TLC can't compare"],
      ['(2 :> 1 @@ 3 :> x) = (2 :> "a" @@ 3 :> 2)', "equality of values TLC can't compare"],
      ["({1} :> x) = (1 :> 1)", "equality of values TLC can't compare"],
      ["{[a |-> x]} = {<<1>>}", "record compared with a function"],
    ];
    for (const [comparison, reason] of failing) {
      const { result, lines } = await checkInEngine(
        `EXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ ~(${comparison}) /\\ x' = x + 1`,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
      );
      expect(result.status).toBe("error");
      expect(lines).toEqual([expect.stringMatching(new RegExp(`handed over .*: ${reason}$`))]);
    }
    // An earlier difference decides before the elements TLC can't compare, and sets or functions of
    // other sizes differ without comparing their elements.
    const differing = [
      '[a |-> 1, b |-> x] = [a |-> 2, b |-> "s"]',
      '<<x, 1>> = <<x + 1, "a">>',
      '(0 :> x @@ 5 :> 1) = (0 :> x @@ 7 :> "a")',
      '(0 :> x @@ 5 :> "a") = <<1, 2>>',
      '{x} = {"a", "b"}',
      '[a |-> x] = [b |-> "s"]',
      "<<>> = [a |-> x]",
    ];
    for (const comparison of differing) {
      const { result, lines } = await checkInEngine(
        `EXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ ~(${comparison}) /\\ x' = x + 1`,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
      );
      expect([result.status, result.distinctStates]).toEqual(["success", 4]);
      expect(lines).toEqual([expect.stringMatching(/^\[engine\] checked 4 states/)]);
    }
    // A primed variable assigned twice compares its values in the same way.
    const { result, lines } = await checkInEngine(
      'VARIABLE x\nInit == x = {<<"b">>}\nNext == x\' = {<<1>>} /\\ UNCHANGED x',
      "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
    );
    expect(result.status).toBe("error");
    expect(lines).toEqual([
      expect.stringMatching(/handed over .*: equality of values TLC can't compare$/),
    ]);
  });

  it("hands over a membership TLC can't decide, past the untyped model values a set starts with", async () => {
    // TLC compares "a" with the integers and fails; the model value it sorts first compares with
    // anything.
    for (const size of [5, 20]) {
      const body = `EXTENDS Naturals\nCONSTANT M\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == ~("a" \\in ({M} \\cup (1..${size})))`;
      const config = "CONSTANT M = M\nINIT Init\nNEXT Next\nINVARIANT Inv";
      const { result, lines } = await checkInEngine(body, config);
      expect(lines).toEqual([
        expect.stringMatching(/handed over .*: (membership of a value|values) TLC can't compare$/),
      ]);
      process.env.PROVE_IT_ENGINE = "0";
      const reference = await check({ source: `---- MODULE M ----\n${body}\n====`, config });
      expect(result.status).toBe("error");
      expect(result.failure?.message).toBe(reference.failure?.message);
    }
  });

  it("answers membership in a set it doesn't build as TLC does, for every kind of value", async () => {
    const sets = [
      "[{1} -> {1}]",
      '[{"a"} -> {1}]',
      "[a : {1}]",
      "{1} \\X {1}",
      "SUBSET {1}",
      "Seq({1})",
      // UNION {S} of a set the engine can't build tests membership in S.
      "UNION {[{1} -> Nat]}",
      "UNION {[a : Nat]}",
      "UNION {Seq({1})}",
    ];
    const values = ["3", '"s"', "{1}", "<<1>>", "[a |-> 1]", "[b |-> 1]", "M", "A_m"];
    const run = async (source: string, config: string) => {
      try {
        const result = await check({ source, config, onPrint: () => {} });
        return [result.status, result.failure?.message];
      } catch (error) {
        return ["thrown", (error as Error).message];
      }
    };
    for (const set of sets) {
      for (const value of values) {
        // The invariant reads x, so it is checked on each state rather than once as a constant.
        const source = `---- MODULE M ----\nEXTENDS Naturals, Sequences\nCONSTANT M, A_m\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1\nInv == x >= 0 => ~(${value} \\in ${set})\n====`;
        const config =
          "CONSTANT M = M\nCONSTANT A_m = A_m\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE";
        delete process.env.PROVE_IT_ENGINE;
        const actual = await run(source, config);
        process.env.PROVE_IT_ENGINE = "0";
        const reference = await run(source, config);
        expect([value, set, ...actual]).toEqual([value, set, ...reference]);
      }
    }
  });

  it("evaluates a set's parts before testing membership in it, as TLC does", async () => {
    // TLC makes the set's value, evaluating its parts, before it tests membership, so a part that
    // fails fails the test even when the element's kind or shape already decides it.
    const memberships = [
      "<<>> \\notin [{1} -> {1 \\div x}]",
      "<<>> \\notin UNION {[{1} -> {1 \\div x}]}",
      "<<>> \\notin [{1 \\div x} -> Nat]",
      "<<>> \\notin [{1} -> [{2} -> {1 \\div x}]]",
      "[b |-> 1] \\notin [a : {1 \\div x}]",
      "[a |-> 1, b |-> 2] \\notin [b : {2 \\div x}, a : {1 \\div x}]",
      "<<1>> \\notin {1} \\X {1 \\div x}",
      "{} \\in SUBSET {1 \\div x}",
      "<<>> \\in Seq({1 \\div x})",
    ];
    for (const membership of memberships) {
      const source = `---- MODULE M ----\nEXTENDS Naturals, Sequences\nVARIABLE x\nInit == x = 0\nNext == UNCHANGED x\nInv == ${membership}\n====`;
      const config = "INIT Init\nNEXT Next\nINVARIANT Inv";
      delete process.env.PROVE_IT_ENGINE;
      const result = await check({ source, config, onPrint: () => {} });
      process.env.PROVE_IT_ENGINE = "0";
      const reference = await check({ source, config, onPrint: () => {} });
      expect([membership, result.status, result.failure?.message]).toEqual([
        membership,
        reference.status,
        reference.failure?.message,
      ]);
      expect(result.status).toBe("error");
    }
  });

  it("reads Nat as the set the model substitutes for it", async () => {
    const { result, lines } = await checkInEngine(
      "EXTENDS Integers\nVARIABLE x\nInit == x = 0\nNext == UNCHANGED x\nInv == -1 \\in Nat",
      "CONSTANT Nat <- Int\nINIT Init\nNEXT Next\nINVARIANT Inv",
    );
    expect(result.status).toBe("success");
    expect(lines).toEqual([expect.stringMatching(/^\[engine\] checked 1 states/)]);
  });

  it("tests membership in the union of one set it can't build", async () => {
    // As in the Disruptor's RingBuffer, whose slots hold integers or NULL.
    const spec = (value: string) =>
      [
        "EXTENDS Integers",
        "CONSTANTS NULL, Other",
        "VARIABLE slots",
        "Init == slots = [i \\in 0..1 |-> NULL]",
        `Next == \\E i \\in 0..1 : slots[i] = NULL /\\ slots' = [slots EXCEPT ![i] = ${value}]`,
        "TypeOk == slots \\in UNION { [0..1 -> Int \\union {NULL}] }",
      ].join("\n");
    const config =
      "CONSTANTS NULL = NULL\nOther = Other\nINIT Init\nNEXT Next\nINVARIANT TypeOk\nCHECK_DEADLOCK FALSE";
    const typed = await checkInEngine(spec("-3"), config);
    expect([typed.result.status, typed.result.distinctStates]).toEqual(["success", 4]);
    expect(typed.lines).toEqual([expect.stringMatching(/^\[engine\] checked 4 states/)]);
    const mistyped = await checkInEngine(spec("Other"), config);
    expect(mistyped.result.status).toBe("invariant-violation");
    expect(mistyped.lines).toEqual([expect.stringMatching(/an invariant violated$/)]);
  });

  it("compiles each level of nested UNION {S} once", async () => {
    // Compiling the one element twice per level, for the set and for membership, took 2^24 compiles.
    const nested = Array.from({ length: 24 }).reduce<string>(
      (set) => `UNION {${set}}`,
      "[{1} -> Int]",
    );
    const { result, lines } = await checkInEngine(
      `EXTENDS Integers\nVARIABLE x\nInit == x = 0\nNext == UNCHANGED x\nInv == [i \\in {1} |-> 5] \\in ${nested}`,
      "INIT Init\nNEXT Next\nINVARIANT Inv",
    );
    expect(result.status).toBe("success");
    expect(lines).toEqual([expect.stringMatching(/^\[engine\] checked 1 states/)]);
  });
});

// The engine hands a model to the interpreter where it can't go on, and the interpreter's answer is
// the same either way, so these tests check that the engine itself finished the search: a wrong
// value in the engine shows up as a hand-over, not as a wrong answer.

import { afterEach, describe, expect, it, spyOn } from "bun:test";

import { check, formatValue } from "../../src";
import { getMemoStatistics, nextEpoch } from "../../src/engine/compile";
import { EpochCache, MemoTable } from "../../src/engine/memo";
import { getEngineThreads } from "../../src/engine/settings";

const settings = [
  "PROVE_IT_ENGINE",
  "PROVE_IT_WORKERS",
  "PROVE_IT_LIVE_CHECK",
  "PROVE_IT_ENGINE_BACKEND",
].map((name) => [name, process.env[name]] as const);

afterEach(() => {
  for (const [name, value] of settings) {
    if (value === undefined) delete process.env[name];
    else process.env[name] = value;
  }
});

describe("the engine between checks", () => {
  // It reads the TypeScript engine's memo tables, so it pins that backend; native/ts-only-tests.json
  // names its Rust counterpart.
  it("keeps only the current check's memo tables", async () => {
    process.env.PROVE_IT_ENGINE_BACKEND = "ts";
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

// The TypeScript engine's lines. The native engine's, with PROVE_IT_ENGINE_BACKEND=rust, come first.
const checkInEngine = async (body: string, config: string) => {
  process.env.PROVE_IT_ENGINE = "debug";
  const lines: string[] = [];
  const spy = spyOn(console, "error").mockImplementation((message: unknown) => {
    if (
      typeof message === "string" &&
      message.startsWith("[engine] ") &&
      !message.startsWith("[engine] native: ")
    ) {
      lines.push(message);
    }
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

  it("reports how many initial states it computed past those the engine reported", async () => {
    // The engine hands over at the third initial state, before it reports two, and the interpreter
    // computes them all again.
    const source = [
      "---- MODULE M ----",
      "EXTENDS Naturals, FiniteSets",
      "VARIABLE x",
      "Init == x \\in 1..20 /\\ (x = 3 => Cardinality(SUBSET (1..21)) > 0)",
      "Next == UNCHANGED x",
      "====",
    ].join("\n");
    const getReported = async (engine: string) => {
      process.env.PROVE_IT_ENGINE = engine;
      const counts: number[] = [];
      const lines: string[] = [];
      const spy = spyOn(console, "error").mockImplementation((message: unknown) => {
        if (
          typeof message === "string" &&
          message.startsWith("[engine] ") &&
          !message.startsWith("[engine] native: ")
        ) {
          lines.push(message);
        }
      });
      try {
        await check({
          source,
          config: "INIT Init\nNEXT Next",
          onProgress: (progress) => {
            if (progress.kind === "initial-states-progress") counts.push(progress.count);
          },
        });
      } finally {
        spy.mockRestore();
      }
      return { counts, lines };
    };
    const engine = await getReported("debug");
    expect(engine.lines).toEqual([expect.stringMatching(/handed over .*: a power set too large/)]);
    // What TLC 2026.11.06 reports.
    expect(engine.counts).toEqual([2, 4, 8, 16]);
    expect((await getReported("0")).counts).toEqual([2, 4, 8, 16]);
  });

  it("hands over a membership TLC can't decide, past the untyped model values a set starts with", async () => {
    // TLC compares "a" with the integers and fails; the model value it sorts first compares with
    // anything.
    for (const size of [5, 20]) {
      const body = `EXTENDS Naturals\nCONSTANT M\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == ~("a" \\in ({M} \\cup (1..${size})))`;
      const config = "CONSTANT M = M\nINIT Init\nNEXT Next\nINVARIANT Inv";
      const { result, lines } = await checkInEngine(body, config);
      expect(lines).toEqual([
        expect.stringMatching(/handed over .*: a mistyped membership in an interval$/),
      ]);
      process.env.PROVE_IT_ENGINE = "0";
      const reference = await check({ source: `---- MODULE M ----\n${body}\n====`, config });
      expect(result.status).toBe("error");
      expect(result.failure?.message).toBe(reference.failure?.message);
    }
  });

  it("hands over a membership whose search of the set TLC fails, deeper than the kinds", async () => {
    // TLC's SetEnumValue.member binary-searches a set it has normalized, such as a constant's, with
    // the element's compareTo. What TLC reports for each, at the commit the recordings pin.
    const cases = [
      [
        "S == {<<1>>, <<2>>}\nInv == [a |-> x] \\notin S",
        "Attempted to compare record:\n[a |-> 0]\nwith non-record\n<<2>>",
      ],
      [
        "S == {[i \\in 0..1 |-> 5]}\nInv == [a |-> x] \\notin S",
        "Attempted to compare record:\n[a |-> 0]\nwith non-record\n(0 :> 5 @@ 1 :> 5)",
      ],
      [
        "S == {<<[a |-> 1]>>, <<[a |-> 2]>>}\nInv == <<<<x>>>> \\notin S",
        'Attempted to compare integer with non-integer:\n"a".',
      ],
      [
        "S == {<<i>> : i \\in 1..40}\nInv == [a |-> x] \\notin S",
        "Attempted to compare record:\n[a |-> 0]\nwith non-record\n<<21>>",
      ],
    ];
    for (const [definitions, message] of cases) {
      const body = `EXTENDS Naturals\nVARIABLE x\n${definitions}\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1`;
      const config = "INIT Init\nNEXT Next\nINVARIANT Inv";
      const { result, lines } = await checkInEngine(body, config);
      expect(lines).toEqual([
        expect.stringMatching(/handed over .*TLC can't compare|with a function$/),
      ]);
      process.env.PROVE_IT_ENGINE = "0";
      const reference = await check({ source: `---- MODULE M ----\n${body}\n====`, config });
      expect(result).toEqual(reference);
      expect(result.failure?.message).toContain(message);
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
      // A part evaluated under one binding is evaluated again under the next.
      "\\A y \\in {0, 1} : [c |-> 1] \\notin [a : {1 \\div (y - 1)}]",
      "<<>> \\notin [{1} -> {z \\in {0, 1} : [c |-> 1] \\notin [a : {1 \\div (z - 1)}]}]",
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

  it("evaluates the parts of a set that definitions share once per membership test", async () => {
    // Each level names the one below twice, so evaluating its parts on every use took 2^28 runs.
    const levels = Array.from(
      { length: 28 },
      (_, level) => `S${level + 1} == [a : S${level}, b : S${level}]`,
    );
    const { result, lines } = await checkInEngine(
      `VARIABLE x\nS0 == {x}\n${levels.join("\n")}\nInit == x = 0\nNext == UNCHANGED x\nInv == [c |-> 1] \\notin S28`,
      "INIT Init\nNEXT Next\nINVARIANT Inv",
    );
    expect(result.status).toBe("success");
    expect(lines).toEqual([expect.stringMatching(/^\[engine\] checked 1 states/)]);
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

// ReadersWriters from tlaplus/Examples, whose fairness is on parts of Next, quantified over actors.
const readersWriters = (fairness: string[]) =>
  [
    "---- MODULE ReadersWriters ----",
    "EXTENDS FiniteSets, Naturals, Sequences",
    "CONSTANT NumActors",
    "VARIABLES readers, writers, waiting",
    "vars == <<readers, writers, waiting>>",
    "Actors == 1..NumActors",
    "ToSet(s) == { s[i] : i \\in DOMAIN s }",
    'read(s) == s[1] = "read"',
    'write(s) == s[1] = "write"',
    "WaitingToRead == { p[2] : p \\in ToSet(SelectSeq(waiting, read)) }",
    "WaitingToWrite == { p[2] : p \\in ToSet(SelectSeq(waiting, write)) }",
    "TryRead(actor) ==",
    "  /\\ actor \\notin WaitingToRead",
    '  /\\ waiting\' = Append(waiting, <<"read", actor>>)',
    "  /\\ UNCHANGED <<readers, writers>>",
    "TryWrite(actor) ==",
    "  /\\ actor \\notin WaitingToWrite",
    '  /\\ waiting\' = Append(waiting, <<"write", actor>>)',
    "  /\\ UNCHANGED <<readers, writers>>",
    "Read(actor) ==",
    "  /\\ readers' = readers \\union {actor}",
    "  /\\ waiting' = Tail(waiting)",
    "  /\\ UNCHANGED writers",
    "Write(actor) ==",
    "  /\\ readers = {}",
    "  /\\ writers' = writers \\union {actor}",
    "  /\\ waiting' = Tail(waiting)",
    "  /\\ UNCHANGED readers",
    "ReadOrWrite ==",
    "  /\\ waiting /= <<>>",
    "  /\\ writers = {}",
    "  /\\ LET pair == Head(waiting)",
    "         actor == pair[2]",
    '     IN CASE pair[1] = "read" -> Read(actor)',
    '          [] pair[1] = "write" -> Write(actor)',
    "StopActivity(actor) ==",
    "  IF actor \\in readers",
    "  THEN /\\ readers' = readers \\ {actor}",
    "       /\\ UNCHANGED <<writers, waiting>>",
    "  ELSE /\\ writers' = writers \\ {actor}",
    "       /\\ UNCHANGED <<readers, waiting>>",
    "Stop == \\E actor \\in readers \\cup writers : StopActivity(actor)",
    "Init == readers = {} /\\ writers = {} /\\ waiting = <<>>",
    "Next ==",
    "  \\/ \\E actor \\in Actors : TryRead(actor)",
    "  \\/ \\E actor \\in Actors : TryWrite(actor)",
    "  \\/ ReadOrWrite",
    "  \\/ Stop",
    "Fairness ==",
    ...fairness.map((part) => `  /\\ ${part}`),
    "Spec == Init /\\ [][Next]_vars /\\ Fairness",
    "Liveness ==",
    "  /\\ \\A actor \\in Actors : []<>(actor \\in readers)",
    "  /\\ \\A actor \\in Actors : []<>(actor \\in writers)",
    "BoundedWaiting == Len(waiting) <= 2",
    "NoWriteAfterRead == ~(readers /= {} /\\ writers' /= {})",
    "====",
  ].join("\n");
const READERS_WRITERS_FAIRNESS = [
  "\\A actor \\in Actors : WF_vars(TryRead(actor))",
  "\\A actor \\in Actors : WF_vars(TryWrite(actor))",
  "WF_vars(ReadOrWrite)",
  "WF_vars(Stop)",
];
const READERS_WRITERS_CONFIG = "CONSTANT NumActors = 2\nSPECIFICATION Spec\nPROPERTY Liveness";

// EWD426's token ring from tlaplus/Examples, whose fairness is on the whole of Next.
const tokenRing = (property: string) =>
  [
    "---- MODULE TokenRing ----",
    "EXTENDS Naturals",
    "CONSTANTS N, M",
    "Node == 0 .. N-1",
    "VARIABLE c",
    "vars == << c >>",
    "Init == c \\in [ Node -> 0 .. M-1 ]",
    "CreateToken ==",
    "  /\\ c[0] = c[N-1]",
    "  /\\ c' = [ c EXCEPT ![0] = (c[N-1] + 1) % M ]",
    "PassToken(i) ==",
    "  /\\ i # 0",
    "  /\\ c[i] # c[i-1]",
    "  /\\ c' = [ c EXCEPT ![i] = c[i-1] ]",
    "Next == CreateToken \\/ \\E i \\in Node \\ {0} : PassToken(i)",
    "Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)",
    "UniqueToken ==",
    "  \\E i \\in 0 .. N :",
    "    /\\ \\A j \\in 0..i-1 : c[j] = c[0]",
    "    /\\ \\A j \\in i..N-1 : c[j] = (c[0] - 1) % M",
    `Property == ${property}`,
    "====",
  ].join("\n");
const TOKEN_RING_CONFIG =
  "CONSTANTS N = 3\nM = 3\nCHECK_DEADLOCK FALSE\nSPECIFICATION Spec\nPROPERTY Property";

describe("the engine's initial states", () => {
  // TLC's InitialLivenessEvaluationError: TLC adds each initial state to the liveness checker as it
  // computes them, and fails there before it reports them.
  it("hands over an initial state the liveness checker fails on before reporting them", async () => {
    const options = {
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == (x = 0 /\\ x' = 1) \\/ UNCHANGED x\nSpec == Init /\\ [][Next]_x\nInv == x = 0\nProp == <>~ENABLED (x' > x)\n====",
      config: "SPECIFICATION Spec\nINVARIANT Inv\nPROPERTY Prop",
    };
    const run = async () => {
      const progress: string[] = [];
      const result = await check({ ...options, onProgress: (event) => progress.push(event.kind) });
      return { result, progress };
    };
    delete process.env.PROVE_IT_ENGINE;
    const actual = await run();
    process.env.PROVE_IT_ENGINE = "0";
    const reference = await run();
    expect(actual).toEqual(reference);
    expect(reference.progress).not.toContain("initial-states-computed");
  });
});

describe("the engine's answers to ENABLED", () => {
  // Checks a model with the engine, with PROVE_IT_LIVE_CHECK=1, which also runs each action whose
  // ENABLED it answers from the steps of its search and takes each step through Next as well as
  // through the actions that label it, and without the engine.
  const checkBoth = async (source: string, config: string) => {
    process.env.PROVE_IT_ENGINE = "debug";
    process.env.PROVE_IT_LIVE_CHECK = "1";
    const lines: string[] = [];
    const spy = spyOn(console, "error").mockImplementation((message: unknown) => {
      if (typeof message === "string" && message.startsWith("[engine] ")) lines.push(message);
    });
    try {
      const result = await check({ source, config, onPrint: () => {} });
      process.env.PROVE_IT_ENGINE = "0";
      const reference = await check({ source, config, onPrint: () => {} });
      expect(result).toEqual(reference);
      // The engine searched every state, rather than handing the search over.
      expect(lines).toContainEqual(expect.stringMatching(/^\[engine\] found \d+ states/));
      return {
        result,
        lines,
        isFromSteps: lines.some((line) =>
          line.endsWith("answers ENABLED from the steps its search took"),
        ),
      };
    } finally {
      spy.mockRestore();
    }
  };

  it("answers ENABLED of the whole next-state relation from the steps the search took", async () => {
    const stable = await checkBoth(tokenRing("<>[]UniqueToken"), TOKEN_RING_CONFIG);
    expect([stable.result.status, stable.result.distinctStates]).toEqual(["success", 27]);
    expect(stable.isFromSteps).toBe(true);
    const violated = await checkBoth(tokenRing("<>[](c[0] = 0)"), TOKEN_RING_CONFIG);
    expect(violated.result.status).toBe("liveness-violation");
    expect(violated.result.violation?.loopStart).toBeDefined();
    expect(violated.isFromSteps).toBe(true);
  });

  it("answers ENABLED of quantified parts of the next-state relation from the actions that took each step", async () => {
    const live = await checkBoth(readersWriters(READERS_WRITERS_FAIRNESS), READERS_WRITERS_CONFIG);
    expect(live.result.status).toBe("success");
    expect(live.isFromSteps).toBe(true);
    // Without fairness on TryWrite, an actor need never ask to write.
    const unfair = await checkBoth(
      readersWriters(READERS_WRITERS_FAIRNESS.filter((fairness) => !fairness.includes("TryWrite"))),
      READERS_WRITERS_CONFIG,
    );
    expect(unfair.result.status).toBe("liveness-violation");
    expect(unfair.result.violation?.loopStart).toBeDefined();
    expect(unfair.isFromSteps).toBe(true);
    const strong = await checkBoth(
      readersWriters(["\\A actor \\in Actors : SF_vars(TryRead(actor) \\/ TryWrite(actor))"]),
      READERS_WRITERS_CONFIG,
    );
    expect(strong.result.status).toBe("liveness-violation");
    expect(strong.isFromSteps).toBe(true);
  });

  it("runs the action for ENABLED of what isn't the next-state relation's actions in order", async () => {
    for (const fairness of [
      "WF_vars(Stop \\/ ReadOrWrite)",
      "WF_vars(waiting' = <<>> /\\ UNCHANGED <<readers, writers>>)",
    ]) {
      const { result } = await checkBoth(
        readersWriters([...READERS_WRITERS_FAIRNESS, fairness]),
        READERS_WRITERS_CONFIG,
      );
      expect([fairness, result.status, result.failure?.message]).toEqual([
        fairness,
        "success",
        undefined,
      ]);
    }
  });

  it("runs the action for ENABLED under a constraint, which drops steps", async () => {
    for (const constraint of ["CONSTRAINT BoundedWaiting", "ACTION_CONSTRAINT NoWriteAfterRead"]) {
      const { result, isFromSteps } = await checkBoth(
        readersWriters(READERS_WRITERS_FAIRNESS),
        `${READERS_WRITERS_CONFIG}\n${constraint}`,
      );
      expect(result.status).not.toBe("error");
      expect(isFromSteps).toBe(false);
    }
  });

  it("leaves ENABLED to the interpreter where the engine fails, so the error reads as TLC's", async () => {
    const { result } = await checkBoth(
      [
        "---- MODULE M ----",
        "EXTENDS Naturals",
        "VARIABLE x",
        "Init == x = 0",
        "Next == x' = 1 - x",
        "A == x = 1 /\\ x' \\in Nat",
        "Spec == Init /\\ [][Next]_x /\\ WF_x(A)",
        "P == <>(x = 0)",
        "====",
      ].join("\n"),
      "SPECIFICATION Spec\nPROPERTY P",
    );
    expect(result.failure?.message).toContain("The right side of \\IN is not enumerable.");
  });

  it("evaluates <<A>>_v and [A]_v of the temporal properties itself", async () => {
    for (const [property, status] of [
      ["[]<><<Next>>_vars", "success"],
      ["[]<><<CreateToken>>_vars", "success"],
      ["<>[][PassToken(1)]_vars", "liveness-violation"],
      ["<>[][CreateToken \\/ PassToken(1)]_c", "liveness-violation"],
      ["[]<><<PassToken(1) /\\ c[0] = M>>_vars", "liveness-violation"],
      ["<>[][Next]_vars", "success"],
    ]) {
      const { result, lines } = await checkBoth(tokenRing(property), TOKEN_RING_CONFIG);
      expect([property, result.status]).toEqual([property, status]);
      expect(lines.filter((line) => line.includes("leaves a temporal predicate"))).toEqual([]);
    }
  });

  it("runs the action for ENABLED once the search evaluated a conjunct TLC's ENABLED walks", async () => {
    // From x = 1, TLC's ENABLED takes the first branch's step, which leaves x unchanged, and fails
    // comparing x with "a" in the second, which the search never evaluated once the first held.
    const { result, isFromSteps } = await checkBoth(
      [
        "---- MODULE M ----",
        "VARIABLE x",
        "Init == x = 0",
        "Next ==",
        "  \\/ x = 0 /\\ x' = 1",
        "  \\/ x = 1 /\\ x' = x /\\ (x' = 1 \\/ x' = \"a\")",
        "Spec == Init /\\ [][Next]_x /\\ WF_x(Next)",
        "Live == <>(x = 2)",
        "====",
      ].join("\n"),
      "SPECIFICATION Spec\nPROPERTY Live",
    );
    expect(result.status).toBe("error");
    expect(isFromSteps).toBe(false);
  });
});

describe("the engine's hand-over to the interpreter part way through a search", () => {
  // Checks a model with the engine and without, comparing the results and what each reported in
  // order, and returns what the engine said it did.
  const checkBoth = async (lines: string[], config: string) => {
    const source = ["---- MODULE M ----", ...lines, "===="].join("\n");
    const checkReporting = async () => {
      const reported: string[] = [];
      const result = await check({
        source,
        config,
        onPrint: (line) => reported.push(line),
        onProgress: (progress) => reported.push(progress.kind),
      });
      return { result, reported };
    };
    process.env.PROVE_IT_ENGINE = "0";
    const reference = await checkReporting();
    process.env.PROVE_IT_ENGINE = "debug";
    const engineLines: string[] = [];
    const spy = spyOn(console, "error").mockImplementation((message: unknown) => {
      if (typeof message === "string" && message.startsWith("[engine] ")) {
        engineLines.push(message);
      }
    });
    try {
      const reported = await checkReporting();
      expect(reported).toEqual(reference);
      const result = reported.result;
      return {
        result,
        handedOver: engineLines.find((line) => /handed over|found \d+ states/.test(line)),
      };
    } finally {
      spy.mockRestore();
    }
  };
  // A counter and a bit that flips below 3, so each level holds states the search hasn't expanded
  // when it stops.
  const counter = (move: string, extra: string[] = []) => [
    "EXTENDS Naturals, FiniteSets",
    "VARIABLES x, y",
    "vars == <<x, y>>",
    "Init == x = 0 /\\ y = 0",
    `Move == ${move} /\\ y' = y`,
    "Flip == x < 3 /\\ y' = 1 - y /\\ x' = x",
    "Next == Flip \\/ Move",
    "Spec == Init /\\ [][Next]_vars /\\ WF_vars(Move)",
    ...extra,
  ];
  const LIVE_CONFIG = "SPECIFICATION Spec\nPROPERTY Live";

  it("checks the temporal properties on the graph found up to a deadlock", async () => {
    const { result, handedOver } = await checkBoth(
      counter("x < 3 /\\ x' = x + 1", ["Live == <>(x = 3)"]),
      `${LIVE_CONFIG}\nCHECK_DEADLOCK TRUE`,
    );
    expect(handedOver).toMatch(/: deadlock$/);
    expect(result.status).toBe("deadlock");
  });

  it("checks the temporal properties on the graph found up to an invariant violated", async () => {
    const { result, handedOver } = await checkBoth(
      counter("x' = (x + 1) % 4", ["Live == []<>(x = 0)", "Inv == x + y < 4"]),
      `${LIVE_CONFIG}\nINVARIANT Inv`,
    );
    expect(handedOver).toMatch(/: an invariant violated$/);
    expect(result.status).toBe("invariant-violation");
  });

  it("goes on from the graph found when the engine stops for what it doesn't build", async () => {
    // The engine doesn't build a power set of more than 2^20 sets, which TLC counts without
    // building, so it stops once x = 1.
    const move = "x' = (x + 1) % 4 /\\ Cardinality(SUBSET (0..((x % 2) * 25))) > 0";
    for (const [live, status] of [
      ["[]<>(x = 0)", "success"],
      ["<>[](y = 0)", "liveness-violation"],
      ["[](x = 0 => <>(x = 2 /\\ ENABLED Move))", "success"],
    ]) {
      const { result, handedOver } = await checkBoth(
        counter(move, [`Live == ${live}`]),
        LIVE_CONFIG,
      );
      expect(handedOver).toMatch(/: a power set too large to build$/);
      expect([live, result.status]).toEqual([live, status]);
    }
  });

  it("reports an error the liveness checker meets in an initial state as without the engine", async () => {
    const { result, handedOver } = await checkBoth(
      counter("x < 3 /\\ x' = x + 1", ["Live == <>~ENABLED (x' > x)"]),
      LIVE_CONFIG,
    );
    expect(handedOver).toMatch(/: deadlock$/);
    expect(result.status).toBe("error");
  });

  it("counts the initial states up to one the liveness checker fails on as without the engine", async () => {
    // The constraint drops the initial states with y = 1, which TLC still counts as generated.
    const { result, handedOver } = await checkBoth(
      [
        "EXTENDS Naturals, TLC",
        "VARIABLES x, y",
        "Init == x \\in 0..3 /\\ y \\in 0..1",
        "Next == x' = (x + 1) % 4 /\\ y' = y",
        "Spec == Init /\\ [][Next]_<<x, y>>",
        'Counts == PrintT(<<TLCGet("level"), TLCGet("distinct"), TLCGet("generated")>>)',
        "Live == <>(x = 1 /\\ ~ENABLED (Counts /\\ x' > x))",
        "Bound == y = 0",
      ],
      "SPECIFICATION Spec\nPROPERTY Live\nCONSTRAINT Bound",
    );
    expect(handedOver).toMatch(/found \d+ states/);
    expect([result.status, result.generatedStates, result.distinctStates]).toEqual(["error", 8, 4]);
  });

  it("rebuilds a trace through the engine's states at the levels TLCGet reads", async () => {
    const levels = [
      "EXTENDS Naturals, TLC",
      "VARIABLES x, y",
      'Init == x = 0 /\\ y = TLCGet("level")',
      'Next == TLCGet("level") > 0 /\\ x < 3 /\\ x\' = x + 1 /\\ y\' = TLCGet("level")\'',
      "Spec == Init /\\ [][Next]_<<x, y>>",
      "Live == <>(x = 3)",
      "Inv == x < 3",
    ];
    for (const [config, expected] of [
      ["SPECIFICATION Spec\nPROPERTY Live", "deadlock"],
      ["INIT Init\nNEXT Next\nINVARIANT Inv", "invariant-violation"],
    ]) {
      const { result, handedOver } = await checkBoth(levels, config);
      expect(handedOver).toBeDefined();
      expect([config, result.status, result.violation?.trace.length]).toEqual([
        config,
        expected,
        4,
      ]);
    }
  });

  it("asks the engine whether a successor is among the states it found", async () => {
    // From (2, 0), Flip goes to (2, 1), found from (1, 1) before, then Move breaks the invariant.
    const { result, handedOver } = await checkBoth(
      counter("x' = x + 1", ["Inv == x < 3"]),
      "INIT Init\nNEXT Next\nINVARIANT Inv",
    );
    expect(handedOver).toMatch(/: an invariant violated$/);
    expect(result.status).toBe("invariant-violation");
    expect(result.violation?.trace).toHaveLength(4);
  });

  it("counts a new successor the engine found before it stopped as new", async () => {
    const { result, handedOver } = await checkBoth(
      [
        "EXTENDS Naturals",
        "VARIABLE x",
        "Init == x = 0",
        "Next == x' = x + 1 \\/ x' = x + 1 \\/ x' = x + 10",
        "Inv == x < 10",
      ],
      "INIT Init\nNEXT Next\nINVARIANT Inv",
    );
    expect(handedOver).toMatch(/: an invariant violated$/);
    expect([result.status, result.distinctStates]).toEqual(["invariant-violation", 3]);
  });

  it("finds a successor among the states it found by the view or the symmetry TLC fingerprints", async () => {
    const symmetric = [
      "EXTENDS Naturals, TLC",
      "CONSTANTS A, B",
      "VARIABLES x, owner",
      "Init == x = 0 /\\ owner = A",
      "Next == \\/ x' = x + 1 /\\ owner' = owner",
      "        \\/ owner' \\in {A, B} /\\ x' = x",
      "Inv == x < 3",
      "View == x",
      "Perms == Permutations({A, B})",
    ];
    const config = "CONSTANTS A = A\nB = B\nINIT Init\nNEXT Next\nINVARIANT Inv";
    for (const reduction of ["VIEW View", "SYMMETRY Perms"]) {
      const { result, handedOver } = await checkBoth(symmetric, `${config}\n${reduction}`);
      expect(handedOver).toMatch(/: an invariant violated$/);
      expect([reduction, result.status]).toEqual([reduction, "invariant-violation"]);
    }
  });

  it("takes over the engine's states to find a successor holding a set it keeps lazy", async () => {
    // SUBSET {1} is the set {{}, {1}}, which the interpreter holds unenumerated.
    const { result, handedOver } = await checkBoth(
      [
        "EXTENDS Naturals",
        "VARIABLES x, s",
        "Init == x = 0 /\\ s = {}",
        "Next == \\/ s' = SUBSET {1} /\\ x' = x",
        "        \\/ s' = {{}, {1}} /\\ x' = x",
        "        \\/ x' = x + 1 /\\ s' = s",
        "Inv == x < 3",
      ],
      "INIT Init\nNEXT Next\nINVARIANT Inv",
    );
    expect(handedOver).toMatch(/: an invariant violated$/);
    expect(result.status).toBe("invariant-violation");
  });

  it("takes over the engine's states once it goes past the one the engine stopped in", async () => {
    const { result, handedOver } = await checkBoth(
      counter("x' = (x + 1) % 4 /\\ Cardinality(SUBSET (0..((x % 2) * 25))) > 0", ["Inv == x < 4"]),
      "INIT Init\nNEXT Next\nINVARIANT Inv",
    );
    expect(handedOver).toMatch(/: a power set too large to build$/);
    expect(result.status).toBe("success");
  });
});

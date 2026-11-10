// The native engine's search, with PROVE_IT_ENGINE_BACKEND=rust: it must reach what the interpreter
// reaches, whether it completes the search or hands over part way, and find the same states in the
// same order as the TypeScript engine. Each test also checks what the native engine did, so a
// model it declines can't pass by the TypeScript engine's search. They run where the addon was
// built, with PROVE_IT_ENGINE_ADDON naming it, as the native job in verification.yml does.

import { afterEach, describe, expect, it } from "bun:test";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { readLogLines } from "../../scripts/state-logs";
import {
  ADDON,
  compareStateLogs,
  compareWithInterpreter,
  COMPLETE,
  declined,
  restoreSettings,
  run,
  stopped,
  toModule,
} from "./native-runs";

afterEach(restoreSettings);

// A spec whose actions walk each construct the walker handles: disjunctions, existentials over one
// and several bounds, IF, CASE, =>, UNCHANGED, a guard, a lazily applied function, x' \in S, and an
// action as an operator's argument.
const WALKS = [
  "EXTENDS Naturals",
  "VARIABLES x, y, z",
  "Step(A) == A /\\ UNCHANGED z",
  "Init == x \\in 0..1 /\\ y = 0 /\\ z \\in {1, 2}",
  "Next ==",
  "  \\/ \\E a \\in 0..2, b \\in 0..1 : x' = (a + b) % 4 /\\ y' = (y + a) % 3 /\\ UNCHANGED z",
  "  \\/ Step(IF x > 1 THEN x' = 0 /\\ y' = y ELSE x' = x + 1 /\\ y' \\in {y, (y + 1) % 3})",
  "  \\/ CASE x = 0 -> x' = 3 /\\ y' = y /\\ z' = z",
  "       [] x = 3 -> LET f[n \\in 0..3] == x' = n \\/ x' = (n + 1) % 4",
  "                   IN f[x] /\\ y' = 0 /\\ z' = 3 - z",
  "       [] OTHER -> UNCHANGED <<x, y, z>>",
  "  \\/ (y = 2 => x' = 1) /\\ x' = 1 /\\ y' = y /\\ z' = z",
];

describe.if(ADDON !== undefined)("the native engine's search", () => {
  it("walks actions in TLC's order", async () => {
    const config = "INIT Init\nNEXT Next";
    for (const isWarningEnabled of [false, true]) {
      expect(await compareStateLogs(WALKS, config, isWarningEnabled)).toContainEqual(
        expect.stringMatching(COMPLETE),
      );
    }
    expect(await compareWithInterpreter(WALKS, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("searches strings with a lone surrogate, which TLC computes at startup", async () => {
    // Java's strings are UTF-16, as JavaScript's are: Tail("😀a") is half the emoji and "a".
    const body = [
      "EXTENDS Sequences",
      "VARIABLE x",
      'Lone == Tail("😀a")',
      "Init == x = Lone",
      'Next == x\' \\in {Lone, SubSeq("😀b", 1, 1), "b"}',
    ];
    expect(await compareWithInterpreter(body, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("assigns each subset of a set to x' \\subseteq S, as x' \\in SUBSET S", async () => {
    // TLC's test-model/SubseteqNextState.tla. The TypeScript engine leaves it to the interpreter.
    const body = [
      "VARIABLES x, y",
      "Init == x \\subseteq {1, 2} /\\ y = {1, 2, 3}",
      "Next == UNCHANGED y /\\ x' \\subseteq y'",
    ];
    const config = "INIT Init\nNEXT Next";
    expect(await compareWithInterpreter(body, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("intersects and subtracts sets TLC only tests for membership, as TLC enumerates them", async () => {
    // From TLC's test-model/suite/test8.tla, which the TypeScript engine leaves to the interpreter.
    const body = [
      "EXTENDS Integers, Sequences",
      "VARIABLE x",
      "Init == x \\in {1, 2, 3, 4} \\cap {i \\in Int : i > 2}",
      "Next ==",
      "  /\\ x' \\in ({1, 2, 3, 4} \\ {i \\in Int : i > 2}) \\cup {x}",
      "  /\\ -5 \\notin {-5} \\ Int",
      "  /\\ <<1, 2>> \\in Seq({1, 2, 3}) \\cap Seq({0, 1, 2})",
      "  /\\ <<1, 2>> \\notin Seq({1, 2, 3}) \\ Seq({1, 2})",
    ];
    const config = "INIT Init\nNEXT Next";
    expect(await compareWithInterpreter(body, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("searches an invariant that reads TLCExt's Trace only once it fails", async () => {
    // As ewd840/EWD840_json does: the second disjunct, which serializes the trace, is never reached.
    const body = [
      "EXTENDS Naturals, Sequences, TLCExt",
      "VARIABLE x",
      "Init == x = 0",
      "Next == x < 3 /\\ x' = x + 1",
      "Inv == x < 10 \\/ Len(Trace) > 0",
    ];
    expect(
      await compareWithInterpreter(
        body,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
      ),
    ).toContainEqual(expect.stringMatching(COMPLETE));
  });

  it("tests guards fused in place: f[k] = c, f[k] = j, x = c and membership", async () => {
    const body = [
      "CONSTANT P",
      "VARIABLES f, x, s",
      'Init == f = [p \\in P |-> "a"] /\\ x = "go" /\\ s = {}',
      "Next ==",
      "  \\E p, q \\in P :",
      '    \\/ f[p] = "a" /\\ x = "go" /\\ f\' = [f EXCEPT ![p] = "b"] /\\ UNCHANGED <<x, s>>',
      '    \\/ f[p] # "a" /\\ f[p] \\in {"b", "c"} /\\ f\' = [f EXCEPT ![p] = "c"] /\\ UNCHANGED <<x, s>>',
      "    \\/ p \\notin s /\\ f[p] = f[q] /\\ s' = s \\cup {p} /\\ UNCHANGED <<f, x>>",
      '    \\/ x # "stop" /\\ s = P /\\ x\' = "stop" /\\ UNCHANGED <<f, s>>',
    ];
    const config = "CONSTANT P = {p1, p2, p3}\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE";
    expect(await compareStateLogs(body, config, false)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    expect(await compareWithInterpreter(body, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    // TLC can't compare a string with the integers it searches.
    const mistyped = ["VARIABLE x", 'Init == x = "a"', "Next == x \\in {1, 2} /\\ x' = x"];
    expect(await compareWithInterpreter(mistyped, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(stopped("values TLC can't compare")),
    );
  });

  it("reads a PlusCal pc once for the actions it switches between, finding and failing as each would", async () => {
    const body = [
      "EXTENDS Naturals",
      "CONSTANT N",
      "VARIABLES pc, x",
      "Procs == 1..N",
      'Init == pc = [p \\in Procs |-> "a"] /\\ x = 0',
      'a(p) == pc[p] = "a" /\\ pc\' = [pc EXCEPT ![p] = "b"] /\\ x\' = x + 1',
      'b(p) == pc[p] = "b" /\\ pc\' = [pc EXCEPT ![p] = "c"] /\\ UNCHANGED x',
      'c(p) == pc[p] = "c" /\\ x < 4 /\\ pc\' = [pc EXCEPT ![p] = "a"] /\\ UNCHANGED x',
      "Next == \\E p \\in Procs : a(p) \\/ b(p) \\/ c(p)",
    ];
    const config = "CONSTANT N = 2\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE";
    expect(await compareStateLogs(body, config, false)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    expect(await compareWithInterpreter(body, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    // An action that doesn't start with pc[p] = c leaves the others to test their own guards.
    const mixed = body.map((line) =>
      line.replace('c(p) == pc[p] = "c" /\\ x < 4', 'c(p) == x < 4 /\\ pc[p] = "c"'),
    );
    expect(await compareStateLogs(mixed, config, false)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    // A process outside pc's domain fails where the first action reads pc[p], and a constant TLC
    // can't compare with a string fails where its action compares it.
    const outside = body.map((line) => line.replace("\\E p \\in Procs", "\\E p \\in 0..N"));
    expect(await compareWithInterpreter(outside, config)).toContainEqual(
      expect.stringMatching(stopped("applied a function outside its domain")),
    );
    const mistyped = body.map((line) => line.replace('pc[p] = "b"', "pc[p] = 2"));
    expect(await compareWithInterpreter(mistyped, config)).toContainEqual(
      expect.stringMatching(stopped("equality of values TLC can't compare")),
    );
  });

  it("reads f[i][j] of a variable and two bound names in place", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLE f",
      "Init == f = [i \\in 1..2 |-> [j \\in 1..2 |-> 0]]",
      "Next == \\E i, j \\in 1..2 : f[i][j] < 2 /\\ f[j][i] # 1 /\\ f' = [f EXCEPT ![i][j] = @ + 1]",
    ];
    const config = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE";
    expect(await compareStateLogs(body, config, false)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    expect(await compareWithInterpreter(body, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    const outside = [
      "EXTENDS Naturals",
      "VARIABLE f",
      "Init == f = <<<<0>>, <<0, 0>>>>",
      "Next == \\E i, j \\in 1..2 : f[i][j] = 0 /\\ f' = f",
    ];
    expect(await compareWithInterpreter(outside, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(stopped("applied a function outside its domain")),
    );
  });

  it("takes TLC's shortcut past a walk once every variable is assigned, with warnings on", async () => {
    // With warnings on, the disjunction after y' = 1 is a guard once x and y are assigned, so it
    // gives one successor rather than two.
    const body = [
      "EXTENDS Naturals",
      "VARIABLES x, y",
      "Init == x = 0 /\\ y = 0",
      "Next == x' = (x + 1) % 3 /\\ y' = 1 /\\ (x' = 1 \\/ x' # 5)",
    ];
    for (const isWarningEnabled of [false, true]) {
      await compareStateLogs(body, "INIT Init\nNEXT Next", isWarningEnabled);
      expect(
        await compareWithInterpreter(body, "INIT Init\nNEXT Next", {}, isWarningEnabled),
      ).toContainEqual(expect.stringMatching(COMPLETE));
    }
  });

  it("walks a universal quantifier that assigns, in the initial predicate and an action", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLES s, t",
      "Init == /\\ \\A v \\in {1, 2} : s = v \\/ s \\in {1, 3}",
      "        /\\ t \\in {0, 1}",
      "Next == \\A i \\in {1, 2} : (s' = (s + i) % 4 /\\ t' = t) \\/ UNCHANGED <<s, t>>",
    ];
    await compareStateLogs(body, "INIT Init\nNEXT Next", false);
    // TLC walks the first binding, then the others in reverse: from the first, y' = 3 comes
    // before y' = 2.
    const reversed = [
      "EXTENDS Naturals",
      "VARIABLES x, y",
      "Init == x = 0 /\\ y = 0",
      "Next == \\A i \\in {1, 2, 3} : IF i = 1 THEN x' = (x + 1) % 3 ELSE y' = i \\/ y' \\in 0..4",
    ];
    await compareStateLogs(reversed, "INIT Init\nNEXT Next", false);
    expect(await compareWithInterpreter(body, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("walks a universal quantifier whose body only assigns, in the initial predicate", async () => {
    // TLC walks \A in getInitStates whatever its body, so s = v assigns s for the first binding
    // and tests it for the others, as AssignmentInit (TLC's tests) does.
    const body = [
      "EXTENDS Naturals",
      "VARIABLE s",
      "Init == \\/ \\A v \\in {2} : s = v /\\ s \\in {2}",
      "        \\/ \\A v \\in {6, 7} : s = v",
      "        \\/ \\A v \\in {9} : s \\in {8, 9} /\\ s > v - 1",
      "Next == UNCHANGED s",
    ];
    expect(await compareWithInterpreter(body, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("assigns or tests where a path may or may not have assigned a variable", async () => {
    // The walk is compiled path by path, knowing which variables each has assigned. Past more
    // paths than it compiles apart, or a walked \A, it knows only what every path assigned, and
    // decides at run time whether x' = e and UNCHANGED assign or test, and whether TLC's shortcut
    // applies.
    const paths = [
      "EXTENDS Naturals",
      "VARIABLES x, y, z",
      "Init == x = 0 /\\ y = 0 /\\ z = 0",
      "Next ==",
      "  /\\ \\/ x' = (x + 1) % 3",
      "     \\/ y' = (y + 1) % 3",
      "     \\/ z' = (z + 1) % 3",
      "     \\/ x' = x /\\ y' = (y + 2) % 3",
      "     \\/ y' = y /\\ z' = z",
      "     \\/ x' = (x + 2) % 3 /\\ z' = (z + 2) % 3",
      "     \\/ TRUE",
      "  /\\ x' \\in {x, (x + 1) % 3}",
      "  /\\ y' = y",
      "  /\\ UNCHANGED <<y, z>>",
      "  /\\ x' + y' + z' # 5",
      "  /\\ x' = 2 \\/ z' = 1 \\/ y' = 0",
    ];
    const walked = [
      "EXTENDS Naturals",
      "VARIABLES x, y, z",
      "Init == x = 0 /\\ y = 0 /\\ z \\in {0, 1}",
      "Next == /\\ \\A i \\in {1, 2} : x' = i \\/ y' = (y + i) % 3",
      "        /\\ x' \\in {0, 1, 2}",
      "        /\\ y' = y \\/ y' = 2",
      "        /\\ UNCHANGED z",
      "        /\\ x' = 1 \\/ y' = 2",
    ];
    const config = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE";
    for (const body of [paths, walked]) {
      for (const isWarningEnabled of [false, true]) {
        expect(await compareStateLogs(body, config, isWarningEnabled)).toContainEqual(
          expect.stringMatching(COMPLETE),
        );
        expect(await compareWithInterpreter(body, config, {}, isWarningEnabled)).toContainEqual(
          expect.stringMatching(COMPLETE),
        );
      }
    }
  });

  it("compiles a walk of many independent branches in time linear in its size", async () => {
    // Each conjunct has a path that assigns its variable and one that doesn't, so the paths into
    // the rest of the walk double with each conjunct. Only one is ever walked, as the guard fails.
    const variables = Array.from({ length: 40 }, (_, index) => `x${index}`);
    const body = [
      `VARIABLES flag, ${variables.join(", ")}`,
      `Init == flag = 0 /\\ ${variables.map((name) => `${name} = 0`).join(" /\\ ")}`,
      "Next ==",
      ...variables.map((name) => `  /\\ \\/ flag = 1 /\\ ${name}' = 1\n     \\/ flag = 0`),
      `  /\\ UNCHANGED <<flag, ${variables.join(", ")}>>`,
    ];
    const config = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE";
    expect(await compareStateLogs(body, config, false)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("checks a successor before what the walk does after it, as it hands over", async () => {
    // Where nothing prints, the search checks a successor once the walk reaches the next one, so
    // its fingerprint's probe doesn't wait on memory. A successor the walk completed is still
    // checked before the walk's next failure or incomplete successor, so the search stops where
    // it did: at the first successor's invariant.
    const config = "INIT Init\nNEXT Next\nINVARIANT Inv";
    const failing = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "Init == x = 0",
      "Next == \\/ x' = x + 1",
      "        \\/ x' = x + 2 /\\ 1 \\div (x - x) = 1",
      "Inv == x < 1",
    ];
    const incomplete = [
      "EXTENDS Naturals",
      "VARIABLES x, y",
      "Init == x = 0 /\\ y = 0",
      "Next == \\/ x' = x + 1 /\\ y' = y",
      "        \\/ x' = x + 2",
      "Inv == x < 1",
    ];
    for (const body of [failing, incomplete]) {
      expect(await compareWithInterpreter(body, config)).toContainEqual(
        expect.stringMatching(stopped("an invariant violated")),
      );
    }
    // A walk that reads the count of distinct states sees each new successor added at once.
    const counting = [
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      "Init == x = 0",
      "Next == \\/ x' = (x + 1) % 5",
      '        \\/ x\' = (10 + TLCGet("distinct")) % 20',
    ];
    await compareStateLogs(counting, "INIT Init\nNEXT Next", false);
    expect(await compareWithInterpreter(counting, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("caches membership in a set that isn't constant by the element and the set", async () => {
    // x \in S is cached by the ids it reads when S isn't constant: a miss would compare x with
    // S's elements, as TLC's binary search does, to fail where TLC fails, which isn't cached.
    const body = [
      "EXTENDS Naturals",
      "VARIABLES sent, n",
      "Init == sent = {} /\\ n = 0",
      "Next == \\E p \\in 1..3 :",
      '  /\\ [kind |-> "ack", from |-> p] \\notin sent',
      '  /\\ \\/ [kind |-> "req", from |-> p] \\in sent',
      "     \\/ p = n + 1",
      '  /\\ sent\' = sent \\cup {[kind |-> IF [kind |-> "req", from |-> p] \\in sent',
      '                                   THEN "ack" ELSE "req", from |-> p]}',
      "  /\\ n' = (n + p) % 3",
    ];
    const config = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE";
    await compareStateLogs(body, config, false);
    expect(await compareWithInterpreter(body, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    const incomparable = [
      "EXTENDS Naturals, FiniteSets",
      "VARIABLE s",
      "Init == s = {[a |-> 1]}",
      'Next == s\' = s \\cup {[a |-> Cardinality(s) + 1]} /\\ (Cardinality(s) < 3 \\/ "x" \\in s)',
    ];
    expect(await compareWithInterpreter(incomparable, config)).toContainEqual(
      expect.stringMatching(stopped("values TLC can't compare")),
    );
  });

  it("walks a universal quantifier with 2^32 bindings, and doesn't skip its body", async () => {
    // The product of the sizes doesn't fit 32 bits, and the first binding already rules out every
    // successor. The interpreter builds the product of the sets, so this compares with the
    // TypeScript engine, which walks the bindings as the native engine does.
    const options = {
      source: toModule([
        "EXTENDS Naturals",
        "VARIABLE x",
        "Init == x = 0",
        "Next == x' = 1 /\\ (\\A i \\in 1..65536, j \\in 1..65536 : x' = 0)",
      ]),
      config: "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
      isWarningEnabled: false,
    };
    const native = await run(options, {
      PROVE_IT_ENGINE: "debug",
      PROVE_IT_ENGINE_BACKEND: "rust",
    });
    const typescript = await run(options, {
      PROVE_IT_ENGINE: "debug",
      PROVE_IT_ENGINE_BACKEND: "ts",
    });
    expect(native.result).toEqual(typescript.result);
    expect(native.lines).toContainEqual(expect.stringMatching(COMPLETE));
  });

  it("evaluates a walked function's argument once, so a Print in it prints once", async () => {
    const body = [
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      "Init == x = 0",
      'Next == LET f[n \\in 0..2] == x\' = n IN f[Print("ARG", (x + 1) % 3)]',
    ];
    expect(await compareWithInterpreter(body, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  // TLC evaluates a record's fields in the order written (Tool's OPCODE_rc), a set map's body for
  // each element of its normalized set, and a union's operands left to right, so what they print
  // comes in that order.
  it("prints in records, set maps, unions and membership in the order TLC evaluates them", async () => {
    const body = [
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      "Init == x = 0",
      "Next == x < 2 /\\ x' = x + 1",
      'Record == [zeta |-> PrintT(<<"zeta", x>>), alpha |-> PrintT(<<"alpha", x>>)]',
      'Mapped == {PrintT(<<"map", n, x>>) : n \\in {3, 1, 2}}',
      'Joined == UNION {{PrintT(<<"left", x>>)} \\cup {PrintT(<<"right", x>>)}}',
      'Held == PrintT(<<"element", x>>) \\in {PrintT(<<"set", x>>)}',
      "Inv == Record.alpha /\\ Mapped = {TRUE} /\\ Joined = {TRUE} /\\ Held",
    ];
    const config = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE";
    expect(await compareWithInterpreter(body, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    // TLC evaluates a definition each time it is named, in a set enumeration too.
    const named = [
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      "Init == x = 0",
      "P == Print(x, TRUE)",
      "Next == P /\\ {P} # {} /\\ x' = (x + 1) % 3",
    ];
    expect(await compareWithInterpreter(named, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("fails where TLC's evaluation of a lazy function or a later bound fails", async () => {
    const config = "INIT Init\nNEXT Next\nINVARIANT Inv";
    for (const [invariant, reason] of [
      // TLC reads a function it keeps lazy at the key of an EXCEPT (FcnLambdaValue.select): the
      // EXCEPT changes nothing outside the domain, and the value there may fail.
      [
        "LET f == [i \\in Nat |-> i + x] g == [f EXCEPT ![-1] = 5] IN g[-1] = 5",
        "applied a function outside its domain",
      ],
      [
        "LET f == [i \\in Nat |-> 10 \\div (i + x)] IN [f EXCEPT ![0] = 7][3] = 3",
        "division by zero",
      ],
      // TLC builds a lazy function to compare it, with itself too.
      [
        "LET f == [i \\in Nat |-> i + x] IN f = f",
        "unsupported: comparing a function TLC keeps lazy",
      ],
      [
        "LET f == [i \\in Nat |-> i + x] IN {f} = {f}",
        "unsupported: comparing a function TLC keeps lazy",
      ],
      [
        "LET f == [i \\in Nat |-> i + x] IN f \\in {f}",
        "unsupported: comparing a function TLC keeps lazy",
      ],
      // TLC evaluates every bound's set before it binds any (Tool.contexts).
      ["~(\\E i \\in {}, j \\in (1 \\div x) .. 2 : TRUE)", "division by zero"],
      ["\\A i \\in {}, j \\in x : FALSE", "quantified over a non-set"],
      ["{<<i, j>> : i \\in {}, j \\in (1 \\div x) .. 2} = {}", "division by zero"],
    ]) {
      const body = [
        "EXTENDS Integers",
        "VARIABLE x",
        "Init == x = 0",
        "Next == x < 1 /\\ x' = x + 1",
        `Inv == ${invariant}`,
      ];
      expect([invariant, await compareWithInterpreter(body, config)]).toEqual([
        invariant,
        expect.arrayContaining([expect.stringMatching(stopped(reason))]),
      ]);
    }
  });

  it("checks invariants, constraints, action constraints and action properties", async () => {
    const body = [
      "EXTENDS Naturals, TLC",
      "VARIABLES x, y",
      "Init == x = 0 /\\ y = 0",
      "Next == \\/ x' = x + 1 /\\ y' = y",
      "        \\/ y' = y + 1 /\\ x' = x",
      "Spec == Init /\\ [][Next]_<<x, y>>",
      'Inv == x + y < 20 /\\ TLCGet("level") < 30',
      "Bound == x < 4 /\\ y < 5",
      'Steps == x\' >= x /\\ TLCGet("distinct") < 100',
      "Moves == [][x' + y' > x + y]_<<x, y>>",
    ];
    const config =
      "SPECIFICATION Spec\nINVARIANT Inv\nCONSTRAINT Bound\nACTION_CONSTRAINT Steps\nPROPERTY Moves";
    await compareStateLogs(body, config, false);
    expect(await compareWithInterpreter(body, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("tells states apart by their VIEW", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLES x, steps",
      "Init == x = 0 /\\ steps = 0",
      "Next == x' = (x + 1) % 5 /\\ steps' = steps + 1",
      "View == x % 3",
    ];
    const config = "INIT Init\nNEXT Next\nVIEW View";
    await compareStateLogs(body, config, false);
    expect(await compareWithInterpreter(body, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("checks the invariant of the state that first takes a VIEW's key, on any number of threads", async () => {
    // Every initial state's successor has the key 0, and only the first's, (0, 0), holds the
    // invariant, or evaluates at all: TLC checks only that one, though a thread that expands other
    // initial states meets the others first.
    const body = [
      "EXTENDS Naturals",
      "VARIABLES x, y",
      "Init == x \\in 1..4096 /\\ y = 0",
      "Next == \\/ x > 0 /\\ x' = 0 /\\ y' = IF x = 1 THEN 0 ELSE 1",
      "        \\/ x = 0 /\\ UNCHANGED <<x, y>>",
      "View == x",
      "Inv == y = 0",
      "Divides == 1 \\div (1 - y) = 1",
    ];
    const config = "INIT Init\nNEXT Next\nVIEW View\nINVARIANT ";
    for (const [workers, invariant] of ["1", "2", "4"].flatMap((count) =>
      ["Inv", "Divides"].map((name) => [count, name]),
    )) {
      const settings = { PROVE_IT_WORKERS: workers, PROVE_IT_SHARED_LEVEL: "1" };
      expect(await compareWithInterpreter(body, config + invariant, settings)).toContainEqual(
        expect.stringMatching(COMPLETE),
      );
    }
  });

  it("searches a spec that ranks the strings ToString makes on one thread", async () => {
    const body = [
      "EXTENDS Naturals, TLC",
      "VARIABLES x, text",
      'Init == x \\in 1..3000 /\\ text = ""',
      "Next == \\/ x < 3002 /\\ x' = x + 1 /\\ text' = ToString(x)",
      "        \\/ x = 3002 /\\ UNCHANGED <<x, text>>",
    ];
    const config = "INIT Init\nNEXT Next";
    const settings = { PROVE_IT_WORKERS: "4", PROVE_IT_SHARED_LEVEL: "1" };
    expect(await compareWithInterpreter(body, config, settings)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("reduces by symmetry, with and without a VIEW, and hands over representatives", async () => {
    const body = [
      "EXTENDS Naturals, FiniteSets, TLC",
      "CONSTANT Procs",
      "VARIABLES pc, owner",
      'Init == pc = [p \\in Procs |-> "idle"] /\\ owner = {}',
      "Next == \\E p \\in Procs :",
      '  \\/ pc[p] = "idle" /\\ pc\' = [pc EXCEPT ![p] = "busy"] /\\ owner\' = owner \\cup {p}',
      '  \\/ pc[p] = "busy" /\\ pc\' = [pc EXCEPT ![p] = "idle"] /\\ owner\' = owner \\ {p}',
      "Sym == Permutations(Procs)",
      "View == <<pc, Cardinality(owner)>>",
      "Inv == Cardinality(owner) < 3",
    ];
    const withSets = body;
    const config = "CONSTANT Procs = {p1, p2, p3}\nINIT Init\nNEXT Next\nSYMMETRY Sym";
    await compareStateLogs(withSets, config, false);
    expect(await compareWithInterpreter(withSets, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    await compareStateLogs(withSets, `${config}\nVIEW View`, false);
    expect(
      await compareWithInterpreter(withSets, `${config}\nVIEW View`, { PROVE_IT_STOP_AT: "2" }),
    ).toContainEqual(expect.stringMatching(stopped("stopped where PROVE_IT_STOP_AT asked")));
    expect(await compareWithInterpreter(withSets, `${config}\nINVARIANT Inv`)).toContainEqual(
      expect.stringMatching(stopped("an invariant violated")),
    );
  });

  // TLC evaluates the SYMMETRY definition as it starts, and the engine builds the group as TLC
  // does: from sets with fewer than two elements too, and none where no set has two.
  it("builds the group of the SYMMETRY definition as TLC starts", async () => {
    const body = [
      "EXTENDS TLC",
      "CONSTANTS Procs, Single",
      "VARIABLE owner",
      "Init == owner \\in Procs \\cup Single",
      "Next == owner' \\in Procs \\cup Single",
      "Sym == Permutations(Procs) \\cup Permutations(Single)",
    ];
    for (const procs of ["{p1, p2, p3}", "{p1}"]) {
      const config = `CONSTANTS Procs = ${procs}\nSingle = {q1}\nINIT Init\nNEXT Next\nSYMMETRY Sym`;
      expect(await compareWithInterpreter(body, config)).toContainEqual(
        expect.stringMatching(COMPLETE),
      );
    }
  });

  // summerset's Crossword_MC: the operator that gives each set's permutations is applied once per
  // set, and looked through again for each is no recursion.
  it("builds the group of a SYMMETRY that applies one operator to several sets", async () => {
    const body = [
      "EXTENDS Naturals, FiniteSets, TLC",
      "CONSTANTS Procs, Values",
      "VARIABLES owner, value",
      "Perms(set) == IF Cardinality(set) > 1 THEN Permutations(set) ELSE {}",
      "Init == owner \\in Procs /\\ value \\in Values",
      "Next == owner' \\in Procs /\\ value' \\in Values",
      "Sym == Perms(Procs) \\cup Perms(Values)",
    ];
    const config =
      "CONSTANTS Procs = {p1, p2, p3}\nValues = {v1, v2}\nINIT Init\nNEXT Next\nSYMMETRY Sym";
    expect(await compareWithInterpreter(body, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("answers ENABLED by running the action", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "Up == x < 3 /\\ x' = x + 1",
      "Reset == x = 3 /\\ x' = 0",
      "Init == x = 0",
      "Next == Up \\/ Reset",
      "Inv == ENABLED Up \\/ ENABLED Reset",
      "NotStuck == ENABLED (\\E n \\in 0..3 : x' = n /\\ n # x)",
    ];
    const config = "INIT Init\nNEXT Next\nINVARIANT Inv\nINVARIANT NotStuck";
    await compareStateLogs(body, config, false);
    expect(await compareWithInterpreter(body, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("records the graph and answers the temporal properties' predicates", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLES x, y",
      "vars == <<x, y>>",
      "Init == x = 0 /\\ y = 0",
      "Inc == x < 3 /\\ x' = x + 1 /\\ y' = y",
      "Flip == y' = 1 - y /\\ x' = x",
      "Reset == x = 3 /\\ x' = 0 /\\ y' = y",
      "Next == Inc \\/ Flip \\/ Reset",
      "Spec == Init /\\ [][Next]_vars /\\ WF_vars(Inc) /\\ WF_vars(Reset)",
      "Returns == []<>(x = 0)",
      "Steps == []<><<Inc>>_vars",
      "Settles == <>[](y = 0)",
    ];
    for (const [properties, status] of [
      ["PROPERTY Returns\nPROPERTY Steps", "success"],
      ["PROPERTY Settles", "liveness-violation"],
    ] as const) {
      const config = `SPECIFICATION Spec\n${properties}`;
      const lines = await compareWithInterpreter(body, config, { PROVE_IT_LIVE_CHECK: "1" });
      expect(lines).toContainEqual(expect.stringMatching(COMPLETE));
      expect(lines).toContainEqual(
        expect.stringMatching(/^\[engine\] found 8 states in \d+ ms; the interpreter checks/),
      );
      expect(lines).toContain("[engine] answers ENABLED from the steps its search took");
      // The native engine answers every predicate, the action ones too, so the interpreter
      // evaluates none.
      expect(lines.filter((line) => line.includes("to the interpreter"))).toEqual([]);
      const stopped = await compareWithInterpreter(body, config, { PROVE_IT_STOP_AT: "3" });
      expect(stopped).toContainEqual(
        expect.stringMatching(/^\[engine\] native: stopped: stopped where PROVE_IT_STOP_AT asked/),
      );
      const options = { source: toModule(body), config };
      const native = await run(options, {
        PROVE_IT_ENGINE: "debug",
        PROVE_IT_ENGINE_BACKEND: "rust",
      });
      expect(native.result.status).toBe(status);
    }
    await compareStateLogs(body, "SPECIFICATION Spec\nPROPERTY Returns", false);
  });

  it("checks the temporal properties itself, and the interpreter prints its counterexample", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLES x, y",
      "vars == <<x, y>>",
      "Init == x = 0 /\\ y = 0",
      "Inc == x < 3 /\\ x' = x + 1 /\\ y' = y",
      "Flip == y' = 1 - y /\\ x' = x",
      "Reset == x = 3 /\\ x' = 0 /\\ y' = y",
      "Next == Inc \\/ Flip \\/ Reset",
      "Weak == Init /\\ [][Next]_vars /\\ WF_vars(Inc) /\\ WF_vars(Reset)",
      "Strong == Init /\\ [][Next]_vars /\\ SF_vars(Inc) /\\ SF_vars(Reset)",
      "Unfair == Init /\\ [][Next]_vars",
      "Returns == []<>(x = 0)",
      "Steps == []<><<Inc>>_vars",
      "Settles == <>[](y = 0)",
      "Leads == (x = 3) ~> (y = 1)",
    ];
    for (const [config, verdict] of [
      ["SPECIFICATION Weak\nPROPERTY Returns\nPROPERTY Steps", "holds"],
      ["SPECIFICATION Strong\nPROPERTY Returns", "holds"],
      ["SPECIFICATION Weak\nPROPERTY Settles", "lasso"],
      ["SPECIFICATION Strong\nPROPERTY Leads", "lasso"],
      ["SPECIFICATION Unfair\nPROPERTY Returns", "lasso"],
      ["SPECIFICATION Weak\nPROPERTY Returns\nPROPERTY Settles\nPROPERTY Leads", "lasso"],
    ] as const) {
      const lines = await compareWithInterpreter(body, config);
      expect(lines).toContain(`[engine] native: liveness: ${verdict}`);
      // PROVE_IT_LIVE_CHECK has the interpreter check the properties on the graph too, and throws
      // where it finds otherwise.
      await compareWithInterpreter(body, config, { PROVE_IT_LIVE_CHECK: "1" });
    }
    // Without the replay, TLCGet("diameter") still reads the search's depth.
    const diameter = ["EXTENDS Naturals, TLC", ...body.slice(1), 'Post == TLCGet("diameter") = 5'];
    const lines = await compareWithInterpreter(
      diameter,
      "SPECIFICATION Weak\nPROPERTY Returns\nPOSTCONDITION Post",
    );
    expect(lines).toContain("[engine] native: liveness: holds");
    expect(lines).toContainEqual(expect.stringMatching(COMPLETE));
  });

  it("checks the temporal properties on the states a step reached under a VIEW", async () => {
    // The view tells (0, 1) apart from (0, 0) by x alone, so the step back to x = 0 reaches a
    // state the search doesn't store, on which TLC checks the properties.
    const body = [
      "EXTENDS Naturals",
      "VARIABLES x, t",
      "vars == <<x, t>>",
      "Init == x = 0 /\\ t = 0",
      "Next == x' = (x + 1) % 3 /\\ t' = 1 - t",
      "Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)",
      "View == x",
      "Settles == <>[](t = 0)",
      "Visits == []<>(t = 1)",
    ];
    for (const [property, verdict] of [
      ["Settles", "lasso"],
      ["Visits", "holds"],
    ] as const) {
      const config = `SPECIFICATION Spec\nVIEW View\nPROPERTY ${property}`;
      const lines = await compareWithInterpreter(body, config);
      expect(lines).toContain(`[engine] native: liveness: ${verdict}`);
      await compareWithInterpreter(body, config, { PROVE_IT_LIVE_CHECK: "1" });
    }
  });

  it("compiles a predicate that holds a temporal formula in a branch it never takes", async () => {
    // TLC's test model Github1389ViolatedB: the liveness checker's atom is Reach(0), whose body
    // holds <> in the branch for n > 0.
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "RECURSIVE Reach(_)",
      "Reach(n) == IF n = 0 THEN (x = 99) ELSE <>(Reach(n - 1))",
      "Init == x = 0",
      "Next == x' = 1 - x",
      "Spec == Init /\\ [][Next]_x /\\ WF_x(Next)",
      "PropViolated == Reach(3)",
    ];
    const config = "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\nPROPERTY PropViolated";
    const lines = await compareWithInterpreter(body, config);
    expect(lines).toContain("[engine] native: liveness: lasso");
    await compareWithInterpreter(body, config, { PROVE_IT_LIVE_CHECK: "1" });
  });

  it("takes the steps from a state a step reached but the search didn't store", async () => {
    // TLC's ChooseTableauSymmetry: a late node of the tableau is of a state the search told apart
    // from the one stored for it only under SYMMETRY, so TLC runs Next from that state.
    const body = [
      "EXTENDS TLC",
      "CONSTANTS a, b",
      "VARIABLE arr",
      "Val == {a, b}",
      'Init == arr = [v \\in Val |-> "ready"]',
      `Ready(v) == arr[v] = "ready" /\\ arr' = [arr EXCEPT ![v] = "busy"]`,
      `Busy(v) == arr[v] = "busy" /\\ arr' = [arr EXCEPT ![v] = "done"]`,
      `Done(v) == arr[v] = "done" /\\ arr' = [arr EXCEPT ![v] = "ready"]`,
      "Next == \\E v \\in Val : Ready(v) \\/ Busy(v) \\/ Done(v)",
      "Spec == Init /\\ [][Next]_<<arr>> /\\ WF_<<arr>>(Next)",
      "Symmetry == Permutations(Val)",
      'Liveness == LET v == CHOOSE e \\in Val : TRUE IN (arr[v] = "busy") ~> (arr[v] = "ready")',
      "Negated == ~Liveness",
    ];
    const config =
      "CONSTANTS a = a\nb = b\nSYMMETRY Symmetry\nSPECIFICATION Spec\nPROPERTY Negated";
    const lines = await compareWithInterpreter(body, config);
    expect(lines).toContain("[engine] native: liveness: lasso");
    await compareWithInterpreter(body, config, { PROVE_IT_LIVE_CHECK: "1" });
    // TLC prints what Next prints from that state where the engine doesn't follow, so the
    // interpreter checks from the start.
    const printing = body.map((line) => line.replace("Next == ", "Next == PrintT(arr) /\\ "));
    expect(await compareWithInterpreter(printing, config)).toContainEqual(
      expect.stringMatching(
        /native: stopped: printing where .*: steps from states it didn't store/,
      ),
    );
  });

  it("searches again where a search under SYMMETRY with temporal properties stops part way", async () => {
    // TLC's SymmetryLivenessTableau: the graph a stopped search recorded holds the states it
    // stored, not those each step reached, so the interpreter searches again from the start.
    const body = [
      "EXTENDS TLC",
      "CONSTANTS a, b, c, d, e, f, NoVal",
      "VARIABLES mem, ctl, buf, memInt",
      "Proc == {c, d}",
      "Adr == {e, f}",
      "Val == {a, b}",
      'MReq == [op : {"Rd"}, adr : Adr] \\cup [op : {"Wr"}, adr : Adr, val : Val]',
      "Init == /\\ mem \\in [Adr -> Val]",
      '        /\\ ctl = [p \\in Proc |-> "rdy"]',
      "        /\\ buf = [p \\in Proc |-> NoVal]",
      "        /\\ memInt \\in {<<p, NoVal>> : p \\in Proc}",
      'Req(p) == /\\ ctl[p] = "rdy"',
      "          /\\ \\E req \\in MReq : /\\ memInt' = <<p, req>>",
      "                               /\\ buf' = [buf EXCEPT ![p] = req]",
      `                               /\\ ctl' = [ctl EXCEPT ![p] = "busy"]`,
      "          /\\ UNCHANGED mem",
      'Do(p) == /\\ ctl[p] = "busy"',
      `         /\\ mem' = IF buf[p].op = "Wr" THEN [mem EXCEPT ![buf[p].adr] = buf[p].val] ELSE mem`,
      `         /\\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr" THEN NoVal ELSE mem[buf[p].adr]]`,
      `         /\\ ctl' = [ctl EXCEPT ![p] = "done"]`,
      "         /\\ UNCHANGED memInt",
      'Rsp(p) == /\\ ctl[p] = "done"',
      "          /\\ memInt' = <<p, buf[p]>>",
      `          /\\ ctl' = [ctl EXCEPT ![p] = "rdy"]`,
      "          /\\ UNCHANGED <<mem, buf>>",
      "vars == <<memInt, mem, ctl, buf>>",
      "Next == \\E p \\in Proc : Req(p) \\/ Do(p) \\/ Rsp(p)",
      "Spec == Init /\\ [][Next]_vars /\\ \\A p \\in Proc : WF_vars(Do(p) \\/ Rsp(p))",
      'Liveness == \\A p \\in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")',
      "Symmetry == Permutations(Val) \\union Permutations(Proc) \\union Permutations(Adr)",
    ];
    const config =
      "CONSTANTS a = a\nb = b\nc = c\nd = d\ne = e\nf = f\nNoVal = NoVal\nSYMMETRY Symmetry\nSPECIFICATION Spec\nPROPERTY Liveness";
    for (const backend of ["ts", "rust"]) {
      expect(
        await compareWithInterpreter(body, config, {
          PROVE_IT_ENGINE_BACKEND: backend,
          PROVE_IT_STOP_AT: "65",
        }),
      ).toContainEqual(expect.stringMatching(/stopped where PROVE_IT_STOP_AT asked/));
    }
  });

  it("checks the temporal properties part way through the search, as TLC does", async () => {
    // Without fairness x stutters at 0, which a check after two states finds with states left to
    // expand; with it, x returns to 0 forever, so the check finds nothing and the search goes on.
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "Init == x = 0",
      "Next == x' = (x + 1) % 10",
      "Fair == Init /\\ [][Next]_x /\\ WF_x(Next)",
      "Unfair == Init /\\ [][Next]_x",
      "Reaches == <>(x = 9)",
      "Returns == []<>(x = 0)",
    ];
    const directory = mkdtempSync(join(tmpdir(), "prove-it-native-periodic-"));
    const log = join(directory, "log.jsonl");
    for (const [spec, property, status] of [
      ["Unfair", "Reaches", "liveness-violation"],
      ["Fair", "Returns", "success"],
    ] as const) {
      const options = {
        source: toModule(body),
        config: `SPECIFICATION ${spec}\nPROPERTY ${property}`,
      };
      const native = await run(options, {
        PROVE_IT_ENGINE: "debug",
        PROVE_IT_ENGINE_BACKEND: "rust",
        PROVE_IT_TEST_LIVE_CHECK_AT: "2",
        PROVE_IT_STATE_LOG: log,
      });
      const interpreter = await run(options, {
        PROVE_IT_ENGINE: "0",
        PROVE_IT_TEST_LIVE_CHECK_AT: "2",
      });
      expect(native.lines).toContainEqual(expect.stringMatching(COMPLETE));
      expect(native.result.status).toBe(status);
      expect(native.result).toEqual(interpreter.result);
      expect(native.progress).toEqual(interpreter.progress);
      expect(native.progress).toContainEqual(
        expect.stringMatching(/"isComplete":false,"states":2,/),
      );
      // The log holds the states the search found when the check found the counterexample.
      const header = JSON.parse(readLogLines(log)[0]);
      expect([header.count, header.expanding, header.stopped]).toEqual(
        status === "success"
          ? [10, 10, null]
          : [3, 2, "a counterexample part way through the search"],
      );
    }
    rmSync(directory, { recursive: true, force: true });
  });

  it("keeps the graph past four million states where it checks the properties as it goes", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "Init == x \\in 0..4000000",
      "Spec == Init /\\ [][x' = x]_x",
      "Holds == <>(x >= 0)",
    ];
    const native = await run(
      { source: toModule(body), config: "SPECIFICATION Spec\nPROPERTY Holds" },
      { PROVE_IT_ENGINE: "debug", PROVE_IT_ENGINE_BACKEND: "rust" },
    );
    expect(native.lines).toContainEqual(expect.stringMatching(COMPLETE));
    expect([native.result.status, native.result.distinctStates]).toEqual(["success", 4_000_001]);
  }, 60_000);

  it("answers the temporal properties' predicates on several threads as on one", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLES x, y",
      "vars == <<x, y>>",
      "Init == x \\in 0..40 /\\ y = 0",
      "Inc == x < 40 /\\ x' = x + 1 /\\ y' = y",
      "Flip == y' = 1 - y /\\ x' = x",
      "Reset == x = 40 /\\ x' = 0 /\\ y' = y",
      "Next == Inc \\/ Flip \\/ Reset",
      "Spec == Init /\\ [][Next]_vars /\\ WF_vars(Inc) /\\ SF_vars(Reset)",
      "Returns == []<>(x = 0)",
      "Steps == []<><<Inc>>_vars",
      "Settles == <>[](y = 0)",
    ];
    for (const property of ["Returns\nPROPERTY Steps", "Settles"]) {
      const config = `SPECIFICATION Spec\nPROPERTY ${property}`;
      const lines = await compareWithInterpreter(body, config, { PROVE_IT_WORKERS: "4" });
      expect(lines).toContainEqual(expect.stringMatching(COMPLETE));
    }
  });

  it("hands the graph over past four million states under -lncheck final", async () => {
    // TLC's test model Github710b: TLC stops at the third state, whose tableau node accepts every
    // behavior, though x grows without bound and the properties are checked only at the end.
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "Init == x = 1",
      "Spec == Init /\\ [][x' = x + 1]_x",
      "AtMostOnce == [](x > 1 => [](x > 2))",
    ];
    const native = await run(
      {
        source: toModule(body),
        config: "SPECIFICATION Spec\nPROPERTY AtMostOnce",
        livenessCheck: "final",
      },
      { PROVE_IT_ENGINE: "debug", PROVE_IT_ENGINE_BACKEND: "rust" },
    );
    expect(native.lines).toContainEqual(
      expect.stringMatching(stopped("a state graph too large to keep")),
    );
    expect([native.result.status, native.result.distinctStates]).toEqual(["property-violation", 3]);
  }, 60_000);

  it("reports a tableau node that accepts every behavior as TLC finds it", async () => {
    // TLC's test model Github1389Counting: x becomes TRUE at most twice.
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "RECURSIVE AtMost(_)",
      "AtMost(n) == IF n = 0 THEN []~x ELSE [](x => [](~x => AtMost(n - 1)))",
      "Init == x = FALSE",
      "Next == x' \\in BOOLEAN",
      "Spec == Init /\\ [][Next]_x",
      "CountAtMostTwo == AtMost(2)",
    ];
    const config = "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\nPROPERTY CountAtMostTwo";
    const lines = await compareWithInterpreter(body, config);
    expect(lines).toContain("[engine] native: liveness: accepted");
    // The interpreter prints the node's path without checking the properties itself.
    expect(lines).toContainEqual(
      expect.stringMatching(/^\[engine\] found 2 states in \d+ ms; the interpreter prints/),
    );
    await compareWithInterpreter(body, config, { PROVE_IT_LIVE_CHECK: "1" });
  });

  it("prints what the search and the temporal properties print in TLC's order", async () => {
    // TLC prints PrintT in Next as the search takes each step, and again each time its liveness
    // checks evaluate Next: ENABLED of the fairness and the action on each step.
    const body = [
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      "Next == \\/ x < 3 /\\ PrintT(x) /\\ x' = x + 1",
      "        \\/ x = 3 /\\ UNCHANGED x",
      "Spec == x = 0 /\\ [][Next]_x /\\ WF_x(Next)",
      "Ends == <>(x = 3)",
      'Shown == []<>(PrintT(<<"at", x>>) /\\ x = 3)',
      "Stays == <>[](x = 0)",
    ];
    for (const [property, verdict] of [
      ["Ends", "holds"],
      ["Shown", "holds"],
      ["Stays", "lasso"],
    ] as const) {
      const lines = await compareWithInterpreter(body, `SPECIFICATION Spec\nPROPERTY ${property}`);
      expect(lines).toContain(`[engine] native: liveness: ${verdict}`);
    }
    // Where only the search prints: again as TLC runs Next from a state it adds a node of late; and
    // where a node accepts every behavior, the interpreter checks from the start.
    const cycling = [
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      "Init == x = 0",
      "Next == PrintT(x) /\\ x' = (x + 1) % 3",
      "Fair == Init /\\ [][Next]_x /\\ WF_x(Next)",
      "Unfair == Init /\\ [][Next]_x",
      "Never == ~(<>(x = 2))",
      "Leads == [](x = 0 => <>(x = 2))",
    ];
    for (const [spec, property, verdict] of [
      ["Unfair", "Never", /native: stopped: printing where .*: a node that accepts/],
      ["Fair", "Leads", /native: liveness: holds/],
    ] as const) {
      const lines = await compareWithInterpreter(
        cycling,
        `SPECIFICATION ${spec}\nPROPERTY ${property}`,
      );
      expect(lines).toContainEqual(expect.stringMatching(verdict));
    }
    // TLC checks no invariant as it runs Next again for a late node, so where an invariant prints
    // the interpreter checks from the start.
    const checked = [...cycling, 'Shown == PrintT(<<"inv", x>>)'].map((line) =>
      line.replace("Next == PrintT(x) /\\ ", "Next == "),
    );
    expect(
      await compareWithInterpreter(checked, "SPECIFICATION Fair\nINVARIANT Shown\nPROPERTY Leads"),
    ).toContainEqual(
      expect.stringMatching(/native: stopped: printing where .*: prints it doesn't/),
    );
    // Nor does Next print the same again where it prints the count of distinct states, which
    // has grown since.
    const counted = [
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      "Init == x = 0",
      "A == x' = (x + 1) % 3",
      'Next == PrintT(<<x, TLCGet("distinct")>>) /\\ A',
      "Fair == Init /\\ [][Next]_x /\\ WF_x(A)",
      "Leads == [](x = 0 => <>(x = 2))",
    ];
    expect(
      await compareWithInterpreter(counted, "SPECIFICATION Fair\nPROPERTY Leads"),
    ).toContainEqual(
      expect.stringMatching(/native: stopped: printing where .*: prints it doesn't/),
    );
  });

  it('reads TLCGet("diameter") in a temporal property as TLC\'s search goes', async () => {
    // TLC's diameter is the deepest level its search has found when it adds a state to the
    // behavior graphs, after it expanded the state: 2, 3, 4 and 4 for x = 0 to 3.
    const body = [
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      "Spec == x = 0 /\\ [][x' = (x + 1) % 4]_x /\\ WF_x(x' = (x + 1) % 4)",
      'Below == <>[](x < TLCGet("diameter"))',
      'Past == <>[](TLCGet("diameter") > x + 1)',
      // Holds only where the diameter is read as each state is added, not as the search ends.
      'Early == <>[](TLCGet("diameter") < 4 + x)',
      // The tableau's predicates and a fairness's subscript, read at the diameter TLC has then.
      'Nested == []<>(TLCGet("diameter") < 4 /\\ <>(x = 2))',
      'Sub == IF TLCGet("diameter") < 4 THEN x ELSE 0',
      'Fairly == []<>(x < TLCGet("diameter")) /\\ SF_Sub(x\' = (x + 1) % 4)',
    ];
    for (const [property, verdict] of [
      ["Below", "holds"],
      ["Past", "lasso"],
      ["Early", "holds"],
      // A late node at another diameter, which the interpreter checks.
      ["Nested", "declined: a late node TLC adds at another diameter"],
    ] as const) {
      const lines = await compareWithInterpreter(body, `SPECIFICATION Spec\nPROPERTY ${property}`);
      expect(lines).toContain(`[engine] native: liveness: ${verdict}`);
    }
    await compareWithInterpreter(body, "SPECIFICATION Spec\nPROPERTY Fairly");
  });

  it("hands over a violated invariant, deadlock and a failed action property", async () => {
    const cases: [string[], string, string][] = [
      [
        [
          "EXTENDS Naturals",
          "VARIABLE x",
          "Init == x \\in {0, 1}",
          "Next == x' = x + 1",
          "Inv == x < 5",
        ],
        "INIT Init\nNEXT Next\nINVARIANT Inv",
        "an invariant violated",
      ],
      [
        ["EXTENDS Naturals", "VARIABLE x", "Init == x = 0", "Next == x < 3 /\\ x' = x + 1"],
        "INIT Init\nNEXT Next",
        "deadlock",
      ],
      [
        [
          "EXTENDS Naturals",
          "VARIABLE x",
          "Init == x = 0",
          "Next == x' = (x + 1) % 4",
          "Spec == Init /\\ [][Next]_x",
          "Grows == [][x' > x]_x",
        ],
        "SPECIFICATION Spec\nPROPERTY Grows",
        "an action property violated",
      ],
      [
        ["EXTENDS Naturals", "VARIABLE x", "Init == x \\in 0..3", "Next == x' = x", "Inv == x # 2"],
        "INIT Init\nNEXT Next\nINVARIANT Inv",
        "an invariant violated in an initial state",
      ],
    ];
    for (const [body, config, reason] of cases) {
      expect(await compareWithInterpreter(body, config)).toContainEqual(
        expect.stringMatching(stopped(reason)),
      );
    }
  });

  it("hands over a failure in the initial predicate with nothing found yet", async () => {
    // The interpreter computes the initial states again from the start, as it does when the
    // TypeScript engine stops there. TLC builds the function at once, so s has no value.
    const body = [
      "EXTENDS Naturals",
      "VARIABLE s",
      "Init == [k \\in {1} |-> s = 2][1] \\/ s \\in {3, 4}",
      "Next == UNCHANGED s",
    ];
    expect(await compareWithInterpreter(body, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(stopped("variable not assigned")),
    );
  });

  it("hands over where PROVE_IT_STOP_AT asks, and the interpreter goes on as without the stop", async () => {
    const config = "INIT Init\nNEXT Next";
    const options = { source: toModule(WALKS), config };
    const whole = await run(options, { PROVE_IT_ENGINE: "debug", PROVE_IT_ENGINE_BACKEND: "rust" });
    const directory = mkdtempSync(join(tmpdir(), "prove-it-native-stop-"));
    try {
      for (const stopAt of ["0", "1", "7", "20"]) {
        const log = join(directory, `${stopAt}.jsonl`);
        const lines = await compareWithInterpreter(WALKS, config, {
          PROVE_IT_STOP_AT: stopAt,
          PROVE_IT_STATE_LOG: log,
        });
        expect(lines).toContainEqual(
          expect.stringMatching(stopped("stopped where PROVE_IT_STOP_AT asked")),
        );
        // The search stopped before expanding that state, with the states found before.
        const header = JSON.parse(readLogLines(log)[0]);
        expect([header.expanding, header.stopped]).toEqual([
          Number(stopAt),
          "stopped where PROVE_IT_STOP_AT asked",
        ]);
      }
    } finally {
      rmSync(directory, { recursive: true, force: true });
    }
    const viewed = [...WALKS, "View == <<x, z>>"];
    const lines = await compareWithInterpreter(viewed, `${config}\nVIEW View`, {
      PROVE_IT_STOP_AT: "3",
    });
    expect(lines).toContainEqual(
      expect.stringMatching(stopped("stopped where PROVE_IT_STOP_AT asked")),
    );
    expect(whole.result.status).toBe("success");
  });

  it("reports no fingerprint collision with PROVE_IT_FP_VERIFY", async () => {
    const options = { source: toModule(WALKS), config: "INIT Init\nNEXT Next" };
    const verified = await run(options, {
      PROVE_IT_ENGINE: "debug",
      PROVE_IT_ENGINE_BACKEND: "rust",
      PROVE_IT_FP_VERIFY: "1",
    });
    expect(verified.lines).toContain("[engine] native: fingerprint collisions: 0");
  });

  it("prints what Print and PrintT print once it completes the initial states or an expansion", async () => {
    const body = [
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      'Init == x \\in 1..5 /\\ PrintT(<<"init", x>>)',
      "Next == x < 7 /\\ x' = Print(<<x, {x, x + 2}>>, x + 1)",
      "Inv == PrintT(x) /\\ x < 10",
    ];
    const config = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE";
    expect(await compareWithInterpreter(body, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    // A stop drops what the expansion printed, which the interpreter prints again.
    const failing = body.map((line) => line.replace("x < 10", "x < 6"));
    expect(await compareWithInterpreter(failing, config)).toContainEqual(
      expect.stringMatching(stopped("an invariant violated")),
    );
    // TLC prints a record by how it was built, which the engine forgets.
    const record = body.map((line) => line.replace("<<x, {x, x + 2}>>", "[a |-> x, b |-> 1]"));
    expect(await compareWithInterpreter(record, config)).toContainEqual(
      expect.stringMatching(stopped("printing a value whose text depends on how TLC built it")),
    );
  });

  it("prints once where the walk evaluates an expression as TLC does", async () => {
    const cases: [string[], string, boolean][] = [
      [
        [
          "Init == x = 0 /\\ \\A i \\in {1, 2} : (y = 0 \\/ y = 1) /\\ Print(<<i, y>>, TRUE)",
          "Next == IF Print(x < 2, x < 2) THEN x' = x + 1 /\\ y' = y ELSE x' = 0 /\\ y' = 1 - y",
        ],
        "INIT Init\nNEXT Next",
        false,
      ],
      [
        [
          "Init == x = 0 /\\ y = 0",
          "Next == /\\ CASE Print(x, x = 0) -> x' = 1 [] OTHER -> x' = 0",
          "        /\\ (Print(y, y = 1) => y' = 0) /\\ y' = 1 - y",
        ],
        "INIT Init\nNEXT Next",
        false,
      ],
      [
        [
          "Init == x = 0 /\\ y = 0",
          "Next == \\E i \\in IF Print(<<x, y>>, TRUE) THEN {1, 2} ELSE {} :",
          "  \\A j \\in IF Print(i, TRUE) THEN {3, 4} ELSE {} :",
          "    x' = (x + i) % 3 /\\ y' = 0 /\\ Print(<<i, j, x'>>, TRUE)",
        ],
        "INIT Init\nNEXT Next",
        false,
      ],
      [
        [
          "C == Print(1, 1)",
          "Init == x = 0 /\\ y = 0",
          "Next == LET n == (x + C) % 3",
          "        IN x' = n /\\ y' = y /\\ ~Print(x', FALSE) /\\ Print(y', y') = y'",
          "           /\\ (\\E i \\in {1, 2} : TRUE)",
        ],
        "INIT Init\nNEXT Next",
        true,
      ],
    ];
    for (const [actions, config, isWarningEnabled] of cases) {
      const body = ["EXTENDS Naturals, TLC", "VARIABLES x, y", ...actions];
      expect(await compareWithInterpreter(body, config, {}, isWarningEnabled)).toContainEqual(
        expect.stringMatching(COMPLETE),
      );
    }
  });

  it("leaves a Print to the interpreter where TLC evaluates it otherwise", async () => {
    const prints = "Print(x, TRUE)";
    const next = "x' = (x + 1) % 3";
    const cases: [string[], string, string?][] = [
      [[`Next == <<${next}>>_(Print(x, x))`], ""],
      [[`Next == [${next}]_(Print(x, x)) /\\ x' # x`], ""],
      [[`Next == LET p == ${prints} IN p /\\ ${next}`], ""],
      [["Op(a) == a", `Next == Op(${prints}) /\\ ${next}`], ""],
      [[`Next == {i \\in {1} : ${prints}} # {} /\\ ${next}`], ""],
      // A definition compiled where it may print, then named where it may not.
      [
        [`P == ${prints}`, `Next == (P = TRUE) /\\ {i \\in {1} : P} # {} /\\ ${next}`],
        "",
        " where TLC evaluates it otherwise",
      ],
      [[`Next == ${next}`, `Constraint == ${prints}`], "\nCONSTRAINT Constraint"],
      [[`Next == ${next}`, "Constraint == Print(x', TRUE)"], "\nACTION_CONSTRAINT Constraint"],
      [[`Next == ${next}`, "View == Print(x, x)"], "\nVIEW View"],
    ];
    for (const [actions, config, where = ""] of cases) {
      const body = ["EXTENDS Naturals, TLC", "VARIABLE x", "Init == x = 0", ...actions];
      const spec = "Spec == Init /\\ [][Next]_x /\\ WF_x(Next)";
      expect(
        await compareWithInterpreter([...body, spec], `SPECIFICATION Spec${config}`),
      ).toContainEqual(expect.stringMatching(declined(`unsupported: Print${where}`)));
    }
    // ENABLED evaluates its action until the first successor, so a Print inside it stops the
    // search only where it is evaluated.
    const enabled = ["EXTENDS Naturals, TLC", "VARIABLE x", "Init == x = 0"];
    const reached = [`A == ${prints} /\\ ${next}`, "Next == A \\/ (~ENABLED A /\\ x' = 0)"];
    expect(
      await compareWithInterpreter([...enabled, ...reached], "INIT Init\nNEXT Next"),
    ).toContainEqual(expect.stringMatching(stopped("Print inside ENABLED")));
    const passed = [
      `A == ${next} \\/ (${prints} /\\ x' = 5)`,
      "Next == A \\/ (~ENABLED A /\\ x' = 0)",
    ];
    expect(
      await compareWithInterpreter([...enabled, ...passed], "INIT Init\nNEXT Next"),
    ).toContainEqual(expect.stringMatching(COMPLETE));
  });

  it("evaluates the guard of x' \\in S only where x' has a value", async () => {
    const body = [
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      "Init == x \\in IF Print(0, TRUE) THEN {0, 1} ELSE {}",
      "Next == x' \\in IF Print(x, TRUE) THEN {(x + 1) % 3} ELSE {}",
    ];
    expect(await compareWithInterpreter(body, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    // With x' assigned, x' \in S is a guard: TLC evaluates S once and asks it for x'.
    const assigned = body.map((line) => line.replace("Next == ", "Next == x' = (x + 1) % 3 /\\ "));
    expect(await compareWithInterpreter(assigned, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });

  it("builds a function over a tuple pattern as TLC does", async () => {
    // TLC binds each element's components and keeps the element as the key.
    const body = [
      "EXTENDS Naturals",
      "VARIABLE f",
      "Init == f = [<<i, j>> \\in {<<1, 2>>, <<3, 4>>} |-> i + j]",
      "Next == f' = [<<i, j>> \\in DOMAIN f |-> f[<<i, j>>] + i * j]",
      "Small == \\A key \\in DOMAIN f : f[key] < 40",
    ];
    expect(
      await compareWithInterpreter(body, "INIT Init\nNEXT Next\nINVARIANT Small"),
    ).toContainEqual(expect.stringMatching(stopped("an invariant violated")));
    // A tuple of another length fails in TLC, which the interpreter then reports.
    const mismatched = [
      "VARIABLE f",
      "Init == f = [<<i, j>> \\in {<<1>>} |-> i]",
      "Next == UNCHANGED f",
    ];
    expect(await compareWithInterpreter(mismatched, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(stopped("a tuple pattern that doesn't match")),
    );
  });

  it("binds a tuple pattern in an action's \\E as TLC does", async () => {
    // TLC's ContextEnumerator varies the first bound fastest, a tuple bound as a name bound.
    const body = [
      "EXTENDS Naturals, TLC",
      "VARIABLES x, y",
      "Init == x = 0 /\\ y = 0",
      "Next == \\/ \\E <<i, j>> \\in {<<1, 2>>, <<3, 4>>} : x' = i /\\ y' = j",
      "        \\/ \\E <<i, j>> \\in {<<1, 2>>, <<3, 4>>}, k \\in {10, 20}, <<n, m>> \\in {<<5, 6>>} :",
      "             x' = i + k + m /\\ y' = j + n",
      "        \\/ \\E p \\in Permutations({1, 2, 3}) : x' = p[1] * 10 + p[2] /\\ y' = p[3]",
      "        \\/ x' \\in {p[7] : p \\in Permutations({7, 8})} /\\ y' \\in Permutations({9})",
    ];
    for (const isWarningEnabled of [false, true]) {
      expect(
        await compareWithInterpreter(body, "INIT Init\nNEXT Next", {}, isWarningEnabled),
      ).toContainEqual(expect.stringMatching(COMPLETE));
    }
    // A tuple of another length fails in TLC, which the interpreter then reports.
    const mismatched = [
      "VARIABLE x",
      "Init == x = 0",
      "Next == \\E <<i, j>> \\in {<<1>>} : x' = i",
    ];
    expect(await compareWithInterpreter(mismatched, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(stopped("a tuple pattern that doesn't match")),
    );
  });

  it("leaves a model it can't search to the TypeScript engine", async () => {
    // UNCHANGED in the initial predicate, which TLC evaluates and neither engine walks.
    const body = ["VARIABLE x", "Init == x = 0 /\\ UNCHANGED x", "Next == x' = x"];
    const lines = await compareWithInterpreter(body, "INIT Init\nNEXT Next");
    expect(lines).toEqual([
      expect.stringMatching(/^\[engine\] native: ir: /),
      expect.stringMatching(declined("unsupported: UNCHANGED in the initial predicate")),
      expect.stringMatching(/^\[engine\] handed over after \d+ ms: primed variable not assigned$/),
    ]);
  });

  it("walks the body of a recursive operator as it runs", async () => {
    // TLC walks a RECURSIVE operator's body as any other's, so it assigns the variables its
    // arguments name however deep, as coverage/Github649's Flip does, and each disjunct at each
    // level makes a state (checked with TLC: 3 initial states, 72 generated, 12 distinct).
    const body = [
      "EXTENDS Naturals",
      "VARIABLES x, y",
      "RECURSIVE Pick(_, _), Both(_, _, _), Step(_, _), Keep(_, _)",
      "Pick(v, n) == IF n = 0 THEN v = 0 ELSE (v = n \\/ Pick(v, n - 1))",
      "Both(a, b, n) ==",
      "  IF n = 0 THEN a \\in {0, 1} /\\ b = 0 ELSE Both(a, b, n - 1) /\\ b < 5",
      "Step(n, k) ==",
      "  IF n = 0 THEN x' = (x + k) % 4 /\\ UNCHANGED y",
      "  ELSE Step(n - 1, k + 1) \\/ (y' = (y + n) % 3 /\\ Keep(x', n))",
      "Keep(v, n) == IF n = 0 THEN v \\in {x, 0} ELSE Keep(v, n - 1)",
      "Init == Pick(x, 2) /\\ Both(y, y, 1)",
      "Next ==",
      "  \\/ Step(2, 0)",
      "  \\/ LET RECURSIVE Last(_)",
      "         Last(n) == IF n = 0 THEN x' = 3 /\\ y' = y ELSE Last(n - 1)",
      "     IN Last(3)",
    ];
    const lines = await compareWithInterpreter(body, "INIT Init\nNEXT Next");
    expect(lines).toContainEqual(expect.stringMatching(COMPLETE));
    expect(lines).toContainEqual(expect.stringMatching(/^\[engine\] checked 12 states /));
  });

  it("evaluates ENABLED in the initial predicate", async () => {
    // TLC's EWD840/MC02 conjoins ENABLED Next to its specification, so the initial predicate
    // evaluates it once every variable has a value.
    const body = [
      "EXTENDS Naturals",
      "VARIABLES x, y",
      "Step == x < 2 /\\ x' = x + 1 /\\ y' = y",
      "Init == x \\in 0..3 /\\ y = 0 /\\ ENABLED Step",
      "Next == Step \\/ (x = 2 /\\ x' = 0 /\\ y' = 1 - y)",
    ];
    const lines = await compareWithInterpreter(body, "INIT Init\nNEXT Next");
    expect(lines).toContainEqual(expect.stringMatching(COMPLETE));
    expect(lines).toContainEqual(expect.stringMatching(/^\[engine\] checked 6 states /));
  });

  it("walks a function of several arguments an action applies", async () => {
    // TLC keeps the function lazy and walks its body with each name bound to its argument, as
    // spectacle's Elevator applies CanServiceCall[e, call] (checked with TLC: 10 states generated,
    // 3 distinct).
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "Move[a \\in 0..2, b \\in 0..1] == x' = (a + b) % 3 \\/ (b = 1 /\\ x' = a)",
      "Init == x = 0",
      "Next == \\E b \\in 0..1 : Move[x, b]",
    ];
    const lines = await compareWithInterpreter(body, "INIT Init\nNEXT Next");
    expect(lines).toContainEqual(expect.stringMatching(COMPLETE));
    expect(lines).toContainEqual(expect.stringMatching(/^\[engine\] checked 3 states /));
    const outside = body.map((line) => line.replace("Move[x, b]", "Move[x + 1, b]"));
    expect(await compareWithInterpreter(outside, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(stopped("applied a function outside its domain")),
    );
  });

  it("stops where an action quantifies over a set TLC can't enumerate", async () => {
    // TLC fails on \E k \in Nat in an action, as spectacle's Bakery does.
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "Init == x = 0",
      "Next == (x < 2 /\\ x' = x + 1) \\/ (x = 2 /\\ \\E k \\in Nat : x' = k)",
    ];
    expect(await compareWithInterpreter(body, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(stopped("enumerated a set TLC can't enumerate")),
    );
  });

  it("tests membership in the domain of a function TLC keeps lazy", async () => {
    // FcnLambdaValue.getDomain gives the bound's set, or the tuples of the bounds' sets, which
    // TLC only tests (suite/test11).
    const body = [
      "EXTENDS Integers",
      "VARIABLE x",
      "Shift[i \\in Int] == i + 3",
      "Init == x = 0",
      "Next == x' = (x + 1) % 3",
      "Inv == /\\ x \\in DOMAIN Shift",
      "       /\\ {x, -1} \\in DOMAIN [s \\in SUBSET Int |-> s \\cup {1}]",
      "       /\\ <<x, -2>> \\in DOMAIN [i \\in Nat, j \\in Int |-> i + j]",
      "       /\\ <<-1, x>> \\notin DOMAIN [i \\in Nat, j \\in Int |-> i + j]",
      "       /\\ <<x>> \\notin DOMAIN [i \\in Nat, j \\in Int |-> i + j]",
      "       /\\ x \\in DOMAIN [i \\in 0..2 |-> i]",
    ];
    expect(
      await compareWithInterpreter(body, "INIT Init\nNEXT Next\nINVARIANT Inv"),
    ).toContainEqual(expect.stringMatching(COMPLETE));
  });

  it("compares a function that is no record with a record as TLC's function does", async () => {
    // FcnRcdValue.equals takes any function, where RecordValue.equals fails on one that is no
    // record: the left side of = decides (tla-rs model_values_distinct).
    const body = [
      "EXTENDS Naturals",
      "CONSTANT Node",
      "VARIABLE x",
      "ByNode == [n \\in Node |-> 1]",
      'ByName == [n \\in {"n1", "n2"} |-> 1]',
      "Init == x = 0",
      "Next == x' = 1 - x",
      "Inv == ByNode # ByName /\\ ByNode # [n1 |-> 1, n2 |-> 1] /\\ ~(ByNode = [n1 |-> 1])",
    ];
    const config = "CONSTANT Node = {n1, n2}\nINIT Init\nNEXT Next\nINVARIANT Inv";
    expect(await compareWithInterpreter(body, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    // The store can't tell a record from a function over strings, so it stops where the one
    // asked may be a record.
    const asked = body.map((line) => line.replace(/^Inv == .*/, "Inv == ByName # ByNode"));
    expect(await compareWithInterpreter(asked, config)).toContainEqual(
      expect.stringMatching(/record compared with a function/),
    );
  });

  it("counts the _POSSIBLE predicates as TLC does, and hands the counts over", async () => {
    // TLC counts the states in the model and the steps each predicate holds of, duplicates and
    // all, and reports one that never held with the counts.
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "Init == x \\in 0..1",
      "Next == x' = (x + 1) % 5 \\/ x' = (x + 2) % 5",
      "Spec == Init /\\ [][Next]_x /\\ WF_x(Next)",
      "Even == x % 2 = 0",
      "Wrap == x' < x",
      "Never == x = 7",
      "Reach == <>(x = 4)",
    ];
    for (const possible of ["Even Wrap", "Even Wrap Never"]) {
      const config = `INIT Init\nNEXT Next\n_POSSIBLE ${possible}`;
      expect(await compareWithInterpreter(body, config)).toContainEqual(
        expect.stringMatching(COMPLETE),
      );
      expect(await compareWithInterpreter(body, config, { PROVE_IT_STOP_AT: "3" })).toContainEqual(
        expect.stringMatching(stopped("stopped where PROVE_IT_STOP_AT asked")),
      );
      expect(
        await compareWithInterpreter(
          body,
          `SPECIFICATION Spec\nPROPERTY Reach\n_POSSIBLE ${possible}`,
        ),
      ).toContainEqual(expect.stringMatching(COMPLETE));
    }
  });

  it("merges states whose strings differ only above U+00FF, as TLC's fingerprints do", async () => {
    // TLC fingerprints a string by the low byte of each character, so "Ā" and "Ȁ" make one state.
    const body = [
      "EXTENDS Naturals",
      "VARIABLES x, y",
      'Init == x \\in {"Ā", "Ȁ", "a"} /\\ y = 0',
      "Next == y' = (y + 1) % 3 /\\ UNCHANGED x",
    ];
    const config = "INIT Init\nNEXT Next";
    expect(await compareWithInterpreter(body, config)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    expect(await compareWithInterpreter(body, config, { PROVE_IT_STOP_AT: "2" })).toContainEqual(
      expect.stringMatching(stopped("stopped where PROVE_IT_STOP_AT asked")),
    );
    // Under a VIEW the interpreter takes the states over by TLC's fingerprint of the view.
    const viewed = [...body, "View == y"];
    expect(
      await compareWithInterpreter(viewed, `${config}\nVIEW View`, { PROVE_IT_STOP_AT: "2" }),
    ).toContainEqual(expect.stringMatching(stopped("stopped where PROVE_IT_STOP_AT asked")));
  });

  it("stops where TLC fails on action composition, with the states before", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "Init == x = 0",
      "A == x' = x + 1",
      "Next == \\/ x < 2 /\\ A",
      "        \\/ x = 2 /\\ A \\cdot A",
    ];
    const lines = await compareWithInterpreter(body, "INIT Init\nNEXT Next");
    expect(lines).toEqual([
      expect.stringMatching(/^\[engine\] native: ir: /),
      expect.stringMatching(stopped("action composition")),
      expect.stringMatching(/^\[engine\] handed over after \d+ ms: action composition$/),
    ]);
  });

  it("gives ENABLED's rewrite of an instance's variables a next state of their own", async () => {
    // Under ENABLED, TLC takes the instance's primed variable u for one apart from x, so H holds
    // and K, which asks u' for two values, doesn't.
    const options = {
      source: toModule([
        "EXTENDS Naturals",
        "VARIABLE x",
        "I == INSTANCE Inner WITH u <- x",
        "Init == x = 0",
        "Next == \\/ x' = (x + 1) % 3 /\\ I!H",
        "        \\/ x' = 7 /\\ I!K",
      ]),
      config: "INIT Init\nNEXT Next",
      loadModule: () =>
        "---- MODULE Inner ----\nVARIABLE u\nH == ENABLED (u' = 100)\nK == ENABLED (u' = 100 /\\ u' = 101)\n====",
    };
    const native = await run(options, {
      PROVE_IT_ENGINE: "debug",
      PROVE_IT_ENGINE_BACKEND: "rust",
    });
    const interpreter = await run(options, { PROVE_IT_ENGINE: "0" });
    expect(native.result).toEqual(interpreter.result);
    expect(native.lines).toContainEqual(expect.stringMatching(COMPLETE));
    expect(native.result.distinctStates).toBe(3);
  });

  // From TLC's Github648: TLC computes a constant definition once when it starts, a random one too,
  // and the search reads that value unless TLC may keep it lazy.
  it("reads the value TLC computed at startup for a definition with effects", async () => {
    const body = [
      "EXTENDS TLC, Naturals",
      "Graph == TLCEval(LET g == RandomElement([edge : SUBSET ({1, 2} \\X {1, 2})])",
      "                 IN [edge |-> g.edge \\cup {<<1, 1>>}])",
      "VARIABLE v",
      "Init == v \\in Graph.edge",
      "Next == v' \\in Graph.edge",
      "Inv == v \\in Graph.edge",
    ];
    expect(
      await compareWithInterpreter(body, "INIT Init\nNEXT Next\nINVARIANT Inv"),
    ).toContainEqual(expect.stringMatching(COMPLETE));
    const lazy = [
      "VARIABLE v",
      "S == IF RandomElement({TRUE}) THEN SUBSET {1, 2} ELSE {}",
      "Init == v \\in S",
      "Next == UNCHANGED v",
    ];
    expect(
      await compareWithInterpreter(["EXTENDS TLC", ...lazy], "INIT Init\nNEXT Next"),
    ).toContainEqual(
      expect.stringMatching(declined("unsupported: a value TLC computed at startup with effects")),
    );
  });

  // TLC evaluates a substitute and the constant definitions with effects when it starts, then the
  // assumptions, and the search reads what they drew, which the invariant prints.
  it("draws and prints at startup as TLC does", async () => {
    const body = [
      "EXTENDS TLC, Naturals",
      'Shown == Print("shown", 4)',
      'Sub == IF PrintT("sub") THEN 5 ELSE 0',
      "D == 3",
      "R == RandomElement(1..100)",
      'ASSUME PrintT(<<"assume", R>>)',
      "ASSUME Shown > 0",
      "VARIABLE x",
      "Init == x = R",
      "Next == x' = x",
      'Inv == PrintT(<<"inv", x>>) /\\ x = R /\\ D = 5',
    ];
    const lines = await compareWithInterpreter(
      body,
      "CONSTANT D <- Sub\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
    );
    expect(lines).toContainEqual(expect.stringMatching(COMPLETE));
  });

  // From tla-rs's function_syntax: TLC applies a recursive function of several bounds to tuples
  // of its product, and keeps a recursive function lazy where a spec passes it or takes its
  // domain.
  // From mongodb-txns' ClientCentric, whose fold folds in the operator it applies: a definition
  // reached again through an argument isn't recursion.
  it("expands a definition again through an argument", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "Fold(op(_, _), base, S) ==",
      "  LET it[s \\in SUBSET S] ==",
      "        IF s = {} THEN base ELSE LET y == CHOOSE y \\in s : TRUE IN op(y, it[s \\ {y}])",
      "  IN it[S]",
      "Sum(S) == Fold(LAMBDA a, b : a + b, 0, S)",
      "Init == x = 0",
      "Next == x' = (x + 1) % 3",
      "Inv == /\\ Fold(LAMBDA a, acc : acc + Sum({i + x : i \\in 1..a}), 0, {1, 2}) = 4 + 3 * x",
      "       /\\ Fold(LAMBDA a, acc : a + acc, Fold(LAMBDA a, b : a + b, x, {1}), {2}) = 3 + x",
    ];
    expect(
      await compareWithInterpreter(body, "INIT Init\nNEXT Next\nINVARIANT Inv"),
    ).toContainEqual(expect.stringMatching(COMPLETE));
  });

  // Tool.evalAppl evaluates UNCHANGED e, [A]_e and <<A>>_e in the current state first, so the
  // search stops on the current state's failure.
  it("goes through UNCHANGED of a tuple element by element, as TLC's processUnchanged", async () => {
    // As Github702 (TLC's tests), whose instance substitutes a constant for x in UNCHANGED <<x, z>>:
    // TLC compares the constant's values and assigns z.
    const body = [
      "EXTENDS Naturals",
      "VARIABLES y, z",
      "c == 1",
      "Keep(v) == UNCHANGED <<c, v>>",
      "Init == y \\in {1, 2} /\\ z \\in {1, 2}",
      "Next == \\/ y < 4 /\\ y' = y + 1 /\\ UNCHANGED <<c, z>>",
      "        \\/ y < 3 /\\ y' = y + 2 /\\ Keep(z)",
    ];
    expect(
      await compareWithInterpreter(body, "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE"),
    ).toContainEqual(expect.stringMatching(COMPLETE));
  });

  it("evaluates UNCHANGED in the current state first like TLC", async () => {
    const subscript = 'IF x = 0 THEN Assert(FALSE, "before") ELSE <<>>[1]';
    for (const form of ["[FALSE]_(e)", "IF UNCHANGED (e) THEN TRUE ELSE TRUE", "<<TRUE>>_(e)"]) {
      const body = [
        "EXTENDS TLC",
        "VARIABLE x",
        "Init == x = 0",
        `Next == x' = 1 /\\ ${form.replace("(e)", `(${subscript})`)}`,
      ];
      expect([form, await compareWithInterpreter(body, "INIT Init\nNEXT Next")]).toEqual([
        form,
        expect.arrayContaining([expect.stringMatching(/native: stopped: an assertion failed/)]),
      ]);
    }
  });

  // From tla-rs's function_syntax: TLC applies a recursive function of several bounds to tuples
  // of its product, and keeps a recursive function lazy where a spec passes it or takes its
  // domain.
  // From mongodb-txns' Storage.cfg, which substitutes FALSE for actions with parameters: TLC
  // takes the value and leaves the arguments unevaluated.
  it("takes a value a configuration substitutes for an operator with parameters", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "A(n) == x' = n",
      "Init == x = 0",
      "Next == \\/ x < 3 /\\ x' = x + 1",
      "        \\/ \\E n \\in {0} : A(1 \\div n)",
    ];
    expect(
      await compareWithInterpreter(
        body,
        "INIT Init\nNEXT Next\nCONSTANT A <- FALSE\nCHECK_DEADLOCK FALSE",
      ),
    ).toContainEqual(expect.stringMatching(COMPLETE));
  });

  // From TLC's Github725d: TLC's getPrimedVar looks through a LET to the primed variable it
  // assigns, in the next-state relation and in ENABLED.
  it("assigns a primed variable a LET names", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "Init == x = 0",
      "Next == x < 3 /\\ (LET y == x' IN y) = x + 1",
      "Inv == ENABLED ((LET y == x' IN y) = 0)",
    ];
    expect(
      await compareWithInterpreter(
        body,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
      ),
    ).toContainEqual(expect.stringMatching(COMPLETE));
  });

  // From TLC's test46: SubsetValue.elementsNormalized enumerates SUBSET S in the normalized order
  // of S's elements, whatever S's own order.
  it("assigns from SUBSET of a set it has no order for, in TLC's normalized order", async () => {
    const body = [
      "EXTENDS Naturals, FiniteSets",
      "VARIABLES x, f",
      "S == UNION {[p : {k}, i : DOMAIN f[k]] : k \\in {1, 2}}",
      "Init == f = [k \\in {1, 2} |-> <<0>>] /\\ x = {}",
      "Next == f' = f /\\ x' \\in SUBSET (S' \\X S')",
      "Inv == Cardinality(x) <= 4",
    ];
    expect(
      await compareWithInterpreter(body, "INIT Init\nNEXT Next\nINVARIANT Inv"),
    ).toContainEqual(expect.stringMatching(COMPLETE));
  });

  // From TLC's ConstantOperatorConfiguration: a configuration defines a constant operator by its
  // values, which TLC applies by the row whose arguments equal the arguments, and fails to apply
  // outside its rows.
  it("applies an operator the configuration defines by its values", async () => {
    const body = [
      "EXTENDS Naturals",
      "CONSTANT F(_, _)",
      "VARIABLE x",
      "Init == x = 0",
      "Next == x' = F(x, x + 1)",
    ];
    const rows = "CONSTANT\nF(0, 1) = 1\nF(1, 2) = 2\nF(2, 3) = 2";
    expect(await compareWithInterpreter(body, `INIT Init\nNEXT Next\n${rows}`)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    expect(
      await compareWithInterpreter(body, "INIT Init\nNEXT Next\nCONSTANT\nF(0, 1) = 1"),
    ).toContainEqual(
      expect.stringMatching(stopped("an operator's table applied outside its rows")),
    );
  });

  // From tla-rs's function_instance: an instance's copy of a recursive function names itself as
  // the module did, and an operator that gives a recursive function keeps it lazy, as TLC does.
  it("applies recursive functions an instance or an operator gives", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "---- MODULE Lib ----",
      "EXTENDS Naturals",
      "fact[n \\in Nat] == IF n = 0 THEN 1 ELSE n * fact[n - 1]",
      "====",
      "I == INSTANCE Lib",
      "Scaled(b) == LET s[n \\in Nat] == IF n = 0 THEN b ELSE n * s[n - 1] IN s",
      "Init == x = 0",
      "Next == x' = (x + 1) % 3",
      "Inv == I!fact[4] = 24 /\\ Scaled(2)[3] = 12 /\\ Scaled(x + 1)[2] = 2 * (x + 1)",
    ];
    expect(
      await compareWithInterpreter(body, "INIT Init\nNEXT Next\nINVARIANT Inv"),
    ).toContainEqual(expect.stringMatching(COMPLETE));
  });

  it("walks and evaluates what an INSTANCE in a LET defines, as CyclicRedefineInstance does", async () => {
    // The INSTANCE copies the module's definitions into the LET, under names it binds there.
    const counter = [
      "---- MODULE Counter ----",
      "EXTENDS Naturals",
      "VARIABLE v",
      "CONSTANT K",
      "Bump == v' = (v + K) % 5",
      "Big == v > 2",
      "====",
    ].join("\n");
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "Init == x = 0",
      "Next == LET S == INSTANCE Counter WITH v <- x, K <- 2",
      "        IN  \\/ S!Bump",
      "            \\/ S!Big /\\ x' = 0",
      "Inv == LET T == INSTANCE Counter WITH v <- x, K <- 1 IN T!Big => x \\in {3, 4}",
    ];
    const options = {
      source: toModule(body),
      config: "INIT Init\nNEXT Next\nINVARIANT Inv",
      loadModule: (name: string) => (name === "Counter" ? counter : undefined),
    };
    const native = await run(options, {
      PROVE_IT_ENGINE: "debug",
      PROVE_IT_ENGINE_BACKEND: "rust",
    });
    const interpreter = await run(options, { PROVE_IT_ENGINE: "0" });
    expect(native.result).toEqual(interpreter.result);
    expect(native.lines).toContainEqual(expect.stringMatching(COMPLETE));
  });

  it("takes a string as a sequence in Len and Tail, as TLC's Sequences does", async () => {
    const body = [
      "EXTENDS Naturals, Sequences",
      "VARIABLE x",
      'Init == x = "abc"',
      'Next == x # "" /\\ x\' = Tail(x)',
      'Inv == Len(x) <= 3 /\\ (x # "" => Len(Tail(x)) = Len(x) - 1)',
    ];
    expect(
      await compareWithInterpreter(
        body,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
      ),
    ).toContainEqual(expect.stringMatching(COMPLETE));
  });

  it("applies recursive functions as TLC keeps them lazy", async () => {
    const body = [
      "EXTENDS Naturals, FiniteSets",
      "VARIABLE x",
      "add[a \\in 0..3, b \\in 0..3] == IF b = 0 THEN a ELSE add[a, b - 1] + 1",
      "fact[n \\in Nat] == IF n = 0 THEN 1 ELSE n * fact[n - 1]",
      "selfdom[n \\in 0..3] == IF n = 0 THEN Cardinality(DOMAIN selfdom) ELSE selfdom[n - 1]",
      "k == [a \\in {1}, <<b, c>> \\in {<<2, 3>>, <<4, 5>>} |-> a + b + c]",
      "ApplyAt(f, n) == f[n]",
      "Init == x = 0",
      "Next == x < 3 /\\ x' = add[x, 1]",
      "Inv == /\\ add[2, 3] = 5 /\\ add[<<1, 1>>] = 2 /\\ DOMAIN add = (0..3) \\X (0..3)",
      "       /\\ ApplyAt(fact, 4) = 24",
      "       /\\ selfdom[2] = 4 /\\ k[1, <<4, 5>>] = 10",
    ];
    expect(
      await compareWithInterpreter(
        body,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
      ),
    ).toContainEqual(expect.stringMatching(COMPLETE));
  });
  it("applies a function a recursive body builds to one argument, as TLC keeps it lazy", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "f[i \\in 0..5] == [j \\in 0..5 |->",
      "  IF j = 0 THEN [k \\in 0..i |-> IF k = 0 THEN i ELSE f[i][1] + 1]",
      "  ELSE IF i = 0 THEN j ELSE f[i - 1][j] + 1]",
      "g[i \\in 0..5] == [j \\in 0..i |->",
      "  IF j = 0 THEN IF i = 0 THEN 0 ELSE g[i - 1][i - 1] ELSE g[i][j - 1] + x]",
      "Init == x = 2",
      "Next == x < 4 /\\ x' = x + 1",
      "Inv == /\\ f[4][3] = 7 /\\ f[4][0][2] = 6 /\\ DOMAIN f[5][0] = 0..5",
      "       /\\ g[3][3] = 6 * x /\\ DOMAIN g[3] = 0..3",
    ];
    expect(
      await compareWithInterpreter(
        body,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
      ),
    ).toContainEqual(expect.stringMatching(COMPLETE));
  });
  it("walks a recursive function an action applies, each path a successor, as TLC does", async () => {
    const body = [
      "EXTENDS Naturals",
      "VARIABLE x",
      "Ok(n) == LET R[k \\in 0..n] ==",
      "             \\/ k = 0",
      "             \\/ \\E j \\in 0..1 : (k > 1 => R[k - 1]) /\\ j + k > 1",
      "          IN R[n]",
      "Init == x = 0",
      "Next == x < 4 /\\ Ok(x) /\\ x' = x + 1",
    ];
    expect(
      await compareWithInterpreter(body, "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE"),
    ).toContainEqual(expect.stringMatching(COMPLETE));
  });
});

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
    // TypeScript engine stops there.
    const body = [
      "EXTENDS Naturals",
      "VARIABLE s",
      "All(var, S) == \\A v \\in S : var = v",
      "Init == All(s, {2}) \\/ s \\in {3, 4}",
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
      [[`P == ${prints}`, `Next == P /\\ {P} # {} /\\ ${next}`], ""],
      // A definition compiled where it may print, then named where it may not.
      [
        [`P == ${prints}`, `Next == (P = TRUE) /\\ {P} # {} /\\ ${next}`],
        "",
        " where TLC evaluates it otherwise",
      ],
      [[`A == ${prints} /\\ ${next}`, "Next == A \\/ (~ENABLED A /\\ x' = 0)"], ""],
      [[`Next == ${next}`, `Constraint == ${prints}`], "\nCONSTRAINT Constraint"],
      [[`Next == ${next}`, "Constraint == Print(x', TRUE)"], "\nACTION_CONSTRAINT Constraint"],
      [[`Next == ${next}`, "View == Print(x, x)"], "\nVIEW View"],
      [[`Next == ${prints} /\\ ${next}`, "Live == <>(x = 2)"], "\nPROPERTY Live"],
    ];
    for (const [actions, config, where = ""] of cases) {
      const body = ["EXTENDS Naturals, TLC", "VARIABLE x", "Init == x = 0", ...actions];
      const spec = "Spec == Init /\\ [][Next]_x /\\ WF_x(Next)";
      expect(
        await compareWithInterpreter([...body, spec], `SPECIFICATION Spec${config}`),
      ).toContainEqual(expect.stringMatching(declined(`unsupported: Print${where}`)));
    }
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
    // With x' assigned, x' \in S is a guard, whose S the engine doesn't evaluate as TLC does.
    const assigned = body.map((line) => line.replace("Next == ", "Next == x' = (x + 1) % 3 /\\ "));
    expect(await compareWithInterpreter(assigned, "INIT Init\nNEXT Next")).toContainEqual(
      expect.stringMatching(stopped("unsupported: Print")),
    );
  });

  it("leaves a model it can't search yet to the TypeScript engine", async () => {
    // ToString prints a value as TLC would, which the native engine doesn't.
    const body = [
      "EXTENDS TLC",
      "VARIABLE x",
      "Init == x \\in {ToString(1), ToString(2)}",
      "Next == UNCHANGED x",
    ];
    const lines = await compareWithInterpreter(body, "INIT Init\nNEXT Next");
    expect(lines).toEqual([
      expect.stringMatching(/^\[engine\] native: ir: /),
      expect.stringMatching(/^\[engine\] native: declined: the builtin ToString, /),
      expect.stringMatching(/^\[engine\] checked 2 states on 1 thread /),
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
});

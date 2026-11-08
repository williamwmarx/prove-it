// The native engine's search, with PROVE_IT_ENGINE_BACKEND=rust: it must reach what the interpreter
// reaches, whether it completes the search or hands over part way, and find the same states in the
// same order as the TypeScript engine. Each test also checks what the native engine did, so a
// model it declines can't pass by the TypeScript engine's search. They run where the addon was
// built, with PROVE_IT_ENGINE_ADDON naming it, as the native job in verification.yml does.

import { afterEach, describe, expect, it, spyOn } from "bun:test";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { getStateLogDifference, readLogLines } from "../../scripts/state-logs";
import { check, type CheckOptions } from "../../src";

const ADDON = process.env.PROVE_IT_ENGINE_ADDON;
const SETTINGS = [
  "PROVE_IT_ENGINE",
  "PROVE_IT_ENGINE_BACKEND",
  "PROVE_IT_STATE_LOG",
  "PROVE_IT_STOP_AT",
  "PROVE_IT_FP_VERIFY",
] as const;
const saved = Object.fromEntries(SETTINGS.map((name) => [name, process.env[name]]));

afterEach(() => {
  for (const name of SETTINGS) {
    if (saved[name] === undefined) delete process.env[name];
    else process.env[name] = saved[name];
  }
});

interface Run {
  result: Awaited<ReturnType<typeof check>>;
  lines: string[];
  progress: string[];
}

// Checks a model with the engine set as given, keeping the [engine] lines and what it reports.
const run = async (
  options: Pick<CheckOptions, "source" | "config" | "isWarningEnabled">,
  settings: Partial<Record<(typeof SETTINGS)[number], string>>,
): Promise<Run> => {
  for (const name of SETTINGS) delete process.env[name];
  Object.assign(process.env, settings);
  const lines: string[] = [];
  const progress: string[] = [];
  const spy = spyOn(console, "error").mockImplementation((message: unknown) => {
    if (typeof message === "string" && message.startsWith("[engine] ")) lines.push(message);
  });
  try {
    const result = await check({
      ...options,
      onPrint: () => {},
      onProgress: (report) => {
        if (report.kind !== "progress") progress.push(JSON.stringify(report));
      },
    });
    return { result, lines, progress };
  } finally {
    spy.mockRestore();
  }
};

const toModule = (body: string[]) => `---- MODULE M ----\n${body.join("\n")}\n====`;

// The native engine's run and the interpreter's, which must reach the same result and report the
// same progress.
const compareWithInterpreter = async (
  body: string[],
  config: string,
  settings: Partial<Record<(typeof SETTINGS)[number], string>> = {},
  isWarningEnabled = false,
) => {
  const options = { source: toModule(body), config, isWarningEnabled };
  const native = await run(options, {
    PROVE_IT_ENGINE: "debug",
    PROVE_IT_ENGINE_BACKEND: "rust",
    ...settings,
  });
  const interpreter = await run(options, { PROVE_IT_ENGINE: "0" });
  expect(native.result).toEqual(interpreter.result);
  expect(native.progress).toEqual(interpreter.progress);
  return native.lines;
};

// The state logs of the TypeScript and the native engine, which must be identical.
const compareStateLogs = async (body: string[], config: string, isWarningEnabled: boolean) => {
  const directory = mkdtempSync(join(tmpdir(), "prove-it-native-search-"));
  try {
    const options = { source: toModule(body), config, isWarningEnabled };
    const paths = ["ts", "rust"].map((backend) => join(directory, `${backend}.jsonl`));
    const lines: string[][] = [];
    for (const [index, backend] of ["ts", "rust"].entries()) {
      const logged = await run(options, {
        PROVE_IT_ENGINE: "debug",
        PROVE_IT_ENGINE_BACKEND: backend,
        PROVE_IT_STATE_LOG: paths[index],
      });
      lines.push(logged.lines);
    }
    const [typescript, native] = paths.map(readLogLines);
    expect(getStateLogDifference(typescript, native)).toBeUndefined();
    expect(native.length).toBeGreaterThan(1);
    return lines[1];
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
};

const COMPLETE = /^\[engine\] native: complete: {2}\(\d+\.\d\d ms\)$/;
const stopped = (reason: string) =>
  new RegExp(`^\\[engine\\] native: stopped: ${reason} \\(\\d+\\.\\d\\d ms\\)$`);

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
      "View == x",
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
    for (const stopAt of ["0", "1", "7", "20"]) {
      const lines = await compareWithInterpreter(WALKS, config, { PROVE_IT_STOP_AT: stopAt });
      expect(lines).toContainEqual(
        expect.stringMatching(stopped("stopped where PROVE_IT_STOP_AT asked")),
      );
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

  it("leaves a model it can't search yet to the TypeScript engine", async () => {
    // TLC keeps SUBSET lazy, and the native engine doesn't enumerate it in TLC's order yet.
    const body = ["VARIABLE x", "Init == x \\in SUBSET {1, 2}", "Next == UNCHANGED x"];
    const lines = await compareWithInterpreter(body, "INIT Init\nNEXT Next");
    expect(lines).toEqual([
      expect.stringMatching(/^\[engine\] native: ir: /),
      expect.stringMatching(/^\[engine\] native: declined: enumerating a set TLC keeps lazy /),
      expect.stringMatching(/^\[engine\] checked 4 states on 1 thread /),
    ]);
  });
});

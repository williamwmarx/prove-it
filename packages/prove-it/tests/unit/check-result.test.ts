// check's result: what the native check records as it prints, and what the TypeScript check's
// result converts to, the same for each model, every variable as TLC prints it and as plain data.

import { afterEach, describe, expect, it, spyOn } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { check, type CheckResult } from "../../src";

const setting = process.env.PROVE_IT_ENGINE;

afterEach(() => {
  if (setting === undefined) delete process.env.PROVE_IT_ENGINE;
  else process.env.PROVE_IT_ENGINE = setting;
});

interface Run {
  result: CheckResult;
  printed: string[];
  // Whether the native check checked it, rather than the TypeScript check.
  isNative: boolean;
}

const run = async (source: string, config: string, engine: string): Promise<Run> => {
  process.env.PROVE_IT_ENGINE = engine;
  const printed: string[] = [];
  const lines: string[] = [];
  const spy = spyOn(console, "error").mockImplementation((message: unknown) => {
    if (typeof message === "string") lines.push(message);
  });
  try {
    const result = await check({ source, config, onPrint: (text) => printed.push(text) });
    return { result, printed, isNative: !lines.some((line) => line.includes("declined")) };
  } finally {
    spy.mockRestore();
  }
};

// The native check's run and the TypeScript check's, of a module M of the body.
const runBoth = async (
  body: string,
  config: string,
  source = `---- MODULE M ----\nEXTENDS Naturals, Sequences, TLC\n${body}\n====`,
) => {
  const native = await run(source, config, "debug");
  const typeScript = await run(source, config, "0");
  expect(native.isNative).toBe(true);
  expect(native.result).toEqual(typeScript.result);
  expect(native.printed).toEqual(typeScript.printed);
  return native;
};

describe("check's result", () => {
  it("carries each variable as TLC prints it and as plain data", async () => {
    const run = await runBoth(
      [
        "CONSTANTS a, b",
        "VARIABLES x, r, s, f, m",
        'Init == /\\ x = 0 /\\ r = [p |-> <<1, "s">>, q |-> {2, 1}] /\\ s = 2..3',
        "        /\\ f = (0 :> TRUE @@ 2 :> FALSE) /\\ m = {a, b}",
        "Next == x' = x + 1 /\\ PrintT(x) /\\ UNCHANGED <<r, s, f, m>>",
        "Inv == x < 1",
      ].join("\n"),
      "CONSTANTS a = a b = b\nINIT Init\nNEXT Next\nINVARIANT Inv",
    );
    expect(run.printed).toEqual(["0"]);
    expect(run.result.status).toBe("invariant-violation");
    expect([run.result.generatedStates, run.result.distinctStates, run.result.depth]).toEqual([
      2, 2, 2,
    ]);
    const violation = run.result.violations[0];
    expect([run.result.violations.length, violation.code, violation.headline]).toEqual([
      1,
      2110,
      "Invariant Inv is violated.",
    ]);
    expect(violation.states.map((state) => state.label)).toEqual([
      "Initial predicate",
      "Next line 7, col 9 to line 7, col 59 of module M",
    ]);
    expect(violation.states[1].variables).toEqual({
      x: { text: "1", value: 1 },
      r: {
        text: '[p |-> <<1, "s">>, q |-> {1, 2}]',
        value: { p: [1, "s"], q: { "@set": [1, 2] } },
      },
      s: { text: "2..3", value: { "@set": [2, 3] } },
      f: {
        text: "(0 :> TRUE @@ 2 :> FALSE)",
        value: {
          "@function": [
            [0, true],
            [2, false],
          ],
        },
      },
      m: { text: "{a, b}", value: { "@set": [{ "@model": "a" }, { "@model": "b" }] } },
    });
  });

  it("reports a deadlock, then the temporal property the deadlocked state violates", async () => {
    const directory = join(import.meta.dirname, "../fixtures/github710");
    const run = await runBoth(
      "",
      readFileSync(join(directory, "Github710d.cfg"), "utf8"),
      readFileSync(join(directory, "Github710d.tla"), "utf8"),
    );
    expect(run.result.status).toBe("deadlock");
    expect(
      run.result.violations.map((violation) => [
        violation.code,
        violation.headline,
        violation.states.map((state) => state.variables.x.value),
      ]),
    ).toEqual([
      [2114, "Deadlock reached.", [0, 1, 2, 3]],
      [2116, "Temporal property NeverThree was violated.\n", [0, 1, 2, 3]],
    ]);
  });

  // Lazy.out is the behavior TLC (tla2tools at d8fb231) prints for the model, whose ALIAS holds the
  // sets and functions TLC keeps lazy.
  it("writes a lazy set or function as the text TLC prints for it", async () => {
    const directory = join(import.meta.dirname, "../fixtures/plain-lazy");
    const run = await runBoth(
      "",
      readFileSync(join(directory, "Lazy.cfg"), "utf8"),
      readFileSync(join(directory, "Lazy.tla"), "utf8"),
    );
    const states = run.result.violations[0].states;
    expect(
      states
        .map(
          (state, index) =>
            `State ${index + 1}: <${state.label}>\n${Object.entries(state.variables)
              .map((entry) => `/\\ ${entry[0]} = ${entry[1].text}\n`)
              .join("")}\n`,
        )
        .join(""),
    ).toBe(readFileSync(join(directory, "Lazy.out"), "utf8"));
    const variables = states[0].variables;
    const lazy = Object.entries(variables).filter(
      (entry) => entry[0] !== "x" && entry[0] !== "nested",
    );
    expect(lazy.map((entry) => entry[1].value)).toEqual(
      lazy.map((entry) => ({ "@lazy": entry[1].text })),
    );
    expect(variables.nested.value).toEqual([{ "@lazy": "Nat" }, 1]);
  });

  it("reports where a lasso's cycle starts", async () => {
    const run = await runBoth(
      [
        "VARIABLE x",
        "Init == x = 0",
        "Next == x' = 1 - x",
        "Spec == Init /\\ [][Next]_x /\\ WF_x(Next)",
        "Live == <>[](x = 1)",
      ].join("\n"),
      "SPECIFICATION Spec\nPROPERTY Live",
    );
    expect(run.result.status).toBe("liveness-violation");
    const violation = run.result.violations[0];
    expect([violation.headline, violation.loopStart, violation.states.length]).toEqual([
      "Temporal property Live was violated.\n",
      0,
      2,
    ]);
  });

  it("reports an error with the behavior up to the state TLC was expanding", async () => {
    const run = await runBoth(
      ["VARIABLE x", "Init == x = 0", "Next == x' = 2 \\div (2 - x)"].join("\n"),
      "INIT Init\nNEXT Next",
    );
    expect(run.result.status).toBe("error");
    expect(
      run.result.violations.map((violation) => [
        violation.headline,
        violation.states.map((state) => state.variables.x.text),
      ]),
    ).toEqual([["The second argument of \\div is 0.", ["0", "1", "2"]]]);
  });

  it("reports an initial state that violates an invariant, and a false assumption", async () => {
    const initial = await runBoth(
      "VARIABLE x\nInit == x = 0\nNext == UNCHANGED x\nInv == x > 0",
      "INIT Init\nNEXT Next\nINVARIANT Inv",
    );
    expect(initial.result.violations).toEqual([
      {
        code: 2107,
        headline: "Invariant Inv is violated by the initial state:",
        states: [{ label: "Initial predicate", variables: { x: { text: "0", value: 0 } } }],
      },
    ]);
    const assumption = await runBoth("ASSUME PrintT(1) /\\ 1 = 2", "");
    expect([assumption.result.status, assumption.printed, assumption.result.violations]).toEqual([
      "assumption-violation",
      ["1"],
      [
        {
          code: 2104,
          headline: "Assumption line 3, col 8 to line 3, col 25 of module M is false.",
          states: [],
        },
      ],
    ]);
  });

  it("reports each violation -continue goes on past, through the TypeScript check", async () => {
    const reported: string[] = [];
    const result = await check({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == x # 1 /\\ x # 2\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
      isContinued: true,
      onProgress: (progress) => {
        if (progress.kind === "violation") reported.push(progress.violation.headline);
      },
    });
    expect(reported).toEqual(["Invariant Inv is violated.", "Invariant Inv is violated."]);
    expect(
      result.violations.map((violation) =>
        violation.states.map((state) => state.variables.x.value),
      ),
    ).toEqual([
      [0, 1],
      [0, 1, 2],
    ]);
  });
});

// check's result: what the native check records as it prints, and what the TypeScript check's
// result converts to, the same for each model, every variable as TLC prints it and as plain data.

import { afterEach, describe, expect, it, spyOn } from "bun:test";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { check, type CheckProgress, type CheckResult } from "../../src";
import { checkNatively, checkWithInterpreter } from "../native-check";

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

  it("keeps TLC's text but no data for a value past the bound on plain data", async () => {
    const run = await runBoth(
      [
        "VARIABLE x",
        "Init == x = 0",
        "Next == x' = x + 1",
        "Inv == x < 1",
        "Alias == [x |-> x, big |-> 1..1000000000]",
      ].join("\n"),
      "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias",
    );
    expect(run.result.violations[0].states.map((state) => state.variables.big)).toEqual([
      { text: "1..1000000000", value: null },
      { text: "1..1000000000", value: null },
    ]);
  });

  it("writes a variable a successor leaves undefined as null, and a model value named null", async () => {
    const run = await runBoth(
      [
        "CONSTANT N",
        "VARIABLES x, y",
        "Init == x = N /\\ y = 0",
        "Next == y < 1 /\\ y' = y + 1",
      ].join("\n"),
      "CONSTANT N = null\nINIT Init\nNEXT Next",
    );
    expect(run.result.status).toBe("error");
    expect(
      run.result.violations[0].states.map((state) => [state.variables.x, state.variables.y]),
    ).toEqual([
      [
        { text: "null", value: { "@model": "null" } },
        { text: "0", value: 0 },
      ],
      [
        { text: "null", value: null },
        { text: "1", value: 1 },
      ],
    ]);
  });

  // TLC at d8fb231 prints a function it keeps lazy, and fails to apply, as its lazy text. The
  // native check prints the ALIAS's error in its place, which isn't TLC's, so only the TypeScript
  // check is checked here until the trace printer follows TLC.
  it("carries a lazy function that fails to apply as its lazy text", async () => {
    const result = await checkWithInterpreter({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nf[i \\in 1..1] == IF i = 1 THEN 1 \\div 0 ELSE f[i]\nInit == x = 0\nNext == x' = x + 1\nInv == x < 1\nAlias == [x |-> x, f |-> f]\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias",
    });
    const text = "[i \\in 1..1 |-> <expression line 4, col 18 to line 4, col 49 of module M>]";
    expect(result.violations.map((violation) => violation.states)).toEqual([
      [0, 1].map((x, index) => ({
        label:
          index === 0 ? "Initial predicate" : "Next line 6, col 9 to line 6, col 18 of module M",
        variables: { x: { text: String(x), value: x }, f: { text, value: { "@lazy": text } } },
      })),
    ]);
  });

  // TLC at d8fb231 reports the violation, fails to print its first state, whose ALIAS holds a set
  // it can't normalize, and reports the exception with no states. The native check prints the
  // whole trace, which isn't TLC's, so only the TypeScript check is checked here until the trace
  // printer follows TLC.
  it("reports the exception TLC raises printing a state, after the states it printed", async () => {
    const result = await checkWithInterpreter({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\nInv == x < 1\nAlias == [x |-> x, v |-> {1, TRUE}]\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias",
    });
    expect([result.status, result.violations]).toEqual([
      "invariant-violation",
      [
        { code: 2110, headline: "Invariant Inv is violated.", states: [] },
        {
          code: 1000,
          headline:
            "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: Attempted to compare boolean TRUE with non-boolean:\n1",
          states: [],
        },
      ],
    ]);
  });

  // TLC at d8fb231 reports the overflow, the behavior, and then the Assert that fails as it
  // rebuilds the trace, as the CLI prints them. The native check declines the model, so the
  // TypeScript check reports it.
  it("reports what fails as TLC rebuilds a failure's trace, after the trace", async () => {
    const lines: string[] = [];
    process.env.PROVE_IT_ENGINE = "debug";
    const spy = spyOn(console, "error").mockImplementation((message: unknown) => {
      if (typeof message === "string") lines.push(message);
    });
    const result = await check({
      source:
        '---- MODULE M ----\nEXTENDS Integers, TLC\nVARIABLE x\nInit == x = 0\nNext == x = 0 /\\ \\E i \\in {1, 2} : x\' = IF i = 1 THEN SUBSET (1..31) ELSE Assert(FALSE, "boom")\n====',
      config: "INIT Init\nNEXT Next",
    }).finally(() => spy.mockRestore());
    expect(lines).toContainEqual(expect.stringMatching(/^\[engine\] native: check declined: /));
    expect([result.status, result.violations]).toEqual([
      "error",
      [
        {
          code: 1000,
          headline:
            "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: Overflow when computing the number of elements in:\nSUBSET (1..31)",
          states: [{ label: "Initial predicate", variables: { x: { text: "0", value: 0 } } }],
        },
        {
          code: 1000,
          headline:
            'TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a tlc2.tool.EvalException\n: The first argument of Assert evaluated to FALSE; the second argument was:\n"boom"',
          states: [],
        },
      ],
    ]);
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

  it("logs a check the native check declines once, with what both checks read", async () => {
    const directory = mkdtempSync(join(tmpdir(), "prove-it-check-log-"));
    const logPath = join(directory, "checks.jsonl");
    process.env.PROVE_IT_CHECK_LOG = logPath;
    process.env.PROVE_IT_ENGINE = "debug";
    const lines: string[] = [];
    const spy = spyOn(console, "error").mockImplementation((message: unknown) => {
      if (typeof message === "string") lines.push(message);
    });
    try {
      await check({
        source:
          '---- MODULE M ----\nEXTENDS Naturals, Json, Helper\nVARIABLE x\nInit == x = 0\nNext == x < 1 /\\ x\' = x + 1 /\\ ndJsonSerialize("out.json", <<Value>>)\n====',
        config: "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
        loadModule: (name) =>
          name === "Helper" ? "---- MODULE Helper ----\nValue == 1\n====" : undefined,
        writeFile: () => {},
      });
    } finally {
      spy.mockRestore();
      delete process.env.PROVE_IT_CHECK_LOG;
    }
    expect(lines).toContainEqual(expect.stringMatching(/^\[engine\] native: check declined: /));
    const entries = readFileSync(logPath, "utf8")
      .trim()
      .split("\n")
      .map((line) => JSON.parse(line));
    rmSync(directory, { recursive: true, force: true });
    expect(entries.filter((entry) => "config" in entry)).toHaveLength(1);
    expect(new Set(entries.map((entry) => entry.id)).size).toBe(1);
    expect(entries.filter((entry) => entry.module === "Helper").length).toBeGreaterThan(0);
  });

  // The native check reports the events once it ends, the TypeScript check as it goes; both in
  // the same order among what the spec prints. The search's periodic progress depends on the time.
  it.each([
    [
      "VARIABLE x\nInit == x \\in 0..20 /\\ PrintT(x = 0)\nNext == x' = (x + 1) % 21\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\nLive == []<>(x = 0)\nSafe == x < 21\nP == x >= 0",
      "SPECIFICATION Spec\nPROPERTY Live\nPROPERTY P\nINVARIANT Safe",
    ],
    [
      'VARIABLE x\nInit == x = 0\nNext == x\' = [x EXCEPT !["c"] = 1]\nC == TRUE',
      "INIT Init\nNEXT Next\nINVARIANT C",
    ],
    // What the property prints as TLC finds the behavior that violates it, before the report.
    [
      'VARIABLE x\nInit == x = FALSE\nNext == x\' = FALSE\nSpec == Init /\\ [][Next]_x\nProp == <>[](Print(x, x = TRUE) /\\ TLCGet("diameter") > 0)',
      "SPECIFICATION Spec\nPROPERTY Prop",
    ],
  ])("reports the progress the TypeScript check reports, in order: %s", async (body, config) => {
    const source = `---- MODULE M ----\nEXTENDS Naturals, TLC\n${body}\n====`;
    const run = async (checker: typeof check) => {
      const reported: unknown[] = [];
      await checker({
        source,
        config,
        onPrint: (text) => reported.push(text),
        onProgress: (progress) => {
          if (progress.kind !== "progress") reported.push(progress);
        },
      });
      return reported;
    };
    const reference = await run(checkWithInterpreter);
    const native = await checkNatively({ source, config, onProgress: () => {} });
    expect(native.declined).toBeUndefined();
    expect(await run(check)).toEqual(reference);
  });

  // TLC checks the temporal properties part way through the search, on a schedule of the time,
  // which PROVE_IT_TEST_LIVE_CHECK_AT sets to a count of states for both checks.
  it("reports a check of the temporal properties part way through the search", async () => {
    const source =
      "---- MODULE M ----\nEXTENDS Naturals\nVARIABLES x, y\nInit == x = 0 /\\ y = 0\nNext == \\/ x' = (x + 1) % 30 /\\ UNCHANGED y\n        \\/ y' = (y + 1) % 30 /\\ UNCHANGED x\nSpec == Init /\\ [][Next]_<<x, y>> /\\ WF_<<x, y>>(Next)\nPlain == []<>(x >= 0)\n====";
    const config = "SPECIFICATION Spec\nPROPERTY Plain\nCHECK_DEADLOCK FALSE";
    const run = async (checker: typeof check) => {
      const reported: string[] = [];
      await checker({
        source,
        config,
        onProgress: (progress) => {
          if (progress.kind === "liveness-started") reported.push(`${progress.isComplete}`);
          else if (progress.kind !== "progress") reported.push(progress.kind);
        },
      });
      return reported;
    };
    process.env.PROVE_IT_TEST_LIVE_CHECK_AT = "10";
    try {
      const reference = await run(checkWithInterpreter);
      expect(reference).toContain("false");
      expect(await run(check)).toEqual(reference);
    } finally {
      delete process.env.PROVE_IT_TEST_LIVE_CHECK_AT;
    }
  });

  // TLC reports the search's progress every minute, and the native check reports one event for
  // each report its search made, with the counts it printed, once the check ends.
  // PROVE_IT_TEST_PROGRESS_AT has the native search report it once, at the level's state it
  // names, which the TypeScript check doesn't read.
  it("reports the search's progress where the native search reports it", async () => {
    const settings = {
      PROVE_IT_TEST_PROGRESS_AT: "6000",
      PROVE_IT_WORKERS: "4",
      PROVE_IT_SHARED_LEVEL: "1",
    };
    Object.assign(process.env, settings);
    try {
      const progress: CheckProgress[] = [];
      const checked = await checkNatively({
        source:
          "---- MODULE Wide ----\nEXTENDS Integers\nVARIABLE n\nInit == n = 0\nNext == \\/ n = 0 /\\ n' \\in 1..4000\n        \\/ n \\in 1..4000 /\\ n' = n + 4000\nSpec == Init /\\ [][Next]_n\n====",
        config: "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE",
        workers: 4,
        onProgress: (event) => {
          if (event.kind === "progress") progress.push(event);
        },
      });
      expect(checked.declined).toBeUndefined();
      expect(progress).toHaveLength(1);
      const statistics = progress[0].kind === "progress" ? progress[0].statistics : undefined;
      expect(statistics?.generatedStates).toBeGreaterThan(4001);
      expect(statistics?.generatedStates).toBeLessThanOrEqual(8001);
    } finally {
      Object.keys(settings).forEach((name) => delete process.env[name]);
    }
  });

  it("reports each violation -continue goes on past", async () => {
    const reported: string[] = [];
    const checked = await checkNatively({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == x # 1 /\\ x # 2\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
      isContinued: true,
      onProgress: (progress) => {
        if (progress.kind === "violation") reported.push(progress.violation.headline);
      },
    });
    expect(checked.declined).toBeUndefined();
    const result = checked.result;
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

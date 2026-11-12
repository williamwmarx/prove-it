// check's result: what the native check records as it prints, every variable as TLC prints it and
// as plain data.

import { describe, expect, it } from "bun:test";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { check, type CheckProgress, TlaUnsupportedError } from "../../src";
import { checkOnEngine, expectDeclined } from "../native-check";

// The native check's run of a module M of the body, and what the spec printed.
const getRun = async (
  body: string,
  config: string,
  source = `---- MODULE M ----\nEXTENDS Naturals, Sequences, TLC\n${body}\n====`,
) => {
  const printed: string[] = [];
  const result = await checkOnEngine({ source, config, onPrint: (text) => printed.push(text) });
  return { result, printed };
};

describe("check's result", () => {
  it("carries each variable as TLC prints it and as plain data", async () => {
    const run = await getRun(
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
    // TLC prints 0 as it searches, then as it rebuilds the trace, before its second state and
    // after it.
    expect(run.printed).toEqual(["0", "0", "0"]);
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
    const run = await getRun(
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
    const run = await getRun(
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
    const run = await getRun(
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
    const run = await getRun(
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

  it("declines a failure TLC fails again to evaluate as it rebuilds the trace", async () => {
    await expectDeclined(
      {
        source:
          '---- MODULE M ----\nEXTENDS Integers, TLC\nVARIABLE x\nInit == x = 0\nNext == x = 0 /\\ \\E i \\in {1, 2} : x\' = IF i = 1 THEN SUBSET (1..31) ELSE Assert(FALSE, "boom")\n====',
        config: "INIT Init\nNEXT Next",
      },
      "the engine stopped: an overflow counting the elements of a power set: evaluating the failure again: an action that fails or prints after a successor TLC can't fingerprint",
    );
  });

  it("reports where a lasso's cycle starts", async () => {
    const run = await getRun(
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
    const run = await getRun(
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
    const initial = await getRun(
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
    const assumption = await getRun("ASSUME PrintT(1) /\\ 1 = 2", "");
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

  it("logs a check the native check declines once, with what it reads", async () => {
    const directory = mkdtempSync(join(tmpdir(), "prove-it-check-log-"));
    const logPath = join(directory, "checks.jsonl");
    process.env.PROVE_IT_CHECK_LOG = logPath;
    const source =
      '---- MODULE M ----\nEXTENDS Naturals, Json, Helper\nVARIABLE x\nInit == x = 0\nNext == x < 1 /\\ x\' = x + 1 /\\ ndJsonSerialize("out.json", <<Value>>)\n====';
    const config = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE";
    try {
      await expect(
        check({
          source,
          config,
          loadModule: (name) =>
            name === "Helper" ? "---- MODULE Helper ----\nValue == 1\n====" : undefined,
          writeFile: () => {},
        }),
      ).rejects.toBeInstanceOf(TlaUnsupportedError);
    } finally {
      delete process.env.PROVE_IT_CHECK_LOG;
    }
    const entries = readFileSync(logPath, "utf8")
      .trim()
      .split("\n")
      .map((line) => JSON.parse(line));
    rmSync(directory, { recursive: true, force: true });
    const checks = entries.filter((entry) => "config" in entry);
    expect(checks).toEqual([
      {
        id: expect.any(String),
        source,
        config,
        isTool: false,
        isContinued: false,
        isWarningEnabled: true,
        caller: expect.any(String),
      },
    ]);
    expect(new Set(entries.map((entry) => entry.id)).size).toBe(1);
    expect(entries.filter((entry) => entry.module === "Helper").length).toBeGreaterThan(0);
  });

  // TLC reports the search's progress every minute, and the native check reports one event for
  // each report its search made, with the counts it printed, once the check ends.
  // PROVE_IT_TEST_PROGRESS_AT has the native search report it once, at the level's state it
  // names.
  it("reports the search's progress where the native search reports it", async () => {
    const settings = {
      PROVE_IT_TEST_PROGRESS_AT: "6000",
      PROVE_IT_WORKERS: "4",
      PROVE_IT_SHARED_LEVEL: "1",
    };
    Object.assign(process.env, settings);
    try {
      const progress: CheckProgress[] = [];
      await checkOnEngine({
        source:
          "---- MODULE Wide ----\nEXTENDS Integers\nVARIABLE n\nInit == n = 0\nNext == \\/ n = 0 /\\ n' \\in 1..4000\n        \\/ n \\in 1..4000 /\\ n' = n + 4000\nSpec == Init /\\ [][Next]_n\n====",
        config: "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE",
        workers: 4,
        onProgress: (event) => {
          if (event.kind === "progress") progress.push(event);
        },
      });
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
    const result = await checkOnEngine({
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

// TLC reports a successor it can't fingerprint three times: the exception with the trace, the
// exception again as it prints the trace, and where it failed to fingerprint.
describe("check's result holds each report TLC prints", () => {
  it("reports a successor TLC can't fingerprint as TLC does", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals, FiniteSets\nVARIABLE x\nInit == x = 0\nNext == x' = SUBSET (SUBSET (1..32))\n====",
      config: "INIT Init\nNEXT Next",
      onPrint: () => {},
    });
    const exception =
      "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: Overflow when computing the number of elements in:\nSUBSET (1..32)";
    expect(
      result.violations.map((violation) => [
        violation.code,
        violation.headline,
        violation.states.length,
      ]),
    ).toEqual([
      [1000, exception, 1],
      [1000, exception, 0],
      [
        2147,
        "TLC was unable to fingerprint.\n\nFingerprint Stack Trace:\n1) line 5, col 22 to line 5, col 35 of module M\n0) line 5, col 14 to line 5, col 36 of module M\n\nReason:\nOverflow when computing the number of elements in:\nSUBSET (1..32)",
        0,
      ],
    ]);
  });
});

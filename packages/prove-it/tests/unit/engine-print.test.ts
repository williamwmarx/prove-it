// The engine reads TLCGet("level") and TLCGet("distinct") as TLC does. Each check runs with the
// engine and without it, and compares the whole result and every line printed.

import { afterEach, describe, expect, it, spyOn } from "bun:test";

import { check } from "../../src";

const setting = process.env.PROVE_IT_ENGINE;

afterEach(() => {
  if (setting === undefined) delete process.env.PROVE_IT_ENGINE;
  else process.env.PROVE_IT_ENGINE = setting;
});

const run = async (body: string, config: string, engine: string) => {
  process.env.PROVE_IT_ENGINE = engine;
  const printed: string[] = [];
  const lines: string[] = [];
  const spy = spyOn(console, "error").mockImplementation((message: unknown) => {
    if (typeof message === "string" && message.startsWith("[engine] ")) lines.push(message);
  });
  try {
    const result = await check({
      source: `---- MODULE M ----\n${body}\n====`,
      config,
      onPrint: (text) => printed.push(text),
    });
    return { result, printed, lines };
  } finally {
    spy.mockRestore();
  }
};

const checkBoth = async (body: string, config: string) => {
  const engine = await run(body, config, "debug");
  const reference = await run(body, config, "0");
  expect(engine.result).toEqual(reference.result);
  expect(engine.printed).toEqual(reference.printed);
  return engine;
};

const CHECKED = /^\[engine\] checked \d+ states/;

describe("the engine's TLCGet", () => {
  it("reads TLCGet in the initial predicate, the next-state relation and invariants as TLC does", async () => {
    const body = [
      "EXTENDS Naturals, FiniteSets, TLC",
      "VARIABLES x, y",
      'Init == x = 0 /\\ TLCGet("level") = 0 /\\ TLCGet("distinct") = 0 /\\ y \\in {0, 1}',
      "Next == \\/ /\\ x < 3",
      '           /\\ TLCGet("level") = x + 1',
      "           /\\ x' = x + 1",
      "           /\\ y' = 1 - y",
      `           /\\ TLCGet("level")' = x' + 1`,
      "        \\/ UNCHANGED <<x, y>>",
      // TLC counts a new state before it checks the invariants.
      'Inv == TLCGet("distinct") = 2 * x + 1 + y \\/ TLCGet("distinct") = 2 * x + 2 - y',
      // A memo table keyed by y alone would answer for another level.
      'Counted == Cardinality({z \\in 0..10 : z < TLCGet("level") + y}) = TLCGet("level") + y',
    ].join("\n");
    const { result, lines } = await checkBoth(body, "INIT Init\nNEXT Next\nINVARIANT Inv Counted");
    expect(lines).toEqual([expect.stringMatching(CHECKED)]);
    expect([result.status, result.generatedStates, result.distinctStates]).toEqual([
      "success",
      16,
      8,
    ]);
  });

  it("reads TLCGet in constraints and action constraints as TLC does", async () => {
    const body = [
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      "Init == x = 0",
      "Next == x' = x + 1",
      'Shallow == TLCGet("level") < 4',
      `Step == TLCGet("level") + 1 = TLCGet("level")' /\\ TLCGet("distinct") < 10`,
      'Inv == x + 1 = TLCGet("level")',
    ].join("\n");
    const { result, lines } = await checkBoth(
      body,
      "INIT Init\nNEXT Next\nINVARIANT Inv\nCONSTRAINT Shallow\nACTION_CONSTRAINT Step",
    );
    expect(lines).toEqual([expect.stringMatching(CHECKED)]);
    // As TLC 2026.11.06 counts them.
    expect([result.status, result.generatedStates, result.distinctStates, result.depth]).toEqual([
      "success",
      4,
      3,
      3,
    ]);
  });
});

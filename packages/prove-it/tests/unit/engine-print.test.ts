// The engine prints, and reads TLCGet("level") and TLCGet("distinct"), only where it evaluates
// them exactly as TLC does, and hands the rest over. Each check runs with the engine and without
// it, and compares the whole result and every line printed.

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

describe("the engine's Print, PrintT and TLCGet", () => {
  it("prints as TLC does from the initial predicate, the next-state relation and invariants", async () => {
    const body = [
      "EXTENDS Naturals, FiniteSets, TLC",
      "VARIABLES x, y",
      'Init == /\\ x = 0 /\\ PrintT(<<"init", x, TLCGet("level"), TLCGet("distinct")>>)',
      "        /\\ y \\in {0, 1}",
      "Next == \\/ /\\ x < 3",
      '           /\\ Print(<<"next", x, y, TLCGet("level"), TLCGet("distinct")>>, TRUE)',
      "           /\\ x' = x + 1",
      "           /\\ y' = 1 - y",
      `           /\\ PrintT(<<"primed", x', TLCGet("level")'>>)`,
      "        \\/ UNCHANGED <<x, y>>",
      'Inv == PrintT(<<"inv", x, y, TLCGet("level"), TLCGet("distinct")>>)',
      // A memo table keyed by y alone would answer for another level.
      'Counted == Cardinality({z \\in 0..10 : z < TLCGet("level") + y}) = TLCGet("level") + y',
    ].join("\n");
    const { result, printed, lines } = await checkBoth(
      body,
      "INIT Init\nNEXT Next\nINVARIANT Inv Counted",
    );
    expect(lines).toEqual([expect.stringMatching(CHECKED)]);
    expect([result.status, result.generatedStates, result.distinctStates]).toEqual([
      "success",
      16,
      8,
    ]);
    // What TLC 2026.11.06 prints.
    expect(printed).toEqual([
      '<<"init", 0, 0, 0>>',
      '<<"inv", 0, 0, 1, 1>>',
      '<<"inv", 0, 1, 1, 2>>',
      '<<"next", 0, 0, 1, 2>>  TRUE',
      '<<"primed", 1, 2>>',
      '<<"inv", 1, 1, 2, 3>>',
      '<<"next", 0, 1, 1, 3>>  TRUE',
      '<<"primed", 1, 2>>',
      '<<"inv", 1, 0, 2, 4>>',
      '<<"next", 1, 1, 2, 4>>  TRUE',
      '<<"primed", 2, 3>>',
      '<<"inv", 2, 0, 3, 5>>',
      '<<"next", 1, 0, 2, 5>>  TRUE',
      '<<"primed", 2, 3>>',
      '<<"inv", 2, 1, 3, 6>>',
      '<<"next", 2, 0, 3, 6>>  TRUE',
      '<<"primed", 3, 4>>',
      '<<"inv", 3, 1, 4, 7>>',
      '<<"next", 2, 1, 3, 7>>  TRUE',
      '<<"primed", 3, 4>>',
      '<<"inv", 3, 0, 4, 8>>',
    ]);
  });

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
  it("prints each time it evaluates a definition, however little the definition reads", async () => {
    const body = [
      "EXTENDS Naturals, TLC",
      "VARIABLES x, y",
      'Tick == PrintT(<<"tick", y>>)',
      "Init == x = 0 /\\ y = 0",
      "Next == x < 4 /\\ Tick /\\ x' = x + 1 /\\ y' = 0",
      "Inv == Tick /\\ Tick",
    ].join("\n");
    const { printed, lines } = await checkBoth(
      body,
      "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
    );
    expect(lines).toEqual([expect.stringMatching(CHECKED)]);
    // Twice for each of the 5 states, and once for each of the 4 steps.
    expect(printed).toEqual(new Array(14).fill('<<"tick", 0>>'));
  });

  it("takes the value TLC computed at startup for a definition that prints", async () => {
    const body = [
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      'Inv == Print("checked once", TRUE)',
      "Init == x = 0",
      "Next == x < 2 /\\ x' = x + 1",
    ].join("\n");
    const { printed, lines } = await checkBoth(
      body,
      "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
    );
    expect(lines).toEqual([expect.stringMatching(CHECKED)]);
    expect(printed).toEqual(['"checked once"  TRUE']);
  });

  it("names a definition that prints, which TLC computed at startup, without printing again", async () => {
    // The interpreter evaluates C again wherever the spec names it, so this compares with TLC.
    const body = [
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      'C == Print("c", TRUE)',
      "Init == C /\\ x = 0",
      "Next == C /\\ x < 2 /\\ x' = x + 1",
      "Inv == x < 5 /\\ C",
    ].join("\n");
    const { result, printed, lines } = await run(
      body,
      "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
      "debug",
    );
    expect(lines).toEqual([expect.stringMatching(CHECKED)]);
    expect([result.status, result.distinctStates]).toEqual(["success", 3]);
    // What TLC 2026.11.06 prints.
    expect(printed).toEqual(['"c"  TRUE']);
  });

  it("hands over Print where TLC evaluates it otherwise", async () => {
    const prints = [
      // TLC evaluates an operator's argument where the operator uses it, and caches it.
      "Twice(e) == e /\\ e\nP == Twice(Print(x, TRUE))",
      "P == LET e == Print(x, TRUE) IN e /\\ e",
      "P == IF \\E z \\in {x, 5} : Print(z, z = 5) THEN TRUE ELSE FALSE",
      "P == {Print(z, z) : z \\in {x, 5}} # {}",
      "P == [z \\in {x, 5} |-> Print(z, z)][x] = x",
      "P == Print(Print(x, 1), TRUE)",
    ];
    for (const print of prints) {
      const body = `EXTENDS Naturals, TLC\nVARIABLE x\n${print}\nInit == x = 0\nNext == x < 2 /\\ P /\\ x' = x + 1`;
      const { lines } = await checkBoth(body, "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE");
      expect([print, lines]).toEqual([
        print,
        [expect.stringMatching(/handed over .*: unsupported: Print/)],
      ]);
    }
  });

  it("hands over Print in a constraint, in ENABLED, and in a spec with temporal properties", async () => {
    const models = [
      ["Next == x < 2 /\\ x' = x + 1\nC == Print(x, TRUE)", "CONSTRAINT C"],
      [
        "Next == x < 2 /\\ Print(x, TRUE) /\\ x' = x + 1\nInv == x = 2 \\/ ENABLED Next",
        "INVARIANT Inv",
      ],
      ["Next == x < 2 /\\ Print(x, TRUE) /\\ x' = x + 1\nLive == <>(x = 2)", "PROPERTY Live"],
    ];
    for (const [definitions, check] of models) {
      const body = `EXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\n${definitions}`;
      const { lines } = await checkBoth(
        body,
        `INIT Init\nNEXT Next\n${check}\nCHECK_DEADLOCK FALSE`,
      );
      expect([check, lines]).toEqual([
        check,
        [expect.stringMatching(/handed over .*: unsupported: Print/)],
      ]);
    }
  });

  it("hands over printing a value whose text depends on how TLC built it", async () => {
    // TLC prints an interval as one, and a record's fields in the order they were written.
    const values = ["1..3", "{2}", "[b |-> 1, a |-> 2]", '[z \\in {"a b"} |-> 1]', "{1..2}"];
    for (const value of values) {
      const body = `EXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ PrintT(${value}) /\\ x' = x + 1`;
      const { lines } = await checkBoth(body, "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE");
      expect([value, lines]).toEqual([
        value,
        [expect.stringMatching(/handed over .*: printing a value whose text depends/)],
      ]);
    }
    const printable = ['<<1, "a", TRUE>>', "{1, 3}", "[a |-> {}]", "(1 :> 2 @@ 3 :> 4)", "{}"];
    for (const value of printable) {
      const body = `EXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == (x < 2 /\\ PrintT(${value}) /\\ x' = x + 1) \\/ UNCHANGED x`;
      const { lines } = await checkBoth(body, "INIT Init\nNEXT Next");
      expect([value, lines]).toEqual([value, [expect.stringMatching(CHECKED)]]);
    }
  });

  it("prints nothing of an expansion it hands over, which the interpreter does again", async () => {
    const body = [
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      'Init == x \\in {0, 1} /\\ PrintT(<<"init", x>>)',
      'Next == \\/ PrintT(<<"before", x>>) /\\ x\' = x + 2',
      '        \\/ PrintT(<<"after", x>>) /\\ x\' = x + 3',
      'Inv == PrintT(<<"inv", x>>) /\\ x < 7',
    ].join("\n");
    const { result, printed, lines } = await checkBoth(body, "INIT Init\nNEXT Next\nINVARIANT Inv");
    expect(lines).toEqual([expect.stringMatching(/handed over .*: an invariant violated$/)]);
    expect(result.status).toBe("invariant-violation");
    // The engine stops in the expansion of 4, whose second step violates Inv.
    expect(printed.filter((line) => line === '<<"before", 4>>')).toHaveLength(1);
    // A failing initial state hands over before the engine prints anything.
    const initial = await checkBoth(
      body.replace("x < 7", "x < 1"),
      "INIT Init\nNEXT Next\nINVARIANT Inv",
    );
    expect(initial.lines).toEqual([
      expect.stringMatching(/handed over .*: an invariant violated in an initial state$/),
    ]);
  });
});

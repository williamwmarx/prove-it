import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { checkOnEngine, expectDeclined } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-ext");

const getFixture = (name: string, configName = name) => ({
  source: readFileSync(join(DIRECTORY, `${name}.tla`), "utf8"),
  config: readFileSync(join(DIRECTORY, `${configName}.cfg`), "utf8"),
});

// The check of a fixture, with what it printed.
const checkFixture = async (name: string, configName = name) => {
  const printed: string[] = [];
  const result = await checkOnEngine({
    ...getFixture(name, configName),
    onPrint: (text) => printed.push(text),
  });
  return { ...result, printed };
};

const getSource = (body: string) =>
  `---- MODULE M ----\nEXTENDS Naturals, TLCExt\nVARIABLE x\n${body}\n====`;

const checkModule = (body: string, config: string) =>
  checkOnEngine({ source: getSource(body), config });

describe("TLCExt operators match TLC", () => {
  it("prints the string and both values when AssertEq fails", async () => {
    const result = await checkFixture("AssertEq");
    expect(result.status).toBe("success");
    expect(result.printed).toEqual([
      '"Assertion failed"',
      "1",
      "0",
      '"Assertion failed"',
      "2",
      "0",
    ]);
  });

  it("declines Trace with no state", async () => {
    await expectDeclined(
      getFixture("TraceAssume"),
      "an assumption that fails to evaluate: evaluating the assumption again: the builtin Trace",
    );
  });

  it("picks every seen successor without asking", async () => {
    const result = await checkFixture("Pick", "PickSeen");
    expect(result.status).toBe("success");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([4, 3, 3]);
  });

  it("fails PickSuccessor without a complete successor state", async () => {
    expect((await checkFixture("Pick", "PickIncomplete")).violations[0]?.headline).toContain(
      'Cannot invoke "tlc2.value.IValue.fingerPrint(long)" because "minVals[i]" is null',
    );
  });

  it("declines to ask interactively for an unseen successor", async () => {
    await expectDeclined(
      {
        source: getSource("Init == x = 0\nNext == x' = (x + 1) % 3\nAsk == PickSuccessor(x' # 1)"),
        config: "INIT Init\nNEXT Next\nACTION_CONSTRAINT Ask",
      },
      "the engine stopped: unsupported: PickSuccessor, which asks TLC's user",
    );
  });

  it("requires a string literal as the message of AssertError", async () => {
    const result = await checkModule(
      'Message == "x"\nASSUME AssertError(Message, 1 \\div 0)\nInit == x = 0\nNext == x\' = x',
      "INIT Init\nNEXT Next",
    );
    expect(result.status).toBe("assumption-violation");
    expect(result.violations[0]?.headline).toContain(
      "In computing AssertError, a non-string expression (line 5, col 20 to line 5, col 26 of module M) was used as the err of an AssertError(err, exp).",
    );
  });

  it("compares AssertError's message with the error's, which holds its code under -tool", async () => {
    const checks = await Promise.all(
      [false, true].map((isTool) =>
        checkOnEngine({
          source:
            '---- MODULE M ----\nEXTENDS Naturals, TLCExt\nASSUME AssertError("The second argument of \\\\div is 0.", 1 \\div 0)\n====',
          config: "",
          isTool,
        }),
      ),
    );
    expect(checks.map((result) => result.status)).toEqual(["success", "assumption-violation"]);
  });

  it("declines TLCGetAndSet of the exit key", async () => {
    await expectDeclined(
      {
        source: getSource(
          'Init == x = 0\nNext == x < 5 /\\ x\' = x + 1 /\\ (x = 2 => TLCGetAndSet("exit", LAMBDA old, new : new, TRUE, FALSE) = FALSE)',
        ),
        config: "INIT Init\nNEXT Next",
      },
      "the engine stopped: unsupported: TLCGetAndSet of a key that stops or configures TLC",
    );
  });
});

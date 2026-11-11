import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { TlaUnsupportedError } from "../../src";
import { checkParsed } from "../../src/parallel";
import { checkNatively } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-ext");

// The check of a fixture, with what it printed, which the engine answers unless it declines for
// the reason `declinedFor`.
const checkFixture = async (name: string, configName = name, declinedFor?: string) => {
  const printed: string[] = [];
  const { result, declined } = await checkNatively({
    source: readFileSync(join(DIRECTORY, `${name}.tla`), "utf8"),
    config: readFileSync(join(DIRECTORY, `${configName}.cfg`), "utf8"),
    onPrint: (text) => printed.push(text),
  });
  expect(declined).toBe(declinedFor);
  return { ...result, printed };
};

const getSource = (body: string) =>
  `---- MODULE M ----\nEXTENDS Naturals, TLCExt\nVARIABLE x\n${body}\n====`;

const checkModule = (body: string, config: string) =>
  checkNatively({ source: getSource(body), config });

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

  it("reports the unassigned variables when Trace has no state", async () => {
    const result = await checkFixture(
      "TraceAssume",
      "TraceAssume",
      "an assumption that fails to evaluate: evaluating the assumption again: the builtin Trace",
    );
    expect(result.status).toBe("assumption-violation");
    expect(result.violations[0]?.headline).toBe(
      "Evaluating assumption line 7, col 8 to line 7, col 19 of module TraceAssume failed.\nAttempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.TupleValue tlc2.module.TLCExt.getTrace(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel) throws java.io.IOException,\nbut it produced the following error:\nIn evaluating TLCExt!Trace, the state is not completely specified yet (variables x, y undefined).",
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

  // The TypeScript check's refusal, which the library throws until the engine answers it.
  it("does not ask interactively for an unseen successor", async () => {
    await expect(
      checkParsed({
        source: getSource("Init == x = 0\nNext == x' = (x + 1) % 3\nAsk == PickSuccessor(x' # 1)"),
        config: "INIT Init\nNEXT Next\nACTION_CONSTRAINT Ask",
      }),
    ).rejects.toThrow(TlaUnsupportedError);
  });

  it("requires a string literal as the message of AssertError", async () => {
    const { result, declined } = await checkModule(
      'Message == "x"\nASSUME AssertError(Message, 1 \\div 0)\nInit == x = 0\nNext == x\' = x',
      "INIT Init\nNEXT Next",
    );
    expect(declined).toBeUndefined();
    expect(result.status).toBe("assumption-violation");
    expect(result.violations[0]?.headline).toContain(
      "In computing AssertError, a non-string expression (line 5, col 20 to line 5, col 26 of module M) was used as the err of an AssertError(err, exp).",
    );
  });

  it("compares AssertError's message with the error's, which holds its code under -tool", async () => {
    const checks = await Promise.all(
      [false, true].map((isTool) =>
        checkNatively({
          source:
            '---- MODULE M ----\nEXTENDS Naturals, TLCExt\nASSUME AssertError("The second argument of \\\\div is 0.", 1 \\div 0)\n====',
          config: "",
          isTool,
        }),
      ),
    );
    expect(checks.map((check) => check.declined)).toEqual([undefined, undefined]);
    expect(checks.map((check) => check.result.status)).toEqual(["success", "assumption-violation"]);
  });

  it("stops checking when TLCGetAndSet sets the exit key", async () => {
    const { result, declined } = await checkModule(
      'Init == x = 0\nNext == x < 5 /\\ x\' = x + 1 /\\ (x = 2 => TLCGetAndSet("exit", LAMBDA old, new : new, TRUE, FALSE) = FALSE)',
      "INIT Init\nNEXT Next",
    );
    expect(declined).toBe(
      "the engine stopped: unsupported: TLCGetAndSet of a key that stops or configures TLC",
    );
    expect(result.status).toBe("success");
    expect([result.generatedStates, result.distinctStates, result.queuedStates]).toEqual([4, 4, 1]);
  });
});

import { describe, expect, it } from "bun:test";

import { check, TlaEvaluationError } from "../../src";
import { UNEXPECTED_EXCEPTION } from "../../src/errors";
import { getErrors, runOnEngine, runTlcNatively } from "../native-check";

const STEP = "Init == x = 0\nNext == x < 2 /\\ x' = x + 1";

const getSource = (definitions: string) =>
  `---- MODULE M ----\nEXTENDS Naturals, Sequences, TLC\nVARIABLE x\n${definitions}\n====`;

const getExitCode = (definitions: string, config = "INIT Init\nNEXT Next") =>
  runOnEngine({ source: getSource(definitions), config }).exitCode;

// Asserts that the CLI declines the model for `reason`, and exits with 1.
const expectRunDeclined = (definitions: string, config: string, reason: string) => {
  const run = runTlcNatively({ source: getSource(definitions), config });
  expect([run.declined, run.exitCode]).toEqual([reason, 1]);
};

describe("CLI exit codes match TLC", () => {
  it.each<[string, string, number]>([
    ["a parse error", "Init == x = = 0\nNext == x' = x", 150],
    ["an unresolved symbol", "Init == x = y\nNext == x' = x", 150],
    ["a constant without a value", "CONSTANT C\nInit == x = 0\nNext == x' = x", 151],
    ["a literal too big for TLC", "Init == x = 3000000000\nNext == x' = x", 255],
    ["an unused literal too big for TLC", "Big == 3000000000\nInit == x = 0\nNext == x' = x", 255],
    ["an unused decimal literal", "Half == 1.5\nInit == x = 0\nNext == x' = x", 151],
    ["a failure in the initial predicate", "Init == x = 1 \\div 0\nNext == x' = x", 75],
    [
      "an Assert in the initial predicate",
      'Init == x = 0 /\\ Assert(FALSE, "a")\nNext == x\' = x',
      75,
    ],
    ["an initial state that is not complete", "VARIABLE y\nInit == x = 0\nNext == x' = x", 255],
    ["a core failure in the next-state relation", "Init == x = 0\nNext == x' = <<1>>[2]", 75],
    [
      "a standard-module failure in the next-state relation",
      "Init == x = 0\nNext == x' = 1 \\div 0",
      255,
    ],
    ["a wrong argument to Len", "Init == x = 0\nNext == x' = Len(1)", 255],
    [
      "an Assert in the next-state relation",
      'Init == x = 0\nNext == Assert(x < 0, "a") /\\ x\' = x',
      14,
    ],
  ])("exits for %s", (_, definitions, code) => {
    expect(getExitCode(definitions)).toBe(code);
  });

  it("exits with 75 for a wrong argument to +", () => {
    const run = runOnEngine({
      source: getSource('Init == x = 0\nNext == x\' = x + "a"'),
      config: "INIT Init\nNEXT Next",
    });
    expect(run.exitCode).toBe(75);
    expect(getErrors(run.output)[0]).toBe(
      `${UNEXPECTED_EXCEPTION}Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.Naturals.Plus(tlc2.value.impl.IntValue,tlc2.value.impl.IntValue),\nbut it produced the following error:\nCannot cast tlc2.value.impl.StringValue to tlc2.value.impl.IntValue`,
    );
  });

  it("exits with 255 for a next-state relation that is not a boolean", () => {
    const run = runOnEngine({
      source: getSource("Init == x = 0\nNext == 3"),
      config: "INIT Init\nNEXT Next",
    });
    expect(run.exitCode).toBe(255);
    expect(getErrors(run.output)[0]).toBe(
      `${UNEXPECTED_EXCEPTION}The next state relation is not a boolean expression.\n3`,
    );
  });

  it("exits with 255 for a symmetry that isn't a set of permutations", () => {
    const config = "INIT Init\nNEXT Next\nSYMMETRY P";
    expect(getExitCode(`${STEP}\nP == 1`, config)).toBe(255);
    expect(getExitCode(STEP, config)).toBe(151);
  });

  it("exits with 255 for a box over a state predicate in the specification", async () => {
    const config = "SPECIFICATION Spec";
    expect(getExitCode(`${STEP}\nSpec == Init /\\ [][Next]_x /\\ [](x < 3)`, config)).toBe(255);
  });

  // TLC reports a recursion without end in the next-state relation, in an invariant of a successor
  // and in an assumption as the StackOverflowError it is, and exits with 255. As it computes the
  // initial states, the call stack it prints of its replay may keep a frame or not, so that
  // declines, as an invariant TLC computes as it starts does.
  it("exits with 255 for a stack overflow it reports", () => {
    const recursion = "RECURSIVE R(_)\nR(n) == R(n + 1)";
    const config = "INIT Init\nNEXT Next\nINVARIANT Inv";
    expect(getExitCode(`${recursion}\nInit == x = 0\nNext == x' = R(0)`)).toBe(255);
    expect(getExitCode(`${recursion}\n${STEP}\nInv == x = 0 \\/ R(0) = 0`, config)).toBe(255);
    expect(getExitCode(`${recursion}\nASSUME R(0) = 0\n${STEP}`)).toBe(255);
  });

  it("declines a stack overflow as TLC computes the initial states", () => {
    const recursion = "RECURSIVE R(_)\nR(n) == R(n + 1)";
    const config = "INIT Init\nNEXT Next\nINVARIANT Inv";
    expectRunDeclined(
      `${recursion}\nInit == x = R(0)\nNext == x' = x`,
      "INIT Init\nNEXT Next",
      "the engine stopped: recursion too deep: a recursion that overflows TLC's stack as it computes the initial states",
    );
    expectRunDeclined(
      `${recursion}\n${STEP}\nInv == R(0) = 0`,
      config,
      "the engine stopped: recursion too deep: a recursion that overflows TLC's stack as it computes the initial states",
    );
  });

  it("exits with the status of an error in the liveness check of an initial state", async () => {
    const config = "SPECIFICATION Spec\nPROPERTY Prop";
    const spec = `${STEP}\nSpec == Init /\\ [][Next]_x`;
    expect(getExitCode(`${spec}\nProp == <>~ENABLED (x' > x)`, config)).toBe(151);
    expect(getExitCode(`${spec}\nProp == <>(1 = {})`, config)).toBe(255);
  });

  it("exits with 75 when an invariant fails on an initial state and 76 afterwards", async () => {
    const config = "INIT Init\nNEXT Next\nINVARIANT Inv";
    expect(getExitCode(`${STEP}\nInv == 1 \\div 0 = x`, config)).toBe(75);
    expect(getExitCode(`${STEP}\nInv == x < 1 \\/ 1 \\div 0 = 1`, config)).toBe(76);
  });

  // TLC exits with the status of the failure's kind: 14 for an Assert, 255 otherwise.
  it.each([
    ["an Assert", 'Assert(x < 1, "a")', 14],
    ["a standard-module failure", "1 \\div (1 - x) = 1", 255],
  ])("exits with the status of %s in an action property", (_, action, status) => {
    expect(
      getExitCode(
        `${STEP}\nSpec == Init /\\ [][Next]_x\nProp == [][${action}]_x`,
        "SPECIFICATION Spec\nPROPERTY Prop",
      ),
    ).toBe(status);
  });

  it("declines a core failure in an action property", () => {
    expectRunDeclined(
      `${STEP}\nSpec == Init /\\ [][Next]_x\nProp == [][<<1>>[x + 1] = 1]_x`,
      "SPECIFICATION Spec\nPROPERTY Prop",
      "the engine stopped: applied a function outside its domain: evaluating the failure again: a failure TLC reports as a FingerprintException",
    );
  });

  it("exits with 255 when a liveness property fails to evaluate", async () => {
    const definitions = `${STEP}\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\nProp == <>(1 \\div 0 = x)`;
    expect(getExitCode(definitions, "SPECIFICATION Spec\nPROPERTY Prop")).toBe(255);
  });

  it("exits with 255 for a temporal quantifier over variables in the specification", () => {
    const run = runOnEngine({
      source: getSource(`${STEP}\nSpec == Init /\\ [][Next]_x /\\ \\EE y : y = x`),
      config: "SPECIFICATION Spec",
    });
    expect(run.exitCode).toBe(255);
    expect(getErrors(run.output)).toEqual([
      "TLC does not support temporal existential, nor universal, quantification over state variables.",
    ]);
  });

  it("exits with 77 for a property that is a tautology and 76 for an invariant with a prime", async () => {
    const definitions = `${STEP}\nSpec == Init /\\ [][Next]_x\nProp == <>[]TRUE => TRUE\nInv == x' = x`;
    expect(getExitCode(definitions, "SPECIFICATION Spec\nPROPERTY Prop")).toBe(77);
    expect(getExitCode(definitions, "SPECIFICATION Spec\nINVARIANT Inv")).toBe(76);
  });

  it("exits with 255 for a formula too large in disjunctive normal form, which check throws", async () => {
    const definitions = `Init == x = FALSE\nNext == x' \\in BOOLEAN\nSpec == Init /\\ [][Next]_x /\\ \\A i \\in 1..6 : \\A j \\in 1..6 : SF_x(Next)\nProp == <>[](x \\in BOOLEAN)`;
    const config = "SPECIFICATION Spec\nPROPERTY Prop";
    await expect(
      check({
        source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\n${definitions}\n====`,
        config,
      }),
    ).rejects.toThrow(
      new TlaEvaluationError(
        "TLC cannot handle the temporal formula because it exceeds the maximum supported size in disjunctive normal form.",
      ),
    );
    expect(getExitCode(definitions, config)).toBe(255);
  });

  it("exits with 75 when the configuration has no next-state relation", async () => {
    expect(getExitCode("Init == x = 0", "INIT Init")).toBe(75);
  });
});

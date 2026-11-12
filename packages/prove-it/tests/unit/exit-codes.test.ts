import { describe, expect, it } from "bun:test";

import { expectDeclined, runOnEngine, runTlcNatively } from "../native-check";

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

  it("declines a wrong argument to +", () => {
    expectRunDeclined(
      'Init == x = 0\nNext == x\' = x + "a"',
      "INIT Init\nNEXT Next",
      "the engine stopped: expected an integer: evaluating the failure again: expected an integer, not a string",
    );
  });

  it("declines a next-state relation that is not a boolean", () => {
    expectRunDeclined(
      "Init == x = 0\nNext == 3",
      "INIT Init\nNEXT Next",
      "the engine stopped: a guard that isn't a boolean: evaluating the failure again: a next-state relation the IR holds no actions of",
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

  it("declines a stack overflow in each phase", () => {
    const recursion = "RECURSIVE R(_)\nR(n) == R(n + 1)";
    const config = "INIT Init\nNEXT Next\nINVARIANT Inv";
    const step = "INIT Init\nNEXT Next";
    const overflow = "the engine stopped: recursion too deep";
    expectRunDeclined(`${recursion}\nInit == x = R(0)\nNext == x' = x`, step, overflow);
    expectRunDeclined(`${recursion}\nInit == x = 0\nNext == x' = R(0)`, step, overflow);
    expectRunDeclined(
      `${recursion}\n${STEP}\nInv == R(0) = 0`,
      config,
      "the engine declined: recursion too deep",
    );
    expectRunDeclined(`${recursion}\n${STEP}\nInv == x = 0 \\/ R(0) = 0`, config, overflow);
    expectRunDeclined(
      `${recursion}\nASSUME R(0) = 0\n${STEP}`,
      step,
      "an assumption that fails to evaluate: evaluating the assumption again: recursion too deep",
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

  it.each([
    ["an Assert", 'Assert(x < 1, "a")'],
    ["a standard-module failure", "1 \\div (1 - x) = 1"],
    ["a core failure", "<<1>>[x + 1] = 1"],
  ])("declines %s in an action property", (_, action) => {
    expectRunDeclined(
      `${STEP}\nSpec == Init /\\ [][Next]_x\nProp == [][${action}]_x`,
      "SPECIFICATION Spec\nPROPERTY Prop",
      "the engine stopped: a constraint, a VIEW or an action property that fails on a successor",
    );
  });

  it("exits with 255 when a liveness property fails to evaluate", async () => {
    const definitions = `${STEP}\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\nProp == <>(1 \\div 0 = x)`;
    expect(getExitCode(definitions, "SPECIFICATION Spec\nPROPERTY Prop")).toBe(255);
  });

  it("declines a temporal quantifier over variables in the specification", () => {
    expectRunDeclined(
      `${STEP}\nSpec == Init /\\ [][Next]_x /\\ \\EE y : y = x`,
      "SPECIFICATION Spec",
      "temporal quantification in the specification",
    );
  });

  it("exits with 77 for a property that is a tautology and 76 for an invariant with a prime", async () => {
    const definitions = `${STEP}\nSpec == Init /\\ [][Next]_x\nProp == <>[]TRUE => TRUE\nInv == x' = x`;
    expect(getExitCode(definitions, "SPECIFICATION Spec\nPROPERTY Prop")).toBe(77);
    expect(getExitCode(definitions, "SPECIFICATION Spec\nINVARIANT Inv")).toBe(76);
  });

  it("exits with 255 for a formula too large in disjunctive normal form, which check declines", async () => {
    const definitions = `Init == x = FALSE\nNext == x' \\in BOOLEAN\nSpec == Init /\\ [][Next]_x /\\ \\A i \\in 1..6 : \\A j \\in 1..6 : SF_x(Next)\nProp == <>[](x \\in BOOLEAN)`;
    const config = "SPECIFICATION Spec\nPROPERTY Prop";
    await expectDeclined(
      {
        source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\n${definitions}\n====`,
        config,
      },
      "the engine stopped before it searched (exit 255)",
    );
    expect(getExitCode(definitions, config)).toBe(255);
  });

  it("exits with 75 when the configuration has no next-state relation", async () => {
    expect(getExitCode("Init == x = 0", "INIT Init")).toBe(75);
  });
});

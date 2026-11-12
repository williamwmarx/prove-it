import { describe, expect, it } from "bun:test";

import { TlaError } from "../../src";
import { getErrorExitCode } from "../../src/errors";
import { checkParsed } from "../../src/parallel";
import { runOnEngine } from "../native-check";

const STEP = "Init == x = 0\nNext == x < 2 /\\ x' = x + 1";

const getSource = (definitions: string) =>
  `---- MODULE M ----\nEXTENDS Naturals, Sequences, TLC\nVARIABLE x\n${definitions}\n====`;

// The CLI's exit code on the engine, or where it declines for `declinedFor`, on the TypeScript check.
const getExitCode = (definitions: string, config = "INIT Init\nNEXT Next", declinedFor?: string) =>
  runOnEngine({ source: getSource(definitions), config }, declinedFor).exitCode;

const getFailureExitCode = async (definitions: string, config = "INIT Init\nNEXT Next") => {
  try {
    const result = await checkParsed({
      source: getSource(definitions),
      config,
      onPrint: () => {},
    });
    return result.failure?.exitCode;
  } catch (error) {
    if (error instanceof TlaError) return getErrorExitCode(error);
    throw error;
  }
};

describe("CLI exit codes match TLC", () => {
  it.each<[string, string, number, string | undefined]>([
    ["a parse error", "Init == x = = 0\nNext == x' = x", 150, undefined],
    ["an unresolved symbol", "Init == x = y\nNext == x' = x", 150, undefined],
    ["a constant without a value", "CONSTANT C\nInit == x = 0\nNext == x' = x", 151, undefined],
    ["a literal too big for TLC", "Init == x = 3000000000\nNext == x' = x", 255, undefined],
    [
      "an unused literal too big for TLC",
      "Big == 3000000000\nInit == x = 0\nNext == x' = x",
      255,
      undefined,
    ],
    ["an unused decimal literal", "Half == 1.5\nInit == x = 0\nNext == x' = x", 151, undefined],
    ["a failure in the initial predicate", "Init == x = 1 \\div 0\nNext == x' = x", 75, undefined],
    [
      "an Assert in the initial predicate",
      'Init == x = 0 /\\ Assert(FALSE, "a")\nNext == x\' = x',
      75,
      undefined,
    ],
    [
      "an initial state that is not complete",
      "VARIABLE y\nInit == x = 0\nNext == x' = x",
      255,
      undefined,
    ],
    [
      "a core failure in the next-state relation",
      "Init == x = 0\nNext == x' = <<1>>[2]",
      75,
      undefined,
    ],
    [
      "a standard-module failure in the next-state relation",
      "Init == x = 0\nNext == x' = 1 \\div 0",
      255,
      undefined,
    ],
    [
      "a wrong argument to +",
      'Init == x = 0\nNext == x\' = x + "a"',
      75,
      "the engine stopped: expected an integer: evaluating the failure again: expected an integer, not a string",
    ],
    ["a wrong argument to Len", "Init == x = 0\nNext == x' = Len(1)", 255, undefined],
    [
      "an Assert in the next-state relation",
      'Init == x = 0\nNext == Assert(x < 0, "a") /\\ x\' = x',
      14,
      undefined,
    ],
  ])("exits for %s", (_, definitions, code, declinedFor) => {
    expect(getExitCode(definitions, undefined, declinedFor)).toBe(code);
  });

  // TLC fails before it computes the initial states, which the TypeScript check, that the engine
  // leaves this to, computes first.
  it("exits for a next-state relation that is not a boolean", async () => {
    expect(await getFailureExitCode("Init == x = 0\nNext == 3")).toBe(255);
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

  it("exits like TLC on a stack overflow in each phase", async () => {
    const recursion = "RECURSIVE R(_)\nR(n) == R(n + 1)";
    const config = "INIT Init\nNEXT Next\nINVARIANT Inv";
    const step = "INIT Init\nNEXT Next";
    const overflow = "the engine stopped: recursion too deep";
    expect(getExitCode(`${recursion}\nInit == x = R(0)\nNext == x' = x`, step, overflow)).toBe(75);
    expect(getExitCode(`${recursion}\nInit == x = 0\nNext == x' = R(0)`, step, overflow)).toBe(255);
    expect(
      getExitCode(
        `${recursion}\n${STEP}\nInv == R(0) = 0`,
        config,
        "the engine declined: recursion too deep",
      ),
    ).toBe(75);
    expect(getExitCode(`${recursion}\n${STEP}\nInv == x = 0 \\/ R(0) = 0`, config, overflow)).toBe(
      255,
    );
    expect(
      getExitCode(
        `${recursion}\nASSUME R(0) = 0\n${STEP}`,
        step,
        "an assumption that fails to evaluate: evaluating the assumption again: recursion too deep",
      ),
    ).toBe(255);
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
    ["an Assert", 'Assert(x < 1, "a")', 14],
    ["a standard-module failure", "1 \\div (1 - x) = 1", 255],
    ["a core failure", "<<1>>[x + 1] = 1", 75],
  ])("exits for %s in an action property", (_, action, code) => {
    const definitions = `${STEP}\nSpec == Init /\\ [][Next]_x\nProp == [][${action}]_x`;
    expect(
      getExitCode(
        definitions,
        "SPECIFICATION Spec\nPROPERTY Prop",
        "the engine stopped: a constraint, a VIEW or an action property that fails on a successor",
      ),
    ).toBe(code);
  });

  it("exits with 255 when a liveness property fails to evaluate", async () => {
    const definitions = `${STEP}\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\nProp == <>(1 \\div 0 = x)`;
    expect(getExitCode(definitions, "SPECIFICATION Spec\nPROPERTY Prop")).toBe(255);
  });

  it("exits with 255 for a temporal quantifier over variables in the specification", async () => {
    const definitions = `${STEP}\nSpec == Init /\\ [][Next]_x /\\ \\EE y : y = x`;
    expect(
      getExitCode(
        definitions,
        "SPECIFICATION Spec",
        "temporal quantification in the specification",
      ),
    ).toBe(255);
  });

  it("exits with 77 for a property that is a tautology and 76 for an invariant with a prime", async () => {
    const definitions = `${STEP}\nSpec == Init /\\ [][Next]_x\nProp == <>[]TRUE => TRUE\nInv == x' = x`;
    expect(getExitCode(definitions, "SPECIFICATION Spec\nPROPERTY Prop")).toBe(77);
    expect(getExitCode(definitions, "SPECIFICATION Spec\nINVARIANT Inv")).toBe(76);
  });

  it("rejects a formula too large in disjunctive normal form as TLC does", async () => {
    const definitions = `Init == x = FALSE\nNext == x' \\in BOOLEAN\nSpec == Init /\\ [][Next]_x /\\ \\A i \\in 1..6 : \\A j \\in 1..6 : SF_x(Next)\nProp == <>[](x \\in BOOLEAN)`;
    const config = "SPECIFICATION Spec\nPROPERTY Prop";
    await expect(
      checkParsed({
        source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\n${definitions}\n====`,
        config,
      }),
    ).rejects.toThrow(
      "TLC cannot handle the temporal formula because it exceeds the maximum supported size in disjunctive normal form.",
    );
    expect(getExitCode(definitions, config)).toBe(255);
  });

  it("exits with 75 when the configuration has no next-state relation", async () => {
    expect(getExitCode("Init == x = 0", "INIT Init")).toBe(75);
  });
});

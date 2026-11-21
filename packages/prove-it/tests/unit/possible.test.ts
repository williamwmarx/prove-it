import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { TlaConfigError } from "../../src";
import { checkOnEngine, expectDeclined } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/possible");

const getModule = (body: string, config: string) => ({
  source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 3\n${body}\n====`,
  config: `INIT Init\nNEXT Next\n${config}`,
});

const getPostconditionModule = (kind: string, body: string) => ({
  source: `---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 5 /\\ x' = x + 1\nNever == TLCGet("level") < 0\n${body}\nSpec == Init /\\ [][${body.includes("Step") ? "Step" : "Next"}]_x\n====`,
  config: `SPECIFICATION Spec\nPOSTCONDITION Never\n${kind}`,
});

// TLC's report of the first _POSSIBLE predicate the search didn't witness, after it prints the
// record of how often it witnessed each.
const getUnwitnessed = (name: string, location: string) =>
  `The _POSSIBLE predicate ${name} at ${location} was never witnessed.\nOthers may be unwitnessed too; only witnessed predicates appear with a\nnon-zero count in the record printed above.\nSee https://explain.tlapl.us/possible-conditions for additional details.`;

const checkPrinting = async (options: { source: string; config: string }) => {
  const printed: string[] = [];
  const result = await checkOnEngine({ ...options, onPrint: (text) => printed.push(text) });
  return [
    result.status,
    result.violations[0]?.headline,
    [result.generatedStates, result.distinctStates],
    printed,
  ];
};

describe("_POSSIBLE matches TLC", () => {
  it.each<[string, [string, string], number[], string]>([
    [
      "PossibleFailStateTest",
      ["Unreachable", "line 12, col 16 to line 12, col 20"],
      [4, 3],
      "[Unreachable |-> 0]",
    ],
    [
      "PossibleFailActionTest",
      ["BigJump", "line 16, col 15 to line 16, col 24"],
      [4, 3],
      "[BigJump |-> 0]",
    ],
    [
      "PossibleFailMixedTest",
      ["Unreachable", "line 12, col 16 to line 12, col 20"],
      [4, 3],
      "[AtOne |-> 1, AllDone |-> 1, Unreachable |-> 0, WrapAround |-> 1, BigJump |-> 0]",
    ],
    ["PossibleFailNoTransTest", ["BigJump", "line 16, col 15 to line 16, col 24"], [1, 1], "<<>>"],
  ])(
    "reports the unwitnessed predicate of %s like TLC",
    async (configName, [name, location], counts, record) => {
      expect(
        await checkPrinting({
          source: readFileSync(join(DIRECTORY, "PossibleFail.tla"), "utf8"),
          config: `${readFileSync(join(DIRECTORY, `${configName}.cfg`), "utf8")}\nCHECK_DEADLOCK FALSE`,
        }),
      ).toEqual([
        "postcondition-violation",
        getUnwitnessed(name, `${location} of module PossibleFail`),
        counts,
        [record],
      ]);
    },
  );

  it("reports the first of the predicates no state witnesses in the order TLC lists them", async () => {
    expect(
      await checkPrinting(
        getModule("Zeta == x = 5\nAlpha == x = 6\nMid == x = 7", "_POSSIBLE Mid Alpha Zeta"),
      ),
    ).toEqual([
      "postcondition-violation",
      getUnwitnessed("Mid", "line 8, col 8 to line 8, col 12 of module M"),
      [4, 3],
      ["[Zeta |-> 0, Alpha |-> 0, Mid |-> 0]"],
    ]);
  });

  it("declines _POSSIBLE after a violation", async () => {
    await expectDeclined(
      getModule("Unreachable == x = 5\nInv == x < 2", "_POSSIBLE Unreachable\nINVARIANT Inv"),
      "the engine stopped: an invariant violated: a _POSSIBLE predicate",
    );
  });

  it("checks a POSTCONDITION after a violation without changing its status", async () => {
    const result = await checkOnEngine({
      source:
        '---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ x\' = x + 1\nNever == TLCGet("level") < 0\nInv == x < 1\n====',
      config: "INIT Init\nNEXT Next\nPOSTCONDITION Never\nINVARIANT Inv",
    });
    expect([result.status, result.violations.slice(1)]).toEqual([
      "invariant-violation",
      [
        {
          code: 2404,
          headline: "Postcondition Never at line 6, col 10 to line 6, col 28 of module M is false.",
          states: [],
        },
      ],
    ]);
  });

  // TLC checks it after the next-state relation fails, but not after an invariant or action
  // property does.
  it("doesn't check a POSTCONDITION after an invariant fails to evaluate", async () => {
    const result = await checkOnEngine(
      getPostconditionModule("INVARIANT P", "P == x < 2 \\/ 1 \\div 0 = 0"),
    );
    expect([result.status, result.violations.map((violation) => violation.code)]).toEqual([
      "error",
      [2111],
    ]);
  });

  it.each([
    [
      "PROPERTY P",
      "P == [][x' < 2 \\/ 1 \\div 0 = 0]_x",
      "the engine stopped: division by zero: a failure with a POSTCONDITION or -dumpTrace",
    ],
    [
      "INVARIANT P",
      "P == TRUE\nStep == IF x = 2 THEN 1 \\div 0 = 0 ELSE Next",
      "the engine stopped: division by zero: a failure with a POSTCONDITION or -dumpTrace",
    ],
  ])("declines a POSTCONDITION after %s fails to evaluate", async (kind, body, reason) => {
    await expectDeclined(getPostconditionModule(kind, body), reason);
  });

  it("declines a constant POSTCONDITION and skips it after a violation like TLC", async () => {
    await expectDeclined(
      getModule("Never == FALSE", "POSTCONDITION Never"),
      "the engine stopped before it searched (exit 255)",
    );
    const violated = await checkOnEngine(
      getModule("Never == FALSE\nInv == x < 2", "POSTCONDITION Never\nINVARIANT Inv"),
    );
    expect([violated.status, violated.violations.map((violation) => violation.code)]).toEqual([
      "invariant-violation",
      [2110],
    ]);
  });

  it("rejects predicates TLC cannot track", async () => {
    const body = "AtOne == x = 1\nConstant == TRUE\nArgument(n) == x = n\nTemporal == <>(x = 1)";
    const cases = [
      [
        "Undefined",
        "The possible Undefined specified in the configuration file\nis not defined in the specification.",
      ],
      [
        "x",
        "The possible x specified in the configuration file\nis not defined in the specification.",
      ],
      ["Constant", "The possible Constant cannot be a constant."],
      ["Argument", "TLC requires possible not to take any argument, but one was given: Argument"],
      [
        "Temporal",
        "The possible of Temporal is equal to a temporal formula; only state- and action-level predicates are supported",
      ],
    ];
    for (const [possible, message] of cases) {
      await expect(checkOnEngine(getModule(body, `_POSSIBLE ${possible}`))).rejects.toThrow(
        new TlaConfigError(message),
      );
    }
  });

  // TLC fails the semantic analysis of the module it generates for the predicates, which defines
  // one twice, with "Parsing or semantic analysis failed._POSSIBLE: semantic analysis of generated
  // module failed" (exit 150), after it has checked every name the configuration lists.
  it("declines a predicate listed twice", async () => {
    await expectDeclined(
      getModule("AtOne == x = 1", "_POSSIBLE AtOne AtOne"),
      "a _POSSIBLE predicate listed more than once",
    );
  });
});

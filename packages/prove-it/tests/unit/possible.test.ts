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

describe("_POSSIBLE matches TLC", () => {
  it.each([
    "PossibleFailStateTest",
    "PossibleFailActionTest",
    "PossibleFailMixedTest",
    "PossibleFailNoTransTest",
  ])("declines the unwitnessed predicate of %s", async (configName) => {
    await expectDeclined(
      {
        source: readFileSync(join(DIRECTORY, "PossibleFail.tla"), "utf8"),
        config: `${readFileSync(join(DIRECTORY, `${configName}.cfg`), "utf8")}\nCHECK_DEADLOCK FALSE`,
      },
      "a _POSSIBLE predicate the search didn't witness",
    );
  });

  it("declines predicates no state witnesses", async () => {
    await expectDeclined(
      getModule("Zeta == x = 5\nAlpha == x = 6\nMid == x = 7", "_POSSIBLE Mid Alpha Zeta"),
      "a _POSSIBLE predicate the search didn't witness",
    );
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
      "the engine stopped: a constraint, a VIEW or an action property that fails on a successor",
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
      ["AtOne AtOne", "_POSSIBLE lists AtOne more than once"],
    ];
    for (const [possible, message] of cases) {
      await expect(checkOnEngine(getModule(body, `_POSSIBLE ${possible}`))).rejects.toThrow(
        new TlaConfigError(message),
      );
    }
  });
});

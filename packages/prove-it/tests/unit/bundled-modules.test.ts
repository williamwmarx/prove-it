import { describe, expect, it } from "bun:test";

import { checkParsed } from "../../src/parallel";
import { checkOnEngine } from "../native-check";

const getOptions = (init: string) => ({
  source: `---- MODULE M ----\nEXTENDS RealTime, Toolbox\nVARIABLE x\nInit == x = 0 /\\ now = 0 /\\ ${init}\nNext == UNCHANGED <<x, now>>\n====`,
  config: "INIT Init\nNEXT Next",
});

const checkInit = (init: string, declinedFor?: string) =>
  checkOnEngine(getOptions(init), declinedFor);

describe("bundled modules match TLC's sources", () => {
  it("reports errors at the lines of TLC's Reals and RealTime modules", async () => {
    expect((await checkInit("Infinity = 0")).violations[0]?.headline).toContain(
      "line 17, col 13 to line 17, col 65 of module Reals",
    );
    // TLC reports the \EE inside RTBound as a temporal formula it can't evaluate here, where the
    // TypeScript check, which the engine leaves this to, reports an unbounded quantifier.
    expect((await checkParsed(getOptions("RTBound(x' = x, x, 0, 1)"))).failure?.message).toContain(
      "at line 20, column 6",
    );
  });

  it("evaluates the definitions of TLC's Reals and Toolbox modules", async () => {
    expect((await checkInit('Real = "Reals"')).status).toBe("success");
    expect(
      (
        await checkInit(
          "_TETrace = 0",
          "the engine stopped: enumerated an operation on infinite sets",
        )
      ).violations[0]?.headline,
    ).toContain("Attempted to enumerate S \\ T when S:\nNat\nis not enumerable.");
  });
});

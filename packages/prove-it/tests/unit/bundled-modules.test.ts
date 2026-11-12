import { describe, expect, it } from "bun:test";

import { checkOnEngine, expectDeclined } from "../native-check";

const getOptions = (init: string) => ({
  source: `---- MODULE M ----\nEXTENDS RealTime, Toolbox\nVARIABLE x\nInit == x = 0 /\\ now = 0 /\\ ${init}\nNext == UNCHANGED <<x, now>>\n====`,
  config: "INIT Init\nNEXT Next",
});

const checkInit = (init: string) => checkOnEngine(getOptions(init));

describe("bundled modules match TLC's sources", () => {
  it("reports errors at the lines of TLC's Reals module", async () => {
    expect((await checkInit("Infinity = 0")).violations[0]?.headline).toContain(
      "line 17, col 13 to line 17, col 65 of module Reals",
    );
  });

  it("evaluates the definitions of TLC's Reals module and declines Toolbox's _TETrace", async () => {
    expect((await checkInit('Real = "Reals"')).status).toBe("success");
    await expectDeclined(
      getOptions("_TETrace = 0"),
      "the engine stopped: enumerated an operation on infinite sets",
    );
  });
});

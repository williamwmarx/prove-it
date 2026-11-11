import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { checkParsed } from "../../src/parallel";
import { checkNatively } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/strings");

describe("STRING matches TLC's Strings class", () => {
  it("evaluates every assumption of the STRING fixture", async () => {
    const { result, declined } = await checkNatively({
      source: readFileSync(join(DIRECTORY, "StringSet.tla"), "utf8"),
      config: readFileSync(join(DIRECTORY, "StringSet.cfg"), "utf8"),
    });
    expect(declined).toBeUndefined();
    expect(result.status).toBe("success");
  });

  // The engine evaluates AssertError over a membership in {Nat} to FALSE, where TLC's is TRUE
  // (native/design/fallback.md, "Known wrong outputs"), so the TypeScript check answers it.
  it("compares Nat, Int, and Seq(S) like TLC's Java classes", async () => {
    const result = await checkParsed({
      source: readFileSync(join(DIRECTORY, "OverriddenSets.tla"), "utf8"),
      config: readFileSync(join(DIRECTORY, "OverriddenSets.cfg"), "utf8"),
    });
    expect(result.status).toBe("success");
  });

  it("fails to compare STRING with another set instead of answering FALSE", async () => {
    const { result, declined } = await checkNatively({
      source:
        "---- MODULE M ----\nVARIABLE x\nASSUME STRING # {}\nInit == x = 0\nNext == x' = x\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect(declined).toBeUndefined();
    expect(result.status).toBe("assumption-violation");
    expect(result.violations[0]?.headline).toBe(
      "Evaluating assumption line 3, col 8 to line 3, col 18 of module M failed.\nAttempted to compare overridden value STRING with non-overridden value:\n{}",
    );
  });
});

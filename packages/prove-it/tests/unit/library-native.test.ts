import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { check } from "../../src";

const FIXTURES = join(import.meta.dirname, "../fixtures");

const checkFixture = async (directory: string, name: string) => {
  const prints: string[] = [];
  const result = await check({
    source: readFileSync(join(FIXTURES, directory, `${name}.tla`), "utf8"),
    config: readFileSync(join(FIXTURES, directory, `${name}.cfg`), "utf8"),
    onPrint: (text) => prints.push(text),
  });
  return { status: result.status, prints };
};

// What the library's check answers natively, as the TypeScript check answered.
describe("check answers natively as the TypeScript check", () => {
  it("compares the elements of an enumerated set with the value as AssertError reads it", async () => {
    expect(await checkFixture("strings", "OverriddenSets")).toEqual({
      status: "success",
      prints: [],
    });
  });

  it("prints SANY's warnings before the check", async () => {
    expect(await checkFixture("cli-output", "Warned")).toEqual({
      status: "success",
      prints: [
        "*** Warnings: 1\n\nline 14, col 1 to line 14, col 16 of module Naturals\n\nMultiple declarations or definitions for symbol Nat.  \nThis duplicates the one at line 3, col 1 to line 3, col 10 of module Warned.\n\n\n",
      ],
    });
  });
});

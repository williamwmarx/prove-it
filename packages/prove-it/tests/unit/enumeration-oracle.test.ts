// The cases of tests/conformance/enumeration, which scripts/enumeration-oracle.ts --record froze
// with TLC's answers: the interpreter, asked as the TypeScript engine asks it, must list each
// set's elements in the order TLC does and fail where TLC fails. cargo test checks the native
// engine on the same cases.

import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { answerCase, CASE_STRINGS } from "../../scripts/enumeration-cases";
import { setStringOrder } from "../../src/values";

const DIRECTORY = join(import.meta.dirname, "../conformance/enumeration");

const toKind = (answer: string) => (answer.startsWith("!") ? "fails" : answer);

describe("the enumeration oracle's frozen cases", () => {
  it("enumerate in TLC's order", () => {
    setStringOrder(CASE_STRINGS);
    const cases = readFileSync(join(DIRECTORY, "requests.txt"), "utf8")
      .split("\n")
      .filter((line) => line.startsWith("value "))
      .map((line) => line.slice("value ".length));
    const expected = readFileSync(join(DIRECTORY, "answers.txt"), "utf8").trimEnd().split("\n");
    expect(cases.length * 2).toBe(expected.length);
    expect(cases.flatMap(answerCase).map(toKind)).toEqual(expected.map(toKind));
  });
});

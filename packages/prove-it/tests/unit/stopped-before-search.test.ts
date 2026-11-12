import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { check, type CheckOptions, type TlaSyntaxError } from "../../src";

interface RecordedCheck {
  test: string;
  options: Omit<CheckOptions, "loadModule"> & { modules?: Record<string, string> };
  error: Pick<TlaSyntaxError, "name" | "message" | "sany">;
  prints: string[];
}

// Each call of the library's check in these tests that stops before it searches, at a spec or a
// configuration TLC rejects, and specs chosen to tell SANY's report and the TypeScript check's
// errors apart, with what the TypeScript check printed and the error it threw, which the library
// prints and throws whichever check runs it.
const RECORDED: RecordedCheck[] = JSON.parse(
  readFileSync(join(import.meta.dirname, "../fixtures/stopped-before-search/checks.json"), "utf8"),
);

describe("a check that stops before it searches", () => {
  it.each(RECORDED.map((recorded, index) => [`${recorded.test} #${index}`, recorded] as const))(
    "throws the TypeScript check's error for %s",
    async (_, recorded) => {
      const modules = recorded.options.modules ?? {};
      const prints: string[] = [];
      const error = await check({
        ...recorded.options,
        loadModule: (name) => modules[name],
        onPrint: (text) => prints.push(text),
      }).then(
        () => undefined,
        (thrown: TlaSyntaxError) => thrown,
      );
      expect({
        name: error?.constructor.name,
        message: error?.message,
        sany: error?.sany,
      }).toEqual(recorded.error);
      expect(prints).toEqual(recorded.prints);
    },
  );
});

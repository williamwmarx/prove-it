import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { check, type CheckOptions, type TlaSyntaxError } from "../../src";
import { expectDeclined } from "../native-check";

interface RecordedCheck {
  test: string;
  options: Omit<CheckOptions, "loadModule"> & { modules?: Record<string, string> };
  error?: Pick<TlaSyntaxError, "name" | "message" | "sany">;
  prints?: string[];
  declined?: string;
}

// Each call of the library's check in these tests that stops before it searches, at a spec or a
// configuration TLC rejects, with what the check prints and the error it throws, or why the native
// check declines it.
const RECORDED: RecordedCheck[] = JSON.parse(
  readFileSync(join(import.meta.dirname, "../fixtures/stopped-before-search/checks.json"), "utf8"),
);

const getOptions = (recorded: RecordedCheck) => {
  const modules = recorded.options.modules ?? {};
  return { ...recorded.options, loadModule: (name: string) => modules[name] };
};

const getCases = (isDeclined: boolean) =>
  RECORDED.flatMap((recorded, index) =>
    (recorded.declined !== undefined) === isDeclined
      ? [[`${recorded.test} #${index}`, recorded] as const]
      : [],
  );

describe("a check that stops before it searches", () => {
  it.each(getCases(false))("throws the check's error for %s", async (_, recorded) => {
    const prints: string[] = [];
    const error = await check({
      ...getOptions(recorded),
      onPrint: (text) => prints.push(text),
    }).then(
      () => undefined,
      (thrown: TlaSyntaxError) => thrown,
    );
    expect({
      name: error?.constructor.name,
      message: error?.message,
      sany: error?.sany,
    }).toEqual<object | undefined>(recorded.error);
    expect(prints).toEqual<string[] | undefined>(recorded.prints);
  });

  it.each(getCases(true))("declines %s", async (_, recorded) => {
    await expectDeclined(getOptions(recorded), recorded.declined ?? "");
  });
});

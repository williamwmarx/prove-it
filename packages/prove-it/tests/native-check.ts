// The library's check, which reports whether the native engine answered: `check` takes the
// TypeScript path where the engine declines, and says so only under PROVE_IT_ENGINE=debug, so a
// test moved off the interpreter asserts on `declined` that the engine itself gave its result.

import { expect } from "bun:test";

import { check, type CheckOptions, type CheckResult } from "../src";
import { getNativeAddon } from "../src/engine/native";

export interface NativeCheck {
  result: CheckResult;
  // Why the engine left the check to the TypeScript path, if it did.
  declined: string | undefined;
}

const DECLINED = /^\[engine\] native: (?:check declined|check takes the TypeScript path): (.*)$/s;

// `check` reports a decline only through console.error under PROVE_IT_ENGINE=debug, both global,
// so the calls run one at a time and each sees only its own reports.
let queue: Promise<unknown> = Promise.resolve();

const checkCapturing = async (options: CheckOptions): Promise<NativeCheck> => {
  // Without the addon `check` takes the TypeScript path without a word.
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new Error(`no native engine: ${addon}`);
  const setting = process.env.PROVE_IT_ENGINE;
  const report = console.error;
  const reports: string[] = [];
  process.env.PROVE_IT_ENGINE = "debug";
  console.error = (...parts: unknown[]) => {
    const text = parts.map(String).join(" ");
    if (text.startsWith("[engine]")) reports.push(text);
    else report(...parts);
  };
  try {
    const result = await check(options);
    const declined = reports.map((text) => DECLINED.exec(text)?.[1]).find(Boolean);
    return { result, declined };
  } finally {
    console.error = report;
    if (setting === undefined) delete process.env.PROVE_IT_ENGINE;
    else process.env.PROVE_IT_ENGINE = setting;
  }
};

export const checkNatively = (options: CheckOptions): Promise<NativeCheck> => {
  const checked = queue.then(() => checkCapturing(options));
  queue = checked.catch(() => undefined);
  return checked;
};

// The TypeScript check's result, where a test asserts what only it reports so far:
// PROVE_IT_ENGINE=0 asks for it, and is global too, so the call waits its turn.
export const checkWithInterpreter = (options: CheckOptions): Promise<CheckResult> => {
  const checked = queue.then(async () => {
    const setting = process.env.PROVE_IT_ENGINE;
    process.env.PROVE_IT_ENGINE = "0";
    try {
      return await check(options);
    } finally {
      if (setting === undefined) delete process.env.PROVE_IT_ENGINE;
      else process.env.PROVE_IT_ENGINE = setting;
    }
  });
  queue = checked.catch(() => undefined);
  return checked;
};

// The engine's result, asserting that it gave it, or that it declined for `declinedFor`.
export const checkOnEngine = async (options: CheckOptions, declinedFor?: string) => {
  const { result, declined } = await checkNatively(options);
  expect(declined).toBe(declinedFor);
  return result;
};

// TLC's report of an assumption that fails to evaluate, whose text starts at column 8 of `line`.
export const getAssumptionFailure = (line: number, assumption: string, message: string) => {
  const lines = assumption.split("\n");
  const endLine = line + lines.length - 1;
  const endColumn = lines.length === 1 ? 7 + assumption.length : (lines.at(-1) ?? "").length;
  return `Evaluating assumption line ${line}, col 8 to line ${endLine}, col ${endColumn} of module M failed.\n${message}`;
};

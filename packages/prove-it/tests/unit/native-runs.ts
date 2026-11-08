// Runs of check() with the native engine, the TypeScript engine and the interpreter, for the tests
// of the native engine. They run where the addon was built, with PROVE_IT_ENGINE_ADDON naming it.

import { expect, spyOn } from "bun:test";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { getStateLogDifference, readLogLines } from "../../scripts/state-logs";
import { check, type CheckOptions } from "../../src";

export const ADDON = process.env.PROVE_IT_ENGINE_ADDON;
const SETTINGS = [
  "PROVE_IT_ENGINE",
  "PROVE_IT_ENGINE_BACKEND",
  "PROVE_IT_STATE_LOG",
  "PROVE_IT_STOP_AT",
  "PROVE_IT_FP_VERIFY",
  "PROVE_IT_LIVE_CHECK",
] as const;
const saved = Object.fromEntries(SETTINGS.map((name) => [name, process.env[name]]));

export const restoreSettings = () => {
  for (const name of SETTINGS) {
    if (saved[name] === undefined) delete process.env[name];
    else process.env[name] = saved[name];
  }
};

interface Run {
  result: Awaited<ReturnType<typeof check>>;
  lines: string[];
  progress: string[];
  printed: string[];
}

// Checks a model with the engine set as given, keeping the [engine] lines and what it reports.
export const run = async (
  options: Pick<CheckOptions, "source" | "config" | "isWarningEnabled" | "loadModule">,
  settings: Partial<Record<(typeof SETTINGS)[number], string>>,
): Promise<Run> => {
  for (const name of SETTINGS) delete process.env[name];
  Object.assign(process.env, settings);
  const lines: string[] = [];
  const progress: string[] = [];
  const printed: string[] = [];
  const spy = spyOn(console, "error").mockImplementation((message: unknown) => {
    if (typeof message === "string" && message.startsWith("[engine] ")) lines.push(message);
  });
  try {
    const result = await check({
      ...options,
      onPrint: (text) => printed.push(text),
      onProgress: (report) => {
        if (report.kind !== "progress") progress.push(JSON.stringify(report));
      },
    });
    return { result, lines, progress, printed };
  } finally {
    spy.mockRestore();
  }
};

export const toModule = (body: string[]) => `---- MODULE M ----\n${body.join("\n")}\n====`;

// The native engine's run and the interpreter's, which must reach the same result and report the
// same progress.
export const compareWithInterpreter = async (
  body: string[],
  config: string,
  settings: Partial<Record<(typeof SETTINGS)[number], string>> = {},
  isWarningEnabled = false,
) => {
  const options = { source: toModule(body), config, isWarningEnabled };
  const native = await run(options, {
    PROVE_IT_ENGINE: "debug",
    PROVE_IT_ENGINE_BACKEND: "rust",
    ...settings,
  });
  const interpreter = await run(options, { PROVE_IT_ENGINE: "0" });
  expect(native.result).toEqual(interpreter.result);
  expect(native.progress).toEqual(interpreter.progress);
  expect(native.printed).toEqual(interpreter.printed);
  return native.lines;
};

// The state logs of the TypeScript and the native engine, which must be identical.
export const compareStateLogs = async (
  body: string[],
  config: string,
  isWarningEnabled: boolean,
) => {
  const directory = mkdtempSync(join(tmpdir(), "prove-it-native-search-"));
  try {
    const options = { source: toModule(body), config, isWarningEnabled };
    const paths = ["ts", "rust"].map((backend) => join(directory, `${backend}.jsonl`));
    const lines: string[][] = [];
    for (const [index, backend] of ["ts", "rust"].entries()) {
      const logged = await run(options, {
        PROVE_IT_ENGINE: "debug",
        PROVE_IT_ENGINE_BACKEND: backend,
        PROVE_IT_STATE_LOG: paths[index],
      });
      lines.push(logged.lines);
    }
    const [typescript, native] = paths.map(readLogLines);
    expect(getStateLogDifference(typescript, native)).toBeUndefined();
    expect(native.length).toBeGreaterThan(1);
    return lines[1];
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
};

export const COMPLETE = /^\[engine\] native: complete: {2}\(\d+\.\d\d ms\)$/;
export const stopped = (reason: string) =>
  new RegExp(`^\\[engine\\] native: stopped: ${reason} \\(\\d+\\.\\d\\d ms\\)$`);

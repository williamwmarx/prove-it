// Runs of check() with the native engine and the interpreter, for the tests of the native engine.
// They run where the addon was built, with PROVE_IT_ENGINE_ADDON naming it.

import { expect, spyOn } from "bun:test";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { readLogLines } from "../../scripts/state-logs";
import { check, type CheckOptions } from "../../src";
import { createStateDecoder } from "../../src/transfer";
import { formatState } from "../../src/values";

export const ADDON = process.env.PROVE_IT_ENGINE_ADDON;
const SETTINGS = [
  "PROVE_IT_ENGINE",
  "PROVE_IT_STATE_LOG",
  "PROVE_IT_STOP_AT",
  "PROVE_IT_TEST_LIVE_CHECK_AT",
  "PROVE_IT_FP_VERIFY",
  "PROVE_IT_LIVE_CHECK",
  "PROVE_IT_WORKERS",
  "PROVE_IT_SHARED_LEVEL",
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
  options: Pick<
    CheckOptions,
    "source" | "config" | "isWarningEnabled" | "loadModule" | "livenessCheck" | "dump" | "writeFile"
  >,
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
    ...settings,
  });
  const interpreter = await run(options, { PROVE_IT_ENGINE: "0" });
  expect(native.result).toEqual(interpreter.result);
  expect(native.progress).toEqual(interpreter.progress);
  expect(native.printed).toEqual(interpreter.printed);
  return native.lines;
};

// The states the native engine's state log holds, in its order, which must be those the interpreter
// writes to TLC's -dump, in TLC's order: all of them, or the first of them where the engine
// stopped part way.
export const compareStateLogs = async (
  body: string[],
  config: string,
  isWarningEnabled: boolean,
) => {
  const directory = mkdtempSync(join(tmpdir(), "prove-it-native-search-"));
  try {
    const options = { source: toModule(body), config, isWarningEnabled };
    const path = join(directory, "native.jsonl");
    const native = await run(options, { PROVE_IT_ENGINE: "debug", PROVE_IT_STATE_LOG: path });
    const dumped: string[] = [];
    await run(
      {
        ...options,
        dump: { path: "states.dump" },
        writeFile: (_path, content) => dumped.push(content),
      },
      { PROVE_IT_ENGINE: "0" },
    );
    // A state's conjuncts, in no order: the dump orders the variables as TLC prints them.
    const getConjuncts = (text: string) =>
      text
        .trimEnd()
        .split(/\n(?=\/\\ )/)
        .sort();
    const expected = dumped
      .join("")
      .split(/^State \d+:\n/m)
      .slice(1)
      .map(getConjuncts);
    const lines = readLogLines(path).filter((line) => line !== "");
    const header: { variables: string[]; stopped: string | null } = JSON.parse(lines[0]);
    const decode = createStateDecoder(header.variables.length);
    const states = lines.slice(1).map((line) => {
      const record: [number, number, number, string, number[], string[]] = JSON.parse(line);
      const state = decode({ words: Int32Array.from(record[4]), strings: record[5], count: 1 })[0];
      return getConjuncts(
        formatState(
          Object.fromEntries(header.variables.map((name, index) => [name, state[index]])),
        ),
      );
    });
    expect(states).toEqual(header.stopped === null ? expected : expected.slice(0, states.length));
    expect(states.length).toBeGreaterThan(0);
    return native.lines;
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
};

export const COMPLETE = /^\[engine\] native: complete: {2}\(\d+\.\d\d ms\)$/;
export const stopped = (reason: string) =>
  new RegExp(`^\\[engine\\] native: stopped: ${reason} \\(\\d+\\.\\d\\d ms\\)$`);
export const declined = (reason: string) =>
  new RegExp(`^\\[engine\\] native: declined: ${reason} \\(\\d+\\.\\d\\d ms\\)$`);

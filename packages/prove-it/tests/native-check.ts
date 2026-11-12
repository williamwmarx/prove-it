// The library's check, which reports whether the native engine answered: `check` takes the
// TypeScript path where the engine declines, and says so only under PROVE_IT_ENGINE=debug, so a
// test moved off the interpreter asserts on `declined` that the engine itself gave its result.

import { expect } from "bun:test";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { getSteadyLines } from "../scripts/normalize-output";
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

const CLI = join(import.meta.dirname, "../src/cli.ts");

const TLC_VERSION_PROPERTY = "-Dtla-ts.tlc=";

// The JVM options that launch TLC 1.7.4 through the CLI.
export const TLC_174_LAUNCH = [`${TLC_VERSION_PROPERTY}1.7.4`, "tlc2.TLC"];

// The CLI's report of the native check of the sources, under PROVE_IT_ENGINE=debug: its exit, or
// why it left the check to the TypeScript path.
const SOURCES_REPORT = /^\[engine\] native: checkSources(?: declined: (.*)|: exit \d+ \(.*\))$/;

export interface TlcRunOptions {
  source: string;
  config: string;
  // The modules beside M.tla, by name.
  modules?: Record<string, string>;
  // TLC's options, and the JVM's before a tlc2.TLC that takes them.
  args?: string[];
}

export interface TlcRun {
  exitCode: number | null;
  // The lines the run printed, without the startup lines, with times and dates as _.
  output: string;
  // Why the engine left the check to the TypeScript path, if it did.
  declined: string | undefined;
}

// TLC's run of M.tla and M.cfg through the CLI, as `tlc2.TLC -noGenerateSpecTE -workers 1 M.tla`.
export const runTlcNatively = ({
  source,
  config,
  modules = {},
  args = [],
}: TlcRunOptions): TlcRun => {
  const directory = mkdtempSync(join(tmpdir(), "prove-it-tlc-"));
  try {
    writeFileSync(join(directory, "M.tla"), source);
    writeFileSync(join(directory, "M.cfg"), config);
    Object.entries(modules).forEach(([name, text]) =>
      writeFileSync(join(directory, `${name}.tla`), text),
    );
    // TLC 1.7.4 has no -noGenerateSpecTE.
    const isTlc174 = args.includes(`${TLC_VERSION_PROPERTY}1.7.4`);
    const result = spawnSync(
      "bun",
      [CLI, ...args, ...(isTlc174 ? [] : ["-noGenerateSpecTE"]), "-workers", "1", "M.tla"],
      {
        cwd: directory,
        env: { ...process.env, PROVE_IT_ENGINE: "debug" },
        encoding: "utf8",
      },
    );
    const reports = result.stderr.split("\n").filter((line) => SOURCES_REPORT.test(line));
    if (reports.length !== 1) {
      throw new Error(`the CLI didn't report one native check:\n${result.stderr}`);
    }
    const errorOutput = result.stderr.replace(/^\[engine\] .*\n/gm, "");
    return {
      exitCode: result.status,
      output: getSteadyLines(`${result.stdout}${errorOutput}`).join("\n"),
      declined: SOURCES_REPORT.exec(reports[0] ?? "")?.[1],
    };
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
};

// The CLI's run on the engine, asserting that it gave it, or that it declined for `declinedFor`.
export const runOnEngine = (options: TlcRunOptions, declinedFor?: string) => {
  const run = runTlcNatively(options);
  expect(run.declined).toBe(declinedFor);
  return run;
};

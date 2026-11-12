// The library's check, which is the native check, and what it throws where it declines a model.

import { expect } from "bun:test";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { getSteadyLines } from "../scripts/normalize-output";
import { check, type CheckOptions, TlaUnsupportedError } from "../src";

export const checkOnEngine = (options: CheckOptions) => check(options);

// Asserts that the native check declines the model for `reason`.
export const expectDeclined = async (options: CheckOptions, reason: string) => {
  const error = await check(options).then(
    () => undefined,
    (thrown: unknown) => thrown,
  );
  expect(error).toBeInstanceOf(TlaUnsupportedError);
  expect((error as Error).message).toBe(`not native yet: ${reason}`);
};

// TLC's report of an assumption that fails to evaluate, whose text starts at column 8 of `line`.
export const getAssumptionFailure = (line: number, assumption: string, message: string) => {
  const lines = assumption.split("\n");
  const endLine = line + lines.length - 1;
  const endColumn = lines.length === 1 ? 7 + assumption.length : (lines.at(-1) ?? "").length;
  return `Evaluating assumption line ${line}, col 8 to line ${endLine}, col ${endColumn} of module M failed.\n${message}`;
};

const CLI = join(import.meta.dirname, "../src/cli.ts");

// What the CLI prints where the native check declines the model.
const DECLINED = /^prove-it: not native yet: (.*)$/m;

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
  // Why the native check declined the model, if it did.
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
    const result = spawnSync("bun", [CLI, ...args, "-noGenerateSpecTE", "-workers", "1", "M.tla"], {
      cwd: directory,
      encoding: "utf8",
    });
    return {
      exitCode: result.status,
      output: getSteadyLines(`${result.stdout}${result.stderr}`).join("\n"),
      declined: DECLINED.exec(result.stderr)?.[1],
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

// The lines with which TLC reports the search, which end the message before them.
const SEARCH_LINE =
  /^(Error: |\d+ states generated, |The depth of the complete state graph search is |The average outdegree |Finished in |Starting\.\.\.|Computing initial states|Finished computing initial states|Model checking completed|Checking temporal properties|Implied-temporal checking|Progress\()/;

// Each error TLC printed, without its "Error: " and the empty lines after it.
export const getErrors = (output: string) => {
  const errors: string[][] = [];
  let current: string[] | undefined;
  for (const line of output.split("\n")) {
    if (line.startsWith("Error: ")) {
      current = [line.slice("Error: ".length)];
      errors.push(current);
    } else if (SEARCH_LINE.test(line)) current = undefined;
    else current?.push(line);
  }
  return errors.map((lines) => lines.join("\n").replace(/\n+$/, ""));
};

// The counts TLC printed as it ended the search.
export const getStatistics = (output: string) =>
  output
    .split("\n")
    .filter((line) =>
      /^(\d+ states generated, |The depth of the complete state graph search is |The average outdegree )/.test(
        line,
      ),
    );

export const findError = (output: string, start: string) =>
  getErrors(output).find((error) => error.startsWith(start));

// The positions TLC printed of the expressions it was evaluating when it failed.
export const getNestedExpressions = (output: string) =>
  findError(
    output,
    "The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n",
  )
    ?.split("\n")
    .filter((line) => /^\d+\. /.test(line));

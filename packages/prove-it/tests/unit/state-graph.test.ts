import { describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import type { CheckOptions } from "../../src";
import { checkOnEngine, expectDeclined } from "../native-check";

const FIXTURES = join(import.meta.dirname, "../fixtures");

// TLC 1.8.0 -dump output for each model, recorded with -fp 0 so that its fingerprints match, and
// with -seed 4 for RandomElementXandY.
const readTlcDump = (name: string) => readFileSync(join(FIXTURES, "state-graph", name), "utf8");

const getDumpOptions = (
  directory: string,
  name: string,
  dump: NonNullable<CheckOptions["dump"]>,
  written = new Map<string, string>(),
  options: Partial<CheckOptions> = {},
): CheckOptions => ({
  source: readFileSync(join(FIXTURES, directory, `${name}.tla`), "utf8"),
  config: readFileSync(join(FIXTURES, directory, `${name}.cfg`), "utf8"),
  loadModule: (module) => {
    const path = join(FIXTURES, directory, `${module}.tla`);
    return existsSync(path) ? readFileSync(path, "utf8") : undefined;
  },
  onPrint: () => {},
  writeFile: (path, content) => written.set(path, content),
  dump,
  ...options,
});

const dumpFixture = async (directory: string, name: string, path: string) => {
  const written = new Map<string, string>();
  const result = await checkOnEngine(getDumpOptions(directory, name, { path }, written));
  return { result, written };
};

describe("check dumps the state graph like TLC's -dump", () => {
  it("lists the reachable states without dot", async () => {
    const dump = await dumpFixture("counter", "Counter", "Counter.dump");
    expect(dump.written.get("Counter.dump")).toBe(readTlcDump("Counter.dump"));
  });

  it("lists the states it reached when an invariant fails", async () => {
    const dump = await dumpFixture("water-jugs", "WaterJugs", "WaterJugs.dump");
    expect(dump.result.status).toBe("invariant-violation");
    expect(dump.written.get("WaterJugs.dump")).toBe(readTlcDump("WaterJugs.dump"));
  });

  // The library has no directory to write a counterexample's trace exploration spec into, so it
  // never writes one over the dump.
  it("declines a dump with a recorded trace of a counterexample", async () => {
    await expectDeclined(
      getDumpOptions("water-jugs", "WaterJugs", { path: "WaterJugs.dump" }, undefined, {
        isTraceRecorded: true,
      }),
      "the engine stopped: an invariant violated: -dumpTrace into a directory that doesn't exist",
    );
  });

  it.each([
    ["a deadlocked counter", "counter", "Counter", {}],
    ["an invariant violation", "water-jugs", "WaterJugs", {}],
    ["action parameters", "mutex", "Mutex", {}],
    ["an alias", "state-graph", "Labels", {}],
    ["several workers", "mutex", "Mutex", { workers: 2 }],
    ["RandomElement", "randomization", "RandomElementXandY", { seed: 4n }],
    ["an invariant that fails to evaluate", "state-graph", "FailedInvariant", {}],
  ] as const)("declines the dot graph of %s", async (_, directory, name, options) => {
    await expectDeclined(
      getDumpOptions(directory, name, { path: `${name}.dot`, dot: true }, undefined, options),
      "-dump dot",
    );
  });
});

const runCli = (args: string[]) =>
  spawnSync("bun", [join(import.meta.dirname, "../../src/cli.ts"), "Counter.tla", ...args], {
    cwd: join(import.meta.dirname, "../fixtures/counter"),
    encoding: "utf8",
  });

// Why the CLI declines to dump the state graph of the counter like TLC's -dump with `args`.
const getDeclined = (args: string[]) => {
  const result = runCli(args);
  expect(result.status).toBe(1);
  return /^prove-it: not native yet: (.*)$/m.exec(result.stderr)?.[1];
};

describe("the CLI takes TLC's -dump flag", () => {
  it("adds the extension of the format to the file name, and declines dot", () => {
    const directory = mkdtempSync(join(tmpdir(), "prove-it-dump-"));
    expect(getDeclined(["-dump", "dot,actionlabels", join(directory, "Counter")])).toBe(
      "-dump dot",
    );
    runCli(["-dump", join(directory, "Counter")]);
    expect(readFileSync(join(directory, "Counter.dump"), "utf8")).toBe(
      readFileSync(join(import.meta.dirname, "../fixtures/state-graph/Counter.dump"), "utf8"),
    );
    rmSync(directory, { recursive: true, force: true });
  });

  it("declines -dump without a file name", () => {
    expect(getDeclined(["-dump"])).toBe("-dump");
  });
});

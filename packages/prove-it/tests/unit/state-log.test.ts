import { afterAll, describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { getStateLogDifference } from "../../scripts/state-logs";

// The workers run from the build, which bun run test makes first.
const CLI = join(import.meta.dirname, "../../dist/cli.js");

const directory = mkdtempSync(join(tmpdir(), "prove-it-state-log-"));

afterAll(() => rmSync(directory, { recursive: true, force: true }));

const logRun = (
  directoryPath: string,
  name: string,
  logName: string,
  environment: Record<string, string> = {},
) => {
  const path = join(directory, `${logName}.jsonl`);
  const result = spawnSync("bun", [CLI, `${name}.tla`], {
    cwd: directoryPath,
    encoding: "utf8",
    env: { ...process.env, PROVE_IT_ENGINE: "debug", PROVE_IT_STATE_LOG: path, ...environment },
  });
  return { stderr: result.stderr, log: readFileSync(path, "utf8") };
};

const FIXTURES = join(import.meta.dirname, "../fixtures");

describe("PROVE_IT_STATE_LOG", () => {
  it("writes the same states with 1 and 4 threads when the workers take levels", () => {
    const commit = join(import.meta.dirname, "../../benchmarks/commit");
    const serial = logRun(commit, "Commit", "serial", { PROVE_IT_WORKERS: "1" });
    const parallel = logRun(commit, "Commit", "parallel", { PROVE_IT_WORKERS: "4" });
    expect(serial.stderr).toContain("checked 282251 states on 1 thread ");
    expect(parallel.stderr).toMatch(/checked 282251 states on [2-4] threads /);
    expect(parallel.log).toBe(serial.log);
    expect(getStateLogDifference(serial.log, parallel.log)).toBeUndefined();
  }, 60_000);

  it("writes each state's parent and TLC's fingerprint, in TLC's order", () => {
    const lines = logRun(join(FIXTURES, "cli-output"), "Success", "success").log.split("\n");
    expect(JSON.parse(lines[0])).toEqual({
      version: 1,
      variables: ["x"],
      count: 6,
      stopped: null,
      expanding: 6,
    });
    const states = lines.slice(1, -1).map((line) => JSON.parse(line));
    expect(states.map((state) => state.slice(0, 3))).toEqual([
      [0, -1, -1],
      [1, -1, -1],
      [2, 0, -1],
      [3, 1, -1],
      [4, 2, -1],
      [5, 3, -1],
    ]);
    expect(states.every((state) => /^[\da-f]{16}$/.test(state[3]))).toBe(true);
    expect(new Set(states.map((state) => state[3])).size).toBe(6);
  });

  it("writes the states found before the engine stopped", () => {
    const run = logRun(join(FIXTURES, "water-jugs"), "WaterJugs", "violation");
    expect(run.stderr).toContain("handed over after");
    const header = JSON.parse(run.log.split("\n")[0]);
    expect(header.stopped).toBe("an invariant violated");
    expect(header.count).toBeGreaterThan(header.expanding);
  });

  it("names the first state two logs differ in, and prints it and its parent", () => {
    const log = logRun(join(FIXTURES, "water-jugs"), "WaterJugs", "original").log;
    const lines = log.split("\n");
    const record = JSON.parse(lines[4]);
    lines[4] = JSON.stringify([...record.slice(0, 3), "0000000000000000", ...record.slice(4)]);
    const difference = getStateLogDifference(log, lines.join("\n")) ?? "";
    expect(difference.split("\n")[0]).toBe("state 3:");
    expect(difference).toContain(`with fingerprint ${record[3]} from ${record[1]} (`);
    expect(difference).toContain("with fingerprint 0000000000000000 from");
    expect(difference).toMatch(/left reached \/\\ small = \d+ \/\\ big = \d+|left reached \w+ = /);
  });
});

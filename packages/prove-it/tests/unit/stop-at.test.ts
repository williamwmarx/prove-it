import { afterAll, describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { getTranscript } from "../../scripts/normalize-output";

const CLI = join(import.meta.dirname, "../../src/cli.ts");

const FIXTURES = join(import.meta.dirname, "../fixtures");

const directory = mkdtempSync(join(tmpdir(), "prove-it-stop-at-"));

afterAll(() => rmSync(directory, { recursive: true, force: true }));

const run = (
  fixture: string,
  name: string,
  args: string[],
  environment: Record<string, string> = {},
) => {
  const result = spawnSync("bun", [CLI, `${name}.tla`, ...args], {
    cwd: join(FIXTURES, fixture),
    encoding: "utf8",
    env: {
      ...process.env,
      PROVE_IT_ENGINE: "debug",
      ...environment,
    },
  });
  return {
    transcript: getTranscript(String(result.status), result.stdout, result.stderr),
    stderr: result.stderr,
  };
};

// How many states the engine expands before it ends on its own, as its state log says.
const getExpanded = (fixture: string, name: string) => {
  const path = join(directory, `${name}.jsonl`);
  run(fixture, name, [], { PROVE_IT_STATE_LOG: path });
  return JSON.parse(readFileSync(path, "utf8").split("\n")[0]).expanding;
};

// Specs that violate an invariant, deadlock, end in an error and succeed.
const MODELS = [
  ["water-jugs", "WaterJugs"],
  ["counter", "Counter"],
  ["cli-output", "FailedInvariant"],
  ["commit", "Commit"],
];

describe("PROVE_IT_STOP_AT", () => {
  it.each(MODELS)(
    "hands %s over before a state and prints what it prints without",
    (fixture, name) => {
      const expanded = getExpanded(fixture, name);
      expect(expanded).toBeGreaterThan(0);
      for (const args of [[], ["-tool"]]) {
        const expected = run(fixture, name, args).transcript;
        for (const stopAt of new Set([0, 1, Math.floor(expanded / 2), expanded - 1])) {
          const stopped = run(fixture, name, args, { PROVE_IT_STOP_AT: String(stopAt) });
          expect(stopped.stderr).toContain(": stopped where PROVE_IT_STOP_AT asked\n");
          expect(stopped.transcript).toBe(expected);
        }
      }
    },
    60_000,
  );

  it("leaves a search that ends before the state alone", () => {
    const result = run("counter", "Counter", [], { PROVE_IT_STOP_AT: "1000" });
    expect(result.stderr).not.toContain("PROVE_IT_STOP_AT");
  });
});

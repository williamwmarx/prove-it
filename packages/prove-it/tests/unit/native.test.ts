// With PROVE_IT_ENGINE_BACKEND=rust the native engine searches the model, and when the addon
// doesn't load the TypeScript engine checks it. The model is lowered to the engine IR only once the
// addon has loaded. Each check runs in a process of its own, since a process loads the addon once. The tests that load it run where the addon was built,
// with PROVE_IT_ENGINE_ADDON naming it, as the native job in verification.yml does.

import { describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { join } from "node:path";

const COMMIT = join(import.meta.dirname, "../fixtures/commit");
const SOURCE_CLI = join(import.meta.dirname, "../../src/cli.ts");
const BUILT_CLI = join(import.meta.dirname, "../../dist/cli.js");
const ADDON = process.env.PROVE_IT_ENGINE_ADDON;

const getEngineLines = (runtime: string, cli: string, env: Record<string, string | undefined>) => {
  const run = spawnSync(runtime, [cli, "Commit.cfg"], {
    cwd: COMMIT,
    encoding: "utf8",
    env: { ...process.env, PROVE_IT_ENGINE_ADDON: undefined, PROVE_IT_ENGINE: "debug", ...env },
  });
  expect(run.status).toBe(0);
  return run.stderr.split("\n").filter((line) => line.startsWith("[engine] "));
};

describe("the native engine", () => {
  it("is left alone with ts", () => {
    const lines = getEngineLines("bun", SOURCE_CLI, { PROVE_IT_ENGINE_BACKEND: "ts" });
    expect(lines).toEqual([expect.stringMatching(/^\[engine\] checked 251 states on 1 thread /)]);
  });

  it.each([undefined, "rust", "auto"])(
    "leaves the model to the TypeScript engine with %s when it can't load the addon",
    (backend) => {
      const missing = join(COMMIT, "missing.node");
      const lines = getEngineLines("bun", SOURCE_CLI, {
        PROVE_IT_ENGINE_BACKEND: backend,
        PROVE_IT_ENGINE_ADDON: missing,
      });
      expect(lines).toEqual([
        expect.stringContaining(`[engine] native: unavailable: can't load ${missing}: `),
        expect.stringMatching(/^\[engine\] checked 251 states on 1 thread /),
      ]);
    },
  );

  it.if(ADDON !== undefined).each([
    ["bun", SOURCE_CLI],
    ["node", BUILT_CLI],
  ])("decodes the IR and searches the model in %s", (runtime, cli) => {
    const lines = getEngineLines(runtime, cli, {
      PROVE_IT_ENGINE_BACKEND: "rust",
      PROVE_IT_ENGINE_ADDON: ADDON,
    });
    expect(lines).toEqual([
      expect.stringMatching(/^\[engine\] native: ir: \d+ bytes in \d+\.\d\d ms$/),
      expect.stringMatching(/^\[engine\] native: complete: {2}\(\d+\.\d\d ms\)$/),
      expect.stringMatching(/^\[engine\] checked 251 states on 1 thread /),
    ]);
  });
});

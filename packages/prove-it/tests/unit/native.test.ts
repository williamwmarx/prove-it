// The native engine searches the model, and where it can't be loaded check throws
// EngineUnavailableError, which names PROVE_IT_ENGINE=0, the interpreter. The model is lowered to
// the engine IR only once the engine has loaded. Each check runs in a process of its own, since a
// process loads the engine once. The tests that load it run where the addon was built, with
// PROVE_IT_ENGINE_ADDON naming it (tests/setup.ts), and those of the engine as WebAssembly where
// PROVE_IT_ENGINE_WASM names the module it built.

import { describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { join } from "node:path";

const COMMIT = join(import.meta.dirname, "../fixtures/commit");
const SOURCE_CLI = join(import.meta.dirname, "../../src/cli.ts");
const BUILT_CLI = join(import.meta.dirname, "../../dist/cli.js");
const ADDON = process.env.PROVE_IT_ENGINE_ADDON;
const WASM = process.env.PROVE_IT_ENGINE_WASM;
const MISSING = join(COMMIT, "missing.node");
// Each test spawns a CLI. The first spawn transpiles the sources, about 0.8 s on Windows runners
// against 0.2 s for the next, and a loaded runner can take several times that.
const SPAWN_LIMIT_MS = 30_000;

const checkCommit = (runtime: string, cli: string, env: Record<string, string | undefined>) =>
  spawnSync(runtime, [cli, "Commit.cfg"], {
    cwd: COMMIT,
    encoding: "utf8",
    env: {
      ...process.env,
      PROVE_IT_ENGINE_ADDON: undefined,
      PROVE_IT_ENGINE_WASM: undefined,
      PROVE_IT_ENGINE: "debug",
      ...env,
    },
  });

const getEngineLines = (runtime: string, cli: string, env: Record<string, string | undefined>) => {
  const run = checkCommit(runtime, cli, env);
  // The status with what the run wrote to stderr, so that a crash on any platform says why.
  expect({ status: run.status, stderr: run.stderr }).toMatchObject({ status: 0 });
  return run.stderr.split("\n").filter((line) => line.startsWith("[engine] "));
};

describe("the native engine", () => {
  it(
    "is left alone with PROVE_IT_ENGINE=0, which needs no engine",
    () => {
      const run = checkCommit("bun", SOURCE_CLI, {
        PROVE_IT_ENGINE: "0",
        PROVE_IT_ENGINE_ADDON: MISSING,
      });
      expect({ status: run.status, stderr: run.stderr }).toEqual({ status: 0, stderr: "" });
      expect(run.stdout).toContain("251 distinct states found");
    },
    SPAWN_LIMIT_MS,
  );

  it(
    "exits 255 where it can't load the engine, naming PROVE_IT_ENGINE=0",
    () => {
      const run = checkCommit("bun", SOURCE_CLI, { PROVE_IT_ENGINE_ADDON: MISSING });
      expect(run.status).toBe(255);
      expect(run.stderr).toContain(`The native engine is unavailable: can't load ${MISSING}: `);
      expect(run.stderr).toContain("or set PROVE_IT_ENGINE=0 to check with the interpreter.");
    },
    SPAWN_LIMIT_MS,
  );

  it(
    "rejects check with EngineUnavailableError where it can't load the engine",
    () => {
      const script = [
        'import { check, EngineUnavailableError } from "./src";',
        'const source = "---- MODULE M ----\\nVARIABLE x\\nInit == x = 0\\nNext == x\' = x\\n====";',
        'const error = await check({ source, config: "INIT Init\\nNEXT Next" }).catch((thrown) => thrown);',
        "console.log(error instanceof EngineUnavailableError);",
      ].join("\n");
      const run = spawnSync("bun", ["-e", script], {
        cwd: join(import.meta.dirname, "../.."),
        encoding: "utf8",
        env: { ...process.env, PROVE_IT_ENGINE_ADDON: MISSING, PROVE_IT_ENGINE_WASM: undefined },
      });
      expect({ stdout: run.stdout, stderr: run.stderr }).toEqual({ stdout: "true\n", stderr: "" });
    },
    SPAWN_LIMIT_MS,
  );

  it.if(ADDON !== undefined)(
    "searches natively by default on more than one thread",
    () => {
      const lines = getEngineLines("bun", SOURCE_CLI, {
        PROVE_IT_WORKERS: "2",
        PROVE_IT_SHARED_LEVEL: "1",
        PROVE_IT_ENGINE_ADDON: ADDON,
      });
      expect(lines).toContainEqual(expect.stringMatching(/^\[engine\] native: complete: /));
      expect(lines).toContainEqual(
        expect.stringMatching(/^\[engine\] checked 251 states on 2 threads /),
      );
    },
    SPAWN_LIMIT_MS,
  );

  it.if(ADDON !== undefined).each([
    ["bun", SOURCE_CLI],
    ["node", BUILT_CLI],
  ])(
    "decodes the IR and searches the model in %s",
    (runtime, cli) => {
      const lines = getEngineLines(runtime, cli, {
        PROVE_IT_ENGINE_ADDON: ADDON,
      });
      expect(lines).toEqual([
        expect.stringMatching(/^\[engine\] native: ir: \d+ bytes in \d+\.\d\d ms$/),
        expect.stringMatching(/^\[engine\] native: complete: {2}\(\d+\.\d\d ms\)$/),
        expect.stringMatching(/^\[engine\] checked 251 states on 1 thread /),
      ]);
    },
    SPAWN_LIMIT_MS,
  );

  // WebAssembly has no threads, so the search runs on one whatever PROVE_IT_WORKERS asks.
  it.if(WASM !== undefined).each([
    ["bun", SOURCE_CLI],
    ["node", BUILT_CLI],
  ])(
    "searches the model with the engine as WebAssembly in %s",
    (runtime, cli) => {
      const lines = getEngineLines(runtime, cli, {
        PROVE_IT_WORKERS: "2",
        PROVE_IT_SHARED_LEVEL: "1",
        PROVE_IT_ENGINE_WASM: WASM,
      });
      expect(lines).toContainEqual(expect.stringMatching(/^\[engine\] native: complete: /));
      expect(lines).toContainEqual(
        expect.stringMatching(/^\[engine\] checked 251 states on 1 thread /),
      );
    },
    SPAWN_LIMIT_MS,
  );
});

// With PROVE_IT_ENGINE_BACKEND=rust the native engine searches the model, and when the addon
// doesn't load the TypeScript engine checks it. The model is lowered to the engine IR only once the
// addon has loaded. Each check runs in a process of its own, since a process loads the addon once. The tests that load it run where the addon was built,
// with PROVE_IT_ENGINE_ADDON naming it, as the native job in verification.yml does, and those of
// the engine as WebAssembly where PROVE_IT_ENGINE_WASM names the module it built.

import { describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const COMMIT = join(import.meta.dirname, "../fixtures/commit");
const SOURCE_CLI = join(import.meta.dirname, "../../src/cli.ts");
const BUILT_CLI = join(import.meta.dirname, "../../dist/cli.js");
const ADDON = process.env.PROVE_IT_ENGINE_ADDON;
const WASM = process.env.PROVE_IT_ENGINE_WASM;
// Each test spawns a CLI. The first spawn transpiles the sources, about 0.8 s on Windows runners
// against 0.2 s for the next, and a loaded runner can take several times that.
const SPAWN_LIMIT_MS = 30_000;

const getEngineLines = (runtime: string, cli: string, env: Record<string, string | undefined>) => {
  const run = spawnSync(runtime, [cli, "Commit.cfg"], {
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
  // The status with what the run wrote to stderr, so that a crash on any platform says why.
  expect({ status: run.status, stderr: run.stderr }).toMatchObject({ status: 0 });
  return run.stderr.split("\n").filter((line) => line.startsWith("[engine] "));
};

describe("the native engine", () => {
  it(
    "is left alone with ts",
    () => {
      const lines = getEngineLines("bun", SOURCE_CLI, { PROVE_IT_ENGINE_BACKEND: "ts" });
      expect(lines).toEqual([expect.stringMatching(/^\[engine\] checked 251 states on 1 thread /)]);
    },
    SPAWN_LIMIT_MS,
  );

  it.if(ADDON !== undefined)(
    "searches natively by default on more than one thread",
    () => {
      const lines = getEngineLines("bun", SOURCE_CLI, {
        PROVE_IT_ENGINE_BACKEND: undefined,
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
    SPAWN_LIMIT_MS,
  );

  it.if(ADDON !== undefined).each([
    ["bun", SOURCE_CLI],
    ["node", BUILT_CLI],
  ])(
    "decodes the IR and searches the model in %s",
    (runtime, cli) => {
      const lines = getEngineLines(runtime, cli, {
        PROVE_IT_ENGINE_BACKEND: "rust",
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
        PROVE_IT_ENGINE_BACKEND: undefined,
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

  // As the addon does, the engine writes no state log where it can't create the file, and checks.
  it.if(WASM !== undefined)(
    "checks the model as WebAssembly where it can't write the state log",
    () => {
      const lines = getEngineLines("bun", SOURCE_CLI, {
        PROVE_IT_ENGINE_WASM: WASM,
        PROVE_IT_STATE_LOG: join(COMMIT, "missing", "states.jsonl"),
      });
      expect(lines).toContainEqual(expect.stringMatching(/^\[engine\] native: complete: /));
    },
    SPAWN_LIMIT_MS,
  );

  // A recursion as deep as this exhausts the stack the engine has as WebAssembly, and the
  // interpreter searches again from the start, after the search had printed.
  it.if(WASM !== undefined)(
    "prints once what it printed before WebAssembly ran out of stack",
    () => {
      const directory = mkdtempSync(join(tmpdir(), "prove-it-wasm-stack-"));
      try {
        writeFileSync(
          join(directory, "Deep.tla"),
          [
            "---- MODULE Deep ----",
            "EXTENDS Naturals, TLC",
            "VARIABLE x",
            "RECURSIVE Sum(_)",
            "Sum(k) == IF k = 0 THEN 0 ELSE 1 + Sum(k - 1)",
            'Init == PrintT("init") /\\ x = 0',
            "Next == x < 2 /\\ PrintT(x) /\\ x' = IF x = 1 THEN Sum(3000) - 2998 ELSE x + 1",
            "====",
          ].join("\n"),
        );
        writeFileSync(join(directory, "Deep.cfg"), "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n");
        const runDeep = (env: Record<string, string>) =>
          spawnSync("bun", [SOURCE_CLI, "Deep.cfg"], {
            cwd: directory,
            encoding: "utf8",
            env: { ...process.env, PROVE_IT_ENGINE_ADDON: undefined, ...env },
          });
        const printed = (stdout: string) =>
          stdout.split("\n").filter((line) => /^("init"|\d+)$/.test(line));
        const native = runDeep({ PROVE_IT_ENGINE: "debug", PROVE_IT_ENGINE_WASM: WASM ?? "" });
        expect(native.stderr).toContain("native: stopped: WebAssembly ran out of stack");
        const interpreter = runDeep({ PROVE_IT_ENGINE: "0" });
        expect(printed(native.stdout)).toEqual(['"init"', "0", "1"]);
        expect(printed(native.stdout)).toEqual(printed(interpreter.stdout));
      } finally {
        rmSync(directory, { recursive: true, force: true });
      }
    },
    SPAWN_LIMIT_MS,
  );
});

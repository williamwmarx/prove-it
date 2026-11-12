import { describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

// HourClock comes from tlaplus/Examples. Workers load from the build, as in a package.
const DIRECTORY = join(import.meta.dirname, "../fixtures/prove");
const DIST = join(import.meta.dirname, "../../dist/index.js");

const tlaTs: typeof import("../../src") = await import(DIST);

const loadModule = (name: string) => {
  const path = join(DIRECTORY, `${name}.tla`);
  return existsSync(path) ? readFileSync(path, "utf8") : undefined;
};

const SOURCE = loadModule("HourClock_proof") ?? "";

describe("prove with workers matches one thread", () => {
  it.each([2, 3])("proves HourClock with %i workers, reporting in order", async (workers) => {
    const sequential = await tlaTs.prove({ source: SOURCE, loadModule });
    const reported: number[] = [];
    const result = await tlaTs.prove({
      source: SOURCE,
      loadModule,
      workers,
      onObligation: (obligation) => reported.push(obligation.id),
    });
    expect(result).toEqual(sequential);
    expect(reported).toEqual(sequential.obligations.map((obligation) => obligation.id));
  });

  it("stops when its signal aborts", async () => {
    const controller = new AbortController();
    const proving = tlaTs.prove({
      source: SOURCE,
      loadModule,
      workers: 2,
      signal: controller.signal,
      onObligation: () => controller.abort(),
    });
    await expect(proving).rejects.toThrow(controller.signal.reason);
  });
});

// A browser has no process.dlopen, so prove needs the engine as WebAssembly the package ships, which
// it compiles before deciding: Zenon has no TypeScript decider to fall back to. The build has the
// engine once `platform-packages.ts build --target wasm32-unknown-unknown` writes it.
describe("prove without process.dlopen", () => {
  it.if(existsSync(join(DIST, "../prove-it-engine.wasm")))(
    "proves with Zenon through the engine as WebAssembly",
    () => {
      const script = [
        'Object.defineProperty(process, "dlopen", { value: undefined });',
        `const { prove } = await import(${JSON.stringify(DIST)});`,
        'const source = "---- MODULE M ----\\nEXTENDS TLAPS\\nTHEOREM \\\\A x : x = x BY Zenon\\n====\\n";',
        "const result = await prove({ source });",
        "console.log(JSON.stringify(result.obligations.map((o) => [o.status, o.prover ?? null])));",
      ].join("\n");
      const run = spawnSync("bun", ["-e", script], {
        encoding: "utf8",
        env: { ...process.env, PROVE_IT_ENGINE_ADDON: undefined },
      });
      expect(run.stderr).toBe("");
      expect(JSON.parse(run.stdout)).toEqual([
        ["proved", "zenon"],
        ["trivial", null],
      ]);
    },
  );
});

// As with the addon, the engine as WebAssembly reads two different lone surrogates as two strings.
describe("prove a lone surrogate without process.dlopen", () => {
  it.if(existsSync(join(DIST, "../prove-it-engine.wasm")))(
    "proves neither string = nor # the other",
    () => {
      const sources = ["=", "#"].map(
        (operator) =>
          `---- MODULE M ----\nEXTENDS TLAPS\nTHEOREM "\uD800" ${operator} "\uDC00" BY SMT\n====\n`,
      );
      const script = [
        'Object.defineProperty(process, "dlopen", { value: undefined });',
        `const { prove } = await import(${JSON.stringify(DIST)});`,
        `for (const source of ${JSON.stringify(sources)}) {`,
        "  const result = await prove({ source });",
        "  console.log(JSON.stringify(result.obligations.map((o) => [o.status, o.reason ?? null])));",
        "}",
      ].join("\n");
      const run = spawnSync("bun", ["-e", script], {
        encoding: "utf8",
        env: { ...process.env, PROVE_IT_ENGINE_ADDON: undefined },
      });
      expect(run.stderr).toBe("");
      const declined = [
        ["failed", "smt failed: smt declined: the text holds a lone surrogate"],
        ["trivial", null],
      ];
      expect(
        run.stdout
          .trim()
          .split("\n")
          .map((line) => JSON.parse(line)),
      ).toEqual([declined, declined]);
    },
  );
});

// A worker that can't decide fails the proof rather than leaving it waiting: here no engine loads,
// as the named addon is missing, and Zenon has no TypeScript decider, so the worker's decide throws
// EngineUnavailableError.
describe("prove with workers and no engine", () => {
  it("rejects", () => {
    const script = [
      `const { prove } = await import(${JSON.stringify(DIST)});`,
      'const source = "---- MODULE M ----\\nEXTENDS TLAPS\\nTHEOREM \\\\A x : x = x BY Zenon\\n====\\n";',
      "await prove({ source, workers: 2 }).then(",
      '  () => console.log("resolved"),',
      '  (error) => console.log("rejected", String(error?.message).includes("native engine is unavailable")),',
      ");",
    ].join("\n");
    const run = spawnSync("bun", ["-e", script], {
      encoding: "utf8",
      env: {
        ...process.env,
        PROVE_IT_ENGINE_ADDON: join(DIRECTORY, "missing.node"),
        PROVE_IT_ENGINE_WASM: undefined,
      },
    });
    expect(run.stdout.trim()).toBe("rejected true");
  });
});

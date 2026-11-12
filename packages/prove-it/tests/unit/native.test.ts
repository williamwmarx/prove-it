// The native engine checks the model, and where it can't be loaded check throws
// EngineUnavailableError and the CLI exits 255. Each check runs in a process of its own, since a
// process loads the engine once. The tests that load it run where the addon was built, with
// PROVE_IT_ENGINE_ADDON naming it (tests/setup.ts), and those of the engine as WebAssembly where
// PROVE_IT_ENGINE_WASM names the module it built.

import { describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { cpSync, existsSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

import { WebAssemblyStackError } from "../../src";

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
      ...env,
    },
  });

// The status with what the run wrote to stderr, so that a crash on any platform says why, and
// whether it found the model's states.
const expectChecked = (run: ReturnType<typeof checkCommit>) => {
  expect({ status: run.status, stderr: run.stderr }).toMatchObject({ status: 0 });
  expect(run.stdout).toContain("251 distinct states found");
};

describe("the native engine", () => {
  it.each([
    ["PROVE_IT_MEMO", "off"],
    ["PROVE_IT_EPOCH_CHECK", "1"],
    ["PROVE_IT_FP_VERIFY", "1"],
    ["PROVE_IT_LIVE_CHECK", "1"],
  ])(
    "checks the model with the engine's self-check %s",
    (name, value) => {
      expectChecked(
        checkCommit("bun", SOURCE_CLI, {
          PROVE_IT_ENGINE_ADDON: ADDON,
          PROVE_IT_ENGINE_WASM: WASM,
          [name]: value,
        }),
      );
    },
    SPAWN_LIMIT_MS,
  );

  it(
    "exits 255 where it can't load the engine named",
    () => {
      const run = checkCommit("bun", SOURCE_CLI, { PROVE_IT_ENGINE_ADDON: MISSING });
      expect(run.status).toBe(255);
      expect(run.stderr).toContain(`The native engine is unavailable: can't load ${MISSING}: `);
      expect(run.stderr).toContain(
        ". Install @atemp/prove-it with its optional dependencies on a supported platform.",
      );
    },
    SPAWN_LIMIT_MS,
  );

  // An install without the platform package, as on a platform none is built for or with optional
  // dependencies left out, checks with the engine as WebAssembly the package ships beside the CLI,
  // here a copy of dist/ that no package resolves from.
  it.if(existsSync(join(BUILT_CLI, "../prove-it-engine.wasm"))).each(["bun", "node"])(
    "checks in %s with the engine as WebAssembly where no addon is installed",
    (runtime) => {
      const directory = mkdtempSync(join(tmpdir(), "prove-it-no-addon-"));
      try {
        cpSync(join(BUILT_CLI, ".."), directory, { recursive: true });
        expectChecked(checkCommit(runtime, join(directory, "cli.js"), {}));
      } finally {
        rmSync(directory, { recursive: true, force: true });
      }
    },
    SPAWN_LIMIT_MS,
  );

  it(
    "rejects check with EngineUnavailableError where it can't load the engine",
    () => {
      // A script of its own, since Windows passes no argument with a line break to bun.
      const directory = mkdtempSync(join(tmpdir(), "prove-it-unavailable-"));
      const script = join(directory, "check.ts");
      try {
        writeFileSync(
          script,
          [
            `import { check, EngineUnavailableError } from ${JSON.stringify(pathToFileURL(join(import.meta.dirname, "../../src/index.ts")).href)};`,
            'const source = "---- MODULE M ----\\nVARIABLE x\\nInit == x = 0\\nNext == x\' = x\\n====";',
            'const error = await check({ source, config: "INIT Init\\nNEXT Next" }).catch((thrown) => thrown);',
            "console.log(error instanceof EngineUnavailableError);",
          ].join("\n"),
        );
        const run = spawnSync("bun", [script], {
          encoding: "utf8",
          env: { ...process.env, PROVE_IT_ENGINE_ADDON: MISSING, PROVE_IT_ENGINE_WASM: undefined },
        });
        expect({ stdout: run.stdout, stderr: run.stderr }).toEqual({
          stdout: "true\n",
          stderr: "",
        });
      } finally {
        rmSync(directory, { recursive: true, force: true });
      }
    },
    SPAWN_LIMIT_MS,
  );

  it.if(ADDON !== undefined)(
    "checks the model on more than one thread",
    () => {
      expectChecked(
        checkCommit("bun", SOURCE_CLI, {
          PROVE_IT_WORKERS: "2",
          PROVE_IT_SHARED_LEVEL: "1",
          PROVE_IT_ENGINE_ADDON: ADDON,
        }),
      );
    },
    SPAWN_LIMIT_MS,
  );

  it.if(ADDON !== undefined).each([
    ["bun", SOURCE_CLI],
    ["node", BUILT_CLI],
  ])(
    "checks the model with the addon in %s",
    (runtime, cli) => {
      expectChecked(checkCommit(runtime, cli, { PROVE_IT_ENGINE_ADDON: ADDON }));
    },
    SPAWN_LIMIT_MS,
  );

  // WebAssembly has no threads, so the search runs on one whatever PROVE_IT_WORKERS asks.
  it.if(WASM !== undefined).each([
    ["bun", SOURCE_CLI],
    ["node", BUILT_CLI],
  ])(
    "checks the model with the engine as WebAssembly in %s",
    (runtime, cli) => {
      expectChecked(
        checkCommit(runtime, cli, {
          PROVE_IT_WORKERS: "2",
          PROVE_IT_SHARED_LEVEL: "1",
          PROVE_IT_ENGINE_WASM: WASM,
        }),
      );
    },
    SPAWN_LIMIT_MS,
  );

  // As the addon does, the engine writes no state log where it can't create the file, and checks.
  it.if(WASM !== undefined)(
    "checks the model as WebAssembly where it can't write the state log",
    () => {
      expectChecked(
        checkCommit("bun", SOURCE_CLI, {
          PROVE_IT_ENGINE_WASM: WASM,
          PROVE_IT_STATE_LOG: join(COMMIT, "missing", "states.jsonl"),
        }),
      );
    },
    SPAWN_LIMIT_MS,
  );

  // The engine as WebAssembly stops a recursion at 1,000 calls, where the addon and the binary go on
  // to 20,000 (fallback.md, "WebAssembly's stack"): the library's check answers these models with
  // the addon, and rejects them with WebAssemblyStackError as WebAssembly, whether the engine stops
  // as it searches, as it starts on a constant invariant, or under -continue.
  it.if(WASM !== undefined && ADDON !== undefined)(
    "rejects with WebAssemblyStackError a recursion the addon checks",
    () => {
      const directory = mkdtempSync(join(tmpdir(), "prove-it-wasm-depth-"));
      const script = join(directory, "check.ts");
      try {
        writeFileSync(
          script,
          [
            `import { check, WebAssemblyStackError } from ${JSON.stringify(pathToFileURL(join(import.meta.dirname, "../../src/index.ts")).href)};`,
            'const header = "---- MODULE Deep ----\\nEXTENDS Naturals\\nRECURSIVE F(_)\\nF(n) == IF n = 0 THEN 0 ELSE 1 + F(n - 1)\\nVARIABLE x\\nInit == x = 0\\n";',
            "const models = [",
            '  [header + "Next == x < 1 /\\\\ x\' = F(1500) - 1499\\n====", "INIT Init\\nNEXT Next\\nCHECK_DEADLOCK FALSE", false],',
            '  [header + "Next == UNCHANGED x\\nInv == F(1500) = 1500\\n====", "INIT Init\\nNEXT Next\\nINVARIANT Inv", false],',
            '  [header + "Next == x < 1 /\\\\ x\' = F(1500) - 1499\\n====", "INIT Init\\nNEXT Next\\nCHECK_DEADLOCK FALSE", true],',
            "];",
            "const answers = [];",
            "for (const [source, config, isContinued] of models) {",
            "  answers.push(await check({ source, config, isContinued }).then(",
            "    (result) => [result.status, result.distinctStates],",
            "    (error) => [error instanceof WebAssemblyStackError, error.message],",
            "  ));",
            "}",
            "console.log(JSON.stringify(answers));",
          ].join("\n"),
        );
        const runDeep = (env: Record<string, string | undefined>) =>
          spawnSync("bun", [script], { encoding: "utf8", env: { ...process.env, ...env } }).stdout;
        expect(runDeep({ PROVE_IT_ENGINE_WASM: undefined, PROVE_IT_ENGINE_ADDON: ADDON })).toBe(
          `${JSON.stringify([
            ["success", 2],
            ["success", 1],
            ["success", 2],
          ])}\n`,
        );
        const rejected = [true, new WebAssemblyStackError().message];
        expect(runDeep({ PROVE_IT_ENGINE_WASM: WASM })).toBe(
          `${JSON.stringify([rejected, rejected, rejected])}\n`,
        );
      } finally {
        rmSync(directory, { recursive: true, force: true });
      }
    },
    SPAWN_LIMIT_MS,
  );

  // The engine as WebAssembly writes SANY's report on its module's stack, which holds the nesting
  // the front end writes before it declines, as the addon's report thread does.
  it.if(WASM !== undefined && ADDON !== undefined)(
    "writes SANY's report of a deeply nested module as WebAssembly as the addon does",
    () => {
      const directory = mkdtempSync(join(tmpdir(), "prove-it-wasm-report-"));
      const nest = (depth: number) =>
        Array.from({ length: depth }).reduce<string>(
          (body, _, index) => `LET a${index} == ${body} IN a${index}`,
          "TRUE",
        );
      const specs = {
        Lets99: nest(99),
        Lets110: nest(110),
        Parens1100: `${"(".repeat(1100)}TRUE${")".repeat(1100)}`,
      };
      try {
        const report = (name: string, env: Record<string, string | undefined>) => {
          const run = spawnSync("bun", [SOURCE_CLI, `${name}.cfg`], {
            cwd: directory,
            encoding: "utf8",
            env: { ...process.env, PROVE_IT_ENGINE_ADDON: undefined, ...env },
          });
          return {
            status: run.status,
            lines: `${run.stdout}${run.stderr}`
              .split("\n")
              .filter((line) => /not native yet|distinct states found|Error/.test(line)),
          };
        };
        Object.entries(specs).forEach(([name, body]) => {
          writeFileSync(
            join(directory, `${name}.tla`),
            `---- MODULE ${name} ----\nVARIABLE x\nB == ${body}\nInit == x = 0 /\\ B\nNext == x' = x\n====\n`,
          );
          writeFileSync(join(directory, `${name}.cfg`), "INIT Init\nNEXT Next\n");
        });
        const wasm = Object.keys(specs).map((name) => report(name, { PROVE_IT_ENGINE_WASM: WASM }));
        expect(wasm.map(({ status }) => status)).toEqual([0, 1, 0]);
        expect(wasm[1].lines).toEqual([
          "prove-it: not native yet: SANY's report of LETs nested 100 deep",
        ]);
        expect(wasm).toEqual(
          Object.keys(specs).map((name) => report(name, { PROVE_IT_ENGINE_ADDON: ADDON })),
        );
      } finally {
        rmSync(directory, { recursive: true, force: true });
      }
    },
    SPAWN_LIMIT_MS,
  );
});

import { describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { join } from "node:path";

import { classifyEngineLine, getEngineLine } from "../../scripts/engine-runs";

const SCRIPTS = join(import.meta.dirname, "../../scripts");

const FIXTURE = join(import.meta.dirname, "../fixtures/cli-output");

const checkModel = (environment: Record<string, string>) =>
  spawnSync(
    "bun",
    [join(SCRIPTS, "check-model.ts"), join(FIXTURE, "Success.tla"), join(FIXTURE, "Success.cfg")],
    { encoding: "utf8", env: { ...process.env, ...environment } },
  );

describe("the engine's backends in the conformance scripts", () => {
  it("checks a model with the TypeScript engine", () => {
    const result = checkModel({ PROVE_IT_ENGINE: "debug", PROVE_IT_ENGINE_BACKEND: "ts" });
    expect(JSON.parse(result.stdout)).toMatchObject({
      status: "success",
      generatedStates: 10,
      distinctStates: 6,
    });
    expect(classifyEngineLine(getEngineLine(result.stderr))).toEqual({
      engine: "completed",
      reason: undefined,
    });
  });

  it("refuses a backend that doesn't exist yet", () => {
    const result = checkModel({ PROVE_IT_ENGINE_BACKEND: "rust" });
    expect(result.status).toBe(2);
    expect(result.stderr).toBe("PROVE_IT_ENGINE_BACKEND takes one of ts, not rust\n");
  });

  it("reads what the engine did from its [engine] lines", () => {
    expect(
      getEngineLine("[engine] Next runs as closures\n[engine] skipped: -dump\n[engine] other\n"),
    ).toBe("skipped: -dump");
    expect(classifyEngineLine("handed over after 12 ms: deadlock")).toEqual({
      engine: "handed over",
      reason: "deadlock",
      engineMilliseconds: 12,
    });
    expect(classifyEngineLine(undefined)).toEqual({ engine: "not reached", reason: undefined });
  });
});

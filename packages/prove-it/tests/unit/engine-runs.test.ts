import { describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { join } from "node:path";

import { classifyEngineLine, getEngineLine, getNativeTier } from "../../scripts/engine-runs";

const SCRIPTS = join(import.meta.dirname, "../../scripts");

const FIXTURE = join(import.meta.dirname, "../fixtures/cli-output");

describe("the engine in the conformance scripts", () => {
  it("checks a model with the engine", () => {
    const result = spawnSync(
      "bun",
      [join(SCRIPTS, "check-model.ts"), join(FIXTURE, "Success.tla"), join(FIXTURE, "Success.cfg")],
      { encoding: "utf8" },
    );
    expect(JSON.parse(result.stdout)).toMatchObject({
      status: "success",
      generatedStates: 10,
      distinctStates: 6,
    });
  });

  it("reads what the engine did from its [engine] lines", () => {
    expect(
      getEngineLine("[engine] Next runs as closures\n[engine] skipped: -dump\n[engine] other\n"),
    ).toBe("skipped: -dump");
    expect(
      getEngineLine(
        "[engine] level of 255 states: 3 workers, coordinator generated 112 of 255\n[engine] checked 9 states on 4 threads in 1 ms with 7 values\n",
      ),
    ).toBe("checked 9 states on 4 threads in 1 ms with 7 values");
    expect(classifyEngineLine("handed over after 12 ms: deadlock")).toEqual({
      engine: "handed over",
      reason: "deadlock",
      engineMilliseconds: 12,
    });
    expect(classifyEngineLine(undefined)).toEqual({ engine: "not reached", reason: undefined });
  });

  it("reads what the native engine did apart from the engine's outcome", () => {
    const stderr = [
      "[engine] native: ir: 5384 bytes in 1.43 ms",
      "[engine] native: stopped: deadlock (4.13 ms)",
      "[engine] handed over after 6 ms: deadlock",
      "",
    ].join("\n");
    expect(getEngineLine(stderr)).toBe("handed over after 6 ms: deadlock");
    expect(getNativeTier(stderr)).toEqual({ tier: "stopped", reason: "deadlock" });
    expect(getNativeTier("[engine] native: complete:  (977.20 ms)\n")).toEqual({
      tier: "complete",
      reason: "",
    });
    expect(getNativeTier("[engine] checked 9 states on 1 thread in 1 ms with 7 values\n")).toBe(
      undefined,
    );
  });
});

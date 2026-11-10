import { afterEach, describe, expect, it } from "bun:test";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { getDigest } from "../../scripts/tlapm-digest";
import { decideSmt } from "../../src/prover/smt/solver/solver";
import type { Statistics } from "../../src/prover/verdict";

const TEXT = readFileSync(join(import.meta.dirname, "../fixtures/smt/Barriers-63.smt"), "utf8");

const directory = mkdtempSync(join(tmpdir(), "lp-trace-"));

const decide = () => {
  const statistics: Statistics = {};
  const verdict = decideSmt(TEXT, { timeLimitMs: Infinity, statistics });
  return { verdict, statistics };
};

afterEach(() => {
  delete process.env.PROVE_IT_LP_TRACE;
  rmSync(directory, { recursive: true, force: true });
});

describe("the lp trace", () => {
  it("records the theory's lp calls without changing the search", () => {
    const untraced = decide();
    process.env.PROVE_IT_LP_TRACE = directory;
    const traced = decide();
    expect(traced).toEqual(untraced);
    const lines = readFileSync(join(directory, `${getDigest(TEXT)}.lptrace`), "utf8")
      .split("\n")
      .filter((line) => line !== "")
      .map((line) => JSON.parse(line));
    expect(lines[0]).toEqual({ c: "lar#0", m: "new", a: [{ cb: "lar#0.new.0" }] });
    expect(lines.some((line) => line.c === "lar#0" && line.m === "findFeasibleSolution")).toBe(
      true,
    );
    expect(lines.some((line) => line.cb === "lar#0.new.0")).toBe(true);
    expect(
      lines.every(
        (line) =>
          (typeof line.c === "string" && typeof line.m === "string" && Array.isArray(line.a)) ||
          (typeof line.cb === "string" && Array.isArray(line.a)) ||
          (typeof line.f === "string" && typeof line.p === "string" && "r" in line) ||
          (typeof line.w === "string" && typeof line.p === "string"),
      ),
    ).toBe(true);
  });
});

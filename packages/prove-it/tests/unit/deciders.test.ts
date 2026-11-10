import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { decide } from "../../src/prover/deciders";

const TESTS_DIRECTORY = join(import.meta.dirname, "..");

const read = (path: string) => readFileSync(join(TESTS_DIRECTORY, path), "utf8");

// An input each backend proves, from tlapm's recordings.
const INPUTS = [
  ["smt", read("fixtures/smt/Allocator-37.smt")],
  ["zenon", read("fixtures/zenon/proved/AtomicBakeryWithoutSMT-116.znn")],
  ["isabelle", read("fixtures/isabelle/AllocatorImplementation_proof-33.thy")],
  ["ls4", read("conformance/ptl/equivalence-of-boxes.ls4")],
] as const;

const OPTIONS = { timeLimitMs: Infinity };

describe("the deciders' steps and statistics", () => {
  it.each(INPUTS)(
    "%s proves its input and reports the same statistics each time",
    (prover, text) => {
      const first = decide(prover, text, OPTIONS);
      const second = decide(prover, text, OPTIONS);
      expect(first.verdict).toBe("unsat");
      expect(first.statistics.steps).toBeGreaterThan(0);
      expect(second.statistics).toEqual(first.statistics);
    },
  );

  // A step limit stops a backend where its time limit would, so a search cut short is unknown.
  it.each(INPUTS)("%s gives up at a step limit", (prover, text) => {
    const decision = decide(prover, text, OPTIONS, 1);
    expect(decision.verdict).toBe("unknown");
  });

  // A limit as large as the steps the proof took changes nothing.
  it.each(INPUTS)("%s proves its input within the steps it took", (prover, text) => {
    const steps = Number(decide(prover, text, OPTIONS).statistics.steps);
    expect(decide(prover, text, OPTIONS, steps)).toMatchObject({
      verdict: "unsat",
      statistics: { steps },
    });
  });
});

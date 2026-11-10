import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { getNativeAddon } from "../../src/engine/native";
import { TlaProverError } from "../../src/errors";
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

// Z3 takes steps parsing up to a malformed term, so a step limit can stop it before the error, which
// is why prover-inputs.ts records an input that throws without a step limit.
describe("a malformed input", () => {
  const text = "(declare-const x Int)\n(assert (= (+ x 1) x))\n(assert (foo x))\n(check-sat)";

  it("throws without a step limit", () => {
    expect(() => decide("smt", text, OPTIONS)).toThrow(TlaProverError);
  });

  it("is unknown when the step limit stops it first", () => {
    expect(decide("smt", text, OPTIONS, 0)).toMatchObject({
      verdict: "unknown",
      statistics: { stop: "steps" },
    });
  });
});

// Until a backend's port lands, the native engine declines its inputs and TypeScript decides them.
describe("the Rust ports", () => {
  const getAddon = () => {
    const addon = getNativeAddon();
    if (typeof addon === "string") throw new Error(addon);
    return addon;
  };

  it.each(INPUTS)("%s declines while it isn't ported", (prover, text) => {
    expect(getAddon().decide(prover, text, 1000, undefined, undefined).kind).toBe("declined");
  });

  it("declines a prover without a backend", () => {
    expect(getAddon().decide("cvc4", "", 1000, 10, undefined)).toEqual({
      kind: "declined",
      reason: "the cvc4 backend",
    });
  });

  it.each(INPUTS)("%s falls back to TypeScript where its port declines", (prover, text) => {
    const setting = process.env.PROVE_IT_PROVER;
    process.env.PROVE_IT_PROVER = "rust";
    try {
      expect(decide(prover, text, OPTIONS)).toMatchObject({ verdict: "unsat" });
    } finally {
      if (setting === undefined) delete process.env.PROVE_IT_PROVER;
      else process.env.PROVE_IT_PROVER = setting;
    }
  });
});

import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { getNativeAddon } from "../../src/engine/native";
import { TlaProverError } from "../../src/errors";
import { decide } from "../../src/prover/deciders";
import type { Decision } from "../../src/prover/verdict";

const TESTS_DIRECTORY = join(import.meta.dirname, "..");

const read = (path: string) => readFileSync(join(TESTS_DIRECTORY, path), "utf8");

// An input each backend proves, from tlapm's recordings.
const INPUTS = [
  ["smt", read("fixtures/smt/Allocator-37.smt")],
  ["zenon", read("fixtures/zenon/proved/AtomicBakeryWithoutSMT-116.znn")],
  ["isabelle", read("fixtures/isabelle/AllocatorImplementation_proof-33.thy")],
  ["ls4", read("conformance/ptl/equivalence-of-boxes.ls4")],
] as const;

// What the TypeScript SMT decider answered on the SMT input with no limits, as smt and as z3, before
// it was deleted, as crates/prover/smt/tests/tables/decide.txt records it too.
const SMT_RECORDED: Decision = {
  verdict: "unsat",
  timeUsedMs: 0,
  statistics: { instances: 14, steps: 4626 },
};

// What the TypeScript deciders answered on their inputs with no limits, before they were deleted,
// as tests/fixtures/zenon/decisions.txt and prove-isabelle's testdata/decide.txt record Zenon's and
// Isabelle's too.
const RECORDED: Record<string, Decision> = {
  smt: SMT_RECORDED,
  z3: SMT_RECORDED,
  isabelle: { verdict: "unsat", timeUsedMs: 0, statistics: { steps: 840 } },
  ls4: { verdict: "unsat", timeUsedMs: 0, statistics: { steps: 5 } },
  zenon: {
    verdict: "unsat",
    timeUsedMs: 0,
    statistics: {
      steps: 1932,
      nodesSearched: 2246,
      maxBranchFormulas: 319,
      proofNodes: 183,
      formulasCreated: 13905,
      proof: "25254:004ede84",
    },
  },
};

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

// Z3 reports the malformed term, skips its assertion and answers the check-sat: Z3 5.3.3 prints
// "(error "line 3 column 14: unknown constant foo (Int) ")", then unsat, which tlapm counts as
// proved. It takes steps parsing up to the error, so a step limit can stop it first.
describe("a malformed input", () => {
  const text = "(declare-const x Int)\n(assert (= (+ x 1) x))\n(assert (foo x))\n(check-sat)";

  it("answers past the error as Z3 does", () => {
    expect(decide("smt", text, OPTIONS).verdict).toBe("unsat");
  });

  it("is unknown when the step limit stops it first", () => {
    expect(decide("smt", text, OPTIONS, 0)).toMatchObject({
      verdict: "unknown",
      statistics: { stop: "steps" },
    });
  });
});

// Each backend's TypeScript is deleted, and its Rust port decides as the TypeScript did.
describe("the Rust ports", () => {
  const getAddon = () => {
    const addon = getNativeAddon();
    if (typeof addon === "string") throw new Error(addon);
    return addon;
  };

  // Z3 is sent the SMT input.
  it.each([...INPUTS, ["z3", INPUTS[0][1]] as const])(
    "%s decides as its TypeScript did",
    (prover, text) => {
      expect(decide(prover, text, OPTIONS)).toMatchObject({
        verdict: RECORDED[prover].verdict,
        statistics: RECORDED[prover].statistics,
      });
    },
  );

  // tlapm counts a Zenon, an Isabelle or an LS4 that stops on its input as a failure.
  it.each([
    ["zenon", "$sig a"],
    ["isabelle", "theory \u{e9}"],
    ["ls4", "not ((always h00000) ->"],
  ])("fails on a malformed %s input", (prover, text) => {
    expect(() => decide(prover, text, OPTIONS)).toThrow(TlaProverError);
  });

  it("declines a prover without a backend", () => {
    expect(getAddon().decide("cvc4", "", 1000, 10, undefined)).toEqual({
      kind: "declined",
      reason: "the cvc4 backend",
    });
  });

  it("fails on a prover the engine declines", () => {
    expect(() => decide("cvc4", "", OPTIONS)).toThrow(TlaProverError);
  });

  // The native backends don't see the signal, so an aborted one keeps an input from them.
  it.each(INPUTS)("%s is unknown once its signal has aborted", (prover, text) => {
    const options = { timeLimitMs: Infinity, signal: AbortSignal.abort() };
    expect(decide(prover, text, options).verdict).toBe("unknown");
  });
});

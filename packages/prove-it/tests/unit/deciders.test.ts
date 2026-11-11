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

// What the TypeScript decider answered on the Zenon and PTL inputs with no limits, before it was
// deleted, as tests/fixtures/zenon/decisions.txt records Zenon's too.
const RECORDED: Record<string, Decision> = {
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
// Where it decides, it must answer as TypeScript does, until the TypeScript backend is deleted.
describe("the Rust ports", () => {
  const getAddon = () => {
    const addon = getNativeAddon();
    if (typeof addon === "string") throw new Error(addon);
    return addon;
  };

  // Runs a decision with PROVE_IT_PROVER set to the port given.
  const useProver = <Value>(setting: string, getValue: () => Value) => {
    const previous = process.env.PROVE_IT_PROVER;
    process.env.PROVE_IT_PROVER = setting;
    try {
      return getValue();
    } finally {
      if (previous === undefined) delete process.env.PROVE_IT_PROVER;
      else process.env.PROVE_IT_PROVER = previous;
    }
  };

  // A backend whose TypeScript is deleted decides as its TypeScript did, as it was recorded.
  it.each(INPUTS)("%s declines, or decides as TypeScript does", (prover, text) => {
    const native = getAddon().decide(prover, text, Infinity, undefined, undefined);
    if (native.kind === "declined") return;
    const typescript = RECORDED[prover] ?? useProver("ts", () => decide(prover, text, OPTIONS));
    expect(native).toEqual({
      kind: "decided",
      verdict: typescript.verdict,
      statistics: typescript.statistics,
    });
  });

  // Zenon's and PTL's TypeScript is deleted, so PROVE_IT_PROVER doesn't reach it.
  it.each([INPUTS[1], INPUTS[3]])(
    "decides %s in Rust whatever PROVE_IT_PROVER says",
    (prover, text) => {
      expect(useProver("ts", () => decide(prover, text, OPTIONS))).toMatchObject({
        verdict: "unsat",
        statistics: RECORDED[prover].statistics,
      });
    },
  );

  // tlapm counts a Zenon or an LS4 that stops on its input as a failure.
  it.each([
    ["zenon", "$sig a"],
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

  it.each(INPUTS)("%s falls back to TypeScript where its port declines", (prover, text) => {
    expect(useProver("rust", () => decide(prover, text, OPTIONS))).toMatchObject({
      verdict: "unsat",
    });
  });

  // The native backends don't see the signal, so an aborted one keeps an input from them.
  it.each(INPUTS)("%s is unknown once its signal has aborted", (prover, text) => {
    const options = { timeLimitMs: Infinity, signal: AbortSignal.abort() };
    expect(useProver("rust", () => decide(prover, text, options)).verdict).toBe("unknown");
  });
});

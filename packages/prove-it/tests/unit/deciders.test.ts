import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { getNativeAddon, type NativeDecision } from "../../src/engine/native";

const TESTS_DIRECTORY = join(import.meta.dirname, "..");

const read = (path: string) => readFileSync(join(TESTS_DIRECTORY, path), "utf8");

// An input each backend proves, from tlapm's recordings.
const INPUTS = [
  ["smt", read("fixtures/smt/Allocator-37.smt")],
  ["zenon", read("fixtures/zenon/proved/AtomicBakeryWithoutSMT-116.znn")],
  ["isabelle", read("fixtures/isabelle/AllocatorImplementation_proof-33.thy")],
  ["ls4", read("conformance/ptl/equivalence-of-boxes.ls4")],
] as const;

type Decided = Extract<NativeDecision, { kind: "decided" }>;

// What the TypeScript SMT decider answered on the SMT input with no limits, as smt and as z3, before
// it was deleted, as crates/prover/smt/tests/tables/decide.txt records it too.
const SMT_RECORDED: Decided = {
  kind: "decided",
  verdict: "unsat",
  statistics: { instances: 14, steps: 4626 },
};

// What the TypeScript deciders answered on their inputs with no limits, before they were deleted,
// as tests/fixtures/zenon/decisions.txt and prove-isabelle's testdata/decide.txt record Zenon's and
// Isabelle's too.
const RECORDED: Record<string, Decided> = {
  smt: SMT_RECORDED,
  z3: SMT_RECORDED,
  isabelle: { kind: "decided", verdict: "unsat", statistics: { steps: 840 } },
  ls4: { kind: "decided", verdict: "unsat", statistics: { steps: 5 } },
  zenon: {
    kind: "decided",
    verdict: "unsat",
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

const getAddon = () => {
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new Error(addon);
  return addon;
};

// The decision with no time limit, and stepLimit steps where it is given.
const decide = (prover: string, text: string, stepLimit?: number) =>
  getAddon().decide(prover, text, Infinity, stepLimit, undefined);

const getSteps = (decision: NativeDecision) =>
  decision.kind === "decided" ? Number(decision.statistics.steps) : Number.NaN;

describe("the deciders' steps and statistics", () => {
  it.each(INPUTS)(
    "%s proves its input and reports the same statistics each time",
    (prover, text) => {
      const first = decide(prover, text);
      const second = decide(prover, text);
      expect(first).toMatchObject({ kind: "decided", verdict: "unsat" });
      expect(getSteps(first)).toBeGreaterThan(0);
      expect(second).toEqual(first);
    },
  );

  // A step limit stops a backend where its time limit would, so a search cut short is unknown.
  it.each(INPUTS)("%s gives up at a step limit", (prover, text) => {
    expect(decide(prover, text, 1)).toMatchObject({ kind: "decided", verdict: "unknown" });
  });

  // A limit as large as the steps the proof took changes nothing.
  it.each(INPUTS)("%s proves its input within the steps it took", (prover, text) => {
    const steps = getSteps(decide(prover, text));
    expect(decide(prover, text, steps)).toMatchObject({
      kind: "decided",
      verdict: "unsat",
      statistics: { steps },
    });
  });
});

// Z3 takes steps parsing up to a malformed term, so a step limit can stop it before the error, which
// is why prover-inputs.ts records an input that fails without a step limit.
describe("a malformed input", () => {
  const text = "(declare-const x Int)\n(assert (= (+ x 1) x))\n(assert (foo x))\n(check-sat)";

  it("fails without a step limit", () => {
    expect(decide("smt", text)).toMatchObject({ kind: "error" });
  });

  it("is unknown when the step limit stops it first", () => {
    expect(decide("smt", text, 0)).toMatchObject({
      kind: "decided",
      verdict: "unknown",
      statistics: { stop: "steps" },
    });
  });
});

// Each backend's TypeScript is deleted, and its Rust port decides as the TypeScript did.
describe("the Rust ports", () => {
  // Z3 is sent the SMT input.
  it.each([...INPUTS, ["z3", INPUTS[0][1]] as const])(
    "%s decides as its TypeScript did",
    (prover, text) => {
      expect(decide(prover, text)).toMatchObject(RECORDED[prover]);
    },
  );

  // tlapm counts a Zenon, an Isabelle or an LS4 that stops on its input as a failure.
  it.each([
    ["zenon", "$sig a"],
    ["isabelle", "theory \u{e9}"],
    ["ls4", "not ((always h00000) ->"],
  ])("fails on a malformed %s input", (prover, text) => {
    expect(decide(prover, text)).toMatchObject({ kind: "error" });
  });

  it("declines a prover without a backend", () => {
    expect(getAddon().decide("cvc4", "", 1000, 10, undefined)).toEqual({
      kind: "declined",
      reason: "the cvc4 backend",
    });
  });

  it("declines a prover without a backend with no limits", () => {
    expect(decide("cvc4", "")).toEqual({ kind: "declined", reason: "the cvc4 backend" });
  });

  // The addon reads the cancel cell, so a decision whose cell is set before it starts gives up at
  // once. WebAssembly decides on the thread that would set it, so it doesn't read the cell
  // (prove-it-host's prover.rs) and decides as without one.
  const getCanceledDecision = (prover: string, text: string) => {
    const cancel = new Int32Array(new SharedArrayBuffer(4));
    cancel[0] = 1;
    return getAddon().decide(prover, text, Infinity, undefined, cancel);
  };

  it.if(process.env.PROVE_IT_ENGINE_WASM === undefined).each(INPUTS)(
    "%s is unknown once its decision is canceled",
    (prover, text) => {
      expect(getCanceledDecision(prover, text)).toMatchObject({
        kind: "decided",
        verdict: "unknown",
      });
    },
  );

  it.if(process.env.PROVE_IT_ENGINE_WASM !== undefined).each(INPUTS)(
    "%s decides as WebAssembly whatever its cancel cell holds",
    (prover, text) => {
      expect(getCanceledDecision(prover, text)).toEqual(decide(prover, text));
    },
  );
});

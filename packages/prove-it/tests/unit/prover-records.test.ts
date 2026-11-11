import { describe, expect, it } from "bun:test";

import {
  getInputKey,
  getInputPath,
  getMergedTimeLimits,
  getUpdatedRecords,
  type InputAnswer,
} from "../../scripts/prover-records";

// The smt and z3 methods can be sent the same text, each with its own time limit.
describe("the recorded inputs", () => {
  it("keep the same text sent to two provers apart", () => {
    const smt = getInputKey("smt", "0123456789abcdef");
    const z3 = getInputKey("z3", "0123456789abcdef");
    expect(smt).not.toBe(z3);
    expect(getInputPath(smt)).toEndWith("/smt/0123456789abcdef.smt");
    expect(getInputPath(z3)).toEndWith("/z3/0123456789abcdef.smt2");
  });

  it("take the new answers of the updated inputs and keep their step limits", () => {
    const records = {
      "smt/0000000000000001": {
        prover: "smt",
        stepLimit: 9355,
        verdict: "unsat" as const,
        statistics: { instances: 81, steps: 9355 },
      },
      "smt/0000000000000002": {
        prover: "smt",
        stepLimit: 100,
        verdict: "unsat" as const,
        statistics: { steps: 100 },
      },
      "z3/0000000000000003": {
        prover: "z3",
        verdict: "unknown" as const,
        statistics: {},
        error: "parse error",
      },
    };
    const updated = getUpdatedRecords(
      records,
      new Map<string, InputAnswer>([
        [
          "smt/0000000000000001",
          { verdict: "unknown", statistics: { instances: 81, steps: 9359, stop: "steps" } },
        ],
        ["z3/0000000000000003", { verdict: "unsat", statistics: { steps: 7 } }],
      ]),
    );
    expect(updated).toEqual({
      "smt/0000000000000001": {
        prover: "smt",
        stepLimit: 9355,
        verdict: "unknown",
        statistics: { instances: 81, steps: 9359, stop: "steps" },
      },
      "smt/0000000000000002": records["smt/0000000000000002"],
      "z3/0000000000000003": { prover: "z3", verdict: "unsat", statistics: { steps: 7 } },
    });
  });
});

describe("the time limits of the inputs", () => {
  it("keep the earlier limits of inputs a run over some modules didn't write", () => {
    const earlier = { "smt/0000000000000001": [5], "z3/0000000000000002": [null] };
    const written = { "smt/0000000000000001": [10], "smt/0000000000000003": [5] };
    expect(getMergedTimeLimits(earlier, written)).toEqual({
      "smt/0000000000000001": [10],
      "z3/0000000000000002": [null],
      "smt/0000000000000003": [5],
    });
  });
});

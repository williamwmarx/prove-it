import { describe, expect, it } from "bun:test";

import { getInputKey, getInputPath } from "../../scripts/prover-records";

// The smt and z3 methods can be sent the same text, each with its own time limit.
describe("the recorded inputs", () => {
  it("keep the same text sent to two provers apart", () => {
    const smt = getInputKey("smt", "0123456789abcdef");
    const z3 = getInputKey("z3", "0123456789abcdef");
    expect(smt).not.toBe(z3);
    expect(getInputPath(smt)).toEndWith("/smt/0123456789abcdef.smt");
    expect(getInputPath(z3)).toEndWith("/z3/0123456789abcdef.smt2");
  });
});

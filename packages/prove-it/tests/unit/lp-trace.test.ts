import { describe, expect, it } from "bun:test";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { recordLpTrace, traceLp } from "../../src/prover/smt/solver/lp-trace";
import { KIND_GE, KIND_GT, KIND_LE } from "../../src/prover/smt/solver/lp/constraints";
import { Explanation } from "../../src/prover/smt/solver/lp/explanation";
import { LarSolver } from "../../src/prover/smt/solver/lp/lar-solver";
import { Rational } from "../../src/prover/smt/solver/rational";

// The session the Rust recorder writes too (native/crates/prover/smt/src/lp/trace.rs), which must
// write the same file.
const FIXTURE = join(import.meta.dir, "../fixtures/lp-trace/lar-session.lptrace");
const TEXT = "lar-session";

const runSession = () => {
  const lar = traceLp("lar", LarSolver, () => false);
  const x = lar.addVar(0, false);
  const y = lar.addVar(1, false);
  const sum = lar.addTerm(
    [
      [x, Rational.one],
      [y, Rational.of(1n, 2n)],
    ],
    2,
  );
  lar.activate(lar.mkVarBound(x, KIND_GE, Rational.of(3n, 1n)));
  lar.activate(lar.mkVarBound(y, KIND_GT, Rational.zero));
  lar.findFeasibleSolution();
  lar.getValue(sum);
  lar.getBound(x, false);
  lar.getBound(x, true);
  lar.push();
  lar.constraints.isAuxiliaryMode = true;
  lar.activate(lar.mkVarBound(sum, KIND_LE, Rational.of(-7n, 3n)));
  lar.constraints.isAuxiliaryMode = false;
  if (lar.findFeasibleSolution() !== lar.status) throw new Error("status");
  lar.getInfeasibilityExplanation(new Explanation());
  lar.pop(1);
  lar.findFeasibleSolution();
  lar.getTerm(sum);
  expect(() => lar.getTerm(x)).toThrow("column 0 has no term");
};

describe("lp trace", () => {
  it("records the session the Rust recorder is checked against", () => {
    const directory = mkdtempSync(join(tmpdir(), "lp-trace-"));
    const previous = process.env.PROVE_IT_LP_TRACE;
    process.env.PROVE_IT_LP_TRACE = directory;
    try {
      recordLpTrace(TEXT, runSession);
    } finally {
      if (previous === undefined) delete process.env.PROVE_IT_LP_TRACE;
      else process.env.PROVE_IT_LP_TRACE = previous;
    }
    const text = readFileSync(join(directory, "ef5a0fc173b80a86.lptrace"), "utf8");
    rmSync(directory, { recursive: true });
    expect(text).toBe(readFileSync(FIXTURE, "utf8"));
  });
});

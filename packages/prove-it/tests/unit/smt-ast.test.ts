import { describe, expect, it } from "bun:test";

import { AstManager, OP_IDIV0, SORT_INT } from "../../src/prover/smt/solver/ast";
import { ResourceLimit } from "../../src/prover/smt/solver/rlimit";

// (div0 x x), held, and the number of ASTs with it.
const getDivisionByZero = () => {
  const manager = new AstManager(new ResourceLimit(Number.POSITIVE_INFINITY));
  const x = manager.mkApp(manager.mkFuncDecl("x", [], SORT_INT), [], SORT_INT);
  const division = manager.mkApp(OP_IDIV0, [x, x], SORT_INT);
  manager.incRef(division);
  return { manager, division, numAsts: manager.getNumAsts() };
};

// Z3 counts the references to a func_decl together, whether an application or a model holds it, as
// MBQI's models hold the div0 and mod0 they interpret. The number of ASTs seeds model completion.
describe("the SMT AST manager counts a builtin declaration that a model holds", () => {
  it("keeps it while an application holds it", () => {
    const divisionByZero = getDivisionByZero();
    const manager = divisionByZero.manager;
    const declId = manager.getDeclId(divisionByZero.division);
    for (let round = 0; round < 2; round++) {
      manager.incDeclRef(OP_IDIV0);
      manager.decDeclRef(OP_IDIV0);
      expect(manager.getNumAsts()).toBe(divisionByZero.numAsts);
      expect(manager.getDeclId(divisionByZero.division)).toBe(declId);
    }
  });

  it("releases it with the last of the model and the applications", () => {
    const divisionByZero = getDivisionByZero();
    const manager = divisionByZero.manager;
    manager.incDeclRef(OP_IDIV0);
    manager.decRef(divisionByZero.division);
    expect(manager.getNumAsts()).toBe(divisionByZero.numAsts - 2);
    manager.decDeclRef(OP_IDIV0);
    expect(manager.getNumAsts()).toBe(divisionByZero.numAsts - 3);
  });
});

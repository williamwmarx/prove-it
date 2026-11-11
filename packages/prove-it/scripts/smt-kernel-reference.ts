// Runs the TypeScript SMT kernel on the problems of core/context.rs's Rust unit tests, building the
// same expressions in the same order, and prints the result, conflicts and steps each test expects:
//   bun scripts/smt-kernel-reference.ts
import { AstManager, OP_ITE, SORT_BOOL } from "../src/prover/smt/solver/ast";
import { Context } from "../src/prover/smt/solver/context";
import { ResourceLimit } from "../src/prover/smt/solver/rlimit";

const mk = (relevancyLevel: 0 | 2) => {
  const m = new AstManager(new ResourceLimit(Infinity));
  const context = new Context(m, { isMbqi: true, relevancyLevel });
  context.setupContext();
  return { m, context };
};
const bool = (m: AstManager, name: string) =>
  m.mkApp(m.mkFuncDecl(name, [], SORT_BOOL), [], SORT_BOOL);
const report = (name: string, context: Context, result: number, extra = "") =>
  console.log(
    `${name}: result=${result} conflicts=${context.getNumConflicts()} steps=${context.manager.limit.count}${extra}`,
  );

// 3-SAT from an LCG.
const lcgClauses = (numVars: number, numClauses: number, seed: number) => {
  let state = seed >>> 0;
  const next = () => {
    state = (Math.imul(state, 1103515245) + 12345) >>> 0;
    return state >>> 8;
  };
  const clauses: [number, boolean][][] = [];
  for (let index = 0; index < numClauses; index++) {
    const clause: [number, boolean][] = [];
    for (let k = 0; k < 3; k++) clause.push([next() % numVars, next() % 2 === 0]);
    clauses.push(clause);
  }
  return clauses;
};

(() => {
  // S1: the four clauses over p, q.
  for (const level of [2, 0] as const) {
    const { m, context } = mk(level);
    const p = bool(m, "p");
    const q = bool(m, "q");
    for (const [a, b] of [
      [p, q],
      [m.mkNot(p), q],
      [p, m.mkNot(q)],
      [m.mkNot(p), m.mkNot(q)],
    ])
      context.internalizeAssertion(m.mkOr([a, b]), 0);
    report(`s1-${level}`, context, context.search());
  }
})();
(() => {
  // S2/S3/S4/S9: EUF.
  const setup = () => {
    const { m, context } = mk(2);
    const u = m.mkSort("U");
    const f = m.mkFuncDecl("f", [u], u);
    const [a, b, c] = ["a", "b", "c"].map((name) => m.mkApp(m.mkFuncDecl(name, [], u), [], u));
    const app = (x: number) => m.mkApp(f, [x], u);
    return { m, context, u, a, b, c, app };
  };
  {
    const { m, context, a, b, c, app } = setup();
    context.internalizeAssertion(m.mkEq(a, b), 0);
    context.internalizeAssertion(m.mkEq(b, c), 0);
    context.internalizeAssertion(m.mkNot(m.mkEq(app(a), app(c))), 0);
    report("s2", context, context.search());
  }
  {
    const { m, context, a, b, c, app } = setup();
    context.internalizeAssertion(m.mkOr([m.mkEq(a, b), m.mkEq(a, c)]), 0);
    context.internalizeAssertion(m.mkNot(m.mkEq(app(a), app(b))), 0);
    context.internalizeAssertion(m.mkNot(m.mkEq(app(a), app(c))), 0);
    report("s3", context, context.search());
  }
  {
    const { m, context, a, b, c, app } = setup();
    const ab = m.mkEq(a, b);
    const ac = m.mkEq(a, c);
    context.internalizeAssertion(m.mkOr([ab, ac]), 0);
    context.internalizeAssertion(m.mkNot(m.mkEq(app(a), app(b))), 0);
    const result = context.search();
    report(
      "s4",
      context,
      result,
      ` ab=${context.findAssignment(ab)} ac=${context.findAssignment(ac)}`,
    );
  }
  {
    const { m, context, a, app } = setup();
    const f3 = app(app(app(a)));
    const f5 = app(app(f3));
    context.internalizeAssertion(m.mkEq(f3, a), 0);
    context.internalizeAssertion(m.mkEq(f5, a), 0);
    context.internalizeAssertion(m.mkNot(m.mkEq(app(a), a)), 0);
    report("s9", context, context.search());
  }
  {
    // S6: c = ite(p, a, b), c != a, c != b.
    const { m, context, u, a, b, c } = setup();
    const p = bool(m, "p");
    const ite = m.mkApp(OP_ITE, [p, a, b], u);
    context.internalizeAssertion(m.mkEq(c, ite), 0);
    context.internalizeAssertion(m.mkNot(m.mkEq(c, a)), 0);
    context.internalizeAssertion(m.mkNot(m.mkEq(c, b)), 0);
    report("s6", context, context.search());
  }
  {
    // S10: a chain of disjunctions of equalities over 6 constants, with f distinguishing the ends.
    const { m, context, u, app } = setup();
    const xs = Array.from({ length: 6 }, (_, index) =>
      m.mkApp(m.mkFuncDecl(`x${index}`, [], u), [], u),
    );
    const ys = Array.from({ length: 6 }, (_, index) =>
      m.mkApp(m.mkFuncDecl(`y${index}`, [], u), [], u),
    );
    for (let index = 0; index < 5; index++) {
      context.internalizeAssertion(
        m.mkOr([
          m.mkAnd([m.mkEq(xs[index], ys[index]), m.mkEq(ys[index], xs[index + 1])]),
          m.mkEq(xs[index], xs[index + 1]),
        ]),
        0,
      );
    }
    context.internalizeAssertion(m.mkNot(m.mkEq(app(xs[0]), app(xs[5]))), 0);
    report("s10", context, context.search());
  }
})();
(() => {
  // S7: push and pop.
  const { m, context } = mk(2);
  const p = bool(m, "p");
  context.internalizeAssertion(p, 0);
  context.push();
  context.internalizeAssertion(m.mkNot(p), 0);
  const first = context.search();
  context.pop(1);
  const second = context.search();
  console.log(`s7: first=${first} second=${second} p=${context.findAssignment(p)}`);
})();
(() => {
  // S8: pigeonhole, n + 1 pigeons in n holes.
  for (const holes of [2, 4, 5]) {
    const { m, context } = mk(2);
    const x = Array.from({ length: holes + 1 }, (_, i) =>
      Array.from({ length: holes }, (_, j) => bool(m, `x${i}_${j}`)),
    );
    for (let i = 0; i <= holes; i++) context.internalizeAssertion(m.mkOr(x[i]), 0);
    for (let j = 0; j < holes; j++)
      for (let i = 0; i <= holes; i++)
        for (let k = i + 1; k <= holes; k++)
          context.internalizeAssertion(m.mkOr([m.mkNot(x[i][j]), m.mkNot(x[k][j])]), 0);
    report(`s8-${holes}`, context, context.search());
  }
})();
(() => {
  // S11: random 3-SAT.
  for (const [numVars, numClauses, seed] of [
    [40, 170, 1],
    [40, 170, 2],
    [60, 255, 3],
    [80, 340, 4],
  ]) {
    for (const level of [2, 0] as const) {
      const { m, context } = mk(level);
      const vars = Array.from({ length: numVars }, (_, index) => bool(m, `v${index}`));
      for (const clause of lcgClauses(numVars, numClauses, seed))
        context.internalizeAssertion(
          m.mkOr(
            clause.map(([index, isPositive]) => (isPositive ? vars[index] : m.mkNot(vars[index]))),
          ),
          0,
        );
      const result = context.search();
      const model =
        result === 1 ? vars.map((v) => (context.findAssignment(v) > 0 ? "1" : "0")).join("") : "";
      report(`s11-${numVars}-${seed}-${level}`, context, result, model ? ` model=${model}` : "");
    }
  }
})();
(() => {
  // S12: pigeons as constants equal to some hole, told apart by f.
  for (const holes of [3, 4, 5, 6]) {
    const { m, context } = mk(2);
    const u = m.mkSort("U");
    const f = m.mkFuncDecl("f", [u], u);
    const hs = Array.from({ length: holes }, (_, j) =>
      m.mkApp(m.mkFuncDecl(`h${j}`, [], u), [], u),
    );
    const ps = Array.from({ length: holes + 1 }, (_, i) =>
      m.mkApp(m.mkFuncDecl(`p${i}`, [], u), [], u),
    );
    for (const p of ps) context.internalizeAssertion(m.mkOr(hs.map((h) => m.mkEq(p, h))), 0);
    for (let i = 0; i <= holes; i++)
      for (let k = i + 1; k <= holes; k++)
        context.internalizeAssertion(
          m.mkNot(m.mkEq(m.mkApp(f, [ps[i]], u), m.mkApp(f, [ps[k]], u))),
          0,
        );
    report(`s12-${holes}`, context, context.search(), ` dack=${context["dynAck"]["numInstances"]}`);
  }
})();
(() => {
  for (const holes of [6, 7, 8]) {
    const { m, context } = mk(2);
    const x = Array.from({ length: holes + 1 }, (_, i) =>
      Array.from({ length: holes }, (_, j) => bool(m, `x${i}_${j}`)),
    );
    for (let i = 0; i <= holes; i++) context.internalizeAssertion(m.mkOr(x[i]), 0);
    for (let j = 0; j < holes; j++)
      for (let i = 0; i <= holes; i++)
        for (let k = i + 1; k <= holes; k++)
          context.internalizeAssertion(m.mkOr([m.mkNot(x[i][j]), m.mkNot(x[k][j])]), 0);
    report(`s8-${holes}`, context, context.search());
  }
})();

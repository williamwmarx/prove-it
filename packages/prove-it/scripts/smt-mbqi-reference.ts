// Runs the TypeScript SMT kernel with model-based quantifier instantiation (the model finder,
// its AUF and macro solvers, the quantifier analyzer and the model checker with its auxiliary
// context) on small quantified EUF problems that MBQI decides, building the same expressions in
// the same order as core/model_checker.rs's Rust unit tests, and prints what each test expects:
// the result, the conflicts, the steps, the quantifier instances and the number of ASTs, and for a
// satisfiable problem the model get_model makes. The quantifiers have no patterns, so every
// instance comes from MBQI. The Rust tests read the output as the table mbqi.txt:
//   bun scripts/smt-mbqi-reference.ts > native/crates/prover/smt/tests/tables/mbqi.txt
import { AstManager, SORT_BOOL } from "../src/prover/smt/solver/ast";
import { Context } from "../src/prover/smt/solver/context";
import type { FuncInterp, ProtoModel } from "../src/prover/smt/solver/proto-model";
import { ResourceLimit } from "../src/prover/smt/solver/rlimit";

const show = (m: AstManager, expr: number | null | undefined) =>
  expr === null || expr === undefined || expr === -1
    ? "none"
    : `${m.toString(expr)}#${m.ids[expr]}`;

const getDeclName = (m: AstManager, decl: number) => {
  const name = m.funcDecls[decl].name;
  return typeof name === "number" ? `k!${name}` : name;
};

const getInterpText = (m: AstManager, interp: FuncInterp) =>
  [
    ...interp.entries.map(
      (entry) => `[${entry.args.map((arg) => show(m, arg)).join(" ")} -> ${show(m, entry.result)}]`,
    ),
    `else ${show(m, interp.elseExpr)}`,
  ].join(" ");

const printModel = (m: AstManager, model: ProtoModel, sorts: number[]) => {
  for (const entry of model.constInterps)
    console.log(`const ${getDeclName(m, entry[0])} = ${show(m, entry[1])}`);
  for (const entry of model.funcInterps)
    console.log(`func ${getDeclName(m, entry[0])} ${getInterpText(m, entry[1])}`);
  for (const sort of sorts)
    console.log(
      `universe ${m.sortNames[sort]}: ${model
        .getKnownUniverse(sort)
        .map((value) => show(m, value))
        .join(" ")}`,
    );
};

const mk = () => {
  const m = new AstManager(new ResourceLimit(Infinity));
  const context = new Context(m, { isMbqi: true, relevancyLevel: 2 });
  context.setupContext();
  const u = m.mkSort("U");
  const fn = (name: string, domain: number[], range = u) => m.mkFuncDecl(name, domain, range);
  const app = (decl: number, args: number[], sort = u) => m.mkApp(decl, args, sort);
  const constant = (name: string, sort = u) => app(fn(name, [], sort), [], sort);
  const forall = (numVars: number, body: number, weight = 0) =>
    m.mkQuantifier({
      isForall: true,
      sorts: Array.from({ length: numVars }, () => u),
      names: Array.from({ length: numVars }, (_, index) => `x${index}`),
      body,
      patterns: [],
      weight,
      qid: "",
    });
  const assert = (expr: number) => context.internalizeAssertion(expr, 0);
  const report = (name: string) => {
    console.log(`== ${name} ==`);
    const result = context.search();
    console.log(
      `result=${result} conflicts=${context.getNumConflicts()} steps=${m.limit.count} instances=${context.qmanager.getNumInstances()} asts=${m.getNumAsts()}`,
    );
    if (result !== 1) return;
    printModel(m, context.getModel(), [u]);
    console.log(`modeled: steps=${m.limit.count} asts=${m.getNumAsts()}`);
  };
  return { m, u, fn, app, constant, forall, assert, report };
};

(() => {
  // diseq-sat: ∀x. f(x) ≠ a, f(b) = c, b ≠ c.
  const { m, u, fn, app, constant, forall, assert, report } = mk();
  const f = fn("f", [u]);
  const x = m.mkVar(0, u);
  const [a, b, c] = ["a", "b", "c"].map((name) => constant(name));
  assert(forall(1, m.mkNot(m.mkEq(app(f, [x]), a))));
  assert(m.mkEq(app(f, [b]), c));
  assert(m.mkNot(m.mkEq(b, c)));
  report("diseq-sat");
})();
(() => {
  // or-sat: ∀x. p(x) ∨ q(x), ¬p(a), ¬q(b).
  const { m, u, fn, app, constant, forall, assert, report } = mk();
  const p = fn("p", [u], SORT_BOOL);
  const q = fn("q", [u], SORT_BOOL);
  const x = m.mkVar(0, u);
  const [a, b] = ["a", "b"].map((name) => constant(name));
  assert(forall(1, m.mkOr([app(p, [x], SORT_BOOL), app(q, [x], SORT_BOOL)])));
  assert(m.mkNot(app(p, [a], SORT_BOOL)));
  assert(m.mkNot(app(q, [b], SORT_BOOL)));
  report("or-sat");
})();
(() => {
  // or-unsat: ∀x. p(x) ∨ q(x), ¬p(a), ¬q(a).
  const { m, u, fn, app, constant, forall, assert, report } = mk();
  const p = fn("p", [u], SORT_BOOL);
  const q = fn("q", [u], SORT_BOOL);
  const x = m.mkVar(0, u);
  const a = constant("a");
  assert(forall(1, m.mkOr([app(p, [x], SORT_BOOL), app(q, [x], SORT_BOOL)])));
  assert(m.mkNot(app(p, [a], SORT_BOOL)));
  assert(m.mkNot(app(q, [a], SORT_BOOL)));
  report("or-unsat");
})();
(() => {
  // macro-unsat: ∀x. f(x) = a, f(b) ≠ a.
  const { m, u, fn, app, constant, forall, assert, report } = mk();
  const f = fn("f", [u]);
  const x = m.mkVar(0, u);
  const [a, b] = ["a", "b"].map((name) => constant(name));
  assert(forall(1, m.mkEq(app(f, [x]), a)));
  assert(m.mkNot(m.mkEq(app(f, [b]), a)));
  report("macro-unsat");
})();
(() => {
  // macro-sat: ∀x. f(x) = h(x), f(a) = b, h(c) = d, a ≠ c.
  const { m, u, fn, app, constant, forall, assert, report } = mk();
  const f = fn("f", [u]);
  const h = fn("h", [u]);
  const x = m.mkVar(0, u);
  const [a, b, c, d] = ["a", "b", "c", "d"].map((name) => constant(name));
  assert(forall(1, m.mkEq(app(f, [x]), app(h, [x]))));
  assert(m.mkEq(app(f, [a]), b));
  assert(m.mkEq(app(h, [c]), d));
  assert(m.mkNot(m.mkEq(a, c)));
  report("macro-sat");
})();
(() => {
  // quasi-macro: ∀x. f(x, a) = g(x), f(b, a) = c, g(c) = b.
  const { m, u, fn, app, constant, forall, assert, report } = mk();
  const f = fn("f", [u, u]);
  const g = fn("g", [u]);
  const x = m.mkVar(0, u);
  const [a, b, c] = ["a", "b", "c"].map((name) => constant(name));
  assert(forall(1, m.mkEq(app(f, [x, a]), app(g, [x]))));
  assert(m.mkEq(app(f, [b, a]), c));
  assert(m.mkEq(app(g, [c]), b));
  report("quasi-macro");
})();
(() => {
  // quasi-macro-unsat: ∀x. f(x, a) = g(x), f(b, a) ≠ g(b).
  const { m, u, fn, app, constant, forall, assert, report } = mk();
  const f = fn("f", [u, u]);
  const g = fn("g", [u]);
  const x = m.mkVar(0, u);
  const [a, b] = ["a", "b"].map((name) => constant(name));
  assert(forall(1, m.mkEq(app(f, [x, a]), app(g, [x]))));
  assert(m.mkNot(m.mkEq(app(f, [b, a]), app(g, [b]))));
  report("quasi-macro-unsat");
})();
(() => {
  // rounds: ∀x. ¬p(x) ∨ p(s(x)), p(a), ¬p(s(s(s(a)))).
  const { m, u, fn, app, constant, forall, assert, report } = mk();
  const p = fn("p", [u], SORT_BOOL);
  const s = fn("s", [u]);
  const x = m.mkVar(0, u);
  const a = constant("a");
  assert(forall(1, m.mkOr([m.mkNot(app(p, [x], SORT_BOOL)), app(p, [app(s, [x])], SORT_BOOL)])));
  assert(app(p, [a], SORT_BOOL));
  assert(m.mkNot(app(p, [app(s, [app(s, [app(s, [a])])])], SORT_BOOL)));
  report("rounds");
})();
(() => {
  // two-vars: ∀x y. x = y ∨ ¬r(x, y), r(a, b), a ≠ b.
  const { m, u, fn, app, constant, forall, assert, report } = mk();
  const r = fn("r", [u, u], SORT_BOOL);
  const [x, y] = [1, 0].map((index) => m.mkVar(index, u));
  const [a, b] = ["a", "b"].map((name) => constant(name));
  assert(forall(2, m.mkOr([m.mkEq(x, y), m.mkNot(app(r, [x, y], SORT_BOOL))])));
  assert(app(r, [a, b], SORT_BOOL));
  assert(m.mkNot(m.mkEq(a, b)));
  report("two-vars");
})();
(() => {
  // two-vars-sat: ∀x y. x = y ∨ ¬r(x, y), r(a, a), r(b, c) ∨ b = c.
  const { m, u, fn, app, constant, forall, assert, report } = mk();
  const r = fn("r", [u, u], SORT_BOOL);
  const [x, y] = [1, 0].map((index) => m.mkVar(index, u));
  const [a, b, c] = ["a", "b", "c"].map((name) => constant(name));
  assert(forall(2, m.mkOr([m.mkEq(x, y), m.mkNot(app(r, [x, y], SORT_BOOL))])));
  assert(app(r, [a, a], SORT_BOOL));
  assert(m.mkOr([app(r, [b, c], SORT_BOOL), m.mkEq(b, c)]));
  report("two-vars-sat");
})();
(() => {
  // injective: ∀x y. f(x) ≠ f(y) ∨ x = y, f(a) = f(b), a ≠ b.
  const { m, u, fn, app, constant, forall, assert, report } = mk();
  const f = fn("f", [u]);
  const [x, y] = [1, 0].map((index) => m.mkVar(index, u));
  const [a, b] = ["a", "b"].map((name) => constant(name));
  assert(forall(2, m.mkOr([m.mkNot(m.mkEq(app(f, [x]), app(f, [y]))), m.mkEq(x, y)])));
  assert(m.mkEq(app(f, [a]), app(f, [b])));
  assert(m.mkNot(m.mkEq(a, b)));
  report("injective");
})();
(() => {
  // chained-macros: ∀x. f(x) = g(x), ∀x. g(x) = a, f(b) = c, c ≠ a.
  const { m, u, fn, app, constant, forall, assert, report } = mk();
  const f = fn("f", [u]);
  const g = fn("g", [u]);
  const x = m.mkVar(0, u);
  const [a, b, c] = ["a", "b", "c"].map((name) => constant(name));
  assert(forall(1, m.mkEq(app(f, [x]), app(g, [x]))));
  assert(forall(1, m.mkEq(app(g, [x]), a)));
  assert(m.mkEq(app(f, [b]), c));
  assert(m.mkNot(m.mkEq(c, a)));
  report("chained-macros");
})();
(() => {
  // exceptions-sat: ∀x. x = a ∨ f(x) = b, f(a) = c, b ≠ c.
  const { m, u, fn, app, constant, forall, assert, report } = mk();
  const f = fn("f", [u]);
  const x = m.mkVar(0, u);
  const [a, b, c] = ["a", "b", "c"].map((name) => constant(name));
  assert(forall(1, m.mkOr([m.mkEq(x, a), m.mkEq(app(f, [x]), b)])));
  assert(m.mkEq(app(f, [a]), c));
  assert(m.mkNot(m.mkEq(b, c)));
  report("exceptions-sat");
})();

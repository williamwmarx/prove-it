// Runs the TypeScript SMT kernel on the quantified problems of core/quantifier_manager.rs's Rust
// unit tests, building the same expressions in the same order without model-based instantiation,
// and prints the result, conflicts, steps and quantifier instances each test expects. It then prints
// the code trees the MAM compiler makes for a few patterns, which core/mam_compiler.rs's unit test
// expects:
//   bun scripts/smt-ematching-reference.ts
import { AstManager, SORT_BOOL } from "../src/prover/smt/solver/ast";
import { Context } from "../src/prover/smt/solver/context";
import type { Mam } from "../src/prover/smt/solver/e-matching";
import { type CodeTree, Compiler, type Instruction } from "../src/prover/smt/solver/mam-compiler";
import { ResourceLimit } from "../src/prover/smt/solver/rlimit";

const OP_NAMES = [
  "INIT",
  "BIND",
  "YIELD",
  "COMPARE",
  "CHECK",
  "FILTER",
  "CFILTER",
  "PFILTER",
  "CHOOSE",
  "NOOP",
  "CONTINUE",
  "GET_ENODE",
  "GET_CGR",
  "IS_CGR",
];

const mk = () => {
  const m = new AstManager(new ResourceLimit(Infinity));
  const context = new Context(m, { isMbqi: false, relevancyLevel: 2 });
  context.setupContext();
  const u = m.mkSort("U");
  const fn = (name: string, domain: number[], range = u) => m.mkFuncDecl(name, domain, range);
  const app = (decl: number, args: number[], sort = u) => m.mkApp(decl, args, sort);
  const constant = (name: string) => app(fn(name, []), []);
  const forall = (numVars: number, body: number, patterns: number[][], weight = 0) =>
    m.mkQuantifier({
      isForall: true,
      sorts: Array.from({ length: numVars }, () => u),
      names: Array.from({ length: numVars }, (_, index) => `x${index}`),
      body,
      patterns: patterns.map((terms) => m.mkPattern(terms)),
      weight,
      qid: "",
    });
  const report = (name: string) => {
    const result = context.search();
    console.log(
      `${name}: result=${result} conflicts=${context.getNumConflicts()} steps=${m.limit.count} instances=${context.qmanager.getNumInstances()}`,
    );
  };
  return { m, context, u, fn, app, constant, forall, report };
};

(() => {
  // inverse: ∀x {g(x)}. f(g(x)) = x, g(a) = g(b), a ≠ b.
  const { m, context, u, fn, app, constant, forall, report } = mk();
  const f = fn("f", [u]);
  const g = fn("g", [u]);
  const x = m.mkVar(0, u);
  const gx = app(g, [x]);
  const q = forall(1, m.mkEq(app(f, [gx]), x), [[gx]]);
  const a = constant("a");
  const b = constant("b");
  context.internalizeAssertion(q, 0);
  context.internalizeAssertion(m.mkEq(app(g, [a]), app(g, [b])), 0);
  context.internalizeAssertion(m.mkNot(m.mkEq(a, b)), 0);
  report("inverse");
})();
(() => {
  // transitivity: ∀x y z {r(x, y), r(y, z)}. ¬r(x, y) ∨ ¬r(y, z) ∨ r(x, z), r(a, b), r(b, c),
  // r(c, d), ¬r(a, d).
  const { m, context, u, fn, app, constant, forall, report } = mk();
  const r = fn("r", [u, u], SORT_BOOL);
  const [x, y, z] = [2, 1, 0].map((index) => m.mkVar(index, u));
  const rel = (first: number, second: number) => app(r, [first, second], SORT_BOOL);
  const rxy = rel(x, y);
  const ryz = rel(y, z);
  const q = forall(3, m.mkOr([m.mkNot(rxy), m.mkNot(ryz), rel(x, z)]), [[rxy, ryz]]);
  const [a, b, c, d] = ["a", "b", "c", "d"].map(constant);
  context.internalizeAssertion(q, 0);
  context.internalizeAssertion(rel(a, b), 0);
  context.internalizeAssertion(rel(b, c), 0);
  context.internalizeAssertion(rel(c, d), 0);
  context.internalizeAssertion(m.mkNot(rel(a, d)), 0);
  report("transitivity");
})();
(() => {
  // nested: ∀x {f(f(g(x)))}. f(f(g(x))) = g(x), b = g(a), c = f(b), f(c) ≠ b.
  const { m, context, u, fn, app, constant, forall, report } = mk();
  const f = fn("f", [u]);
  const g = fn("g", [u]);
  const x = m.mkVar(0, u);
  const gx = app(g, [x]);
  const pattern = app(f, [app(f, [gx])]);
  const q = forall(1, m.mkEq(pattern, gx), [[pattern]]);
  const [a, b, c] = ["a", "b", "c"].map(constant);
  context.internalizeAssertion(q, 0);
  context.internalizeAssertion(m.mkEq(b, app(g, [a])), 0);
  context.internalizeAssertion(m.mkEq(c, app(f, [b])), 0);
  context.internalizeAssertion(m.mkNot(m.mkEq(app(f, [c]), b)), 0);
  report("nested");
})();
(() => {
  // rounds: ∀x {p(x)}. ¬p(x) ∨ p(s(x)), p(a), ¬p(s(s(s(a)))).
  const { m, context, u, fn, app, constant, forall, report } = mk();
  const p = fn("p", [u], SORT_BOOL);
  const s = fn("s", [u]);
  const x = m.mkVar(0, u);
  const px = app(p, [x], SORT_BOOL);
  const q = forall(1, m.mkOr([m.mkNot(px), app(p, [app(s, [x])], SORT_BOOL)]), [[px]]);
  const a = constant("a");
  context.internalizeAssertion(q, 0);
  context.internalizeAssertion(app(p, [a], SORT_BOOL), 0);
  context.internalizeAssertion(m.mkNot(app(p, [app(s, [app(s, [app(s, [a])])])], SORT_BOOL)), 0);
  report("rounds");
})();
(() => {
  // weighted: ∀x {p(x)} (weight 12). r(x) ∨ ¬p(x), p(a) ∨ p(b), ¬r(a), ¬r(b).
  const { m, context, u, fn, app, constant, forall, report } = mk();
  const p = fn("p", [u], SORT_BOOL);
  const r = fn("r", [u], SORT_BOOL);
  const x = m.mkVar(0, u);
  const px = app(p, [x], SORT_BOOL);
  const q = forall(1, m.mkOr([app(r, [x], SORT_BOOL), m.mkNot(px)]), [[px]], 12);
  const [a, b] = ["a", "b"].map(constant);
  context.internalizeAssertion(q, 0);
  context.internalizeAssertion(m.mkOr([app(p, [a], SORT_BOOL), app(p, [b], SORT_BOOL)]), 0);
  context.internalizeAssertion(m.mkNot(app(r, [a], SORT_BOOL)), 0);
  context.internalizeAssertion(m.mkNot(app(r, [b], SORT_BOOL)), 0);
  report("weighted");
})();
(() => {
  // lazy: ∀x y {p(x, y), p(y, x)} {q(x), q(y)}. ¬q(x) ∨ ¬q(y) ∨ x = y, q(a), q(b), a ≠ b.
  const { m, context, u, fn, app, constant, forall, report } = mk();
  const p = fn("p", [u, u]);
  const qd = fn("q", [u], SORT_BOOL);
  const [x, y] = [1, 0].map((index) => m.mkVar(index, u));
  const qx = app(qd, [x], SORT_BOOL);
  const qy = app(qd, [y], SORT_BOOL);
  const q = forall(2, m.mkOr([m.mkNot(qx), m.mkNot(qy), m.mkEq(x, y)]), [
    [app(p, [x, y]), app(p, [y, x])],
    [qx, qy],
  ]);
  const [a, b] = ["a", "b"].map(constant);
  context.internalizeAssertion(q, 0);
  context.internalizeAssertion(app(qd, [a], SORT_BOOL), 0);
  context.internalizeAssertion(app(qd, [b], SORT_BOOL), 0);
  context.internalizeAssertion(m.mkNot(m.mkEq(a, b)), 0);
  report("lazy");
})();
(() => {
  // no-match: ∀x {h(x)}. h(x) = x, f(a) ≠ f(b), a = b.
  const { m, context, u, fn, app, constant, forall, report } = mk();
  const h = fn("h", [u]);
  const f = fn("f", [u]);
  const x = m.mkVar(0, u);
  const hx = app(h, [x]);
  const q = forall(1, m.mkEq(hx, x), [[hx]]);
  const [a, b] = ["a", "b"].map(constant);
  context.internalizeAssertion(q, 0);
  context.internalizeAssertion(m.mkNot(m.mkEq(app(f, [a]), app(f, [b]))), 0);
  context.internalizeAssertion(m.mkEq(a, b), 0);
  report("no-match");
})();
(() => {
  // sat: ∀x {h(x)}. h(x) = x, f(a) ≠ b. Without MBQI the kernel gives up with unknown.
  const { m, context, u, fn, app, constant, forall, report } = mk();
  const h = fn("h", [u]);
  const f = fn("f", [u]);
  const x = m.mkVar(0, u);
  const hx = app(h, [x]);
  const q = forall(1, m.mkEq(hx, x), [[hx]]);
  const [a, b] = ["a", "b"].map(constant);
  context.internalizeAssertion(q, 0);
  context.internalizeAssertion(m.mkNot(m.mkEq(app(f, [a]), b)), 0);
  report("sat");
})();

// The code trees: each instruction, numbered in the order a walk of next before alt reaches it.
const dumpTree = (tree: CodeTree) => {
  const numbers = new Map<Instruction, number>();
  const order: Instruction[] = [];
  const stack: Instruction[] = [tree.root];
  for (let instr = stack.pop(); instr !== undefined; instr = stack.pop()) {
    if (numbers.has(instr)) continue;
    numbers.set(instr, order.length);
    order.push(instr);
    if (instr.alt !== null) stack.push(instr.alt);
    if (instr.next !== null) stack.push(instr.next);
  }
  const getNumber = (instr: Instruction | null) =>
    instr === null ? "-" : String(numbers.get(instr));
  console.log(`tree regs=${tree.numRegs} choices=${tree.numChoices}`);
  for (const instr of order) {
    const joints = instr.joints
      .map(
        (joint) =>
          `${joint.kind}/${joint.enode?.owner ?? -1}/${joint.reg}/${joint.decl}/${joint.argPos}`,
      )
      .join(",");
    console.log(
      `  ${getNumber(instr)} ${OP_NAMES[instr.op]} reg=${instr.reg} reg2=${instr.reg2} oreg=${instr.oreg} n=${instr.numArgs} label=${instr.label} enode=${instr.enode?.owner ?? -1} lbl=${instr.lblLow >>> 0},${instr.lblHigh >>> 0} q=${instr.quantifier} regs=[${instr.regs.join(",")}] joints=[${joints}] next=${getNumber(instr.next)} alt=${getNumber(instr.alt)}`,
    );
  }
};

(() => {
  const { m, context, u, fn, app, constant, forall } = mk();
  const f = fn("f", [u, u]);
  const g = fn("g", [u]);
  const h = fn("h", [u]);
  const r = fn("r", [u, u], SORT_BOOL);
  const x = m.mkVar(1, u);
  const y = m.mkVar(0, u);
  const a = constant("a");
  const gx = app(g, [x]);
  const p1 = app(f, [gx, y]);
  const p2 = app(f, [gx, x]);
  const p3 = app(f, [app(h, [x]), a]);
  const p4 = app(f, [y, app(g, [app(h, [x])])]);
  const q1 = forall(2, m.mkEq(p1, y), [[p1]]);
  const q2 = forall(2, m.mkEq(p2, y), [[p2]]);
  const q3 = forall(2, m.mkEq(p3, y), [[p3]]);
  const q4 = forall(2, m.mkEq(p4, y), [[p4]]);
  const mam: Mam = context.qmanager["mam"];
  const compiler = new Compiler(m, context, mam);
  const tree = compiler.mkTree(q1, [p1], 0, false);
  dumpTree(tree);
  compiler.insert(tree, q2, [p2], 0, false);
  dumpTree(tree);
  compiler.insert(tree, q3, [p3], 0, false);
  dumpTree(tree);
  compiler.insert(tree, q4, [p4], 0, false);
  dumpTree(tree);
  // A multi-pattern: r(x, y), r(y, x) and g(x).
  const rxy = app(r, [x, y], SORT_BOOL);
  const ryx = app(r, [y, x], SORT_BOOL);
  const q5 = forall(2, m.mkOr([m.mkNot(rxy), ryx]), [[rxy, ryx, gx]]);
  dumpTree(compiler.mkTree(q5, [rxy, ryx, gx], 0, false));
  dumpTree(compiler.mkTree(q5, [rxy, ryx, gx], 2, true));
})();

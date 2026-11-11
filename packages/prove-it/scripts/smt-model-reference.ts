// Runs the TypeScript models (proto-model.ts, model-evaluator.ts, model-generator.ts) on the
// problems of the Rust port's unit tests, building the same expressions in the same order, and
// prints what each test expects. First on hand-built interpretations and models: the entries, else
// expressions and interpretations of func_interps, the values a proto model makes, and the value of
// terms with and without model completion. Then on ground EUF and propositional problems that the
// kernel finds satisfiable, without quantifiers, so model-based instantiation is not reached: the
// model get_model makes (the constants' values, the functions' entries and else values, the
// universes), the value of each root, and the value of terms under the model. Every expression
// prints with its id, and each step with the resource limit's count and the number of ASTs. The
// Rust tests read the output as the table models.txt:
//   bun scripts/smt-model-reference.ts > native/crates/prover/smt/tests/tables/models.txt
import {
  AstManager,
  OP_IDIV,
  OP_IDIV0,
  OP_ITE,
  OP_MOD,
  SORT_BOOL,
  SORT_INT,
} from "../src/prover/smt/solver/ast";
import { Context } from "../src/prover/smt/solver/context";
import { FuncInterp, ProtoModel } from "../src/prover/smt/solver/proto-model";
import { ResourceLimit } from "../src/prover/smt/solver/rlimit";
import { TheoryLra } from "../src/prover/smt/solver/theory-lra";

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

interface StepCounter {
  steps: number;
  depth: number;
}

// The steps the arithmetic theory of the current problem took, which the steps print without.
const theorySteps: StepCounter = { steps: 0, depth: 0 };
const getSteps = (m: AstManager) => m.limit.count - theorySteps.steps;

const printCounts = (m: AstManager, label: string) =>
  console.log(`${label}: steps=${getSteps(m)} asts=${m.getNumAsts()}`);

// The terms are held, as a caller holds what it evaluates.
const printEvals = (m: AstManager, model: ProtoModel, terms: number[]) => {
  for (const term of terms) m.incRef(term);
  for (const isModelCompletion of [false, true])
    for (const term of terms) {
      const value = model.eval(term, isModelCompletion);
      console.log(
        `eval ${isModelCompletion ? "complete" : "partial"} ${show(m, term)} = ${show(m, value)} steps=${getSteps(m)}`,
      );
      m.decRef(value);
    }
};

const mkManager = () => new AstManager(new ResourceLimit(Infinity));
const mkConst = (m: AstManager, name: string, sort: number) =>
  m.mkApp(m.mkFuncDecl(name, [], sort), [], sort);

(() => {
  console.log("== func-interp ==");
  const m = mkManager();
  const u = m.mkSort("U");
  const [v0, v1, v2] = [0, 1, 2].map((index) => m.mkModelValue(index, u));
  for (const value of [v0, v1, v2]) m.incRef(value);
  const unary = new FuncInterp(m, 1);
  unary.insertNewEntry([v0], v1);
  unary.insertEntry([v1], v0);
  unary.insertEntry([v0], v2);
  console.log(`unary ${getInterpText(m, unary)} partial=${unary.isPartial()}`);
  console.log(`max-occ ${show(m, unary.getMaxOccResult())} constant=${unary.isConstant()}`);
  unary.setElse(v2);
  console.log(`interp ${show(m, unary.getInterp())}`);
  unary.compress();
  console.log(`compressed ${getInterpText(m, unary)} interp ${show(m, unary.getInterp())}`);
  const x0 = m.mkVar(0, u);
  const inner = m.mkApp(OP_ITE, [m.mkEq(v0, x0), v0, v1], u);
  const ite = m.mkApp(OP_ITE, [m.mkEq(x0, v1), v2, inner], u);
  const fromIte = new FuncInterp(m, 1);
  fromIte.setElse(ite);
  console.log(`from-ite ${getInterpText(m, fromIte)} interp ${show(m, fromIte.getInterp())}`);
  fromIte.compress();
  console.log(`from-ite compressed ${getInterpText(m, fromIte)}`);
  const x1 = m.mkVar(1, u);
  const binaryIte = m.mkApp(OP_ITE, [m.mkAnd([m.mkEq(x0, v0), m.mkEq(v1, x1)]), v2, v0], u);
  const binary = new FuncInterp(m, 2);
  binary.setElse(binaryIte);
  binary.insertEntry([v1, v1], v0);
  console.log(`binary ${getInterpText(m, binary)} interp ${show(m, binary.getInterp())}`);
  binary.compress();
  console.log(`binary compressed ${getInterpText(m, binary)} constant=${binary.isConstant()}`);
  const predicate = new FuncInterp(m, 2);
  predicate.insertNewEntry([v0, v1], m.trueExpr);
  predicate.insertNewEntry([v1, v0], m.falseExpr);
  predicate.insertNewEntry([v2, v2], m.trueExpr);
  predicate.setElse(m.falseExpr);
  console.log(`predicate interp ${show(m, predicate.getInterp())}`);
  predicate.setElse(m.trueExpr);
  console.log(`predicate interp ${show(m, predicate.getInterp())}`);
  const identity = new FuncInterp(m, 1);
  identity.insertNewEntry([m.trueExpr], m.trueExpr);
  identity.setElse(m.falseExpr);
  identity.compress();
  console.log(`identity ${getInterpText(m, identity)}`);
  const constant = new FuncInterp(m, 1);
  constant.insertNewEntry([v0], v1);
  constant.insertNewEntry([v2], v1);
  constant.setElse(v1);
  console.log(`constant=${constant.isConstant()}`);
  for (const interp of [unary, fromIte, binary, predicate, identity, constant]) interp.release();
  console.log(
    `refs ${[v0, v1, v2].map((value) => m.getRefCount(value)).join(" ")} asts=${m.getNumAsts()}`,
  );
})();

(() => {
  console.log("== proto-model ==");
  const m = mkManager();
  const u = m.mkSort("U");
  const f = m.mkFuncDecl("f", [u], u);
  const g = m.mkFuncDecl("g", [u, u], u);
  const p = m.mkFuncDecl("p", [u], SORT_BOOL);
  const h = m.mkFuncDecl("h", [u], u);
  const [a, b, c, k] = ["a", "b", "c", "k"].map((name) => mkConst(m, name, u));
  const q = mkConst(m, "q", SORT_BOOL);
  const x = mkConst(m, "x", SORT_INT);
  mkConst(m, "y", SORT_INT);
  const model = new ProtoModel(m);
  model.incRef();
  const v0 = model.getFreshValue(u) as number;
  const v1 = model.getFreshValue(u) as number;
  console.log(`fresh ${show(m, v0)} ${show(m, v1)} int ${show(m, model.getFreshValue(SORT_INT))}`);
  console.log(
    `some ${show(m, model.getSomeValue(u))} ${[0, 1, 2, 3]
      .map(() => show(m, model.getSomeValue(SORT_BOOL)))
      .join(" ")}`,
  );
  model.registerConst(m.decls[a], v0);
  model.registerConst(m.decls[b], v1);
  const fInterp = new FuncInterp(m, 1);
  fInterp.insertNewEntry([v0], v1);
  model.registerFunc(f, fInterp);
  const gInterp = new FuncInterp(m, 2);
  gInterp.insertNewEntry([v0, v1], v0);
  gInterp.setElse(v1);
  model.registerFunc(g, gInterp);
  model.registerConst(m.decls[k], m.mkApp(OP_ITE, [m.mkEq(a, b), a, b], u));
  printCounts(m, "built");
  printModel(m, model, [u, SORT_INT]);
  const app = (decl: number, args: number[], sort = u) => m.mkApp(decl, args, sort);
  const zero = m.mkNumeral(0n);
  const terms = [
    app(f, [a]),
    app(f, [b]),
    app(f, [app(f, [a])]),
    app(g, [a, b]),
    app(g, [b, a]),
    app(g, [a, c]),
    app(p, [a], SORT_BOOL),
    k,
    m.mkEq(k, b),
    c,
    m.mkAnd([q, m.mkEq(a, b)]),
    m.mkApp(OP_IDIV, [x, zero], SORT_INT),
    m.mkApp(OP_MOD, [x, m.mkNumeral(2n)], SORT_INT),
    app(h, [a]),
    m.mkApp(OP_ITE, [m.mkEq(c, a), app(f, [c]), app(h, [b])], u),
  ];
  printEvals(m, model, terms);
  printModel(m, model, [u, SORT_INT]);
  const auxDecl = m.mkFreshFuncDecl("aux", [u], u);
  const unused = m.mkFreshFuncDecl("unused", [u], u);
  const auxInterp = new FuncInterp(m, 1);
  auxInterp.setElse(v1);
  model.registerAuxDecl(auxDecl, auxInterp);
  model.registerAuxDecl(unused, new FuncInterp(m, 1));
  const hInterp = new FuncInterp(m, 1);
  hInterp.setElse(m.mkApp(auxDecl, [m.mkVar(0, u)], u));
  model.reregisterDecl(h, hInterp, m.mkFreshFuncDecl("h", [u], u));
  model.registerFunc(p, new FuncInterp(m, 1));
  model.completePartialFuncs(false);
  printCounts(m, "completed");
  printModel(m, model, [u, SORT_INT]);
  model.cleanup();
  printCounts(m, "cleaned");
  printModel(m, model, [u, SORT_INT]);
  model.compress();
  model.freezeUniverse(u);
  console.log(
    `finite=${model.isFinite(u)} some ${show(m, model.getSomeValue(u))} fresh ${show(m, model.getFreshValue(u))} const ${show(m, model.getSomeConstInterp(m.decls[c]))} ${show(m, model.getSomeConstInterp(m.decls[q]))}`,
  );
  const final = model.mkModel();
  final.incRef();
  printCounts(m, "made");
  printModel(m, final, [u, SORT_INT]);
  printModel(m, model, [u, SORT_INT]);
  printEvals(m, final, terms.slice(0, 4));
  model.decRef();
  final.decRef();
  printCounts(m, "released");
})();

(() => {
  console.log("== partial-theory ==");
  const m = mkManager();
  const x = mkConst(m, "x", SORT_INT);
  const y = mkConst(m, "y", SORT_INT);
  const model = new ProtoModel(m);
  model.incRef();
  const interp = new FuncInterp(m, 2);
  interp.setElse(m.mkNumeral(7n));
  model.registerFunc(OP_IDIV0, interp);
  printEvals(m, model, [
    m.mkApp(OP_IDIV, [x, y], SORT_INT),
    m.mkApp(OP_IDIV, [x, m.mkNumeral(0n)], SORT_INT),
    m.mkApp(OP_MOD, [x, y], SORT_INT),
    m.mkApp(OP_MOD, [m.mkNumeral(5n), m.mkNumeral(0n)], SORT_INT),
  ]);
  printModel(m, model, [SORT_INT]);
  model.decRef();
  printCounts(m, "released");
})();

interface Problem {
  m: AstManager;
  context: Context;
  sorts: number[];
  terms: number[];
}

const runProblem = (name: string, problem: Problem) => {
  console.log(`== ${name} ==`);
  const m = problem.m;
  const context = problem.context;
  console.log(`result=${context.search()}`);
  printCounts(m, "searched");
  const model = context.getModel();
  printCounts(m, "modeled");
  printModel(m, model, problem.sorts);
  const generated = (
    context as unknown as {
      modelState: { generated: { model: ProtoModel; root2value: Map<{ owner: number }, number> } };
    }
  ).modelState.generated;
  for (const entry of generated.root2value)
    console.log(`root ${show(m, entry[0].owner)} = ${show(m, entry[1])}`);
  console.log("proto:");
  printModel(m, generated.model, problem.sorts);
  console.log(`valid=${context.validateModel(model)}`);
  printCounts(m, "validated");
  printEvals(m, model, problem.terms);
  printModel(m, model, problem.sorts);
};

const THEORY_METHODS = [
  "canPropagate",
  "propagate",
  "pushScopeEh",
  "popScopeEh",
  "finalCheckEh",
  "restartEh",
  "initSearchEh",
  "initModel",
  "mkValue",
];

// Counts the steps taken inside a method, once per outermost call.
const countSteps = (target: object, name: string, m: AstManager, counter: StepCounter) => {
  const original: unknown = Reflect.get(target, name);
  if (typeof original !== "function") return;
  Reflect.set(target, name, (...args: unknown[]) => {
    const start = m.limit.count;
    counter.depth++;
    const result: unknown = Reflect.apply(original, target, args);
    counter.depth--;
    if (counter.depth === 0) counter.steps += m.limit.count - start;
    return result;
  });
};

// The Rust port's arithmetic theory is still a stub, which makes none of the numerals and enodes
// that TheoryLra's init makes, and takes none of the steps of its methods. So init is skipped here,
// and the steps print without the theory's, so that the ids and the steps of both agree. Without
// quantifiers, model-based instantiation is off.
const mkContext = (relevancyLevel: 0 | 2) => {
  const m = mkManager();
  const context = new Context(m, { isMbqi: false, relevancyLevel });
  const init: unknown = Reflect.get(TheoryLra.prototype, "init");
  Reflect.set(TheoryLra.prototype, "init", () => undefined);
  context.setupContext();
  Reflect.set(TheoryLra.prototype, "init", init);
  theorySteps.steps = 0;
  for (const name of THEORY_METHODS) countSteps(context.theory, name, m, theorySteps);
  return { m, context };
};

(() => {
  // The S4 problem of the kernel's tests: a = b or a = c, and f(a) != f(b).
  const { m, context } = mkContext(2);
  const u = m.mkSort("U");
  const f = m.mkFuncDecl("f", [u], u);
  const h = m.mkFuncDecl("h", [u], u);
  const [a, b, c] = ["a", "b", "c"].map((name) => mkConst(m, name, u));
  const app = (decl: number, arg: number) => m.mkApp(decl, [arg], u);
  context.internalizeAssertion(m.mkOr([m.mkEq(a, b), m.mkEq(a, c)]), 0);
  context.internalizeAssertion(m.mkNot(m.mkEq(app(f, a), app(f, b))), 0);
  const d = mkConst(m, "d", u);
  runProblem("euf-branch", {
    m,
    context,
    sorts: [u],
    terms: [
      app(f, a),
      app(f, b),
      app(f, c),
      app(f, app(f, a)),
      m.mkEq(a, b),
      m.mkEq(app(f, a), app(f, c)),
      d,
      app(f, d),
      app(h, a),
      m.mkApp(OP_ITE, [m.mkEq(a, c), b, a], u),
    ],
  });
})();

(() => {
  const { m, context } = mkContext(2);
  const [p, q, r, s] = ["p", "q", "r", "s"].map((name) => mkConst(m, name, SORT_BOOL));
  context.internalizeAssertion(m.mkOr([p, q]), 0);
  context.internalizeAssertion(m.mkOr([m.mkNot(p), r]), 0);
  context.internalizeAssertion(m.mkOr([m.mkNot(q), m.mkNot(r)]), 0);
  runProblem("propositional", {
    m,
    context,
    sorts: [],
    terms: [p, q, r, s, m.mkAnd([p, r]), m.mkOr([q, s]), m.mkNot(s), m.mkEq(p, s)],
  });
})();

for (const level of [2, 0] as const) {
  const { m, context } = mkContext(level);
  const u = m.mkSort("U");
  const f = m.mkFuncDecl("f", [u], u);
  const g = m.mkFuncDecl("g", [u, u], u);
  const pred = m.mkFuncDecl("P", [u], SORT_BOOL);
  const [a, b, c] = ["a", "b", "c"].map((name) => mkConst(m, name, u));
  const q = mkConst(m, "q", SORT_BOOL);
  const app = (decl: number, args: number[], sort = u) => m.mkApp(decl, args, sort);
  context.internalizeAssertion(m.mkNot(m.mkEq(a, b)), 0);
  context.internalizeAssertion(m.mkEq(app(f, [a]), b), 0);
  context.internalizeAssertion(m.mkEq(app(f, [b]), a), 0);
  context.internalizeAssertion(m.mkEq(app(g, [a, b]), c), 0);
  context.internalizeAssertion(app(pred, [c], SORT_BOOL), 0);
  context.internalizeAssertion(m.mkNot(app(pred, [a], SORT_BOOL)), 0);
  context.internalizeAssertion(m.mkOr([q, app(pred, [b], SORT_BOOL)]), 0);
  runProblem(`euf-functions-${level}`, {
    m,
    context,
    sorts: [u],
    terms: [
      app(f, [c]),
      app(f, [app(f, [a])]),
      app(g, [b, a]),
      app(g, [app(f, [b]), app(f, [a])]),
      app(pred, [app(f, [b])], SORT_BOOL),
      app(pred, [b], SORT_BOOL),
      m.mkEq(app(g, [a, b]), a),
      m.mkAnd([q, app(pred, [c], SORT_BOOL)]),
    ],
  });
}

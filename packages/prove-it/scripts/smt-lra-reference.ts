// Runs the TypeScript SMT kernel with its arithmetic theory (theory-lra*.ts) on small linear and
// nonlinear arithmetic problems, and solver.ts's checkSmt on every script of tests/fixtures/smt,
// and prints what core/theory_lra.rs's Rust unit tests expect: the result, the conflicts, the steps
// of the resource limit, the quantifier instances and the number of ASTs, the model of a
// satisfiable arithmetic problem (after its text), and why a run stopped early. The arithmetic problems go to the
// kernel as solver.ts gives it a goal, without the tactic before it, so that the theory decides
// them. The Rust tests read the output as the table lra.txt:
//   bun scripts/smt-lra-reference.ts > native/crates/prover/smt/tests/tables/lra.txt
import { readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { SmtCanceledError, SmtUnsupportedError } from "../src/errors";
import { AssertedFormulas } from "../src/prover/smt/solver/asserted-formulas";
import { AstManager } from "../src/prover/smt/solver/ast";
import { Context } from "../src/prover/smt/solver/context";
import type { FuncInterp, ProtoModel } from "../src/prover/smt/solver/proto-model";
import { applyUfniaTactic } from "../src/prover/smt/solver/quant-tactics";
import { ResourceLimit } from "../src/prover/smt/solver/rlimit";
import { parseSmtlib } from "../src/prover/smt/solver/smtlib-parser";
import { createSteps } from "../src/prover/verdict";

// The step budget of an arithmetic problem and of a fixture.
const PROBLEM_STEP_LIMIT = 1_000_000;
const FIXTURE_STEP_LIMIT = 2_000_000;

const FIXTURES = join(import.meta.dirname, "../tests/fixtures/smt");

const PROBLEMS: [string, string][] = [
  ["int-bounds", "(declare-const x Int) (assert (> x 3)) (assert (< x 5)) (assert (not (= x 4)))"],
  ["real-bounds", "(declare-const x Real) (assert (> x 3.0)) (assert (< x 4.0))"],
  [
    "int-chain",
    "(declare-const x Int) (declare-const y Int) (declare-const z Int) (assert (= x (+ y 1))) (assert (= y (+ z 1))) (assert (>= z 0)) (assert (<= z 0)) (assert (not (= x 2)))",
  ],
  [
    "disequalities",
    "(declare-const x Int) (declare-const y Int) (assert (<= 0 x)) (assert (<= x 2)) (assert (<= 0 y)) (assert (<= y 2)) (assert (distinct x y)) (assert (= (+ x y) 2))",
  ],
  [
    "real-cycle",
    "(declare-const x Real) (declare-const y Real) (declare-const z Real) (assert (< x y)) (assert (< y z)) (assert (< z x))",
  ],
  [
    "ite-abs",
    "(declare-const x Int) (declare-const y Int) (assert (= y (ite (> x 0) x (- x)))) (assert (< y 0))",
  ],
  [
    "ite-choice",
    "(declare-const p Bool) (declare-const x Int) (assert (= x (ite p 3 5))) (assert (> x 4)) (assert p)",
  ],
  [
    "div-mod",
    "(declare-const x Int) (assert (= (mod x 3) 2)) (assert (= (div x 3) 4)) (assert (not (= x 14)))",
  ],
  [
    "div-mod-sat",
    "(declare-const x Int) (declare-const y Int) (assert (= (mod x 4) 3)) (assert (> x 10)) (assert (= y (div x 4)))",
  ],
  [
    "real-division",
    "(declare-const x Real) (declare-const y Real) (assert (= (/ x 2.0) y)) (assert (> y 3.0)) (assert (< x 6.0))",
  ],
  [
    "mod-by-term",
    "(declare-const x Int) (declare-const y Int) (assert (> y 0)) (assert (= (mod x y) y))",
  ],
  [
    "to-int",
    "(declare-const r Real) (assert (> r 1.5)) (assert (< r 2.5)) (assert (is_int r)) (assert (not (= r 2.0)))",
  ],
  [
    "mixed-sum",
    "(declare-const x Int) (declare-const r Real) (assert (= (+ (to_real x) r) 2.5)) (assert (>= r 0.0)) (assert (<= r 1.0)) (assert (>= x 2))",
  ],
  [
    "nonlinear",
    "(declare-const x Int) (declare-const y Int) (assert (= (* x y) 6)) (assert (= x 2)) (assert (not (= y 3)))",
  ],
  [
    "nonlinear-order",
    "(declare-const x Int) (declare-const y Int) (declare-const z Int) (assert (= z (* x y))) (assert (> x 1)) (assert (> y 1)) (assert (< z 4))",
  ],
  [
    "nonlinear-sat",
    "(declare-const x Int) (declare-const y Int) (assert (= (* x y) 12)) (assert (> x y)) (assert (> y 2))",
  ],
  [
    "nonlinear-real",
    "(declare-const x Real) (declare-const y Real) (assert (> x 1.0)) (assert (> y 1.0)) (assert (< (* x y) 1.0))",
  ],
  [
    "theory-combination",
    "(declare-fun f (Int) Int) (declare-const x Int) (declare-const y Int) (assert (<= x y)) (assert (<= y x)) (assert (not (= (f x) (f y))))",
  ],
  [
    "shared-values",
    "(declare-fun f (Int) Int) (declare-const x Int) (declare-const y Int) (assert (>= x 0)) (assert (<= x 1)) (assert (>= y 0)) (assert (<= y 1)) (assert (not (= (f x) (f y)))) (assert (not (= (f x) (f 0))))",
  ],
  [
    "propagation-core",
    "(declare-const a Int) (declare-const b Int) (declare-const c Int) (declare-const p Bool) (assert (or p (> a 10))) (assert (or (not p) (> b 10))) (assert (< (+ a b) 5)) (assert (>= a 0)) (assert (>= b 0)) (assert (=> (> c 0) (< a 3)))",
  ],
  [
    "sat-model",
    "(declare-const x Int) (declare-const y Int) (declare-const r Real) (assert (= (+ x y) 10)) (assert (>= x 3)) (assert (<= y 4)) (assert (= r (/ (to_real x) 2.0))) (assert (> r 3.0))",
  ],
  [
    "quantified",
    "(declare-fun f (Int) Int) (assert (forall ((i Int)) (! (=> (> i 0) (> (f i) i)) :pattern ((f i))))) (assert (< (f 5) 3))",
  ],
  ["gcd-test", "(declare-const x Int) (declare-const y Int) (assert (= (* 2 x) (+ (* 2 y) 1)))"],
  [
    "bounds-before-search",
    "(declare-const x Int) (assert (or (< x 2) (> x 5))) (assert (or (<= x 3) (>= x 7))) (assert (> x 0)) (assert (not (= x 1))) (assert (<= x 8))",
  ],
  [
    "branch",
    "(declare-const x Int) (declare-const y Int) (assert (>= (+ (* 3 x) (* 2 y)) 7)) (assert (<= (+ (* 3 x) (* 2 y)) 7)) (assert (>= x 0)) (assert (>= y 0)) (assert (<= x 1))",
  ],
  [
    "pigeons",
    "(declare-const a Int) (declare-const b Int) (declare-const c Int) (declare-const d Int) (declare-const e Int) (assert (and (<= 0 a) (<= a 3) (<= 0 b) (<= b 3) (<= 0 c) (<= c 3) (<= 0 d) (<= d 3) (<= 0 e) (<= e 3))) (assert (distinct a b c d e))",
  ],
  [
    "real-pigeons",
    "(declare-const a Real) (declare-const b Real) (declare-const c Real) (declare-fun f (Real) Int) (assert (and (<= 0.0 a) (<= a 1.0) (<= 0.0 b) (<= b 1.0) (<= 0.0 c) (<= c 1.0))) (assert (distinct (f a) (f b) (f c))) (assert (or (= a b) (= b c) (= a c)))",
  ],
  // nlsat's model: shared terms compared by their values in it (assume_eqs, is_eq), over variables,
  // terms and integers, and the model's values (mk_value), rational and irrational.
  [
    "nra-shared",
    "(declare-const x Real) (declare-const y Real) (declare-fun f (Real) Real) (assert (= (* x x) 2.0)) (assert (= (* y y) 2.0)) (assert (> (f x) (f y)))",
  ],
  [
    "nra-shared-terms",
    "(declare-const x Real) (declare-const y Real) (declare-fun f (Real) Real) (assert (= (* x x) 2.0)) (assert (= (* y y) 2.0)) (assert (> (f (+ x 1.0)) (f (+ y 1.0))))",
  ],
  [
    "nra-shared-sum",
    "(declare-const x Real) (declare-const y Real) (declare-fun f (Real) Real) (assert (= (* x x) 2.0)) (assert (= (* y y) 2.0)) (assert (> (f (+ x y)) (f 0.0)))",
  ],
  [
    "nra-shared-int",
    "(declare-const x Real) (declare-const n Int) (declare-fun g (Int) Int) (assert (= (* x x x) 2.0)) (assert (> (to_real n) x)) (assert (< (to_real n) (* 2.0 x))) (assert (> (g n) (g 2)))",
  ],
  [
    "nra-equal-values",
    "(declare-const x Real) (declare-const y Real) (declare-fun f (Real) Real) (assert (= (* x y) 3.0)) (assert (= (* x x) 3.0)) (assert (> x 0.0)) (assert (not (= (f x) (f y))))",
  ],
  [
    "nra-model",
    "(declare-const x Real) (declare-const y Real) (declare-const z Real) (declare-fun f (Real) Real) (assert (= (* x y z) 6.0)) (assert (> x 1.0)) (assert (> y x)) (assert (> z y)) (assert (forall ((w Real)) (> (f w) 0.0))) (assert (> (f x) (f z)))",
  ],
  [
    "nra-model-terms",
    "(declare-const x Real) (declare-const y Real) (declare-fun f (Real) Real) (assert (> (* x x) (* 2.0 y y))) (assert (< (* x y) 0.0)) (assert (> (+ x y) 3.0)) (assert (forall ((w Real)) (>= (f w) w))) (assert (> (f (+ x y)) (f y)))",
  ],
  [
    "nra-irrational-value",
    "(declare-const x Real) (declare-fun f (Real) Real) (assert (= (* x x) 2.0)) (assert (forall ((z Real)) (= (f z) z))) (assert (> (f x) 1.0))",
  ],
  [
    "nra-irrational-int",
    "(declare-const x Int) (declare-const y Int) (declare-const r Real) (declare-fun f (Real) Real) (declare-fun g (Int) Int) (assert (= (* r r) 2.0)) (assert (= x 1)) (assert (= (g x) (g y))) (assert (> (to_real y) r)) (assert (forall ((w Real)) (>= (f w) w))) (assert (> (f r) 0.0))",
  ],
];

// Seeded random linear problems over two Int and two Real constants: conjunctions and
// disjunctions of bounds on weighted sums, equalities, disequalities and ite terms.
const getRandomProblems = () => {
  let state = 12345;
  const next = (bound: number) => {
    state = (Math.imul(state, 1103515245) + 12345) >>> 0;
    return (state >>> 8) % bound;
  };
  const names = ["x", "y", "r", "s"];
  const isInt = (name: string) => name === "x" || name === "y";
  const getNumeral = (value: number, isInteger: boolean) => {
    const text = isInteger ? String(Math.abs(value)) : `${Math.abs(value)}.0`;
    return value < 0 ? `(- ${text})` : text;
  };
  const getSum = (isInteger: boolean) => {
    const pool = names.filter((name) => isInt(name) === isInteger);
    const terms = Array.from({ length: 1 + next(2) }, () => {
      const name = pool[next(pool.length)];
      const coeff = next(7) - 3;
      return coeff === 1 ? name : `(* ${getNumeral(coeff, isInteger)} ${name})`;
    });
    return terms.length === 1 ? terms[0] : `(+ ${terms.join(" ")})`;
  };
  const getAtom = (): string => {
    const isInteger = next(2) === 0;
    const kind = next(7);
    const bound = getNumeral(next(11) - 5, isInteger);
    if (kind === 5) return `(not (= ${getSum(isInteger)} ${getSum(isInteger)}))`;
    if (kind === 6) {
      const ite = `(ite (> ${getSum(isInteger)} ${bound}) ${getSum(isInteger)} ${getSum(isInteger)})`;
      return `(<= ${ite} ${getNumeral(next(11) - 5, isInteger)})`;
    }
    return `(${["<", "<=", "=", ">=", ">"][kind]} ${getSum(isInteger)} ${bound})`;
  };
  return Array.from({ length: 80 }, (_, index): [string, string] => {
    const assertions = Array.from({ length: 4 + next(10) }, () =>
      next(3) === 0 ? `(assert (or ${getAtom()} ${getAtom()}))` : `(assert ${getAtom()})`,
    );
    const declarations = names.map(
      (name) => `(declare-const ${name} ${isInt(name) ? "Int" : "Real"})`,
    );
    return [`random-${index}`, [...declarations, ...assertions].join(" ")];
  });
};

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

const printModel = (m: AstManager, model: ProtoModel) => {
  for (const entry of model.constInterps)
    console.log(`const ${getDeclName(m, entry[0])} = ${show(m, entry[1])}`);
  for (const entry of model.funcInterps)
    console.log(`func ${getDeclName(m, entry[0])} ${getInterpText(m, entry[1])}`);
};

const getStop = (error: unknown) => {
  if (error instanceof SmtCanceledError) return "canceled";
  if (error instanceof SmtUnsupportedError) return "unsupported";
  throw error;
};

// The kernel on the assertions as they are parsed, as solver.ts gives it a goal.
const runProblem = (name: string, text: string) => {
  console.log(`== ${name} ==`);
  console.log(`text ${text}`);
  const m = new AstManager(new ResourceLimit(Infinity, undefined, createSteps(PROBLEM_STEP_LIMIT)));
  let context: Context | undefined;
  try {
    const problem = parseSmtlib(text, m, () => undefined);
    const asserted = new AssertedFormulas(m);
    const kernel = new Context(m, { isMbqi: true, relevancyLevel: 2 });
    context = kernel;
    for (const assertion of problem.assertions) asserted.assertExpr(assertion);
    kernel.setupContext();
    kernel.internalizeAssertions(asserted);
    const result = kernel.search();
    console.log(
      `result=${result} conflicts=${kernel.getNumConflicts()} steps=${m.limit.count} instances=${kernel.qmanager.getNumInstances()} asts=${m.getNumAsts()}`,
    );
    if (result !== 1) return;
    printModel(m, kernel.getModel());
    console.log(`modeled: steps=${m.limit.count} asts=${m.getNumAsts()}`);
  } catch (error) {
    console.log(
      `stop=${getStop(error)} conflicts=${context?.getNumConflicts() ?? 0} steps=${m.limit.count}`,
    );
  }
};

// solver.ts's checkSmt.
const runFixture = (name: string, text: string) => {
  console.log(`== ${name} ==`);
  const m = new AstManager(new ResourceLimit(Infinity, undefined, createSteps(FIXTURE_STEP_LIMIT)));
  try {
    const incremental = new AssertedFormulas(m);
    m.limit.inc();
    const problem = parseSmtlib(text, m, (assertion) => {
      m.limit.inc();
      incremental.assertExpr(assertion);
    });
    if (!problem.hasCheckSat) {
      console.log(`result=none steps=${m.limit.count}`);
      return;
    }
    const goal = applyUfniaTactic(m, problem.assertions);
    if (goal.isInconsistent || goal.forms.size === 0) {
      console.log(`goal=${goal.isInconsistent ? "unsat" : "sat"} steps=${m.limit.count}`);
      return;
    }
    const asserted = new AssertedFormulas(m);
    const context = new Context(m, { isMbqi: true, relevancyLevel: 2 });
    for (const assertion of goal.forms.items) asserted.assertExpr(assertion);
    context.setupContext();
    context.internalizeAssertions(asserted);
    const result = context.search();
    console.log(
      `result=${result} conflicts=${context.getNumConflicts()} steps=${m.limit.count} instances=${context.qmanager.getNumInstances()}`,
    );
  } catch (error) {
    console.log(`stop=${getStop(error)} steps=${m.limit.count}`);
  }
};

for (const [name, text] of [...PROBLEMS, ...getRandomProblems()])
  runProblem(name, `${text} (check-sat)`);
for (const name of readdirSync(FIXTURES)
  .filter((file) => file.endsWith(".smt"))
  .sort())
  runFixture(name, readFileSync(join(FIXTURES, name), "utf8"));

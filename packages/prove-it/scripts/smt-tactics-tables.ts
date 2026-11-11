// Writes the table the Rust port of the SMT kernel's preprocessing (design/smt-core.md) is tested
// against, from the TypeScript it ports: quant-tactics.ts (with propagate-values.ts,
// ctx-simplify.ts, qe-lite.ts and qe-lite-der.ts) and asserted-formulas.ts. Each problem, every
// script of tests/fixtures/smt and seeded random quantified scripts, runs three times, each with a
// manager of its own and a step budget:
// - pipeline: as solver.ts runs it before the context: the incremental asserted formulas take each
//   assertion while it is parsed, the ufnia tactic runs, and the asserted formulas of the context
//   take the goal and reduce it;
// - stages: propagate-values, ctx-simplify and qe-lite, one after the other, on a goal of the
//   assertions, with the goal recorded after each;
// - asserted: asserted formulas on the assertions themselves, reduced, then in a pushed scope with
//   the negation of the first assertion, popped and reduced again.
// Each line records what a stage returned, with the step count and the number of ASTs, and each run
// ends with digests of the ids and reference counts of every expression. A budget that cancels a
// run is recorded and ends it, as the small budgets of one fixture's last runs do. The random
// scripts are recorded in the table, one per line.
// prove-smt's tests/tactics.rs replays it:
//   bun scripts/smt-tactics-tables.ts

import { mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import { SmtCanceledError } from "../src/errors";
import { AssertedFormulas } from "../src/prover/smt/solver/asserted-formulas";
import { AstManager, OP_NOT, SORT_BOOL } from "../src/prover/smt/solver/ast";
import { ctxSimplify } from "../src/prover/smt/solver/ctx-simplify";
import { Goal } from "../src/prover/smt/solver/goal";
import { propagateValues } from "../src/prover/smt/solver/propagate-values";
import { applyQeLite } from "../src/prover/smt/solver/qe-lite";
import { applyUfniaTactic } from "../src/prover/smt/solver/quant-tactics";
import { ResourceLimit } from "../src/prover/smt/solver/rlimit";
import { parseSmtlib } from "../src/prover/smt/solver/smtlib-parser";
import { createSteps } from "../src/prover/verdict";

// A text longer than this is recorded as its length and hash.
const MAX_TEXT_LENGTH = 160;
// The step budget of each run: a fixture's, and a random script's.
const FIXTURE_STEP_LIMIT = 3_000_000;
const RANDOM_STEP_LIMIT = 300_000;
// Budgets that cancel the runs of one fixture at different stages.
const BUDGET_FIXTURE = "Quicksort-149.smt";
const BUDGETS = [300, 570, 1000, 2000, 4100, 4500];
const NUM_RANDOM = 300;

const encoder = new TextEncoder();

// FNV-1a over the UTF-8 bytes, which tests/tactics.rs computes the same way.
const getTextHash = (text: string) =>
  encoder.encode(text).reduce((hash, byte) => Math.imul(hash ^ byte, 16777619) >>> 0, 2166136261);

const getShortText = (text: string) => {
  const length = encoder.encode(text).length;
  return length > MAX_TEXT_LENGTH ? `#${length}:${getTextHash(text)}` : text;
};

const lines: string[] = [];
let manager = new AstManager(new ResourceLimit(Number.POSITIVE_INFINITY));

const record = (operation: string, result: string) =>
  lines.push(`${operation} => ${result} steps=${manager.limit.count} asts=${manager.getNumAsts()}`);

// A list of expressions: their number, a hash of their handles, ids and hashes, and their text.
const describeList = (exprs: number[]) => {
  const keys = exprs.map((expr) => `${expr}:${manager.ids[expr]}:${manager.hashes[expr]}`);
  const text = exprs.map((expr) => manager.toString(expr)).join(" ; ");
  return `n=${exprs.length} ids=${getTextHash(keys.join(","))} | ${getShortText(text)}`;
};

const describeGoal = (goal: Goal) =>
  `inconsistent=${goal.isInconsistent ? 1 : 0} ${describeList(goal.forms.items)}`;

// The formulas that reduce commits, after which the asserted formulas may be inconsistent.
const describeReduced = (formulas: AssertedFormulas) => {
  const reduced = formulas.reduce();
  return `inconsistent=${formulas.isInconsistent ? 1 : 0} ${describeList(reduced)}`;
};

// The ids and reference counts of every expression, as two hashes.
const dumpRefs = () => {
  const numNodes: number = Reflect.get(manager, "numNodes");
  const handles = Array.from({ length: numNodes }, (_, index) => index);
  const ids = handles.map((handle) => manager.ids[handle]).join(",");
  const refCounts = handles.map((handle) => manager.getRefCount(handle)).join(",");
  record("refs", `${numNodes} ${getTextHash(ids)} ${getTextHash(refCounts)}`);
};

// The stage being run, which the table records when the step budget cancels it.
let pending = "";
const stage = (name: string, run: () => string) => {
  pending = name;
  record(name, run());
};

const pipeline = (text: string) => {
  // solver.ts's checkSmt up to search.
  const incremental = new AssertedFormulas(manager);
  manager.limit.inc();
  pending = "parse";
  const problem = parseSmtlib(text, manager, (assertion) => {
    manager.limit.inc();
    incremental.assertExpr(assertion);
  });
  record(
    "parse",
    `check-sat=${problem.hasCheckSat ? 1 : 0} incremental=${incremental.getNumFormulas()} ${describeList(problem.assertions)}`,
  );
  if (!problem.hasCheckSat) return;
  let goal = new Goal(manager);
  stage("ufnia", () => {
    goal = applyUfniaTactic(manager, problem.assertions);
    return describeGoal(goal);
  });
  if (goal.isInconsistent || goal.forms.size === 0) return;
  const asserted = new AssertedFormulas(manager);
  stage("assert-goal", () => {
    for (const assertion of goal.forms.items) asserted.assertExpr(assertion);
    return `${asserted.getNumFormulas()}`;
  });
  stage("reduce", () => describeReduced(asserted));
};

const stages = (text: string) => {
  pending = "parse";
  const problem = parseSmtlib(text, manager, () => {});
  record("parse", describeList(problem.assertions));
  const goal = new Goal(manager);
  for (const assertion of problem.assertions) goal.assert(assertion);
  record("goal", describeGoal(goal));
  stage("propagate-values", () => {
    propagateValues(manager, goal);
    return describeGoal(goal);
  });
  stage("ctx-simplify", () => {
    ctxSimplify(manager, goal);
    return describeGoal(goal);
  });
  stage("qe-lite", () => {
    applyQeLite(manager, goal);
    return describeGoal(goal);
  });
  goal.forms.reset();
  record("release-goal", "-");
};

const asserted = (text: string) => {
  pending = "parse";
  const problem = parseSmtlib(text, manager, () => {});
  record("parse", describeList(problem.assertions));
  const formulas = new AssertedFormulas(manager);
  stage("assert", () => {
    for (const assertion of problem.assertions) formulas.assertExpr(assertion);
    return `${formulas.getNumFormulas()}`;
  });
  stage("reduce", () => describeReduced(formulas));
  if (problem.assertions.length === 0) return;
  formulas.push();
  stage("push-assert", () => {
    const negation = manager.mkApp(OP_NOT, [problem.assertions[0]], SORT_BOOL);
    manager.incRef(negation);
    formulas.assertExpr(negation);
    manager.decRef(negation);
    return `${formulas.getNumFormulas()}`;
  });
  stage("push-reduce", () => describeReduced(formulas));
  stage("pop", () => {
    formulas.pop();
    return `${formulas.getNumFormulas()} inconsistent=${formulas.isInconsistent ? 1 : 0}`;
  });
  stage("reassert", () => {
    formulas.assertExpr(problem.assertions[problem.assertions.length - 1]);
    return `${formulas.getNumFormulas()}`;
  });
  stage("rereduce", () => describeReduced(formulas));
};

const RUNS = { pipeline, stages, asserted };

const runProblem = (text: string, stepLimit: number) => {
  for (const [name, run] of Object.entries(RUNS)) {
    manager = new AstManager(
      new ResourceLimit(Number.POSITIVE_INFINITY, undefined, createSteps(stepLimit)),
    );
    record(`run ${name}`, "-");
    try {
      run(text);
      dumpRefs();
    } catch (error) {
      if (!(error instanceof SmtCanceledError)) throw error;
      record(`canceled ${pending}`, "-");
    }
  }
};

// xorshift32, seeded, so that the table doesn't change between runs.
const createRandom = (seed: number) => {
  let state = seed >>> 0;
  return () => {
    state ^= state << 13;
    state >>>= 0;
    state ^= state >>> 17;
    state ^= state << 5;
    state >>>= 0;
    return state;
  };
};

const random = createRandom(0x7ac_7105);
const pick = <T>(items: T[]) => items[random() % items.length];
const chance = (percent: number) => random() % 100 < percent;

const HEADER = [
  "(set-logic UFNIA)",
  "(declare-sort U 0)",
  "(declare-fun a () Int)",
  "(declare-fun b () Int)",
  "(declare-fun c () Int)",
  "(declare-fun p () Bool)",
  "(declare-fun q () Bool)",
  "(declare-fun r () Bool)",
  "(declare-fun u () U)",
  "(declare-fun v () U)",
  "(declare-fun f (Int) Int)",
  "(declare-fun g (Int Int) Bool)",
  "(declare-fun h (U) Int)",
  "(declare-fun k (Int) U)",
  "(declare-fun P (U) Bool)",
].join(" ");

type SortName = "Int" | "Bool" | "U";

interface Bound {
  name: string;
  sort: SortName;
}

// The terms of the script so far, by sort, which later terms often repeat, so that terms are
// shared as propagate-values and ctx-simplify need.
let pool = new Map<SortName, string[]>();
const share = (sort: SortName, term: string) => {
  const terms = pool.get(sort) ?? [];
  pool.set(sort, terms);
  if (terms.length < 40) terms.push(term);
  return term;
};
let numBound = 0;

const getLeaf = (sort: SortName, env: Bound[]): string => {
  const vars = env.filter((bound) => bound.sort === sort);
  if (vars.length > 0 && chance(55)) return pick(vars).name;
  if (sort === "Int") return chance(55) ? pick(["a", "b", "c"]) : `${pick([0, 1, 2, 3, 5])}`;
  if (sort === "U") return chance(70) ? pick(["u", "v"]) : `(k ${getLeaf("Int", env)})`;
  return pick(["p", "q", "r", "true", "false"]);
};

const genInt = (env: Bound[], depth: number): string => {
  const next = depth - 1;
  const choice = random() % 11;
  if (choice <= 1) return `(+ ${gen("Int", env, next)} ${gen("Int", env, next)})`;
  if (choice === 2) return `(- ${gen("Int", env, next)} ${gen("Int", env, next)})`;
  if (choice === 3) return `(* ${pick(["2", "3", "(- 1)"])} ${gen("Int", env, next)})`;
  if (choice === 4) return `(- ${gen("Int", env, next)})`;
  if (choice === 5 || choice === 6) return `(f ${gen("Int", env, next)})`;
  if (choice === 7) return `(h ${gen("U", env, next)})`;
  if (choice === 8)
    return `(ite ${gen("Bool", env, next)} ${gen("Int", env, next)} ${gen("Int", env, next)})`;
  if (choice === 9) return `(${pick(["div", "mod"])} ${gen("Int", env, next)} ${pick(["2", "3"])})`;
  return `(* ${gen("Int", env, next)} ${gen("Int", env, next)})`;
};

const genBool = (env: Bound[], depth: number): string => {
  const next = depth - 1;
  const choice = random() % 14;
  if (choice <= 1) return `(= ${gen("Int", env, next)} ${gen("Int", env, next)})`;
  if (choice <= 3)
    return `(${pick(["<=", "<", ">=", ">"])} ${gen("Int", env, next)} ${gen("Int", env, next)})`;
  if (choice === 4)
    return `(${pick(["and", "or"])} ${gen("Bool", env, next)} ${gen("Bool", env, next)}${chance(40) ? ` ${gen("Bool", env, next)}` : ""})`;
  if (choice === 5) return `(not ${gen("Bool", env, next)})`;
  if (choice === 6) return `(g ${gen("Int", env, next)} ${gen("Int", env, next)})`;
  if (choice === 7) return `(= ${gen("U", env, next)} ${gen("U", env, next)})`;
  if (choice === 8) return `(P ${gen("U", env, next)})`;
  if (choice === 9)
    return `(ite ${gen("Bool", env, next)} ${gen("Bool", env, next)} ${gen("Bool", env, next)})`;
  if (choice === 10) return `(distinct ${gen("Int", env, next)} ${gen("Int", env, next)})`;
  return genQuantifier(env, next);
};

const gen = (sort: SortName, env: Bound[], depth: number): string => {
  if (depth <= 0 || chance(18)) return getLeaf(sort, env);
  const shared = pool.get(sort) ?? [];
  // A pooled term may name variables out of scope, so only those without variables are reused.
  if (shared.length > 0 && chance(15)) {
    const term = pick(shared);
    if (!/\bx\d/.test(term)) return term;
  }
  if (sort === "U")
    return share(sort, chance(50) ? `(k ${gen("Int", env, depth - 1)})` : getLeaf(sort, env));
  return share(sort, sort === "Int" ? genInt(env, depth) : genBool(env, depth));
};

// A quantifier whose body often defines a variable (der), bounds an integer variable (fm, and the
// expansion of a small range), or names it only in disequalities.
const genQuantifier = (env: Bound[], depth: number) => {
  const isForall = chance(55);
  const bound: Bound[] = Array.from({ length: 1 + (random() % 3) }, () => ({
    name: `x${numBound++}`,
    sort: pick<SortName>(["Int", "Int", "Int", "Bool", "U"]),
  }));
  const inner = [...env, ...bound];
  const conjuncts: string[] = [gen("Bool", inner, depth)];
  for (const variable of bound) {
    const kind = random() % 11;
    const other = variable.sort === "Int" ? "Int" : variable.sort;
    if (kind <= 1) {
      // A definition, in either orientation.
      const definition = gen(other, chance(70) ? env : inner, depth);
      conjuncts.push(
        chance(50) ? `(= ${variable.name} ${definition})` : `(= ${definition} ${variable.name})`,
      );
    } else if (kind === 2 && variable.sort === "Int") {
      // A linear definition, which the arithmetic solve plugin solves.
      conjuncts.push(
        `(= (+ (* ${pick(["1", "(- 1)"])} ${variable.name}) ${gen("Int", env, depth)}) ${gen("Int", env, depth)})`,
      );
    } else if (kind === 3 && variable.sort === "Int") {
      const low = random() % 4;
      conjuncts.push(`(<= ${low} ${variable.name})`);
      conjuncts.push(`(${pick(["<=", "<"])} ${variable.name} ${low + (random() % 4)})`);
    } else if (kind === 4 && variable.sort === "Int") {
      conjuncts.push(`(not (= ${variable.name} ${gen("Int", env, depth)}))`);
    } else if (kind === 5 && variable.sort === "Int") {
      conjuncts.push(`(<= (+ ${variable.name} ${gen("Int", env, 1)}) ${gen("Int", env, 1)})`);
      conjuncts.push(`(>= (* 2 ${variable.name}) ${gen("Int", env, 1)})`);
    } else if (kind === 6 && variable.sort === "Bool") {
      conjuncts.push(chance(50) ? variable.name : `(= ${variable.name} ${gen("Bool", env, 1)})`);
    } else if (kind === 7) {
      // A definition in each branch of an ite, which the Boolean solve plugin merges.
      conjuncts.push(
        `(ite ${gen("Bool", env, 1)} (= ${variable.name} ${gen(other, env, 1)}) (= ${variable.name} ${gen(other, env, 1)}))`,
      );
    } else if (kind === 8 && variable.sort === "Int") {
      // Two definitions, the later a value, which replaces the earlier.
      conjuncts.push(`(= ${variable.name} ${gen("Int", inner, depth)})`);
      conjuncts.push(`(= ${variable.name} ${random() % 4})`);
    } else if (kind === 9 && variable.sort === "Int") {
      // Definitions on a cycle through another variable, which der drops.
      const others = bound.filter((item) => item !== variable && item.sort === "Int");
      if (others.length > 0) {
        const another = pick(others);
        conjuncts.push(`(= ${variable.name} (f ${another.name}))`);
        conjuncts.push(`(= ${another.name} (+ ${variable.name} 1))`);
      }
    }
  }
  const body =
    conjuncts.length === 1
      ? conjuncts[0]
      : isForall
        ? `(or ${conjuncts
            .slice(1)
            .map((conjunct) => `(not ${conjunct})`)
            .join(" ")} ${conjuncts[0]})`
        : `(and ${conjuncts.join(" ")})`;
  const intVar = bound.find((variable) => variable.sort === "Int");
  const annotated =
    intVar !== undefined && chance(25)
      ? `(! ${body} :pattern ((f ${intVar.name})))`
      : chance(20)
        ? `(! ${body} :qid q${random() % 5})`
        : body;
  const decls = bound.map((variable) => `(${variable.name} ${variable.sort})`).join(" ");
  return `(${isForall ? "forall" : "exists"} (${decls}) ${annotated})`;
};

const genScript = () => {
  pool = new Map();
  numBound = 0;
  const assertions: string[] = [];
  const count = 2 + (random() % 6);
  for (let index = 0; index < count; index++) {
    const choice = random() % 10;
    const assertion =
      choice === 0
        ? pick(["p", "(not q)", "r"])
        : choice === 1
          ? `(= ${pick(["a", "b", "(f a)", "(h u)"])} ${pick(["0", "1", "2", "b"])})`
          : choice <= 5
            ? genQuantifier([], 2 + (random() % 2))
            : gen("Bool", [], 2 + (random() % 3));
    assertions.push(`(assert ${assertion})`);
  }
  return `${HEADER} ${assertions.join(" ")} (check-sat)`;
};

const fixtures = join(import.meta.dir, "../tests/fixtures/smt");
for (const file of readdirSync(fixtures)
  .filter((name) => name.endsWith(".smt"))
  .sort()) {
  lines.push(`fixture ${file}`);
  runProblem(readFileSync(join(fixtures, file), "utf8"), FIXTURE_STEP_LIMIT);
}
for (let index = 0; index < NUM_RANDOM; index++) {
  lines.push(`random ${genScript()}`);
  runProblem(lines[lines.length - 1].slice("random ".length), RANDOM_STEP_LIMIT);
}
for (const budget of BUDGETS) {
  lines.push(`budget ${budget} ${BUDGET_FIXTURE}`);
  runProblem(readFileSync(join(fixtures, BUDGET_FIXTURE), "utf8"), budget);
}

const directory = join(import.meta.dir, "../native/crates/prover/smt/tests/tables");
mkdirSync(directory, { recursive: true });
writeFileSync(join(directory, "tactics.txt"), `${lines.join("\n")}\n`);

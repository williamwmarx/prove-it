// testdata/provers/hypsubst.txt: the expectations of the Rust tests of provers/hypsubst.ts. Every
// goal is rendered as text (or `@name`, a fixture's statement) and parsed back, so that the Rust
// test, which parses the same text, runs the tactics on the very same goals.
import { TlaIsabelleError } from "../../src/errors";
import { safeTac } from "../../src/prover/isabelle/provers/classical";
import {
  blastHypSubstTac,
  type HypsubstData,
  hypSubstTac,
} from "../../src/prover/isabelle/provers/hypsubst";
import type { Limits } from "../../src/prover/isabelle/pure/interrupt";
import { allConst, listImplies, stripAssumsHyp } from "../../src/prover/isabelle/pure/logic";
import type { GoalTactic } from "../../src/prover/isabelle/pure/tactical";
import {
  funT,
  mkAbs,
  mkApp,
  mkBound,
  mkConst,
  mkFree,
  mkTVar,
  mkType,
  mkVar,
  propT,
  type Term,
  type Typ,
} from "../../src/prover/isabelle/pure/term";
import { premsOf, trivial } from "../../src/prover/isabelle/pure/thm";
import {
  getClaset,
  getClassicalData,
  getHypsubstData,
} from "../../src/prover/isabelle/tla/classical-setup";
import { loadLogic, type TlaLogic } from "../../src/prover/isabelle/tla/logic";
import { createSteps } from "../../src/prover/verdict";
import { joinLines, many, readGoal, showTerm } from "./terms";

const BUDGET = 470_000;
const MAXIMUM_BLOCK = 12_000;
const LARGE = 3000;

// The fixtures the Rust tests know (simp_testing.rs's fixture_goal).
const FIXTURES = [
  "AllocatorImplementation_proof-127",
  "AllocatorImplementation_proof-33",
  "AtomicBakeryWithoutSMT-465",
  "AtomicBakeryWithoutSMT-6",
  "FiniteSetTheorems_proofs-453",
  "NaturalsInduction_proofs-1",
  "Paxos-109",
  "Sets-183",
  "TLAPS-2",
  "constantfcn_test-1",
  "function_except_tuple_soundness_gh201_test-1",
];

const TACTICS: Record<string, (context: { limits: Limits; data: HypsubstData }) => GoalTactic> = {
  hyp_subst: hypSubstTac,
  blast_hyp_subst: blastHypSubstTac,
};

const newLimits = (limit: string) => ({ deadline: Infinity, steps: createSteps(Number(limit)) });

// Synthetic goals: equations x = t and t = x among the premises, both orientations, bound and free
// variables, the occurs check, variables, type variables, and non-equations.
const getSynthetic = (logic: TlaLogic) => {
  const constant = (name: string) => mkConst(name, logic.consts.get(name)!.type);
  const c = mkType("PredicateLogic.c");
  const tp = (term: Term) => mkApp(constant("PredicateLogic.Trueprop"), term);
  const eq = (left: Term, right: Term) => mkApp(mkApp(constant("PredicateLogic.eq"), left), right);
  const eqAt = (type: Typ, left: Term, right: Term) =>
    mkApp(mkApp(mkConst("PredicateLogic.eq", funT(type, funT(type, c))), left), right);
  const app = (fun: Term, ...args: Term[]) => args.reduce((result, arg) => mkApp(result, arg), fun);
  const imp = (...terms: Term[]) => listImplies(terms.slice(0, -1), terms[terms.length - 1]);
  const all = (name: string, type: Typ, body: Term) =>
    mkApp(allConst(type), mkAbs(name, type, body));
  const free = (name: string, arity = 0) =>
    mkFree(
      name,
      Array.from({ length: arity }).reduce<Typ>((type) => funT(c, type), c),
    );
  const [x, y, z, a, b] = ["x", "y", "z", "a", "b"].map((name) => free(name));
  const [f, P, Q, R] = [free("f", 1), free("P", 1), free("Q", 1), free("R", 1)];
  const [P2, P3] = [free("P2", 2), free("P3", 3)];
  const g = free("g", 1);
  const fc = funT(c, c);
  const gFun = mkFree("g", fc);
  const tvarType = mkTVar("'a", 0);
  const xa = mkFree("x", tvarType);
  const aa = mkFree("a", tvarType);
  const Pa = mkFree("P", funT(tvarType, c));
  const B = mkBound;
  const PQ = mkFree("Q", funT(c, propT));
  const tVar = mkVar("t", 0, c);
  const xVar = mkVar("x", 0, c);
  return [
    imp(tp(eq(x, a)), tp(app(P, x))),
    imp(tp(eq(a, x)), tp(app(P, x))),
    imp(tp(eq(x, app(f, x))), tp(app(P, x))),
    imp(tp(eq(app(f, x), x)), tp(app(P, x))),
    imp(tp(eq(x, x)), tp(app(P, x))),
    imp(tp(app(Q, x)), tp(eq(x, a)), tp(app(R, x)), tp(app(P, x))),
    imp(tp(app(Q, x)), tp(eq(a, x)), tp(app(R, x)), tp(app(P, x))),
    imp(tp(eq(x, a)), tp(app(P, a))),
    imp(tp(eq(a, x)), tp(app(P, a))),
    imp(tp(app(Q, x)), tp(eq(x, a)), tp(app(P, a))),
    imp(tp(eq(a, b)), tp(app(P, a))),
    imp(tp(eq(a, b)), tp(app(P, b))),
    imp(tp(app(Q, a)), tp(app(P, b))),
    imp(tp(eq(x, a)), tp(eq(y, x)), tp(app(P2, x, y))),
    imp(tp(eq(x, a)), tp(eq(x, b)), tp(app(P, x))),
    imp(tp(eq(x, a)), tp(eq(y, b)), tp(app(Q, y)), tp(app(P2, x, y))),
    imp(tp(app(R, a)), tp(app(Q, x)), tp(eq(x, a)), tp(app(P, x))),
    imp(tp(app(R, a)), tp(app(Q, x)), tp(eq(a, x)), tp(app(P2, x, a))),
    all("u", c, imp(tp(eq(B(0), a)), tp(app(P, B(0))))),
    all("u", c, imp(tp(eq(a, B(0))), tp(app(P, B(0))))),
    all("u", c, imp(tp(eq(B(0), app(f, B(0)))), tp(app(P, B(0))))),
    all("u", c, imp(tp(eq(B(0), B(0))), tp(app(P, B(0))))),
    all("u", c, all("v", c, imp(tp(eq(B(0), app(f, B(1)))), tp(app(P2, B(1), B(0)))))),
    all("u", c, all("v", c, imp(tp(eq(B(1), app(f, B(0)))), tp(app(P2, B(1), B(0)))))),
    all("u", c, all("v", c, imp(tp(eq(app(f, B(0)), B(1))), tp(app(P2, B(1), B(0)))))),
    all("u", c, all("v", c, all("w", c, imp(tp(eq(B(1), a)), tp(app(P3, B(2), B(1), B(0))))))),
    all(
      "u",
      c,
      all(
        "v",
        c,
        all("w", c, imp(tp(app(Q, B(0))), tp(eq(B(2), B(0))), tp(app(P3, B(2), B(1), B(0))))),
      ),
    ),
    all("u", c, imp(tp(app(Q, B(0))), tp(eq(B(0), x)), tp(app(P2, B(0), x)))),
    all("u", c, imp(tp(app(Q, B(0))), tp(eq(x, B(0))), tp(app(P2, B(0), x)))),
    imp(tp(eq(x, tVar)), tp(app(P, x))),
    imp(tp(eq(tVar, x)), tp(app(P, x))),
    imp(tp(eq(xVar, a)), tp(app(P, xVar))),
    imp(tp(app(Q, x)), tp(eq(x, tVar)), tp(app(P2, x, tVar))),
    all("u", c, imp(tp(eq(B(0), tVar)), tp(app(P, B(0))))),
    imp(tp(eqAt(tvarType, xa, aa)), tp(app(Pa, xa))),
    all("u", tvarType, imp(tp(eqAt(tvarType, B(0), aa)), tp(app(Pa, B(0))))),
    imp(tp(eqAt(fc, gFun, mkAbs("z", c, app(f, B(0))))), tp(app(P, app(gFun, a)))),
    imp(tp(eqAt(fc, mkAbs("z", c, app(f, B(0))), gFun)), tp(app(P, app(gFun, a)))),
    all("h", fc, imp(tp(eqAt(fc, B(0), f)), tp(app(P, app(B(0), a))))),
    imp(all("z", c, tp(app(Q, B(0)))), tp(eq(x, a)), tp(app(P, x))),
    imp(tp(eq(x, a)), app(PQ, x)),
    imp(tp(eq(a, x)), app(PQ, x)),
    imp(tp(eq(x, a)), all("z", c, tp(app(P2, B(0), x)))),
    imp(tp(eq(x, a)), imp(tp(eq(z, x)), tp(app(P2, z, x)))),
    imp(tp(app(Q, x)), tp(app(P, x))),
    tp(app(P, x)),
    imp(tp(eq(app(g, x), a)), tp(app(P, x))),
  ];
};

export const getHypsubstExpectations = () => {
  const logic = loadLogic();
  const data = getHypsubstData(logic);
  const lines: string[] = [];
  let size = 0;
  const seen = new Set<string>();

  const problem = (name: string, limit: number, goal: string): string[] | undefined => {
    const line = `> tactic\t${name}\t${limit}\t${goal}`;
    if (seen.has(line) || size > BUDGET) return undefined;
    seen.add(line);
    const limits = newLimits(String(limit));
    const block: string[] = [];
    many(block, "results", 2, () =>
      TACTICS[name]({ limits, data })(1)(trivial(readGoal(logic, goal))),
    );
    block.push(`steps ${limits.steps.count}`);
    const blockSize = block.reduce((total, item) => total + item.length + 1, line.length + 1);
    if (blockSize > MAXIMUM_BLOCK || size + blockSize > BUDGET) return undefined;
    size += blockSize;
    lines.push(line, ...block);
    return block;
  };

  // Each problem again with fewer steps than it took, to interrupt it midway.
  const interrupted = (name: string, goal: string) => {
    const block = problem(name, Infinity, goal);
    if (block === undefined) return;
    const count = Number(block[block.length - 1].split(" ")[1]);
    for (const limit of new Set([Math.floor(count / 2), count - 1, 1]))
      if (limit >= 1 && limit < count) problem(name, limit, goal);
  };

  const run = (goal: string) => {
    for (const name of Object.keys(TACTICS)) interrupted(name, goal);
  };

  for (const goal of getSynthetic(logic)) run(showTerm(goal));

  for (const name of FIXTURES) run(`@${name}`);

  // Goals as the classical reasoner leaves them: the subgoals that safe_tac (without hypsubst)
  // leaves on the fixtures and on the logic's facts, where they have an equation among their
  // premises.
  const isEquation = (term: Term) => {
    try {
      data.destEq(data.destTrueprop(term));
      return true;
    } catch {
      return false;
    }
  };
  const derived: string[] = [];
  const derive = (goal: Term) => {
    const limits = newLimits("3000");
    try {
      const cell = safeTac({
        limits,
        claset: getClaset(logic, limits),
        data: { ...getClassicalData(logic), hypSubstTacs: [] },
      })(trivial(goal)).pull();
      if (cell === undefined) return;
      for (const prem of premsOf(cell[0])) {
        const text = showTerm(prem);
        if (text.length <= LARGE && stripAssumsHyp(prem).some(isEquation)) derived.push(text);
      }
    } catch (error) {
      if (!(error instanceof TlaIsabelleError)) throw error;
    }
  };
  for (const name of FIXTURES) derive(readGoal(logic, `@${name}`));
  const facts = [...logic.facts.values()]
    .filter((thms) => thms.length === 1)
    .map((thms) => thms[0].prop);
  const equationFacts = facts.filter(
    (prop) => stripAssumsHyp(prop).some(isEquation) && showTerm(prop).length <= LARGE,
  );
  for (const [index, prop] of facts.entries()) if (index % 17 === 0) derive(prop);
  console.error(`${derived.length} derived goals, ${equationFacts.length} equation facts`);
  for (const goal of derived) run(goal);
  for (const [index, prop] of equationFacts.entries()) if (index % 3 === 0) run(showTerm(prop));

  console.error({ problems: seen.size, lines: lines.length, size });
  return { "provers/hypsubst.txt": joinLines(lines) };
};

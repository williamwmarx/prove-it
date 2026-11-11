// testdata/kernel/{simp,simp-tac}.txt: the expectations of the Rust tests of the simplifier
// (raw_simplifier, rewriter, simplifier, object_logic). Every problem is rendered as text, parsed
// back, and solved on the parsed terms, so that the Rust tests, which parse the same text, solve the
// very same problems.
import { readStatement } from "../../src/prover/isabelle/isar/statement";
import { parseTheory } from "../../src/prover/isabelle/isar/theory";
import type { Limits } from "../../src/prover/isabelle/pure/interrupt";
import {
  destEquals,
  isEquals,
  mkImplies,
  stripImpConcl,
  stripImpPrems,
} from "../../src/prover/isabelle/pure/logic";
import { atomizePremsTac } from "../../src/prover/isabelle/pure/object-logic";
import {
  addPrems,
  addSimps,
  emptySimpset,
  extractSafeRrules,
  insertRrule,
  mkProcrule,
  type SimpContext,
} from "../../src/prover/isabelle/pure/raw-simplifier";
import { rewriteCterm, simpleProver } from "../../src/prover/isabelle/pure/rewriter";
import {
  asmFullSimpTac,
  asmLrSimpTac,
  asmSimpTac,
  normHhf,
  safeAsmFullSimpTac,
  simplify,
} from "../../src/prover/isabelle/pure/simplifier";
import type { GoalTactic } from "../../src/prover/isabelle/pure/tactical";
import {
  funT,
  looseBnos,
  maxidxOfTerm,
  mkApp,
  mkConst,
  mkFree,
  mkType,
  type Term,
} from "../../src/prover/isabelle/pure/term";
import { assume, axiomThm, trivial } from "../../src/prover/isabelle/pure/thm";
import { getFact } from "../../src/prover/isabelle/tla/classical-setup";
import { loadLogic } from "../../src/prover/isabelle/tla/logic";
import { getSimpset } from "../../src/prover/isabelle/tla/simpdata";
import { createSteps } from "../../src/prover/verdict";
import {
  attempt,
  digest,
  getFixtureNames,
  joinLines,
  many,
  one,
  parseTerm,
  readFixture,
  readGoal,
  showTerm,
  showThm,
} from "./terms";

const BUDGET = 450_000;
const MAXIMUM_BLOCK = 12_000;
const LARGE = 2500;

const ATOMIZE_RULES = [
  "Zenon.atomize_object_bAll",
  "Zenon.atomize_meta_bAll",
  "PredicateLogic.atomize_conj",
  "PredicateLogic.atomize_eq",
  "PredicateLogic.atomize_not",
  "PredicateLogic.atomize_imp",
  "PredicateLogic.atomize_all",
];

const TACTICS: Record<string, (context: SimpContext) => GoalTactic> = {
  asm_simp: asmSimpTac,
  asm_lr_simp: asmLrSimpTac,
  asm_full_simp: asmFullSimpTac,
  safe_asm_full_simp: safeAsmFullSimpTac,
};

const newLimits = (limit: string) => ({ deadline: Infinity, steps: createSteps(Number(limit)) });

const getMode = (code: string) => ({
  simprem: code[0] === "1",
  useprem: code[1] === "1",
  mutsimp: code[2] === "1",
});

const pushSteps = (lines: string[], limits: Limits) => lines.push(`steps ${limits.steps.count}`);

// The steps a problem took, or 0 where it was interrupted.
const getSteps = (lines: string[] | undefined) => {
  if (lines === undefined || lines.some((line) => line.startsWith("error Interrupt"))) return 0;
  return Number(lines[lines.length - 1].split(" ")[1]);
};

// Each problem again with half the steps it took, to interrupt it midway.
const halved = (run: (limit: number) => string[] | undefined) => {
  const count = getSteps(run(Infinity));
  if (count > 4) run(Math.floor(count / 2));
};

export const getSimpExpectations = () => {
  const files: Record<string, string[]> = { simp: [], "simp-tac": [] };
  const sizes: Record<string, number> = { simp: 0, "simp-tac": 0 };
  const seen = new Set<string>();
  let overflows = 0;

  const problem = (
    file: string,
    kind: string,
    fields: string[],
    solve: (fields: string[]) => string[],
  ): string[] | undefined => {
    const line = `> ${[kind, ...fields].join("\t")}`;
    if (seen.has(line)) return undefined;
    seen.add(line);
    if (sizes[file] > BUDGET) return undefined;
    if (process.env.TRACE) console.error(line.slice(0, 200));
    let lines: string[];
    try {
      lines = solve(fields);
    } catch (error) {
      // JavaScript's stack overflowed: the Rust port stops at its own depth, which differs.
      if (error instanceof RangeError) {
        overflows += 1;
        return undefined;
      }
      throw error;
    }
    const size = lines.reduce((total, item) => total + item.length + 1, line.length + 1);
    if (size > MAXIMUM_BLOCK || sizes[file] + size > BUDGET) return undefined;
    sizes[file] += size;
    files[file].push(line, ...lines);
    return lines;
  };

  const logic = loadLogic();
  const simpset = getSimpset(logic);
  const getContext = (limits: Limits): SimpContext => ({ limits, simpset, bounds: 0 });
  const atomizeRules = ATOMIZE_RULES.map((name) => getFact(logic, name));

  // rewrite_cterm with the simpset of the logic and the simple prover.
  const rewriteProblem = (mode: string, limit: number, goal: string) =>
    problem("simp", "rewrite", [mode, String(limit), goal], ([modeText, limitText, goalText]) => {
      const limits = newLimits(limitText);
      const lines: string[] = [];
      one(lines, "result", () =>
        rewriteCterm(
          getMode(modeText),
          simpleProver,
          getContext(limits),
          readGoal(logic, goalText),
        ),
      );
      pushSteps(lines, limits);
      return lines;
    });

  // rewrite_cterm of a goal's conclusion, with its premises assumed and added to the simpset.
  const premsProblem = (mode: string, limit: number, goal: string) =>
    problem("simp", "prems", [mode, String(limit), goal], ([modeText, limitText, goalText]) => {
      const limits = newLimits(limitText);
      const lines: string[] = [];
      const parsed = readGoal(logic, goalText);
      one(lines, "result", () => {
        const empty = getContext(limits);
        const asms = stripImpPrems(parsed)
          .filter((prem) => maxidxOfTerm(prem) === -1)
          .map(assume);
        const extended = asms.reduce(
          (current, asm) =>
            extractSafeRrules(empty, asm).reduce((inner, raw) => insertRrule(raw, inner), current),
          simpset,
        );
        const context = { ...empty, simpset: addPrems(asms, extended) };
        return rewriteCterm(getMode(modeText), simpleProver, context, stripImpConcl(parsed));
      });
      pushSteps(lines, limits);
      return lines;
    });

  const simplifyProblem = (limit: number, prop: Term) =>
    problem("simp", "simplify", [String(limit), showTerm(prop)], ([limitText, propText]) => {
      const limits = newLimits(limitText);
      const lines: string[] = [];
      one(lines, "result", () => simplify(getContext(limits), axiomThm(parseTerm(propText))));
      pushSteps(lines, limits);
      return lines;
    });

  // How a theorem becomes rewrite rules: mk, extract_safe_rrules, add_simps and mk_procrule.
  const rrulesProblem = (limit: number, prop: Term) =>
    problem("simp", "rrules", [String(limit), showTerm(prop)], ([limitText, propText]) => {
      const limits = newLimits(limitText);
      const lines: string[] = [];
      const thm = axiomThm(parseTerm(propText));
      const context = getContext(limits);
      lines.push("mk");
      attempt(lines, () => {
        for (const rew of simpset.mkRews.mk(thm, context)) lines.push(...showThm(rew));
      });
      lines.push("extract_safe_rrules");
      attempt(lines, () => {
        for (const raw of extractSafeRrules(context, thm))
          lines.push(
            `rrule ${raw.perm} ${digest(raw.lhs)} ${digest(raw.elhs)}`,
            ...showThm(raw.thm),
          );
      });
      lines.push("mk_procrule");
      attempt(lines, () => {
        for (const rrule of mkProcrule(thm))
          lines.push(
            `rrule ${rrule.perm} ${rrule.extra} ${rrule.fo} ${digest(rrule.lhs)} ${digest(rrule.elhs)}`,
            ...showThm(rrule.thm),
          );
      });
      // add_simps to the empty simpset, then rewriting the left-hand side with it.
      one(lines, "add_simps", () => {
        const empty = { limits, simpset: emptySimpset, bounds: 0 };
        const added = { ...empty, simpset: addSimps(empty, [thm]) };
        const concl = stripImpConcl(thm.prop);
        const lhs = isEquals(concl) ? destEquals(concl)[0] : thm.prop;
        return rewriteCterm(getMode("111"), simpleProver, added, lhs);
      });
      pushSteps(lines, limits);
      return lines;
    });

  const normHhfProblem = (prop: Term) =>
    problem("simp", "norm_hhf", [showTerm(prop)], ([propText]) => {
      const limits = newLimits("Infinity");
      const lines: string[] = [];
      one(lines, "result", () => normHhf(limits, axiomThm(parseTerm(propText))));
      pushSteps(lines, limits);
      return lines;
    });

  const tacticProblem = (name: string, count: number, limit: number, goal: string) =>
    problem(
      "simp-tac",
      "tactic",
      [name, String(count), String(limit), goal],
      ([nameText, countText, limitText, goalText]) => {
        const limits = newLimits(limitText);
        const lines: string[] = [];
        many(lines, "results", Number(countText), () =>
          TACTICS[nameText](getContext(limits))(1)(trivial(readGoal(logic, goalText))),
        );
        pushSteps(lines, limits);
        return lines;
      },
    );

  const atomizeProblem = (count: number, goal: string) =>
    problem("simp-tac", "atomize", [String(count), goal], ([countText, goalText]) => {
      const limits = newLimits("Infinity");
      const lines: string[] = [];
      many(lines, "results", Number(countText), () =>
        atomizePremsTac(limits, atomizeRules)(1)(trivial(readGoal(logic, goalText))),
      );
      pushSteps(lines, limits);
      return lines;
    });

  // The goals of the fixtures, their premises, conclusions and subterms, and the logic's facts.

  const fixtures = getFixtureNames().filter((name) => {
    try {
      readGoal(logic, `@${name}`);
      return true;
    } catch {
      return false;
    }
  });
  const statements = fixtures.map((name) => readStatement(logic, parseTheory(readFixture(name))));
  const fits = (term: Term) => showTerm(term).length <= LARGE;
  const parts = statements
    .flatMap((statement) => [...statement.assumptions, statement.conclusion])
    .filter(fits);
  const subterms: Term[] = [];
  const addSubterms = (term: Term) => {
    if (term.kind === "App") {
      addSubterms(term.fun);
      addSubterms(term.arg);
      if (maxidxOfTerm(term) === -1 && looseBnos(term).length === 0 && fits(term))
        subterms.push(term);
    } else if (term.kind === "Abs") addSubterms(term.body);
  };
  for (const statement of statements)
    for (const part of [...statement.assumptions, statement.conclusion]) addSubterms(part);
  const facts = [...logic.facts.values()].flat();
  const factGoals = facts
    .map((thm) => thm.prop)
    .filter((prop) => stripImpPrems(prop).length > 0 && fits(prop));

  console.error(
    `${fixtures.length} fixtures, ${parts.length} parts, ${subterms.length} subterms, ${facts.length} facts, ${factGoals.length} fact goals`,
  );

  // Goals for the neq simproc, which needs a premise x ~= y or (x = y) = FALSE.
  const constant = (name: string) => mkConst(name, logic.consts.get(name)!.type);
  const c = mkType("PredicateLogic.c");
  const tp = (term: Term) => mkApp(constant("PredicateLogic.Trueprop"), term);
  const eq = (left: Term, right: Term) => mkApp(mkApp(constant("PredicateLogic.eq"), left), right);
  const not = (term: Term) => mkApp(constant("PredicateLogic.not"), term);
  const fa = mkFree("a", c);
  const fb = mkFree("b", c);
  const fp = mkFree("P", funT(c, c));
  const falseC = constant("PredicateLogic.FALSE");
  const synthetic = [
    mkImplies(tp(not(eq(fa, fb))), tp(not(eq(fb, fa)))),
    mkImplies(tp(eq(eq(fb, fa), falseC)), tp(not(eq(fa, fb)))),
    mkImplies(tp(not(eq(fa, fb))), tp(mkApp(fp, eq(fa, fb)))),
    mkImplies(tp(not(eq(fb, fa))), tp(mkApp(fp, eq(fa, fb)))),
    mkImplies(tp(eq(eq(fa, fb), falseC)), tp(mkApp(fp, eq(fb, fa)))),
  ];
  for (const goal of synthetic) {
    for (const name of Object.keys(TACTICS)) tacticProblem(name, 2, Infinity, showTerm(goal));
    for (const mode of ["111", "110"]) premsProblem(mode, Infinity, showTerm(goal));
  }

  for (const fixture of fixtures) {
    const goal = `@${fixture}`;
    for (const mode of ["000", "100", "110", "111"])
      halved((limit) => rewriteProblem(mode, limit, goal));
    halved((limit) => premsProblem("111", limit, goal));
    halved((limit) => premsProblem("110", limit, goal));
  }
  for (const [index, part] of parts.entries()) {
    if (index % 2 === 0) halved((limit) => rewriteProblem("000", limit, showTerm(part)));
    halved((limit) => simplifyProblem(limit, part));
  }
  for (const [index, term] of subterms.entries())
    if (index % 23 === 0) rewriteProblem("000", Infinity, showTerm(term));
  for (const [index, thm] of facts.entries()) {
    if (index % 11 === 0) rrulesProblem(Infinity, thm.prop);
    if (index % 29 === 0) rewriteProblem("000", Infinity, showTerm(thm.prop));
    if (index % 37 === 0) normHhfProblem(thm.prop);
  }
  for (const [index, goal] of factGoals.entries()) if (index % 13 === 0) normHhfProblem(goal);

  for (const fixture of fixtures) {
    const goal = `@${fixture}`;
    for (const name of Object.keys(TACTICS)) halved((limit) => tacticProblem(name, 2, limit, goal));
    atomizeProblem(2, goal);
  }
  for (const [index, goal] of factGoals.entries()) {
    if (index % 5 === 0)
      halved((limit) =>
        tacticProblem(Object.keys(TACTICS)[(index / 5) % 4], 2, limit, showTerm(goal)),
      );
    if (index % 9 === 0) atomizeProblem(2, showTerm(goal));
  }

  console.error({ sizes, overflows });
  return Object.fromEntries(
    Object.entries(files).map(([name, lines]) => [`kernel/${name}.txt`, joinLines(lines)]),
  );
};

// testdata/provers/{classical,blast,iprover}.txt: the expectations of the Rust tests of
// classical.ts, intuitionistic.ts and blast. Goals: each fixture theory's statement (assumptions
// ==> conclusion), every 7th and 37th logic fact with a single theorem (only the 37th for
// best-first search), and every 3rd rule of the claset (only the 12th for best-first search);
// tactics run under a step limit, with the contexts tla/context.ts builds.
import { TlaIsabelleError } from "../../src/errors";
import { readStatement } from "../../src/prover/isabelle/isar/statement";
import { parseTheory } from "../../src/prover/isabelle/isar/theory";
import {
  type BlastContext,
  blastDepthTac,
  blastTac,
} from "../../src/prover/isabelle/provers/blast/blast";
import {
  addUnsafeDest,
  addUnsafeIntro,
  appWrappers,
  clarifyTac,
  firstBestTac,
  inst0StepTac,
  instpStepTac,
  safeTac,
  unsafeStepTac,
  withClaset,
} from "../../src/prover/isabelle/provers/classical";
import { blastHypSubstTac } from "../../src/prover/isabelle/provers/hypsubst";
import type { Limits } from "../../src/prover/isabelle/pure/interrupt";
import { listImplies } from "../../src/prover/isabelle/pure/logic";
import { emptyNet } from "../../src/prover/isabelle/pure/net";
import { insertTaggedBrl, type NetPair } from "../../src/prover/isabelle/pure/tactic";
import { appendTac } from "../../src/prover/isabelle/pure/tactical";
import type { Term } from "../../src/prover/isabelle/pure/term";
import { trivial } from "../../src/prover/isabelle/pure/thm";
import {
  getClaset,
  getClassicalData,
  getFact,
  getHypsubstData,
} from "../../src/prover/isabelle/tla/classical-setup";
import type { LogicExtraNetItem, LogicNetPair } from "../../src/prover/isabelle/tla/logic";
import { loadLogic } from "../../src/prover/isabelle/tla/logic";
import { type ContextRule, proverTac } from "../../src/prover/isabelle/tools/intuitionistic";
import { createSteps } from "../../src/prover/verdict";
import { attempt, digest, getFixtureNames, joinLines, many, readFixture } from "./terms";

const LIMIT = 2000;

const ATOMIZE_RULES = [
  "Zenon.atomize_object_bAll",
  "Zenon.atomize_meta_bAll",
  "PredicateLogic.atomize_conj",
  "PredicateLogic.atomize_eq",
  "PredicateLogic.atomize_not",
  "PredicateLogic.atomize_imp",
  "PredicateLogic.atomize_all",
];

// The problems on which the TypeScript runs for seconds or minutes before it reaches the step
// limit, if it ever does.
const SKIP = new Set([
  "best fact:Tuples.seqInduct",
  "best thy:Paxos-109",
  "iprover fact:Functions.DOMAIN",
  "iprover fact:Tuples.appendElt",
  "iprover fact:IntegerDivision.times_div_self2",
]);

// The kinds of problem, each with the file it goes to; `add` is add_unsafe_intro and
// add_unsafe_dest. The Rust tests read each file's kinds in this order.
export const PROVER_KINDS: readonly (readonly [string, string])[] = [
  ["safe", "classical"],
  ["clarify", "classical"],
  ["steps", "classical"],
  ["best", "classical"],
  ["add", "classical"],
  ["blast", "blast"],
  ["depth", "blast"],
  ["iprover", "iprover"],
];

// The JavaScript stack overflowing ends a proof as the Rust port's depth bound does.
const showProverError = (error: unknown) => {
  if (error instanceof TlaIsabelleError) return `error ${error.exception}: ${error.message}`;
  if (error instanceof RangeError) return "error Stack";
  throw error;
};

// Net.content lists a leaf's items newest first, so inserting them in reverse rebuilds the leaf.
const toNetPair = (pair: LogicNetPair<LogicExtraNetItem>) => {
  const insertAll = (items: readonly LogicExtraNetItem[], netpair: NetPair<ContextRule>) =>
    items.reduceRight((result, item) => insertTaggedBrl(item, result), netpair);
  return insertAll(pair.elim, insertAll(pair.intro, { intro: emptyNet, elim: emptyNet }));
};

export const getProverExpectations = (kind: string) => {
  const logic = loadLogic();
  const atomizeRules = ATOMIZE_RULES.map((name) => getFact(logic, name));
  const safeRules = toNetPair(logic.contextRules.bang);
  const plainRules = toNetPair(logic.contextRules.plain);

  const getContexts = (limits: Limits) => {
    const classical = {
      limits,
      claset: getClaset(logic, limits),
      data: getClassicalData(logic),
    };
    const blast: BlastContext = {
      limits,
      claset: classical.claset,
      consts: logic.consts,
      elimTemplates: new WeakMap(),
      introTemplates: new WeakMap(),
      data: {
        trueprop: "PredicateLogic.Trueprop",
        equalityName: "PredicateLogic.eq",
        notName: "PredicateLogic.not",
        notE: getFact(logic, "PredicateLogic.notE"),
        ccontr: getFact(logic, "PredicateLogic.contradiction"),
        hypSubstTac: (blastLimits: Limits) =>
          blastHypSubstTac({ limits: blastLimits, data: getHypsubstData(logic) }),
        classical: getFact(logic, "PredicateLogic.classical"),
        atomize: atomizeRules,
      },
    };
    const intuitionistic = { limits, safeRules, rules: plainRules };
    return { classical, blast, intuitionistic };
  };

  // The goals, by the name the Rust test finds them by; best-first search, the slowest, gets the
  // sparse ones only.
  const goals: [string, Term][] = [];
  const sparse = new Set<string>();
  for (const fixture of getFixtureNames()) {
    const statement = (() => {
      try {
        return readStatement(logic, parseTheory(readFixture(fixture)));
      } catch (error) {
        if (error instanceof TlaIsabelleError) return undefined;
        throw error;
      }
    })();
    if (statement === undefined) continue;
    goals.push([`thy:${fixture}`, listImplies(statement.assumptions, statement.conclusion)]);
    sparse.add(`thy:${fixture}`);
  }
  let single = 0;
  for (const [name, thms] of logic.facts) {
    if (thms.length !== 1) continue;
    if (single % 7 === 0 || single % 37 === 0) goals.push([`fact:${name}`, thms[0].prop]);
    if (single % 37 === 0) sparse.add(`fact:${name}`);
    single += 1;
  }
  const claset = logic.claset;
  const rules = [
    ...claset.safeIs.map((rule, index) => [`rule:safeIs:${index}`, rule.rule] as const),
    ...claset.safeEs.map((rule, index) => [`rule:safeEs:${index}`, rule.rule] as const),
    ...claset.unsafeIs.map((rule, index) => [`rule:unsafeIs:${index}`, rule.rule] as const),
    ...claset.unsafeEs.map((rule, index) => [`rule:unsafeEs:${index}`, rule.rule] as const),
  ];
  for (const [index, [name, rule]] of rules.entries()) {
    if (index % 3 === 0) goals.push([name, rule.prop]);
    if (index % 12 === 0) sparse.add(name);
  }

  const run = (goal: Term, limits: Limits) => {
    const contexts = getContexts(limits);
    const state = trivial(goal);
    switch (kind) {
      case "safe":
        return safeTac(contexts.classical)(state);
      case "clarify":
        return clarifyTac(contexts.classical)(1)(state);
      case "best":
        return firstBestTac(contexts.classical, atomizeRules)(1)(state);
      case "steps":
        return appendTac(
          inst0StepTac(contexts.classical)(1),
          appWrappers(contexts.classical, (index) =>
            appendTac(
              instpStepTac(contexts.classical)(index),
              unsafeStepTac(contexts.classical)(index),
            ),
          )(1),
        )(state);
      case "blast":
        return blastTac(contexts.blast)(1)(state);
      case "depth":
        return blastDepthTac(contexts.blast, 2)(1)(state);
      case "iprover":
        return proverTac(contexts.intuitionistic)(1)(state);
    }
    throw new Error(kind);
  };

  const lines: string[] = [];
  // add_unsafe_intro and add_unsafe_dest of facts, then an unsafe step with the new claset.
  if (kind === "add")
    for (const [name, goal] of goals) {
      if (!name.startsWith("fact:")) continue;
      for (const addition of ["intro", "dest"]) {
        const limits = { deadline: Infinity, steps: createSteps(LIMIT) };
        const block: string[] = [];
        const context = getContexts(limits).classical;
        const fact = logic.facts.get(name.slice("fact:".length))![0];
        attempt(
          block,
          () => {
            const added =
              addition === "intro" ? addUnsafeIntro(context, fact) : addUnsafeDest(context, fact);
            const entries = addition === "intro" ? added.unsafeIs : added.unsafeEs;
            block.push(`count ${entries.length}`);
            const entry = entries[0];
            block.push(`internal ${digest(entry.internal.prop)}`, `dup ${digest(entry.dup.prop)}`);
            for (const swapped of entry.swapped) block.push(`swapped ${digest(swapped.prop)}`);
            for (const swapped of entry.dupSwapped)
              block.push(`dupSwapped ${digest(swapped.prop)}`);
            many(
              block,
              "results",
              2,
              () => unsafeStepTac(withClaset(context, added))(1)(trivial(goal)),
              showProverError,
            );
          },
          showProverError,
        );
        block.push(`steps ${limits.steps.count}`);
        lines.push(`> ${addition}\t${name}\t${LIMIT}`, ...block);
      }
    }
  else
    for (const [name, goal] of goals) {
      if (SKIP.has(`${kind} ${name}`)) continue;
      if (kind === "best" && !sparse.has(name)) continue;
      const limits = { deadline: Infinity, steps: createSteps(LIMIT) };
      const block: string[] = [];
      if (process.env.TRACE) console.error("start", kind, name);
      const start = performance.now();
      many(block, "results", 2, () => run(goal, limits), showProverError);
      block.push(`steps ${limits.steps.count}`);
      if (process.env.TRACE)
        console.error(kind, name, Math.round(performance.now() - start), block.at(-1));
      lines.push(`> ${kind}\t${name}\t${LIMIT}`, ...block);
    }

  const file = PROVER_KINDS.find((entry) => entry[0] === kind)?.[1];
  if (file === undefined) throw new Error(`unknown kind ${kind}`);
  return { [`provers/${file}.txt`]: joinLines(lines) };
};

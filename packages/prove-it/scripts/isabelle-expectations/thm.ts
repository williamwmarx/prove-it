// testdata/kernel/{thm,resolve,tactic,rules}.txt: the expectations of the Rust tests of the
// kernel's theorems and tactics (thm, bicompose, drule, conv, variable, tactical, tactic, goal,
// search). Every problem is rendered as text, parsed back, and solved on the parsed terms, so that
// the Rust tests, which parse the same text, solve the very same problems.
import { readStatement } from "../../src/prover/isabelle/isar/statement";
import { parseTheory } from "../../src/prover/isabelle/isar/theory";
import { fconvRule, gconvRule, paramsConv, premsConv } from "../../src/prover/isabelle/pure/conv";
import {
  compIncr,
  compNoFlatten,
  forallIntrVars,
  genAll,
  isNormHhf,
  makeElim,
  protectI,
  thinRl,
  zeroVarIndexes,
} from "../../src/prover/isabelle/pure/drule";
import { preferGoal, selectGoal } from "../../src/prover/isabelle/pure/goal";
import type { Limits } from "../../src/prover/isabelle/pure/interrupt";
import {
  allConst,
  listImplies,
  mkImplies,
  stripAssumsConcl,
  stripAssumsHyp,
  stripImpConcl,
  stripParams,
} from "../../src/prover/isabelle/pure/logic";
import { emptyNet } from "../../src/prover/isabelle/pure/net";
import { isPattern } from "../../src/prover/isabelle/pure/pattern";
import { bestFirst, deepen } from "../../src/prover/isabelle/pure/search";
import {
  emptyTable,
  fastIndexnameOrd,
  type IndexKey,
  updateTable,
} from "../../src/prover/isabelle/pure/table";
import {
  assumeTac,
  bimatchFromNetsTac,
  biresolveFromNetsTac,
  composeTac,
  dresolveTac,
  ematchTac,
  eqAssumeTac,
  eresolveTac,
  flexflexTac,
  insertTaggedBrl,
  matchTac,
  type NetPair,
  resolveTac,
  rotateTac,
  type TaggedRule,
} from "../../src/prover/isabelle/pure/tactic";
import {
  allGoals,
  allTac,
  appendGoal,
  appendTac,
  changed,
  changedProp,
  depthSolve,
  determ,
  every,
  first,
  firstGoal,
  firstGoalTac,
  type GoalTactic,
  hasFewerPrems,
  noTac,
  orElse,
  orElseGoal,
  repeatAllNew,
  repeatDeterm,
  repeatDeterm1,
  repeatDetermN,
  type Tactic,
  thenAllNew,
  thenElse,
  thenGoal,
  thenTac,
  tryTac,
} from "../../src/prover/isabelle/pure/tactical";
import {
  addVars,
  couldUnify,
  foldAtyps,
  foldTypes,
  funT,
  mkAbs,
  mkApp,
  mkBound,
  mkConst,
  mkFree,
  mkType,
  mkVar,
  propT,
  sizeOfTerm,
  type Term,
  type Typ,
  type Var,
} from "../../src/prover/isabelle/pure/term";
import {
  abstractRule,
  assume,
  assumption,
  axiomThm,
  betaConversion,
  bicompose,
  biresolution,
  combination,
  conclOf,
  eqAssumption,
  equalElim,
  etaConversion,
  flexflexRule,
  forallElim,
  forallIntr,
  generalize,
  impliesElim,
  impliesIntr,
  incrIndexesThm,
  instantiate,
  instantiateTypes,
  majorPremOf,
  nprems,
  permutePrems,
  premOf,
  premsOf,
  reflexive,
  renamedProp,
  rotateRule,
  rsn,
  symmetric,
  type Thm,
  transitive,
  trivial,
} from "../../src/prover/isabelle/pure/thm";
import type { TyEnv } from "../../src/prover/isabelle/pure/type";
import { trade } from "../../src/prover/isabelle/pure/variable";
import { loadLogic } from "../../src/prover/isabelle/tla/logic";
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
  showTerm,
  showThm,
} from "./terms";

const BUDGET = 440_000;
const MAXIMUM_BLOCK: Record<string, number> = { thm: 20_000, resolve: 10_000, tactic: 8_000 };
const SMALL = 1200;

const betaConv = (term: Term) => betaConversion(true, term);

// A rule of a tactic problem: its tag in the nets, i, e or d (intro, elim or dest), and itself.
interface Rule {
  readonly tag: number;
  readonly kind: string;
  readonly thm: Thm;
}

const tokenize = (text: string) =>
  text
    .replaceAll("(", " ( ")
    .replaceAll(")", " ) ")
    .split(" ")
    .filter((token) => token !== "");

const sizeOfThm = (thm: Thm) =>
  thm.tpairs.reduce(
    (size, pair) => size + 2 + sizeOfTerm(pair[0]) + sizeOfTerm(pair[1]),
    sizeOfTerm(thm.prop),
  );

// Tactic expressions: see the Rust test in pure/tactic.rs.
const buildTactics = (limits: Limits, rules: Rule[], text: string) => {
  const tokens = tokenize(text);
  let position = 0;
  const next = () => tokens[position++];
  const number = () => Number(next());
  const getRulesOf = (kind: string) =>
    rules.filter((rule) => rule.kind === kind).map((rule) => rule.thm);
  const netpair = rules
    .filter((rule) => rule.kind !== "d")
    .map((rule) => ({ tag: rule.tag, isElim: rule.kind === "e", rule: rule.thm }))
    .reduceRight<NetPair<TaggedRule>>((result, tagged) => insertTaggedBrl(tagged, result), {
      intro: emptyNet,
      elim: emptyNet,
    });
  const close = () => {
    if (next() !== ")") throw new Error(`expected ) in ${text}`);
  };
  const list = <Item>(parse: () => Item): Item[] => {
    const items: Item[] = [];
    while (tokens[position] !== ")") items.push(parse());
    return items;
  };
  const tactic = (): Tactic => {
    const token = next();
    if (token === "all") return allTac;
    if (token === "no") return noTac;
    if (token === "flex") return flexflexTac(limits);
    if (token !== "(") throw new Error(`bad tactic ${token}`);
    const head = next();
    const result = (() => {
      switch (head) {
        case "then":
          return thenTac(tactic(), tactic());
        case "orelse":
          return orElse(tactic(), tactic());
        case "append":
          return appendTac(tactic(), tactic());
        case "thenelse":
          return thenElse(tactic(), tactic(), tactic());
        case "determ":
          return determ(tactic());
        case "try":
          return tryTac(tactic());
        case "every":
          return every(list(tactic));
        case "first":
          return first(list(tactic));
        case "repeat":
          return repeatDeterm(tactic());
        case "repeat1":
          return repeatDeterm1(tactic());
        case "repeatn":
          return repeatDetermN(number(), tactic());
        case "changed":
          return changed(tactic());
        case "changedprop":
          return changedProp(tactic());
        case "allgoals":
          return allGoals(goal());
        case "firstgoal":
          return firstGoalTac(goal());
        case "depthsolve":
          return depthSolve(tactic());
        case "bestfirst":
          return bestFirst(hasFewerPrems(1), sizeOfThm, tactic());
        case "at": {
          const index = number();
          return goal()(index);
        }
        default:
          throw new Error(`bad tactic ${head}`);
      }
    })();
    close();
    return result;
  };
  const goal = (): GoalTactic => {
    const token = next();
    switch (token) {
      case "rtac":
        return resolveTac(limits, getRulesOf("i"));
      case "etac":
        return eresolveTac(limits, getRulesOf("e"));
      case "dtac":
        return dresolveTac(limits, getRulesOf("d"));
      case "mtac":
        return matchTac(limits, getRulesOf("i"));
      case "ematch":
        return ematchTac(limits, getRulesOf("e"));
      case "atac":
        return assumeTac(limits);
      case "eqatac":
        return eqAssumeTac;
      case "net":
        return biresolveFromNetsTac(limits, netpair);
      case "bimatchnet":
        return bimatchFromNetsTac(limits, netpair);
      case "(":
        break;
      default:
        throw new Error(`bad goal tactic ${token}`);
    }
    const head = next();
    const result = (() => {
      switch (head) {
        case "rtacn":
          return resolveTac(limits, [rules[number()].thm]);
        case "compose":
          return composeTac(limits, false, rules[number()].thm, number());
        case "ecompose":
          return composeTac(limits, true, rules[number()].thm, number());
        case "rot":
          return rotateTac(number());
        case "thenG":
          return thenGoal(goal(), goal());
        case "orelseG":
          return orElseGoal(goal(), goal());
        case "appendG":
          return appendGoal(goal(), goal());
        case "firstG":
          return firstGoal(list(goal));
        case "thenallnew":
          return thenAllNew(goal(), goal());
        case "repeatallnew":
          return repeatAllNew(goal());
        case "select":
          return selectGoal(tactic());
        case "prefer":
          return preferGoal(tactic());
        case "deepen": {
          const increment = number();
          const limit = number();
          const start = number();
          const inner = goal();
          return deepen(
            increment,
            limit,
            (depth) => (index) => repeatDetermN(depth, inner(index)),
            start,
          );
        }
        default:
          throw new Error(`bad goal tactic ${head}`);
      }
    })();
    close();
    return result;
  };
  const result = tactic();
  if (position !== tokens.length) throw new Error(`trailing tokens in ${text}`);
  return result;
};

const EXPRESSIONS = [
  "(at 1 rtac)",
  "(at 1 etac)",
  "(at 1 dtac)",
  "(at 1 mtac)",
  "(at 1 ematch)",
  "(at 1 atac)",
  "(at 1 eqatac)",
  "(at 1 net)",
  "(at 1 bimatchnet)",
  "(at 1 (rot 1))",
  "(at 1 (rot -1))",
  "(at 2 rtac)",
  "flex",
  "(then (at 1 rtac) (allgoals atac))",
  "(at 1 (thenallnew net atac))",
  "(at 1 (repeatallnew rtac))",
  "(depthsolve (firstgoal (orelseG atac net)))",
  "(bestfirst (firstgoal (appendG atac net)))",
  "(every (at 1 net) (allgoals (firstG eqatac atac)))",
  "(orelse (at 1 etac) (at 1 rtac))",
  "(append (at 1 etac) (at 1 rtac))",
  "(thenelse (at 1 etac) (allgoals atac) (at 1 rtac))",
  "(determ (at 1 net))",
  "(try (at 1 etac))",
  "(repeat (firstgoal net))",
  "(repeatn 3 (firstgoal net))",
  "(repeat1 (firstgoal (orelseG atac net)))",
  "(changed (allgoals atac))",
  "(changedprop (try (allgoals eqatac)))",
  "(first (at 1 etac) (at 1 dtac) (at 1 rtac))",
  "(then (at 1 rtac) (at 2 (select (try (at 1 net)))))",
  "(then (at 1 rtac) (at 2 (prefer (try (at 1 net)))))",
  "(at 1 (select (repeatn 2 (firstgoal net))))",
  "(at 1 (deepen 1 3 1 net))",
  "(at 1 (compose 0 1))",
  "(at 1 (ecompose 0 1))",
  "(at 1 (thenG (rtacn 0) atac))",
  "(at 1 (appendG etac dtac))",
  "(every (at 1 rtac) (at 1 atac) (allgoals net))",
];

const toRules = (picked: { intro: Thm[]; elim: Thm[]; dest: Thm[] }): Rule[] =>
  [
    ...picked.intro.map((thm) => ({ kind: "i", thm, subgoals: nprems(thm) })),
    ...picked.elim.map((thm) => ({ kind: "e", thm, subgoals: nprems(thm) - 1 })),
    ...picked.dest.map((thm) => ({ kind: "d", thm, subgoals: 0 })),
  ].map((rule, index) => ({
    tag: 1000000 * rule.subgoals + index,
    kind: rule.kind,
    thm: rule.thm,
  }));

export const getThmExpectations = () => {
  const files: Record<string, string[]> = { thm: [], resolve: [], tactic: [] };
  const sizes: Record<string, number> = { thm: 0, resolve: 0, tactic: 0 };
  const seen = new Set<string>();

  const problem = (
    file: string,
    kind: string,
    fields: string[],
    solve: (fields: string[]) => string[] | undefined,
  ) => {
    const line = `> ${[kind, ...fields].join("\t")}`;
    if (seen.has(line)) return false;
    seen.add(line);
    if (process.env.TRACE) console.error(line.slice(0, 300));
    if (sizes[file] > BUDGET) return false;
    const lines = solve(fields);
    const size =
      lines === undefined
        ? 0
        : lines.reduce((total, item) => total + item.length + 1, line.length + 1);
    if (process.env.TRACE) console.error(file, size, sizes[file]);
    if (lines === undefined || size > MAXIMUM_BLOCK[file] || sizes[file] + size > BUDGET)
      return false;
    sizes[file] += size;
    files[file].push(line, ...lines);
    return true;
  };

  // The rules the problems refer to by number, in rules.txt.
  const ruleTexts: string[] = [];
  const ruleIds = new Map<string, number>();
  const getRuleId = (term: Term) => {
    const text = showTerm(term);
    const known = ruleIds.get(text);
    if (known !== undefined) return known;
    ruleIds.set(text, ruleTexts.length);
    ruleTexts.push(text);
    return ruleTexts.length - 1;
  };
  const getRule = (id: string) => axiomThm(parseTerm(ruleTexts[Number(id)]));

  const i = mkType("i");

  // The kernel's rules, Drule's, conversions and Variable.trade on one proposition.
  const ruleProblem = (term: Term) =>
    problem("thm", "rule", [showTerm(term)], ([text]) => {
      const parsed = parseTerm(text);
      const lines: string[] = [];
      const limits = { deadline: Infinity, steps: createSteps() };
      const thm = axiomThm(parsed);
      one(lines, "axiom", () => thm);
      lines.push(`nprems ${nprems(thm)}`);
      lines.push("major_prem_of");
      attempt(lines, () => lines.push(digest(majorPremOf(thm))));
      lines.push("prem_of");
      attempt(lines, () => lines.push(digest(premOf(thm, 1))));
      attempt(lines, () => lines.push(digest(premOf(thm, 0))));
      one(lines, "trivial", () => trivial(parsed));
      one(lines, "assume", () => assume(parsed));
      const firstPremise = premsOf(thm)[0] ?? parsed;
      one(lines, "implies_intr", () => impliesIntr(firstPremise, thm));
      one(lines, "implies_elim", () => impliesElim(trivial(parsed), thm));
      one(lines, "implies_elim_bad", () => impliesElim(thm, thm));
      one(lines, "incr_indexes", () => incrIndexesThm(2, thm));
      one(lines, "permute_prems 0 1", () => permutePrems(0, 1, thm));
      one(lines, "permute_prems 1 -1", () => permutePrems(1, -1, thm));
      one(lines, "permute_prems 0 -5", () => permutePrems(0, -5, thm));
      one(lines, "rotate_rule 1", () => rotateRule(1, 1, trivial(parsed)));
      one(lines, "rotate_rule -1", () => rotateRule(-1, 1, trivial(parsed)));
      one(lines, "eq_assumption", () => eqAssumption(1, trivial(parsed)));
      many(lines, "assumption", 3, () => assumption(limits, 1, trivial(parsed)));
      many(lines, "flexflex", 3, () => flexflexRule(limits, thm));
      const vars = addVars(parsed, []);
      const insts = vars.map((variable) => ({
        variable,
        term: mkFree(`f_${variable.name}`, variable.type),
      }));
      const instantiated = instantiate(insts, thm);
      one(lines, "instantiate", () => instantiated);
      one(lines, "instantiate_bad", () =>
        instantiate(
          insts.map((inst) => ({ ...inst, term: mkFree("bad", mkType("bad")) })),
          thm,
        ),
      );
      one(lines, "generalize", () =>
        generalize(
          vars.map((variable) => `f_${variable.name}`),
          thm.maxidx + 1,
          instantiated,
        ),
      );
      const tvars = foldTypes(
        (type, table: TyEnv) =>
          foldAtyps(
            (atom, inner) => (atom.kind === "TVar" ? updateTable(inner, atom, mkType("c")) : inner),
            type,
            table,
          ),
        parsed,
        emptyTable<IndexKey, Typ>(fastIndexnameOrd),
      );
      one(lines, "instantiate_types", () => instantiateTypes(tvars, thm));
      const quantified = forallIntrVars(thm);
      one(lines, "forall_intr_vars", () => quantified);
      one(lines, "gen_all", () => genAll(quantified));
      one(lines, "zero_var_indexes", () => zeroVarIndexes(incrIndexesThm(3, thm)));
      one(lines, "make_elim", () => makeElim(thm));
      one(lines, "comp_incr", () => compIncr(thm, thinRl));
      one(lines, "comp_no_flatten", () => compNoFlatten(thm, nprems(thm), 1, protectI));
      lines.push(`is_norm_hhf ${isNormHhf(false, parsed)} ${isNormHhf(true, parsed)}`);
      one(lines, "beta", () => betaConversion(true, parsed));
      one(lines, "beta_redex", () => betaConversion(false, parsed));
      one(lines, "eta", () => etaConversion(parsed));
      one(lines, "symmetric", () => symmetric(reflexive(parsed)));
      one(lines, "transitive", () => transitive(reflexive(parsed), symmetric(reflexive(parsed))));
      one(lines, "equal_elim", () => equalElim(reflexive(parsed), thm));
      const domain =
        quantified.prop.kind === "App" && quantified.prop.arg.kind === "Abs"
          ? quantified.prop.arg.type
          : i;
      one(lines, "forall_elim", () => forallElim(mkFree("t", domain), quantified));
      const free = insts.length > 0 ? insts[0].term : mkFree("t", i);
      one(lines, "forall_intr", () => forallIntr(free, instantiated));
      one(lines, "forall_intr_hyp", () =>
        forallIntr(free, impliesElim(trivial(instantiated.prop), assume(instantiated.prop))),
      );
      one(lines, "abstract_rule", () => abstractRule("z", free, reflexive(instantiated.prop)));
      one(lines, "combination", () =>
        parsed.kind === "App"
          ? combination(reflexive(parsed.fun), reflexive(parsed.arg))
          : combination(reflexive(parsed), reflexive(parsed)),
      );
      one(lines, "renamed_prop", () => renamedProp(parsed, thm));
      const wrapped = listImplies(
        premsOf(thm).map((premise) => mkApp(mkAbs("u", propT, mkBound(0)), premise)),
        conclOf(thm),
      );
      one(lines, "fconv_prems", () => fconvRule(premsConv(betaConv), axiomThm(wrapped)));
      one(lines, "fconv_params", () => fconvRule(paramsConv(betaConv), axiomThm(wrapped)));
      const closedGoal = forallIntrVars(axiomThm(wrapped)).prop;
      one(lines, "gconv", () => gconvRule(paramsConv(premsConv(betaConv)), 1, trivial(closedGoal)));
      one(lines, "gconv_bad", () => gconvRule(betaConv, 2, trivial(closedGoal)));
      lines.push("trade");
      attempt(lines, () => {
        for (const result of trade(
          (fixed) => [fixed, trivial(fixed.prop), incrIndexesThm(1, fixed)],
          thm,
        ))
          lines.push(...showThm(result));
      });
      lines.push(`steps ${limits.steps.count}`);
      return lines;
    });

  // Resolution of a rule with goal 1 of a state, in each of the kernel's ways.
  const resolveProblem = (count: number, rule: Term, state: Term) =>
    problem(
      "resolve",
      "resolve",
      [String(count), String(getRuleId(rule)), showTerm(state)],
      ([countText, ruleText, stateText]) => {
        const innerCount = Number(countText);
        const innerRule = getRule(ruleText);
        const innerState = axiomThm(parseTerm(stateText));
        const lines: string[] = [];
        const limits = { deadline: Infinity, steps: createSteps() };
        const getBrules = (isElim: boolean) => [{ isElim, rule: innerRule }];
        many(lines, "intro", innerCount, () =>
          biresolution(limits, false, getBrules(false), 1, innerState),
        );
        many(lines, "elim", innerCount, () =>
          biresolution(limits, false, getBrules(true), 1, innerState),
        );
        many(lines, "match", innerCount, () =>
          biresolution(limits, true, getBrules(false), 1, innerState),
        );
        many(lines, "ematch", innerCount, () =>
          biresolution(limits, true, getBrules(true), 1, innerState),
        );
        const compose = (isElim: boolean, isIncremented: boolean) =>
          bicompose(
            limits,
            { flatten: true, match: false, incremented: isIncremented },
            { isElim, rule: innerRule, subgoals: nprems(innerRule) },
            1,
            innerState,
          );
        many(lines, "compose", innerCount, () => compose(false, false));
        many(lines, "ecompose", innerCount, () => compose(true, false));
        many(lines, "compose_incremented", innerCount, () => compose(false, true));
        one(lines, "rsn", () => rsn(innerRule, 1, innerState));
        lines.push(`steps ${limits.steps.count}`);
        return lines;
      },
    );

  const tacticProblem = (
    count: number,
    stepLimit: number,
    expression: string,
    state: Term,
    rules: Rule[],
  ) =>
    problem(
      "tactic",
      "tactic",
      [
        String(count),
        String(stepLimit),
        expression,
        showTerm(state),
        ...rules.map((rule) => `${rule.tag}|${rule.kind}|${getRuleId(rule.thm.prop)}`),
      ],
      ([countText, limitText, expressionText, stateText, ...ruleFields]) => {
        const lines: string[] = [];
        const limits = { deadline: Infinity, steps: createSteps(Number(limitText)) };
        const parsed = ruleFields.map((field) => {
          const [tag, kind, id] = field.split("|");
          return { tag: Number(tag), kind, thm: getRule(id) };
        });
        many(lines, "results", Number(countText), () =>
          buildTactics(limits, parsed, expressionText)(trivial(parseTerm(stateText))),
        );
        lines.push(`steps ${limits.steps.count}`);
        return lines;
      },
    );

  // Problems on the Isabelle/TLA+ logic and the fixtures

  const logic = loadLogic();
  const statements = getFixtureNames().flatMap((name) => {
    try {
      return [readStatement(logic, parseTheory(readFixture(name)))];
    } catch {
      return [];
    }
  });

  const isSmall = (term: Term) => showTerm(term).length <= SMALL;
  const goals = statements
    .map((statement) => listImplies(statement.assumptions, statement.conclusion))
    .filter(isSmall)
    .sort((left, right) => showTerm(left).length - showTerm(right).length);
  const intros = [...logic.claset.safeIs, ...logic.claset.unsafeIs].map((rule) => rule.rule);
  const elims = [...logic.claset.safeEs, ...logic.claset.unsafeEs].map((rule) => rule.rule);
  const dests = [...logic.facts.entries()]
    .filter(([name]) => /(D|D1|D2|spec)$/.test(name))
    .flatMap(([, thms]) => thms)
    .filter((thm) => nprems(thm) > 0);

  // Goals with parameters and premises: the premises of intro rules.
  const ruleGoals = intros
    .flatMap((rule) => premsOf(rule))
    .filter((premise) => stripParams(premise).length > 0 || stripAssumsHyp(premise).length > 0);

  const facts = [...logic.facts.values()].flat();
  for (const goal of goals.slice(0, 6)) ruleProblem(goal);
  for (const goal of ruleGoals.slice(0, 10)) ruleProblem(goal);
  for (const thm of [
    ...intros.slice(0, 40),
    ...elims.slice(0, 30),
    ...dests.slice(0, 15),
    ...facts.filter((_, index) => index % 40 === 0),
  ])
    ruleProblem(thm.prop);

  const getRelevant = (goal: Term) => {
    const concl = stripAssumsConcl(goal);
    const hyps = stripAssumsHyp(goal);
    const intro = intros.filter((rule) => couldUnify(conclOf(rule), concl)).slice(0, 6);
    const elim = elims
      .filter((rule) => hyps.some((hyp) => couldUnify(majorPremOf(rule), hyp)))
      .slice(0, 5);
    const dest = dests
      .filter((rule) => hyps.some((hyp) => couldUnify(premsOf(rule)[0], hyp)))
      .slice(0, 3);
    return { intro, elim, dest };
  };

  // Flex-flex problems, whose unifiers keep flex-flex pairs.
  const c = mkType("PredicateLogic.c");
  const tp = (term: Term) => mkApp(mkConst("PredicateLogic.Trueprop", funT(c, propT)), term);
  const cc = funT(c, c);
  const va = (name: string, type: Typ): Var => mkVar(name, 0, type);
  const ca = mkConst("a", c);
  const flexRules = [
    tp(mkApp(va("P", cc), va("x", c))),
    mkImplies(tp(mkApp(va("Q", cc), va("x", c))), tp(mkApp(va("P", cc), va("x", c)))),
    mkImplies(
      tp(mkApp(va("Q", cc), va("x", c))),
      tp(mkApp(va("Q", cc), mkApp(va("P", cc), va("x", c)))),
    ),
  ];
  const flexGoals = [
    tp(mkApp(va("F", cc), ca)),
    mkApp(allConst(c), mkAbs("y", c, tp(mkApp(va("F", cc), mkBound(0))))),
    mkImplies(tp(mkApp(va("G", cc), ca)), tp(mkApp(va("F", cc), ca))),
  ];
  for (const goal of flexGoals) {
    for (const rule of flexRules) {
      resolveProblem(3, rule, trivial(goal).prop);
      for (const expression of [
        "(then (at 1 rtac) flex)",
        "(then (at 1 rtac) (allgoals atac))",
        "(at 1 (thenallnew rtac atac))",
        "(then (at 1 rtac) (then (at 1 rtac) flex))",
      ])
        tacticProblem(3, 300, expression, goal, [{ tag: 0, kind: "i", thm: axiomThm(rule) }]);
    }
  }

  // Rules whose conclusion is not a pattern: Huet's search, with flex-flex pairs left over.
  const nonPatternRules = facts.filter((rule) => !isPattern(stripImpConcl(rule.prop)));
  const huetPairs: [Thm, Term][] = [];
  for (const rule of nonPatternRules) {
    let perRule = 0;
    for (const goal of [...goals, ...ruleGoals]) {
      if (perRule >= 2 || huetPairs.length >= 60) break;
      if (!couldUnify(conclOf(rule), stripAssumsConcl(goal))) continue;
      if (!resolveProblem(3, rule.prop, trivial(goal).prop)) continue;
      huetPairs.push([rule, goal]);
      perRule += 1;
    }
  }

  let resolveCount = 0;
  for (const goal of [...goals, ...ruleGoals.slice(0, 80)]) {
    const state = trivial(goal).prop;
    const rules = getRelevant(goal);
    for (const rule of [
      ...rules.intro.slice(0, 3),
      ...rules.elim.slice(0, 2),
      ...rules.dest.slice(0, 1),
    ]) {
      if (resolveCount >= 400) break;
      if (resolveProblem(3, rule.prop, state)) resolveCount += 1;
    }
  }

  let tacticCount = 0;
  for (const [rule, goal] of huetPairs)
    for (const expression of [
      "(then (at 1 rtac) flex)",
      "(at 1 (thenallnew rtac atac))",
      "(then (at 1 rtac) (allgoals atac))",
    ])
      tacticProblem(3, 300, expression, goal, [{ tag: 0, kind: "i", thm: rule }]);
  const tacticGoals = [...ruleGoals.slice(0, 40), ...goals].sort(
    (left, right) => showTerm(left).length - showTerm(right).length,
  );
  for (const [goalIndex, goal] of tacticGoals.entries()) {
    const rules = toRules(getRelevant(goal));
    if (rules.length === 0) continue;
    for (const [expressionIndex, expression] of EXPRESSIONS.entries()) {
      // Every goal gets the basic tactics; the others take turns.
      if (expressionIndex >= 12 && (expressionIndex + goalIndex) % 2 !== 0) continue;
      if (tacticCount >= 1500) break;
      if (tacticProblem(3, 300, expression, goal, rules)) tacticCount += 1;
    }
  }

  return {
    "kernel/rules.txt": joinLines(ruleTexts),
    ...Object.fromEntries(
      Object.entries(files).map(([name, lines]) => [`kernel/${name}.txt`, joinLines(lines)]),
    ),
  };
};

// testdata/kernel/{envir,pattern,unify}.txt: the expectations of the Rust tests of envir, pattern
// and unify. Every problem is rendered as text, parsed back, and solved on the parsed terms, so
// that the Rust tests, which parse the same text, solve the very same problems.
import { readStatement } from "../../src/prover/isabelle/isar/statement";
import { parseTheory } from "../../src/prover/isabelle/isar/theory";
import { stripAssums2 } from "../../src/prover/isabelle/pure/bicompose";
import {
  above,
  aeconv,
  betaNorm,
  emptyEnvir,
  type Envir,
  etaContract,
  fastype,
  genvars,
  headNorm,
  normTerm,
  substTerm,
  type TEnv,
  vupdate,
} from "../../src/prover/isabelle/pure/envir";
import {
  destEquals,
  stripAssumsConcl,
  stripImpConcl,
  stripImpPrems,
  stripParams,
} from "../../src/prover/isabelle/pure/logic";
import {
  firstOrderMatchPattern,
  isFirstOrder,
  isPattern,
  type MatchEnv,
  matchPattern,
  unifyPattern,
} from "../../src/prover/isabelle/pure/pattern";
import type { Seq } from "../../src/prover/isabelle/pure/seq";
import { tableEntries } from "../../src/prover/isabelle/pure/table";
import {
  couldUnify,
  funT,
  funTs,
  headOf,
  listComb,
  looseBnos,
  maxidxOfTerm,
  mkAbs,
  mkBound,
  mkConst,
  mkTVar,
  mkType,
  mkVar,
  propT,
  type Term,
  type Typ,
} from "../../src/prover/isabelle/pure/term";
import { liftRule, type Thm } from "../../src/prover/isabelle/pure/thm";
import type { TyEnv } from "../../src/prover/isabelle/pure/type";
import { smashUnifiers, type Tpair, unifiers } from "../../src/prover/isabelle/pure/unify";
import { loadLogic } from "../../src/prover/isabelle/tla/logic";
import { createSteps } from "../../src/prover/verdict";
import {
  attempt,
  getFixtureNames,
  joinLines,
  parseTerm,
  parseTyp,
  readFixture,
  showTerm,
  showTyp,
} from "./terms";

// Realistic problems whose expectations run long, or whose search takes long, are left out.
const MAXIMUM_BLOCK = 40_000;
const MAXIMUM_STEPS = 20_000;

const parseVar = (text: string) => {
  const term = parseTerm(text);
  if (term.kind !== "Var") throw new Error(`not a variable: ${text}`);
  return term;
};

const showTables = (tyenv: TyEnv, tenv: TEnv) => [
  ...tableEntries(tenv).map(
    ([key, binding]) =>
      `tenv ?${key.name}.${key.index}:${showTyp(binding.type)} := ${showTerm(binding.term)}`,
  ),
  ...tableEntries(tyenv).map(
    ([key, type]) => `tyenv ?${key.name}.${key.index} := ${showTyp(type)}`,
  ),
];

const showEnvir = (envir: Envir) => [
  `maxidx ${envir.maxidx}`,
  ...showTables(envir.tyenv, envir.tenv),
];

const getEmptyMatchEnv = (): MatchEnv => ({ tyenv: emptyEnvir(0).tyenv, tenv: emptyEnvir(0).tenv });

interface Unifier {
  readonly envir: Envir;
  readonly tpairs: readonly Tpair[];
}

const showUnifiers = <Item>(
  lines: string[],
  count: number,
  pairs: readonly Tpair[],
  seq: Seq<Item>,
  getUnifier: (item: Item) => Unifier,
) => {
  let current = seq;
  for (let index = 0; ; index += 1) {
    if (index === count) {
      lines.push("stop");
      return;
    }
    const cell = current.pull();
    if (cell === undefined) {
      lines.push("end");
      return;
    }
    const result = getUnifier(cell[0]);
    lines.push(`unifier ${index}`, ...showEnvir(result.envir));
    for (const [left, right] of result.tpairs)
      lines.push(`tpair ${showTerm(left)} =?= ${showTerm(right)}`);
    for (const [left, right] of pairs) {
      lines.push(`left ${showTerm(normTerm(result.envir, left))}`);
      lines.push(`right ${showTerm(normTerm(result.envir, right))}`);
    }
    current = cell[1];
  }
};

const unifyLines = (isSmash: boolean, count: number, maxidx: number, pairs: readonly Tpair[]) => {
  const lines: string[] = [];
  const limits = { deadline: Infinity, steps: createSteps() };
  attempt(lines, () => {
    const envir = emptyEnvir(maxidx);
    if (isSmash)
      showUnifiers(lines, count, pairs, smashUnifiers(limits, pairs, envir), (item) => ({
        envir: item,
        tpairs: [],
      }));
    else showUnifiers(lines, count, pairs, unifiers(limits, envir, pairs), (item) => item);
  });
  lines.push(`steps ${limits.steps.count}`);
  return limits.steps.count > MAXIMUM_STEPS ? undefined : lines;
};

// Synthetic problems
const i = mkType("i");
const a = mkTVar("'a", 0);
const b = mkTVar("'b", 0);
const con = (name: string, type: Typ) => mkConst(name, type);
const v = (name: string, index: number, type: Typ) => mkVar(name, index, type);
const app = (head: Term, ...args: Term[]) => listComb(head, args);
const abs = (name: string, type: Typ, body: Term) => mkAbs(name, type, body);
const B = mkBound;
const ca = con("a", i);
const cb = con("b", i);
const f1 = con("f", funT(i, i));
const f2 = con("g", funTs([i, i], i));
const h = con("h", funT(i, i));
const F1 = v("F", 0, funT(i, i));
const F2 = v("F", 0, funTs([i, i], i));
const G1 = v("G", 0, funT(i, i));
const X = v("x", 0, i);
const Y = v("y", 0, i);

const SYNTHETIC: [Term, Term][] = [
  [app(F1, ca), app(f1, ca)],
  [app(F1, X), app(f2, ca, cb)],
  [abs("x", i, app(F1, B(0))), abs("x", i, app(f2, B(0), B(0)))],
  [app(F2, ca, cb), app(G1, cb)],
  [app(F1, X), X],
  [app(F1, app(G1, ca)), app(f1, app(h, ca))],
  [abs("x", i, abs("y", i, app(F2, B(0), B(1)))), abs("x", i, abs("y", i, app(G1, B(1))))],
  [abs("x", i, abs("y", i, app(F2, B(1), B(0)))), abs("x", i, abs("y", i, app(F2, B(0), B(1))))],
  [v("z", 0, a), ca],
  [app(f1, ca), app(h, ca)],
  [app(f1, ca), app(f1, cb)],
  [app(F1, app(F1, ca)), app(f1, app(f1, ca))],
  [abs("x", i, app(f1, B(0))), f1],
  [abs("x", i, app(F2, B(0), ca)), abs("x", i, app(f2, B(0), B(0)))],
  [app(F1, ca), app(G1, cb)],
  [abs("x", i, app(F1, app(G1, B(0)))), abs("x", i, app(f1, B(0)))],
  [v("P", 0, funT(a, propT)), abs("x", i, app(con("Q", funT(i, propT)), B(0)))],
  [app(v("P", 0, funT(a, b)), v("t", 0, a)), app(con("k", funT(i, i)), ca)],
  [abs("x", i, app(F1, B(0))), abs("x", i, app(G1, ca))],
  [abs("x", i, app(F1, B(0))), abs("x", i, app(F1, ca))],
  [app(F2, X, Y), app(f2, Y, X)],
];

const SYNTHETIC_MATCHES: [Term, Term][] = [
  [abs("x", i, app(F1, B(0))), abs("x", i, app(f2, B(0), B(0)))],
  [app(f2, X, X), app(f2, ca, ca)],
  [app(f2, X, X), app(f2, ca, cb)],
  [F1, abs("x", i, app(h, B(0)))],
  [app(F1, ca), app(f1, ca)],
  [v("z", 0, a), ca],
  [abs("x", i, v("c", 0, i)), abs("x", i, app(f1, B(0)))],
  [abs("x", i, abs("y", i, app(F2, B(0), B(1)))), abs("x", i, abs("y", i, app(f2, B(1), B(0))))],
  [abs("x", i, app(f1, app(F1, B(0)))), f1],
  [app(f1, X), abs("x", i, app(f2, B(0), ca))],
  [app(F1, X), app(f1, ca)],
  [abs("x", i, app(F2, B(0), B(0))), abs("x", i, B(0))],
];

const SYNTHETIC_TERMS = [
  app(abs("x", i, app(f2, B(0), B(0))), ca),
  abs("y", i, app(abs("x", i, app(f2, B(0), B(1))), ca)),
  abs("x", i, app(f1, B(0))),
  abs("x", i, abs("y", i, app(f2, B(1), B(0)))),
  abs("x", i, abs("y", i, app(f2, B(0), B(1)))),
  abs("x", i, app(app(abs("z", i, f2), B(0)), B(0))),
  app(app(abs("x", i, abs("y", i, app(f2, B(1), B(0)))), ca), cb),
  app(f1, B(0)),
  app(ca, cb),
  abs("x", i, app(F1, B(0))),
];

export const getKernelExpectations = () => {
  const files: Record<string, string[]> = { envir: [], pattern: [], unify: [] };
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
    const lines = solve(fields);
    if (
      lines === undefined ||
      lines.reduce((total, item) => total + item.length, line.length) > MAXIMUM_BLOCK
    )
      return false;
    files[file].push(line, ...lines);
    return true;
  };

  // envir

  const termProblem = (term: Term) =>
    problem("envir", "term", [showTerm(term)], ([text]) => {
      const parsed = parseTerm(text);
      const lines: string[] = [];
      lines.push(`beta_norm ${showTerm(betaNorm(parsed))}`);
      lines.push(`eta_contract ${showTerm(etaContract(parsed))}`);
      lines.push(`aeconv_beta ${aeconv(parsed, betaNorm(parsed))}`);
      attempt(lines, () => lines.push(`fastype ${showTyp(fastype(emptyEnvir(-1), [], parsed))}`));
      return lines;
    });

  const genvarsProblem = (name: string, maxidx: number, types: Typ[]) =>
    problem(
      "envir",
      "genvars",
      [name, String(maxidx), ...types.map(showTyp)],
      ([innerName, innerMaxidx, ...rest]) => {
        const [envir, vars] = genvars(
          innerName,
          emptyEnvir(Number(innerMaxidx)),
          rest.map(parseTyp),
        );
        return [`maxidx ${envir.maxidx}`, ...vars.map((variable) => `var ${showTerm(variable)}`)];
      },
    );

  // Assigns each pair with vupdate, in order, then normalizes the last term.
  const instantiateProblem = (maxidx: number, pairs: [Term, Term][], target: Term) =>
    problem(
      "envir",
      "instantiate",
      [
        String(maxidx),
        ...pairs.flatMap(([variable, term]) => [showTerm(variable), showTerm(term)]),
        showTerm(target),
      ],
      ([innerMaxidx, ...rest]) => {
        const lines: string[] = [];
        attempt(lines, () => {
          let envir = emptyEnvir(Number(innerMaxidx));
          for (let index = 0; index + 1 < rest.length; index += 2)
            envir = vupdate(parseVar(rest[index]), parseTerm(rest[index + 1]), envir);
          const parsed = parseTerm(rest[rest.length - 1]);
          lines.push(...showEnvir(envir));
          lines.push(`above ${[-1, 0, 1, 2].map((limit) => above(envir, limit)).join(" ")}`);
          lines.push(`norm_term ${showTerm(normTerm(envir, parsed))}`);
          lines.push(`head_norm ${showTerm(headNorm(envir, parsed))}`);
          lines.push(`subst_term ${showTerm(substTerm(envir.tyenv, envir.tenv, parsed))}`);
          lines.push(`fastype ${showTyp(fastype(envir, [], parsed))}`);
        });
        return lines;
      },
    );

  // pattern

  const classifyProblem = (term: Term) =>
    problem("pattern", "classify", [showTerm(term)], ([text]) => {
      const parsed = parseTerm(text);
      return [`pattern ${isPattern(parsed)} first_order ${isFirstOrder(parsed)}`];
    });

  const patternUnifyProblem = (maxidx: number, left: Term, right: Term) =>
    problem(
      "pattern",
      "unify",
      [String(maxidx), showTerm(left), showTerm(right)],
      ([innerMaxidx, leftText, rightText]) => {
        const lines: string[] = [];
        attempt(lines, () => {
          const parsedLeft = parseTerm(leftText);
          const parsedRight = parseTerm(rightText);
          const result = unifyPattern(parsedLeft, parsedRight, emptyEnvir(Number(innerMaxidx)));
          lines.push(result.kind);
          if (result.kind !== "unified") return;
          lines.push(...showEnvir(result.envir));
          lines.push(`left ${showTerm(normTerm(result.envir, parsedLeft))}`);
          lines.push(`right ${showTerm(normTerm(result.envir, parsedRight))}`);
        });
        return lines;
      },
    );

  // Matches with match_pattern and first_order_match, and instantiates the extra terms.
  const matchProblem = (pattern: Term, object: Term, extra: Term[]) =>
    problem(
      "pattern",
      "match",
      [showTerm(pattern), showTerm(object), ...extra.map((term) => showTerm(term))],
      ([patternText, objectText, ...rest]) => {
        const lines: string[] = [];
        const parsedPattern = parseTerm(patternText);
        const parsedObject = parseTerm(objectText);
        const parsedExtra = rest.map(parseTerm);
        const report = (label: string, run: () => MatchEnv | undefined) =>
          attempt(lines, () => {
            const env = run();
            if (env === undefined) {
              lines.push(`${label} none`);
              return;
            }
            lines.push(`${label}`, ...showTables(env.tyenv, env.tenv));
            const instance = substTerm(env.tyenv, env.tenv, parsedPattern);
            lines.push(`instance ${showTerm(instance)}`);
            lines.push(`aeconv ${aeconv(betaNorm(instance), parsedObject)}`);
            for (const term of parsedExtra) {
              const substituted = substTerm(env.tyenv, env.tenv, term);
              lines.push(`extra ${showTerm(substituted)}`);
              lines.push(`extra_norm ${showTerm(etaContract(betaNorm(substituted)))}`);
            }
          });
        const env = getEmptyMatchEnv();
        report("match", () => matchPattern(parsedPattern, parsedObject, env));
        report("first_order_match", () => firstOrderMatchPattern(parsedPattern, parsedObject, env));
        return lines;
      },
    );

  // unify

  const unifyProblem = (
    kind: "unifiers" | "smash",
    count: number,
    maxidx: number,
    pairs: readonly Tpair[],
  ) =>
    problem(
      "unify",
      kind,
      [
        String(count),
        String(maxidx),
        ...pairs.flatMap(([left, right]) => [showTerm(left), showTerm(right)]),
      ],
      ([innerCount, innerMaxidx, ...rest]) => {
        const parsed: Tpair[] = [];
        for (let index = 0; index + 1 < rest.length; index += 2)
          parsed.push([parseTerm(rest[index]), parseTerm(rest[index + 1])]);
        return unifyLines(kind === "smash", Number(innerCount), Number(innerMaxidx), parsed);
      },
    );

  for (const [left, right] of SYNTHETIC) {
    unifyProblem("unifiers", 8, 0, [[left, right]]);
    unifyProblem("smash", 8, 0, [[left, right]]);
    patternUnifyProblem(0, left, right);
    classifyProblem(left);
  }
  unifyProblem("unifiers", 8, 0, [
    [app(F1, ca), app(f1, ca)],
    [app(F1, cb), app(f1, cb)],
  ]);
  unifyProblem("unifiers", 8, 0, [
    [app(F1, X), app(f1, ca)],
    [X, cb],
  ]);
  unifyProblem("unifiers", 8, 0, [
    [X, ca],
    [app(F1, X), app(f1, ca)],
  ]);
  unifyProblem("smash", 8, 0, [
    [app(F2, ca, cb), app(G1, cb)],
    [app(G1, ca), app(F1, X)],
  ]);

  for (const [pattern, object] of SYNTHETIC_MATCHES) {
    matchProblem(pattern, object, [app(G1, pattern)]);
    classifyProblem(pattern);
  }

  for (const term of SYNTHETIC_TERMS) termProblem(term);

  genvarsProblem("x", 3, [i]);
  genvarsProblem("x", -1, [i, funT(i, i), a]);
  genvarsProblem(
    "y",
    7,
    Array.from({ length: 30 }, () => i),
  );

  instantiateProblem(
    2,
    [
      [v("x", 1, i), v("y", 0, i)],
      [v("y", 0, i), ca],
    ],
    app(f2, v("x", 1, i), v("y", 0, i)),
  );
  instantiateProblem(
    2,
    [
      [v("y", 0, i), v("x", 1, i)],
      [v("x", 1, i), ca],
    ],
    app(f2, v("x", 1, i), v("y", 0, i)),
  );
  instantiateProblem(2, [[v("y", 0, i), v("y", 0, i)]], app(f2, v("y", 0, i), v("y", 0, i)));
  instantiateProblem(
    2,
    [
      [v("y", 2, i), ca],
      [v("y", 2, i), cb],
    ],
    v("y", 2, i),
  );
  instantiateProblem(
    3,
    [
      [F2, abs("u", i, abs("w", i, app(f2, B(0), B(1))))],
      [G1, abs("u", i, app(F2, B(0), app(h, B(0))))],
    ],
    abs("x", i, app(G1, app(f1, B(0)))),
  );

  // Realistic problems from the Isabelle/TLA+ logic and the fixtures

  const logic = loadLogic();
  const statements = getFixtureNames().flatMap((name) => {
    // Some fixtures are meant not to parse.
    try {
      return [readStatement(logic, parseTheory(readFixture(name)))];
    } catch {
      return [];
    }
  });

  const subterms = new Map<string, Term>();
  const addClosedSubterms = (term: Term) => {
    if (looseBnos(term).length === 0 && term.kind === "App") subterms.set(showTerm(term), term);
    if (term.kind === "App") {
      addClosedSubterms(term.fun);
      addClosedSubterms(term.arg);
    }
    if (term.kind === "Abs") addClosedSubterms(term.body);
  };
  for (const statement of statements)
    for (const term of [...statement.assumptions, statement.conclusion]) addClosedSubterms(term);
  const objects = [...subterms.values()];

  for (const statement of statements) termProblem(statement.conclusion);

  // Simp rules' left-hand sides against the fixtures' subterms.
  let matchCount = 0;
  let unifyCount = 0;
  for (const simp of logic.simps) {
    if (matchCount >= 150) break;
    const [lhs, rhs] = destEquals(stripImpConcl(simp.prop));
    if (headOf(lhs).kind !== "Const") continue;
    const candidates = objects.filter((object) => couldUnify(lhs, object));
    const isMatching = (object: Term) => {
      try {
        return matchPattern(lhs, object, getEmptyMatchEnv()) !== undefined;
      } catch {
        return true;
      }
    };
    const chosen = [
      ...candidates.filter(isMatching).slice(0, 2),
      ...candidates.filter((object) => !isMatching(object)).slice(0, 1),
    ];
    for (const object of chosen) {
      matchProblem(lhs, object, [rhs]);
      classifyProblem(lhs);
      matchCount += 1;
      if (unifyCount < 50) {
        patternUnifyProblem(simp.maxidx, lhs, object);
        unifyCount += 1;
      }
    }
  }

  const goals = statements.map((statement) => statement.conclusion);
  const assumptions = statements.flatMap((statement) => statement.assumptions);

  // Resolution: an intro rule lifted over a goal, its conclusion against the goal's.
  const resolveProblem = (count: number, goal: Term, rule: Thm) => {
    const goalMaxidx = maxidxOfTerm(goal);
    const lifted = liftRule(goal, goalMaxidx, rule);
    const pair = stripAssums2(stripImpConcl(lifted.prop), goal);
    const isKept = unifyProblem("unifiers", count, Math.max(lifted.maxidx, goalMaxidx), [pair]);
    return [Math.max(lifted.maxidx, goalMaxidx), pair, isKept] as const;
  };

  const intros = [...logic.claset.safeIs, ...logic.claset.unsafeIs].map((rule) => rule.rule);
  const elims = [...logic.claset.safeEs, ...logic.claset.unsafeEs].map((rule) => rule.rule);
  let resolveCount = 0;
  for (const goal of goals) {
    let perGoal = 0;
    for (const rule of intros) {
      if (perGoal >= 6 || resolveCount >= 70) break;
      if (!couldUnify(stripImpConcl(rule.prop), goal)) continue;
      resolveProblem(3, goal, rule);
      perGoal += 1;
      resolveCount += 1;
    }
  }

  // Elimination: a rule's major premise against an assumption.
  let elimCount = 0;
  for (const assumption of assumptions) {
    for (const rule of elims) {
      if (elimCount >= 30) break;
      const major = stripImpPrems(rule.prop)[0];
      if (major === undefined || !couldUnify(major, assumption)) continue;
      unifyProblem("unifiers", 3, rule.maxidx, [[major, assumption]]);
      elimCount += 1;
    }
  }

  // Rules whose conclusion is not a pattern, against the goals: Huet's search.
  const nonPatternRules = [...logic.facts.values()]
    .flat()
    .filter((rule) => !isPattern(stripImpConcl(rule.prop)));
  let huetCount = 0;
  for (const rule of nonPatternRules) {
    let perRule = 0;
    for (const goal of goals) {
      if (perRule >= 2 || huetCount >= 40) break;
      if (!couldUnify(stripImpConcl(rule.prop), goal)) continue;
      if (!resolveProblem(6, goal, rule)[2]) continue;
      perRule += 1;
      huetCount += 1;
    }
  }

  // Chaining: an intro rule lifted over a premise of another, with parameters and unknowns on both
  // sides.
  let chainCount = 0;
  let smashCount = 0;
  for (const outer of intros) {
    if (chainCount >= 60) break;
    for (const premise of stripImpPrems(outer.prop)) {
      if (stripParams(premise).length === 0) continue;
      for (const rule of intros) {
        if (chainCount >= 60) break;
        if (!couldUnify(stripAssumsConcl(premise), stripImpConcl(rule.prop))) continue;
        const [maxidx, pair, isKept] = resolveProblem(4, premise, rule);
        if (!isKept) continue;
        chainCount += 1;
        if (smashCount < 20) {
          unifyProblem("smash", 4, maxidx, [pair]);
          smashCount += 1;
        }
        if (chainCount % 7 === 0) break;
      }
    }
  }

  return Object.fromEntries(
    Object.entries(files).map(([name, lines]) => [`kernel/${name}.txt`, joinLines(lines)]),
  );
};

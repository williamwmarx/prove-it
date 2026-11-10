// Writes the table the Rust port of the SMT core's normal forms (design/smt-core.md) is tested
// against, from the TypeScript it ports. nnf.txt first records a seeded sequence of operations on
// ast.ts's AstManager: it builds random quantified Boolean and arithmetic terms with uninterpreted
// functions, and applies to them nnf.ts, pull-quant.ts, pattern-inference.ts,
// maximize-ac-sharing.ts and qe-lite-fm.ts. Then it parses every script of tests/fixtures/smt with
// smtlib-parser.ts and applies each transformation to every assertion and quantifier. Each line
// records the operation with what it returned (handle, Z3 id, a hash of the structure, the text of
// a shallow term), the fresh declarations it made, the resource limit's step count and the number
// of ASTs, with the ids and reference counts of every expression at checkpoints. prove-smt's
// tests/nnf.rs replays it:
//   bun scripts/smt-nnf-tables.ts

import { mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import {
  AstManager,
  KIND_APP,
  KIND_QUANTIFIER,
  KIND_VAR,
  OP_ADD,
  OP_AND,
  OP_EQ,
  OP_GE,
  OP_IDIV,
  OP_IMPLIES,
  OP_ITE,
  OP_LE,
  OP_MOD,
  OP_MUL,
  OP_NOT,
  OP_NUM,
  OP_OR,
  OP_XOR,
  type SmtSymbol,
  SORT_BOOL,
  SORT_INT,
} from "../src/prover/smt/solver/ast";
import { MaxBvSharing } from "../src/prover/smt/solver/maximize-ac-sharing";
import { DefinedNames, Nnf } from "../src/prover/smt/solver/nnf";
import { PatternInference } from "../src/prover/smt/solver/pattern-inference";
import { PullQuant, pullQuant } from "../src/prover/smt/solver/pull-quant";
import { Fm } from "../src/prover/smt/solver/qe-lite-fm";
import { RefVector } from "../src/prover/smt/solver/ref-vector";
import { ResourceLimit } from "../src/prover/smt/solver/rlimit";
import { parseSmtlib } from "../src/prover/smt/solver/smtlib-parser";

// A shallow term's text longer than this is left out.
const MAX_TEXT_LENGTH = 200;

const encoder = new TextEncoder();

// FNV-1a over the UTF-8 bytes, which tests/nnf.rs computes the same way.
const getTextHash = (text: string) =>
  encoder.encode(text).reduce((hash, byte) => Math.imul(hash ^ byte, 16777619) >>> 0, 2166136261);

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

const random = createRandom(0x0e_f0_4a);
const pick = <T>(items: T[]) => items[random() % items.length];
const chance = (percent: number) => random() % 100 < percent;

const getList = (items: (number | string)[]) => (items.length === 0 ? "-" : items.join(","));
const getSymbolText = (symbol: SmtSymbol) =>
  typeof symbol === "number" ? `n:${symbol}` : `s:${symbol}`;

const lines: string[] = [];
let manager = new AstManager(new ResourceLimit(Number.POSITIVE_INFINITY));

// A hash of the structure of an expression: declarations, sorts, numerals, variables, and the
// variables' names and sorts, the weight, the qid and the patterns of each quantifier.
const getStructHash = (expr: number) => {
  const hashes = new Map<number, number>();
  const visit = (current: number): number => {
    const cached = hashes.get(current);
    if (cached !== undefined) return cached;
    const kind = manager.kinds[current];
    const sort = manager.sorts[current];
    const text =
      kind === KIND_VAR
        ? `v${manager.values[current]}:${sort}`
        : kind === KIND_QUANTIFIER
          ? (() => {
              const data = manager.getQuantifier(current);
              return `q${data.isForall ? 1 : 0}:${data.sorts.join(",")}:${data.names.map(getSymbolText).join(",")}:${data.weight}:${data.qid}:${data.patterns.map(visit).join(",")}:${visit(data.body)}`;
            })()
          : manager.decls[current] === OP_NUM
            ? `n${manager.toString(current)}:${sort}`
            : `a${manager.getDeclName(current)}:${sort}(${manager.mapArgs(current, visit).join(",")})`;
    const hash = getTextHash(text);
    hashes.set(current, hash);
    return hash;
  };
  return visit(expr);
};

// An expression as the table records it, with its text when it is shallow.
const describe = (expr: number) => {
  const fields = `${expr}:${manager.ids[expr]}:${getStructHash(expr)}`;
  if (manager.depths[expr] > 5) return fields;
  const text = manager.toString(expr);
  return text.length <= MAX_TEXT_LENGTH ? `${fields} | ${text}` : fields;
};

const getDescribedList = (exprs: number[]) =>
  exprs.length === 0 ? "-" : exprs.map(describe).join(" ; ");

const record = (operation: string, result: string) =>
  lines.push(`${operation} => ${result} steps=${manager.limit.count} asts=${manager.getNumAsts()}`);

// Runs an operation, and records its result with the names of the declarations it made.
const recordFresh = (operation: string, run: () => string) => {
  const start = manager.funcDecls.length;
  const result = run();
  const names = manager.funcDecls.slice(start).map((decl) => String(decl.name));
  record(operation, `${result} fresh=${getList(names)}`);
};

// HACK: the number of expressions is private to the manager, and only the table reads it.
const getNumNodes = () => Number(Reflect.get(manager, "numNodes"));

const recordRefs = () => {
  const handles = Array.from({ length: getNumNodes() }, (_, index) => index);
  record(
    "refs",
    `${handles.length} ${getTextHash(handles.map((handle) => manager.ids[handle]).join(","))} ${getTextHash(handles.map((handle) => manager.getRefCount(handle)).join(","))}`,
  );
};

// The subterms of a term, under its quantifiers too, each once, in the order of a depth-first
// walk.
const getSubterms = (exprs: number[]) => {
  const subterms: number[] = [];
  const visited = new Set<number>();
  const todo = [...exprs].reverse();
  for (let current = todo.pop(); current !== undefined; current = todo.pop()) {
    if (visited.has(current)) continue;
    visited.add(current);
    subterms.push(current);
    if (manager.kinds[current] === KIND_APP) todo.push(...manager.getArgs(current).reverse());
    else if (manager.kinds[current] === KIND_QUANTIFIER)
      todo.push(manager.getQuantifier(current).body);
  }
  return subterms;
};

const getQuantifiers = (exprs: number[]) =>
  getSubterms(exprs).filter((expr) => manager.kinds[expr] === KIND_QUANTIFIER);

const recordInfer = (
  operation: string,
  inference: PatternInference,
  quantifier: number,
  isPulled: boolean,
) =>
  manager.withTemporaries(
    () => {
      const data = manager.getQuantifier(quantifier);
      if (isPulled) {
        const patterns = inference.inferPulled(data.sorts.length, data.body);
        record(operation, `patterns=${getDescribedList(patterns)}`);
      } else {
        const inferred = inference.infer(data.sorts.length, data.body, data.weight);
        record(
          operation,
          `patterns=${getDescribedList(inferred.patterns)} weight=${inferred.weight}`,
        );
      }
      return 0;
    },
    () => [],
  );

const recordFm = (operation: string, fm: Fm, numVars: number, exprs: number[]) => {
  const fmls = new RefVector(manager);
  for (const expr of exprs) fmls.push(expr);
  fm.numVars = numVars;
  fm.apply(fmls);
  record(operation, getDescribedList(fmls.items));
  fmls.reset();
};

const recordNnf = (operation: string, nnf: Nnf, expr: number) =>
  recordFresh(operation, () => {
    const definitions = new RefVector(manager);
    const result = nnf.apply(expr, definitions);
    const text = `${describe(result)} defs=${getDescribedList(definitions.items)}`;
    manager.decRef(result);
    definitions.reset();
    return text;
  });

// The random terms.

const mkSort = (name: string) => {
  const sort = manager.mkSort(name);
  record(`sort ${name}`, `${sort}`);
  return sort;
};

const mkDecl = (name: string, domain: number[], range: number, isSkolem = false) => {
  const decl = manager.mkFuncDecl(name, domain, range, isSkolem);
  record(`decl ${name} ${getList(domain)} ${range} ${isSkolem ? 1 : 0}`, `${decl}`);
  return decl;
};

const recordExpr = (operation: string, make: () => number) => {
  const expr = make();
  record(operation, describe(expr));
  return expr;
};

const mkApp = (decl: number, args: number[], sort: number) =>
  recordExpr(`app ${decl} ${getList(args)} ${sort}`, () => manager.mkApp(decl, args, sort));

const mkVar = (index: number, sort: number) =>
  recordExpr(`var ${index} ${sort}`, () => manager.mkVar(index, sort));

const mkInt = (value: bigint) => recordExpr(`int ${value}`, () => manager.mkNumeral(value));

const mkPattern = (terms: number[]) =>
  recordExpr(`pattern ${getList(terms)}`, () => manager.mkPattern(terms));

const mkQuantifier = (
  isForall: boolean,
  sorts: number[],
  names: SmtSymbol[],
  body: number,
  patterns: number[],
  weight: number,
  qid: string,
) =>
  recordExpr(
    `quant ${isForall ? 1 : 0} ${getList(sorts)} ${getList(names.map(getSymbolText))} ${body} ${getList(patterns)} ${weight} ${qid === "" ? "-" : qid}`,
    () => manager.mkQuantifier({ isForall, sorts, names, body, patterns, weight, qid }),
  );

const held: number[] = [];
const hold = (expr: number) => {
  manager.incRef(expr);
  held.push(expr);
  record(`hold ${expr}`, `${manager.getRefCount(expr)}`);
  return expr;
};

const sortU = mkSort("U");
const declF = mkDecl("f", [sortU], sortU);
const declG = mkDecl("g", [sortU, sortU], SORT_BOOL);
const declP = mkDecl("P", [sortU], SORT_BOOL);
const declQ = mkDecl("Q", [SORT_INT], SORT_BOOL);
// A predicate of a formula, whose quantifiers nnf names.
const declR = mkDecl("R", [SORT_BOOL, sortU], SORT_BOOL);
const declH = mkDecl("h", [SORT_INT], SORT_INT);
const declK = mkDecl("k", [SORT_INT, sortU], SORT_INT);
const declSk = mkDecl("sk", [sortU], SORT_INT, true);
const constC = hold(mkApp(mkDecl("c", [], sortU), [], sortU));
const constD = hold(mkApp(mkDecl("d", [], sortU), [], sortU));
const constBools = ["p", "q", "r"].map((name) =>
  hold(mkApp(mkDecl(name, [], SORT_BOOL), [], SORT_BOOL)),
);
const constX = hold(mkApp(mkDecl("x", [], SORT_INT), [], SORT_INT));
const constY = hold(mkApp(mkDecl("y", [], SORT_INT), [], SORT_INT));

const NAMES: SmtSymbol[] = [0, 1, 2, "x", "y", "x"];

// An arithmetic term over the variables of sort Int, whose uninterpreted applications take
// arithmetic arguments, so that pattern inference needs its arithmetic rounds.
const genArith = (env: number[], depth: number): number => {
  const indexes = env.flatMap((varSort, index) => (varSort === SORT_INT ? [index] : []));
  const getVar = () => (indexes.length === 0 ? constX : mkVar(pick(indexes), SORT_INT));
  if (depth === 0) return chance(70) ? getVar() : mkInt(BigInt(random() % 4));
  const choice = random() % 6;
  if (choice === 0)
    return mkApp(OP_ADD, [genArith(env, depth - 1), mkInt(BigInt(1 + (random() % 3)))], SORT_INT);
  if (choice === 1) return mkApp(OP_MUL, [getVar(), genArith(env, depth - 1)], SORT_INT);
  if (choice === 2)
    return mkApp(
      pick([OP_IDIV, OP_MOD]),
      [genArith(env, depth - 1), mkInt(BigInt(2 + (random() % 2)))],
      SORT_INT,
    );
  if (choice === 3)
    return mkApp(declH, [mkApp(OP_ADD, [genArith(env, depth - 1), mkInt(1n)], SORT_INT)], SORT_INT);
  return getVar();
};

const genArithAtom = (env: number[]) => {
  const choice = random() % 4;
  if (choice === 0)
    return mkApp(declQ, [mkApp(OP_ADD, [genArith(env, 2), mkInt(2n)], SORT_INT)], SORT_BOOL);
  return mkApp(pick([OP_LE, OP_GE, OP_EQ]), [genArith(env, 2), genArith(env, 2)], SORT_BOOL);
};

// A quantifier for the arithmetic rounds of pattern inference, over variables of sort Int.
const genArithQuantifier = (env: number[]) => {
  const sorts = Array.from({ length: 1 + (random() % 2) }, () => SORT_INT);
  const inner = [...sorts].concat(env);
  const atoms = Array.from({ length: 1 + (random() % 3) }, () => genArithAtom(inner));
  const body = atoms.length === 1 ? atoms[0] : mkApp(pick([OP_AND, OP_OR]), atoms, SORT_BOOL);
  return mkQuantifier(
    true,
    sorts,
    sorts.map((_, index) => index),
    body,
    [],
    random() % 3,
    "",
  );
};

// A quantifier whose atoms each take one variable, which needs a multi-pattern.
const genMultiQuantifier = () => {
  const sorts = Array.from({ length: 2 + (random() % 3) }, () => sortU);
  const atoms = Array.from({ length: sorts.length + (random() % 3) }, () => {
    const variable = mkVar(random() % sorts.length, sortU);
    const choice = random() % 4;
    if (choice === 0) return mkApp(declP, [variable], SORT_BOOL);
    if (choice === 1) return mkApp(declG, [variable, pick([constC, constD])], SORT_BOOL);
    if (choice === 2) return mkApp(OP_EQ, [mkApp(declF, [variable], sortU), constD], SORT_BOOL);
    return mkApp(declP, [mkApp(declF, [mkApp(declF, [variable], sortU)], sortU)], SORT_BOOL);
  });
  const body = mkApp(pick([OP_AND, OP_OR]), atoms, SORT_BOOL);
  return mkQuantifier(
    chance(80),
    sorts,
    sorts.map(() => pick(NAMES)),
    body,
    [],
    random() % 3,
    pick(["", "m"]),
  );
};

// A disjunction or a sum over a few atoms, whose pairs maximize_ac_sharing reuses.
const genFlat = () => {
  if (chance(50)) {
    const pool = [
      ...constBools,
      mkApp(OP_NOT, [constBools[0]], SORT_BOOL),
      mkApp(declP, [constC], SORT_BOOL),
    ];
    const args = Array.from({ length: 3 + (random() % 3) }, () => pick(pool));
    return mkApp(OP_OR, args, SORT_BOOL);
  }
  const pool = [constX, constY, mkApp(declH, [constX], SORT_INT), mkInt(BigInt(random() % 3))];
  const args = Array.from({ length: 3 + (random() % 3) }, () => pick(pool));
  return mkApp(OP_LE, [mkApp(OP_ADD, args, SORT_INT), mkInt(0n)], SORT_BOOL);
};

const getLeaf = (sort: number, env: number[]): number => {
  const indexes = env.flatMap((varSort, index) => (varSort === sort ? [index] : []));
  if (indexes.length > 0 && chance(55)) return mkVar(pick(indexes), sort);
  if (sort === sortU) return pick([constC, constD]);
  if (sort === SORT_INT)
    return chance(50) ? pick([constX, constY]) : mkInt(BigInt(random() % 5) - 1n);
  return chance(85) ? pick(constBools) : pick([manager.trueExpr, manager.falseExpr]);
};

const gen = (sort: number, env: number[], depth: number): number => {
  if (depth === 0 || chance(20)) return getLeaf(sort, env);
  const next = depth - 1;
  if (sort === sortU) {
    if (chance(70)) return mkApp(declF, [gen(sortU, env, next)], sortU);
    return mkApp(
      OP_ITE,
      [gen(SORT_BOOL, env, next), gen(sortU, env, next), gen(sortU, env, next)],
      sortU,
    );
  }
  if (sort === SORT_INT) {
    const choice = random() % 9;
    if (choice === 0) return mkApp(declH, [gen(SORT_INT, env, next)], SORT_INT);
    if (choice === 1)
      return mkApp(declK, [gen(SORT_INT, env, next), gen(sortU, env, next)], SORT_INT);
    if (choice === 2) return mkApp(declSk, [gen(sortU, env, next)], SORT_INT);
    if (choice === 3) {
      const args = Array.from({ length: 2 + (random() % 3) }, () => gen(SORT_INT, env, next));
      return mkApp(OP_ADD, args, SORT_INT);
    }
    if (choice === 4)
      return mkApp(OP_MUL, [mkInt(BigInt(random() % 5) - 2n), gen(SORT_INT, env, next)], SORT_INT);
    if (choice === 5)
      return mkApp(OP_MUL, [gen(SORT_INT, env, next), gen(SORT_INT, env, next)], SORT_INT);
    if (choice === 6)
      return mkApp(
        pick([OP_IDIV, OP_MOD]),
        [gen(SORT_INT, env, next), gen(SORT_INT, env, next)],
        SORT_INT,
      );
    if (choice === 7)
      return mkApp(
        OP_ITE,
        [gen(SORT_BOOL, env, next), gen(SORT_INT, env, next), gen(SORT_INT, env, next)],
        SORT_INT,
      );
    return getLeaf(SORT_INT, env);
  }
  const choice = random() % 18;
  if (choice === 15) return genArithQuantifier(env);
  if (choice === 16) return genMultiQuantifier();
  if (choice === 17) return genFlat();
  if (choice === 14)
    return mkApp(declR, [gen(SORT_BOOL, env, next), gen(sortU, env, next)], SORT_BOOL);
  if (choice === 0) return mkApp(declG, [gen(sortU, env, next), gen(sortU, env, next)], SORT_BOOL);
  if (choice === 1) return mkApp(declP, [gen(sortU, env, next)], SORT_BOOL);
  if (choice === 2) return mkApp(declQ, [gen(SORT_INT, env, next)], SORT_BOOL);
  if (choice === 3 || choice === 4) {
    const args = Array.from({ length: 2 + (random() % 3) }, () => gen(SORT_BOOL, env, next));
    return mkApp(choice === 3 ? OP_AND : OP_OR, args, SORT_BOOL);
  }
  if (choice === 5) return mkApp(OP_NOT, [gen(SORT_BOOL, env, next)], SORT_BOOL);
  if (choice === 6)
    return mkApp(
      pick([OP_EQ, OP_XOR, OP_IMPLIES]),
      [gen(SORT_BOOL, env, next), gen(SORT_BOOL, env, next)],
      SORT_BOOL,
    );
  if (choice === 7)
    return mkApp(
      OP_ITE,
      [gen(SORT_BOOL, env, next), gen(SORT_BOOL, env, next), gen(SORT_BOOL, env, next)],
      SORT_BOOL,
    );
  if (choice === 8)
    return mkApp(
      pick([OP_EQ, OP_LE, OP_GE]),
      [gen(SORT_INT, env, next), gen(SORT_INT, env, next)],
      SORT_BOOL,
    );
  if (choice === 9) return mkApp(OP_EQ, [gen(sortU, env, next), gen(sortU, env, next)], SORT_BOOL);
  // A quantifier over one to three variables, whose first variable in Z3's order is var 0.
  const sorts = Array.from({ length: 1 + (random() % 3) }, () => pick([sortU, sortU, SORT_INT]));
  const inner = [...sorts].reverse().concat(env);
  const body = gen(SORT_BOOL, inner, next);
  const names = sorts.map(() => pick(NAMES));
  const patterns: number[] = [];
  const index = inner.slice(0, sorts.length).indexOf(sortU);
  if (index !== -1 && chance(30))
    patterns.push(mkPattern([mkApp(declF, [mkVar(index, sortU)], sortU)]));
  return mkQuantifier(
    chance(60),
    sorts,
    names,
    body,
    patterns,
    random() % 3,
    pick(["", "q1", "q2"]),
  );
};

// Builds a term inside temporaries, so that its subterms are held only by their parents.
const build = (make: () => number) => {
  const outer = manager.beginTemporaries();
  record("begin", `${outer}`);
  const expr = hold(make());
  manager.endTemporaries(outer);
  record(`end ${outer}`, "-");
  return expr;
};

// A formula for fm: a clause of Boolean constants and a linear inequality over the variables below
// numVars, or a formula that forbids its variables. Some monomials repeat a variable, or have
// a variable fm does not eliminate, or a constant.
const genFm = (numVars: number) => {
  if (chance(15)) {
    const variable = mkVar(random() % (numVars + 1), SORT_INT);
    return chance(50)
      ? mkApp(declQ, [variable], SORT_BOOL)
      : mkApp(OP_EQ, [variable, mkInt(BigInt(random() % 5))], SORT_BOOL);
  }
  const monomials = Array.from({ length: 1 + (random() % 2) }, () => {
    const variable = chance(5)
      ? constX
      : mkVar(random() % (chance(10) ? numVars + 1 : numVars), SORT_INT);
    return chance(40)
      ? variable
      : mkApp(OP_MUL, [mkInt(BigInt(pick([-3, -2, -1, 1, 2, 3]))), variable], SORT_INT);
  });
  const lhs = monomials.length === 1 ? monomials[0] : mkApp(OP_ADD, monomials, SORT_INT);
  const atom = mkApp(pick([OP_LE, OP_GE]), [lhs, mkInt(BigInt(random() % 9) - 4n)], SORT_BOOL);
  const ineq = chance(30) ? mkApp(OP_NOT, [atom], SORT_BOOL) : atom;
  const lits = Array.from({ length: chance(50) ? 0 : 1 + (random() % 2) }, () => {
    const constant = pick(constBools);
    return chance(40) ? mkApp(OP_NOT, [constant], SORT_BOOL) : constant;
  });
  return lits.length === 0 ? ineq : mkApp(OP_OR, [...lits, ineq], SORT_BOOL);
};

const ENVS = [[], [], [sortU], [SORT_INT, sortU]];

for (let index = 0; index < 60; index++) {
  const env = pick(ENVS);
  build(() => gen(SORT_BOOL, env, 2 + (random() % 4)));
}
recordRefs();

let names = new DefinedNames(manager);
let nnf = new Nnf(manager, names);
let pull = new PullQuant(manager);
const inference = new PatternInference(manager);
let sharing = new MaxBvSharing(manager);
const fm = new Fm(manager);

for (let step = 0; step < 1100; step++) {
  const choice = random() % 100;
  const getQuantifier = () => {
    const quantifiers = getQuantifiers(held);
    return quantifiers.length === 0 ? -1 : pick(quantifiers);
  };
  if (choice < 10) {
    const env = pick(ENVS);
    build(() => gen(SORT_BOOL, env, 2 + (random() % 4)));
  } else if (choice < 30) {
    const expr = pick(held);
    recordNnf(`nnf ${expr}`, nnf, expr);
  } else if (choice < 32) {
    const isPush = chance(50);
    if (isPush) names.push();
    else names.pop();
    record(`names-${isPush ? "push" : "pop"}`, "-");
  } else if (choice < 33) {
    nnf.release();
    const isNewNames = chance(30);
    if (isNewNames) names = new DefinedNames(manager);
    nnf = new Nnf(manager, names);
    record(`nnf-renew ${isNewNames ? 1 : 0}`, "-");
  } else if (choice < 43) {
    const expr = pick(held);
    recordFresh(`pull ${expr}`, () => {
      const result = pullQuant(manager, expr);
      const text = describe(result);
      manager.decRef(result);
      return text;
    });
  } else if (choice < 50) {
    const expr = pick(held);
    recordFresh(`pull-rw ${expr}`, () => {
      const result = pull.rewrite(expr);
      const text = describe(result);
      manager.decRef(result);
      return text;
    });
  } else if (choice < 51) {
    pull.release();
    pull = new PullQuant(manager);
    record("pull-renew", "-");
  } else if (choice < 63) {
    const quantifier = getQuantifier();
    if (quantifier !== -1) recordInfer(`infer ${quantifier}`, inference, quantifier, false);
  } else if (choice < 68) {
    const quantifier = getQuantifier();
    if (quantifier !== -1) recordInfer(`infer-pulled ${quantifier}`, inference, quantifier, true);
  } else if (choice < 78) {
    const expr = pick(held);
    recordFresh(`sharing ${expr}`, () => {
      const result = sharing.rewrite(expr);
      const text = describe(result);
      manager.decRef(result);
      return text;
    });
  } else if (choice < 81) {
    sharing.pushScope();
    record("sharing-push", "-");
  } else if (choice < 83) {
    sharing.popScope();
    record("sharing-pop", "-");
  } else if (choice < 84) {
    sharing.release();
    sharing = new MaxBvSharing(manager);
    record("sharing-renew", "-");
  } else {
    const numVars = 1 + (random() % 2);
    const outer = manager.beginTemporaries();
    record("begin", `${outer}`);
    const fmls = Array.from({ length: 2 + (random() % 8) }, () => genFm(numVars));
    if (chance(10)) fmls.push(pick(getQuantifiers(held).concat(held)));
    recordFm(`fm ${numVars} ${getList(fmls)}`, fm, numVars, fmls);
    manager.endTemporaries(outer);
    record(`end ${outer}`, "-");
  }
  if (step % 100 === 0) recordRefs();
}

// Loop patterns: f(x) and f(e(x)) in both orders, where the smaller one is blocked, and pairs that
// are instances of each other, such as g(x, y) and g(y, x), where neither is.
const declE = mkDecl("e", [sortU], sortU);
const loopQuantifiers = [
  () => {
    const variable = mkVar(0, sortU);
    const applied = mkApp(declF, [variable], sortU);
    const nested = mkApp(declF, [mkApp(declE, [variable], sortU)], sortU);
    return mkQuantifier(
      true,
      [sortU],
      ["x"],
      mkApp(OP_EQ, [applied, nested], SORT_BOOL),
      [],
      0,
      "",
    );
  },
  () => {
    const variable = mkVar(0, sortU);
    const nested = mkApp(declF, [mkApp(declE, [variable], sortU)], sortU);
    const applied = mkApp(declF, [variable], sortU);
    return mkQuantifier(
      true,
      [sortU],
      ["x"],
      mkApp(OP_EQ, [nested, applied], SORT_BOOL),
      [],
      0,
      "",
    );
  },
  () => {
    const first = mkVar(0, sortU);
    const second = mkVar(1, sortU);
    const body = mkApp(
      OP_OR,
      [mkApp(declG, [first, second], SORT_BOOL), mkApp(declG, [second, first], SORT_BOOL)],
      SORT_BOOL,
    );
    return mkQuantifier(true, [sortU, sortU], ["x", "y"], body, [], 0, "");
  },
  () => {
    const first = mkVar(0, sortU);
    const second = mkVar(1, sortU);
    const body = mkApp(
      OP_AND,
      [
        mkApp(declG, [first, mkApp(declF, [second], sortU)], SORT_BOOL),
        mkApp(declG, [second, mkApp(declF, [first], sortU)], SORT_BOOL),
      ],
      SORT_BOOL,
    );
    return mkQuantifier(true, [sortU, sortU], ["x", "y"], body, [], 0, "");
  },
  // Eight variables, each in atoms of its own under and, or, iff and ite, so that the search for a
  // multi-pattern reaches MAX_SPLITS. Its first complete multi-pattern takes every candidate, so the
  // cap does not change it.
  () => {
    const sorts = Array.from({ length: 8 }, () => sortU);
    const atoms = sorts.map((_, index) =>
      index % 2 === 0
        ? mkApp(declP, [mkVar(index, sortU)], SORT_BOOL)
        : mkApp(declG, [mkVar(index, sortU), constC], SORT_BOOL),
    );
    const body = mkApp(
      OP_AND,
      [
        mkApp(OP_EQ, [atoms[0], atoms[1]], SORT_BOOL),
        mkApp(
          OP_OR,
          [atoms[2], mkApp(OP_ITE, [atoms[3], atoms[4], atoms[5]], SORT_BOOL)],
          SORT_BOOL,
        ),
        mkApp(OP_IMPLIES, [mkApp(OP_XOR, [atoms[6], atoms[7]], SORT_BOOL), atoms[0]], SORT_BOOL),
      ],
      SORT_BOOL,
    );
    return mkQuantifier(
      true,
      sorts,
      sorts.map((_, index) => index),
      body,
      [],
      0,
      "split",
    );
  },
];
for (const make of loopQuantifiers) {
  const quantifier = build(make);
  recordInfer(`infer ${quantifier}`, inference, quantifier, false);
  recordInfer(`infer-pulled ${quantifier}`, inference, quantifier, true);
}

nnf.release();
pull.release();
sharing.release();
fm.release();
record("release", "-");
recordRefs();
for (const expr of held.splice(0)) manager.decRef(expr);
record("dec-held", "-");
recordRefs();

// The fixtures, each with a manager of its own.

const fixtures = join(import.meta.dir, "../tests/fixtures/smt");
for (const file of readdirSync(fixtures)
  .filter((name) => name.endsWith(".smt"))
  .sort()) {
  lines.push(`fixture ${file}`);
  manager = new AstManager(new ResourceLimit(Number.POSITIVE_INFINITY));
  const assertions = parseSmtlib(
    readFileSync(join(fixtures, file), "utf8"),
    manager,
    () => {},
  ).assertions;
  for (const assertion of assertions) manager.incRef(assertion);
  record(`parsed ${assertions.length}`, "-");
  const fixtureNames = new DefinedNames(manager);
  const fixtureNnf = new Nnf(manager, fixtureNames);
  assertions.forEach((assertion, index) => recordNnf(`nnf ${index}`, fixtureNnf, assertion));
  fixtureNnf.release();
  record("nnf-release", "-");
  assertions.forEach((assertion, index) =>
    recordFresh(`pull ${index}`, () => {
      const result = pullQuant(manager, assertion);
      const text = describe(result);
      manager.decRef(result);
      return text;
    }),
  );
  const quantifiers = getQuantifiers(assertions);
  const fixtureInference = new PatternInference(manager);
  quantifiers.forEach((quantifier, index) => {
    recordInfer(`infer ${index}`, fixtureInference, quantifier, false);
    recordInfer(`infer-pulled ${index}`, fixtureInference, quantifier, true);
  });
  const fixtureSharing = new MaxBvSharing(manager);
  fixtureSharing.pushScope();
  assertions.forEach((assertion, index) =>
    recordFresh(`sharing ${index}`, () => {
      const result = fixtureSharing.rewrite(assertion);
      const text = describe(result);
      manager.decRef(result);
      return text;
    }),
  );
  fixtureSharing.popScope();
  fixtureSharing.release();
  record("sharing-release", "-");
  const fixtureFm = new Fm(manager);
  quantifiers.forEach((quantifier, index) => {
    const data = manager.getQuantifier(quantifier);
    const fmls = manager.getOp(data.body) === OP_AND ? manager.getArgs(data.body) : [data.body];
    recordFm(`fm ${index}`, fixtureFm, data.sorts.length, fmls);
  });
  fixtureFm.release();
  record("fm-release", "-");
  recordRefs();
}

const directory = join(import.meta.dir, "../native/crates/prover/smt/tests/tables");
mkdirSync(directory, { recursive: true });
writeFileSync(join(directory, "nnf.txt"), `${lines.join("\n")}\n`);

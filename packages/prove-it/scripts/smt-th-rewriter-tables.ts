// Writes the table the Rust port of th_rewriter (design/smt-core.md) is tested against, from the
// TypeScript it ports. th-rewriter.txt has two parts. The first is a seeded sequence of operations
// on ast.ts's AstManager: it builds random arithmetic, Boolean, ite, equality and quantified terms
// over Int and Real (numerals big and small, div, mod, abs, to_real, to_int, is_int, nested sums
// and products, distinct, uninterpreted functions), and rewrites them with rewriter.ts's Rewriter
// under its option sets, with its mk_* entry points, and with der.ts. The second parses every
// script of tests/fixtures/smt and rewrites each assertion. Each line records the operation with
// what it returned, the resource limit's step count and the number of ASTs, and a digest of the
// ids and reference counts of every expression at checkpoints. prove-smt's tests/th_rewriter.rs
// replays it:
//   bun scripts/smt-th-rewriter-tables.ts

import { mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import { SmtCanceledError } from "../src/errors";
import {
  AstManager,
  KIND_QUANTIFIER,
  OP_ABS,
  OP_ADD,
  OP_AND,
  OP_DISTINCT,
  OP_DIV,
  OP_EQ,
  OP_GE,
  OP_GT,
  OP_IDIV,
  OP_IMPLIES,
  OP_IS_INT,
  OP_ITE,
  OP_LE,
  OP_LT,
  OP_MOD,
  OP_MUL,
  OP_NOT,
  OP_OR,
  OP_SUB,
  OP_TO_INT,
  OP_TO_REAL,
  OP_UMINUS,
  OP_XOR,
  type SmtSymbol,
  SORT_BOOL,
  SORT_INT,
  SORT_REAL,
} from "../src/prover/smt/solver/ast";
import { Der } from "../src/prover/smt/solver/der";
import { Rational } from "../src/prover/smt/solver/rational";
import {
  KERNEL_REWRITER_OPTIONS,
  Rewriter,
  TACTIC_REWRITER_OPTIONS,
} from "../src/prover/smt/solver/rewriter";
import { ResourceLimit } from "../src/prover/smt/solver/rlimit";
import { parseSmtlib } from "../src/prover/smt/solver/smtlib-parser";
import { createSteps } from "../src/prover/verdict";

// A text longer than this is recorded as its length and hash.
const MAX_TEXT_LENGTH = 200;

const encoder = new TextEncoder();

// FNV-1a over the UTF-8 bytes, which tests/th_rewriter.rs computes the same way.
const getTextHash = (text: string) =>
  encoder.encode(text).reduce((hash, byte) => Math.imul(hash ^ byte, 16777619) >>> 0, 2166136261);

const getShortText = (text: string) => {
  const length = encoder.encode(text).length;
  return length > MAX_TEXT_LENGTH ? `#${length}:${getTextHash(text)}` : text;
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

const random = createRandom(0x7e_5717);
const pick = <T>(items: T[]) => items[random() % items.length];
const chance = (percent: number) => random() % 100 < percent;

const lines: string[] = [];
// Each episode of the random part has a manager of its own with a step budget, so that a rewrite
// that does not end stops with SmtCanceledError, which the table records, and ends the episode.
const STEP_LIMIT = 20_000;
const mkManager = (stepLimit: number) =>
  new AstManager(new ResourceLimit(Number.POSITIVE_INFINITY, undefined, createSteps(stepLimit)));
let manager = mkManager(STEP_LIMIT);

const getList = (items: (number | string)[]) => (items.length === 0 ? "-" : items.join(","));
const getSymbolText = (symbol: SmtSymbol) =>
  typeof symbol === "number" ? `n:${symbol}` : `s:${symbol}`;

// An expression as the table records it: its handle, id, hash and text.
const describe = (expr: number) =>
  `${expr}:${manager.ids[expr]}:${manager.hashes[expr]} | ${getShortText(manager.toString(expr))}`;

const record = (operation: string, result: string) =>
  lines.push(`${operation} => ${result} steps=${manager.limit.count} asts=${manager.getNumAsts()}`);

// The operation being made, which the table records when the step budget cancels it.
let pending = "";
const recordExpr = (operation: string, make: () => number) => {
  pending = operation;
  const expr = make();
  record(operation, describe(expr));
  return expr;
};

// Records a result that comes with a reference, and releases it.
const recordOwned = (operation: string, make: () => number) => {
  const expr = recordExpr(operation, make);
  manager.decRef(expr);
};

// The ids and reference counts of every expression, as two hashes.
const dumpRefs = () => {
  const numNodes: number = Reflect.get(manager, "numNodes");
  const handles = Array.from({ length: numNodes }, (_, index) => index);
  const ids = handles.map((handle) => manager.ids[handle]).join(",");
  const refCounts = handles.map((handle) => manager.getRefCount(handle)).join(",");
  record("refs", `${numNodes} ${getTextHash(ids)} ${getTextHash(refCounts)}`);
};

const mkSort = (name: string) => {
  const sort = manager.mkSort(name);
  record(`sort ${name}`, `${sort}`);
  return sort;
};

const mkDecl = (name: string, domain: number[], range: number) => {
  const decl = manager.mkFuncDecl(name, domain, range, false);
  record(`decl ${name} ${getList(domain)} ${range}`, `${decl}`);
  return decl;
};

const mkApp = (decl: number, args: number[], sort: number) =>
  recordExpr(`app ${decl} ${getList(args)} ${sort}`, () => manager.mkApp(decl, args, sort));

const mkVar = (index: number, sort: number) =>
  recordExpr(`var ${index} ${sort}`, () => manager.mkVar(index, sort));

const mkInt = (value: bigint) => recordExpr(`int ${value}`, () => manager.mkNumeral(value));

const mkReal = (num: bigint, den: bigint) => {
  const value = Rational.of(num, den);
  return recordExpr(`real ${value.num} ${value.den}`, () => manager.mkRealNumeral(value));
};

const mkModelValue = (index: number, sort: number) =>
  recordExpr(`model-value ${index} ${sort}`, () => manager.mkModelValue(index, sort));

const mkPattern = (terms: number[]) =>
  recordExpr(`pattern ${getList(terms)}`, () => manager.mkPattern(terms));

const mkQuantifier = (
  isForall: boolean,
  sorts: number[],
  names: SmtSymbol[],
  body: number,
  patterns: number[],
) =>
  recordExpr(
    `quant ${isForall ? 1 : 0} ${getList(sorts)} ${getList(names.map(getSymbolText))} ${body} ${getList(patterns)}`,
    () => manager.mkQuantifier({ isForall, sorts, names, body, patterns, weight: 0, qid: "q" }),
  );

// The terms the script holds a reference to, by sort.
let held: number[] = [];
let pools = new Map<number, number[]>();
const getPool = (sort: number) => {
  const pool = pools.get(sort) ?? [];
  pools.set(sort, pool);
  return pool;
};
const hold = (expr: number) => {
  manager.incRef(expr);
  held.push(expr);
  getPool(manager.sorts[expr]).push(expr);
  record(`hold ${expr}`, `${manager.getRefCount(expr)}`);
  return expr;
};

// The sorts, declarations and constants, which a fresh manager gives the same handles each time.
const declare = () => {
  const sortU = mkSort("U");
  const declF = mkDecl("f", [SORT_INT], SORT_INT);
  const declG = mkDecl("g", [SORT_INT, SORT_INT], SORT_BOOL);
  const declH = mkDecl("h", [SORT_REAL], SORT_REAL);
  const declK = mkDecl("k", [sortU], SORT_INT);
  const declC = mkDecl("c", [], sortU);
  const declD = mkDecl("d", [], sortU);
  const declP = mkDecl("p", [], SORT_BOOL);
  const declQ = mkDecl("q", [], SORT_BOOL);
  const declX = mkDecl("x", [], SORT_INT);
  const declY = mkDecl("y", [], SORT_INT);
  const declZ = mkDecl("z", [], SORT_INT);
  const declR = mkDecl("r", [], SORT_REAL);
  const declS = mkDecl("s", [], SORT_REAL);
  const constC = hold(mkApp(declC, [], sortU));
  const constD = hold(mkApp(declD, [], sortU));
  const constP = hold(mkApp(declP, [], SORT_BOOL));
  const constQ = hold(mkApp(declQ, [], SORT_BOOL));
  const constX = hold(mkApp(declX, [], SORT_INT));
  const constY = hold(mkApp(declY, [], SORT_INT));
  const constZ = hold(mkApp(declZ, [], SORT_INT));
  const constR = hold(mkApp(declR, [], SORT_REAL));
  const constS = hold(mkApp(declS, [], SORT_REAL));
  return {
    sortU,
    declF,
    declG,
    declH,
    declK,
    constC,
    constD,
    constP,
    constQ,
    constX,
    constY,
    constZ,
    constR,
    constS,
  };
};
record(`episode ${STEP_LIMIT}`, "-");
const {
  sortU,
  declF,
  declG,
  declH,
  declK,
  constC,
  constD,
  constP,
  constQ,
  constX,
  constY,
  constZ,
  constR,
  constS,
} = declare();

const BIG = 2n ** 70n;

const getIntValue = () =>
  chance(15)
    ? pick([BIG + 3n, -BIG, 10n ** 20n, -(2n ** 64n) + 1n])
    : pick([-3n, -2n, -1n, 0n, 1n, 2n, 3n, 4n, 6n, 7n]);

const getLeaf = (sort: number, env: number[]): number => {
  const indexes = env.flatMap((varSort, index) => (varSort === sort ? [index] : []));
  if (indexes.length > 0 && chance(45)) return mkVar(pick(indexes), sort);
  if (sort === sortU)
    return chance(75) ? pick([constC, constD]) : mkModelValue(random() % 3, sortU);
  if (sort === SORT_INT) return chance(55) ? pick([constX, constY, constZ]) : mkInt(getIntValue());
  if (sort === SORT_REAL)
    return chance(50)
      ? pick([constR, constS])
      : mkReal(getIntValue(), pick([1n, 2n, 3n, 7n, 10n ** 15n]));
  return pick([constP, constQ, manager.trueExpr, manager.falseExpr]);
};

// The terms built in the current temporaries, by sort, which later terms may share.
let locals = new Map<number, number[]>();
const share = (expr: number) => {
  const local = locals.get(manager.sorts[expr]) ?? [];
  locals.set(manager.sorts[expr], local);
  local.push(expr);
  return expr;
};

const genArgs = (count: number, sort: number, env: number[], depth: number) =>
  Array.from({ length: count }, () => gen(sort, env, depth));

const genNumeric = (sort: number, env: number[], depth: number): number => {
  const next = depth - 1;
  const choice = random() % 12;
  if (choice === 0)
    return sort === SORT_INT
      ? mkApp(declF, [gen(SORT_INT, env, next)], SORT_INT)
      : mkApp(declH, [gen(SORT_REAL, env, next)], SORT_REAL);
  if (choice === 1 || choice === 2)
    return mkApp(OP_ADD, genArgs(2 + (random() % 3), sort, env, next), sort);
  if (choice === 3) return mkApp(OP_SUB, genArgs(2 + (random() % 2), sort, env, next), sort);
  if (choice === 4) return mkApp(OP_UMINUS, [gen(sort, env, next)], sort);
  if (choice === 5 || choice === 6) {
    const args = genArgs(2 + (random() % 2), sort, env, next);
    if (chance(50)) args[0] = getLeaf(sort, []);
    return mkApp(OP_MUL, args, sort);
  }
  if (choice === 7) return mkApp(OP_ABS, [gen(sort, env, next)], sort);
  if (choice === 8) {
    const branches = genArgs(2, sort, env, next).map((branch) =>
      chance(40) ? getLeaf(sort, []) : branch,
    );
    return mkApp(OP_ITE, [gen(SORT_BOOL, env, next), ...branches], sort);
  }
  if (sort === SORT_INT) {
    if (choice === 9 || choice === 10) {
      const divisor = chance(60)
        ? mkInt(pick([0n, 1n, -1n, 2n, 3n, 4n, -6n]))
        : gen(SORT_INT, env, next);
      return mkApp(pick([OP_IDIV, OP_MOD]), [gen(SORT_INT, env, next), divisor], SORT_INT);
    }
    return chance(50)
      ? mkApp(OP_TO_INT, [gen(SORT_REAL, env, next)], SORT_INT)
      : mkApp(declK, [gen(sortU, env, next)], SORT_INT);
  }
  if (choice === 9 || choice === 10) {
    const divisor = chance(60)
      ? mkReal(pick([0n, 1n, 2n, -3n]), pick([1n, 2n]))
      : gen(SORT_REAL, env, next);
    return mkApp(OP_DIV, [gen(SORT_REAL, env, next), divisor], SORT_REAL);
  }
  return mkApp(OP_TO_REAL, [gen(SORT_INT, env, next)], SORT_REAL);
};

const genBool = (env: number[], depth: number): number => {
  const next = depth - 1;
  const choice = random() % 15;
  if (choice === 0 || choice === 1)
    return mkApp(
      pick([OP_AND, OP_OR]),
      genArgs(2 + (random() % 3), SORT_BOOL, env, next),
      SORT_BOOL,
    );
  if (choice === 2) return mkApp(OP_NOT, [gen(SORT_BOOL, env, next)], SORT_BOOL);
  if (choice === 3)
    return mkApp(pick([OP_IMPLIES, OP_XOR]), genArgs(2, SORT_BOOL, env, next), SORT_BOOL);
  if (choice === 4 || choice === 5) {
    const sort = pick([SORT_INT, SORT_INT, SORT_REAL, SORT_BOOL, sortU]);
    return mkApp(OP_EQ, genArgs(2, sort, env, next), SORT_BOOL);
  }
  if (choice === 6) {
    const sort = pick([SORT_INT, sortU]);
    return mkApp(OP_DISTINCT, genArgs(2 + (random() % 3), sort, env, next), SORT_BOOL);
  }
  if (choice === 7 || choice === 8) {
    const sort = pick([SORT_INT, SORT_INT, SORT_REAL]);
    return mkApp(pick([OP_LE, OP_GE, OP_LT, OP_GT]), genArgs(2, sort, env, next), SORT_BOOL);
  }
  if (choice === 9) return mkApp(OP_IS_INT, [gen(SORT_REAL, env, next)], SORT_BOOL);
  if (choice === 10) return mkApp(declG, genArgs(2, SORT_INT, env, next), SORT_BOOL);
  if (choice === 11) return mkApp(OP_ITE, genArgs(3, SORT_BOOL, env, next), SORT_BOOL);
  return genQuantifier(env, next);
};

// A quantifier over one or two variables, whose first variable in Z3's order is var 0. Its body
// often defines a variable, as der eliminates.
const genQuantifier = (env: number[], depth: number) => {
  const isForall = chance(60);
  const sorts = Array.from({ length: 1 + (random() % 2) }, () => pick([SORT_INT, SORT_INT, sortU]));
  const inner = [...sorts].reverse().concat(env);
  let body = gen(SORT_BOOL, inner, depth);
  if (chance(50)) {
    const index = random() % sorts.length;
    const variable = mkVar(index, inner[index]);
    const definition = chance(60)
      ? gen(inner[index], chance(70) ? [] : inner, depth)
      : getLeaf(inner[index], []);
    const eq = mkApp(
      OP_EQ,
      chance(50) ? [variable, definition] : [definition, variable],
      SORT_BOOL,
    );
    body = isForall
      ? mkApp(OP_OR, [mkApp(OP_NOT, [eq], SORT_BOOL), body], SORT_BOOL)
      : mkApp(OP_AND, [eq, body], SORT_BOOL);
  }
  // A directly nested quantifier, which th_rewriter merges into this one when they agree.
  if (chance(25))
    body = mkQuantifier(
      chance(60) === isForall,
      [SORT_INT],
      [0],
      gen(SORT_BOOL, [SORT_INT, ...inner], depth),
      [],
    );
  const names: SmtSymbol[] = sorts.map((_, index) => (chance(50) ? `v${index}` : index));
  const patterns: number[] = [];
  const index = inner.slice(0, sorts.length).indexOf(SORT_INT);
  if (index !== -1 && chance(30))
    patterns.push(mkPattern([mkApp(declF, [mkVar(index, SORT_INT)], SORT_INT)]));
  return mkQuantifier(isForall, sorts, names, body, patterns);
};

const gen = (sort: number, env: number[], depth: number): number => {
  if (depth <= 0 || chance(20)) return getLeaf(sort, env);
  const shared = [...getPool(sort), ...(locals.get(sort) ?? [])];
  if (shared.length > 0 && chance(12)) return pick(shared);
  if (sort === sortU)
    return share(
      mkApp(OP_ITE, [gen(SORT_BOOL, env, depth - 1), ...genArgs(2, sortU, env, depth - 1)], sortU),
    );
  if (sort === SORT_INT || sort === SORT_REAL) return share(genNumeric(sort, env, depth));
  return share(genBool(env, depth));
};

// Builds a term inside temporaries, so that its subterms are held only by their parents.
const build = (sort: number) => {
  const outer = manager.beginTemporaries();
  record("begin", `${outer}`);
  locals = new Map();
  const expr = gen(sort, [], 2 + (random() % 4));
  hold(expr);
  manager.endTemporaries(outer);
  record(`end ${outer}`, "-");
  return expr;
};

const OPTIONS = {
  kernel: KERNEL_REWRITER_OPTIONS,
  tactic: TACTIC_REWRITER_OPTIONS,
  pull: { ...TACTIC_REWRITER_OPTIONS, isPullingCheapIte: true },
  kpull: { ...KERNEL_REWRITER_OPTIONS, isPullingCheapIte: true },
  elim: KERNEL_REWRITER_OPTIONS,
};
type Name = keyof typeof OPTIONS;
const NAMES = Object.keys(OPTIONS) as Name[];

const mkRewriters = () => {
  const rewriters = Object.fromEntries(
    NAMES.map((name) => [name, new Rewriter(manager, OPTIONS[name])]),
  ) as Record<Name, Rewriter>;
  rewriters.elim.setEliminatingAnd(true);
  return rewriters;
};

const BOOL_SORTS = [SORT_BOOL, SORT_BOOL, SORT_BOOL, SORT_INT, SORT_REAL];

const pickTerm = (sort?: number) =>
  sort === undefined ? pick(held) : pick(getPool(sort).length > 0 ? getPool(sort) : held);

let rewriters = mkRewriters();
let der = new Der(manager);

// One operation of the random part.
const step = () => {
  const choice = random() % 100;
  const name = pick(NAMES);
  const rewriter = rewriters[name];
  if (choice < 8) build(pick(BOOL_SORTS));
  else if (choice < 52) {
    const expr = pickTerm();
    recordOwned(`rw ${name} ${expr}`, () => rewriter.rewrite(expr));
  } else if (choice < 58) {
    const sort = pick([SORT_INT, SORT_REAL, SORT_BOOL]);
    const ops =
      sort === SORT_BOOL
        ? [OP_AND, OP_OR, OP_NOT, OP_IMPLIES, OP_XOR, OP_EQ, OP_DISTINCT, OP_ITE]
        : [OP_ADD, OP_SUB, OP_MUL, OP_UMINUS, OP_LE, OP_GE, OP_LT, OP_GT, OP_EQ, OP_ITE, OP_ABS];
    const op = pick(ops);
    const arity =
      op === OP_NOT || op === OP_UMINUS || op === OP_ABS
        ? 1
        : op === OP_ITE
          ? 3
          : op === OP_AND || op === OP_OR || op === OP_ADD || op === OP_DISTINCT
            ? 2 + (random() % 3)
            : 2;
    const args = Array.from({ length: arity }, (_, index) =>
      op === OP_ITE && index === 0 ? pickTerm(SORT_BOOL) : pickTerm(sort),
    );
    const range = [OP_LE, OP_GE, OP_LT, OP_GT, OP_EQ, OP_DISTINCT].includes(op) ? SORT_BOOL : sort;
    const isCore = chance(50);
    recordOwned(
      `${isCore ? "mk-app-core" : "mk-app"} ${name} ${op} ${getList(args)} ${range}`,
      () =>
        manager.withTemporaries(() =>
          isCore ? rewriter.mkAppCore(op, args, range) : rewriter.mkApp(op, args, range),
        ),
    );
  } else if (choice < 64) {
    const kind = random() % 6;
    if (kind === 0) {
      const args = [pickTerm(SORT_BOOL), pickTerm(SORT_BOOL)];
      recordOwned(`mk-eq ${name} ${getList(args)}`, () =>
        manager.withTemporaries(() => rewriter.mkEq(args[0], args[1])),
      );
    } else if (kind === 1) {
      const arg = pickTerm(SORT_BOOL);
      recordOwned(`mk-not ${name} ${arg}`, () =>
        manager.withTemporaries(() => rewriter.mkNot(arg)),
      );
    } else if (kind === 2 || kind === 3) {
      const args = Array.from({ length: 1 + (random() % 4) }, () => pickTerm(SORT_BOOL));
      const op = kind === 2 ? "mk-or" : "mk-and";
      recordOwned(`${op} ${name} ${getList(args)}`, () =>
        manager.withTemporaries(() => (kind === 2 ? rewriter.mkOr(args) : rewriter.mkAnd(args))),
      );
    } else if (kind === 4) {
      const sort = pick([SORT_INT, SORT_REAL]);
      const args = Array.from({ length: 1 + (random() % 4) }, () => pickTerm(sort));
      recordOwned(`mk-add ${name} ${getList(args)}`, () =>
        manager.withTemporaries(() => rewriter.mkAdd(args)),
      );
    } else {
      const sort = pick([SORT_INT, SORT_REAL]);
      const args = [pickTerm(sort), pickTerm(sort)];
      recordOwned(`mk-sub ${name} ${getList(args)}`, () =>
        manager.withTemporaries(() => rewriter.mkSub(args[0], args[1])),
      );
    }
  } else if (choice < 76) {
    // der on a quantifier, often after rewriting it.
    const quantifiers = held.filter((expr) => manager.kinds[expr] === KIND_QUANTIFIER);
    if (quantifiers.length === 0) return;
    const expr = pick(quantifiers);
    recordOwned(`der ${expr}`, () => manager.withTemporaries(() => der.apply(expr)));
  } else if (choice < 80) {
    const pairs: [number, number][] = [];
    for (let count = random() % 4; count > 0; count--) {
      const sort = pick([SORT_INT, SORT_BOOL, SORT_REAL]);
      const key = pickTerm(sort);
      const value =
        sort === SORT_BOOL ? pick([manager.trueExpr, manager.falseExpr]) : pickTerm(sort);
      if (manager.sorts[key] === manager.sorts[value]) pairs.push([key, value]);
    }
    rewriter.setSubstitution(new Map(pairs));
    record(`set-subst ${name} ${getList(pairs.map((pair) => pair.join(":")))}`, "-");
  } else if (choice < 82) {
    const isCleanup = chance(50);
    if (isCleanup) rewriter.cleanup();
    else rewriter.reset();
    record(`${isCleanup ? "cleanup" : "reset"} ${name}`, "-");
  } else if (choice < 83) {
    const isEliminatingAnd = chance(50);
    rewriter.setEliminatingAnd(isEliminatingAnd);
    rewriter.reset();
    record(`elim-and ${name} ${isEliminatingAnd ? 1 : 0}`, "-");
  } else {
    const expr = pickTerm(SORT_BOOL);
    recordOwned(`rw ${name} ${expr}`, () => rewriter.rewrite(expr));
  }
};

const NUM_EPISODES = 25;
for (let episode = 0; episode < NUM_EPISODES; episode++) {
  // The last episode has a small budget, which a rewrite spends.
  const stepLimit = episode === NUM_EPISODES - 1 ? 200 : STEP_LIMIT;
  if (episode > 0) {
    manager = mkManager(stepLimit);
    record(`episode ${stepLimit}`, "-");
    held = [];
    pools = new Map();
    declare();
    rewriters = mkRewriters();
    der = new Der(manager);
  }
  try {
    for (let index = 0; index < 12; index++) build(pick(BOOL_SORTS));
    dumpRefs();
    for (let index = 0; index < 150; index++) {
      step();
      if (index % 50 === 0) dumpRefs();
    }
    for (const name of NAMES) {
      rewriters[name].release();
      record(`release ${name}`, "-");
    }
    der.release();
    record("release-der", "-");
    dumpRefs();
  } catch (error) {
    if (!(error instanceof SmtCanceledError)) throw error;
    // The operation that the budget stopped, with the steps it took.
    record(`canceled ${pending}`, "-");
  }
}

// The fixtures: each is parsed with a manager of its own, and each assertion rewritten with the
// kernel's and the tactics' rewriters and, when it is a quantifier, with der.
const fixtures = join(import.meta.dir, "../tests/fixtures/smt");
for (const file of readdirSync(fixtures)
  .filter((name) => name.endsWith(".smt"))
  .sort()) {
  manager = mkManager(Number.POSITIVE_INFINITY);
  const problem = parseSmtlib(readFileSync(join(fixtures, file), "utf8"), manager, () => {});
  record(`fixture ${file}`, `${problem.assertions.length}`);
  rewriters = mkRewriters();
  const fixtureDer = new Der(manager);
  problem.assertions.forEach((assertion, index) => {
    for (const name of ["kernel", "tactic"] as const)
      recordOwned(`frw ${name} ${index}`, () => rewriters[name].rewrite(assertion));
    if (manager.kinds[assertion] === KIND_QUANTIFIER)
      recordOwned(`fder ${index}`, () =>
        manager.withTemporaries(() => fixtureDer.apply(assertion)),
      );
  });
  for (const name of NAMES) rewriters[name].release();
  fixtureDer.release();
  record("frelease", "-");
  dumpRefs();
}

const directory = join(import.meta.dir, "../native/crates/prover/smt/tests/tables");
mkdirSync(directory, { recursive: true });
writeFileSync(join(directory, "th-rewriter.txt"), `${lines.join("\n")}\n`);

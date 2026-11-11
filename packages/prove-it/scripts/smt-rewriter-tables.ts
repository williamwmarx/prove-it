// Writes the table the Rust port of the SMT core's rewriters (design/smt-core.md) is tested against,
// from the TypeScript it ports. rewriter.txt is a seeded sequence of operations on ast.ts's
// AstManager: it builds random terms with quantifiers and de Bruijn variables, and applies to them
// var-subst.ts (substitution in standard order and not, used variables, elimination of unused
// variables, replacement of free variables), the var shifters and the beta reducer of
// rewriter-tpl.ts, expr-safe-replace.ts, ast-lt.ts, ast-util.ts and rewriter-tpl.ts's main loop with
// the default configuration and a test one. Each line records the operation with what it returned,
// the resource limit's step count and the number of ASTs, and the ids and reference counts of every
// expression at checkpoints. prove-smt's tests/rewriter.rs replays the operations:
//   bun scripts/smt-rewriter-tables.ts

import { mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import {
  AstManager,
  KIND_APP,
  KIND_QUANTIFIER,
  OP_ADD,
  OP_AND,
  OP_EQ,
  OP_IMPLIES,
  OP_ITE,
  OP_LE,
  OP_NOT,
  OP_OR,
  type SmtSymbol,
  SORT_BOOL,
  SORT_INT,
  SORT_REAL,
} from "../src/prover/smt/solver/ast";
import { isAstLess } from "../src/prover/smt/solver/ast-lt";
import {
  flattenAndVector,
  flattenOrVector,
  mkNot,
  pushNotOwned,
} from "../src/prover/smt/solver/ast-util";
import { ExprSafeReplace } from "../src/prover/smt/solver/expr-safe-replace";
import { Rational } from "../src/prover/smt/solver/rational";
import { RefVector } from "../src/prover/smt/solver/ref-vector";
import {
  BetaReducer,
  InvVarShifter,
  type Rewrite,
  RewriterTpl,
  VarShifter,
} from "../src/prover/smt/solver/rewriter-tpl";
import { ResourceLimit } from "../src/prover/smt/solver/rlimit";
import {
  collectUsedVars,
  elimUnusedVars,
  getFreeVarSorts,
  replaceFreeVars,
  UnusedVarsEliminator,
  VarSubst,
} from "../src/prover/smt/solver/var-subst";

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

const random = createRandom(0x2e_717e);
const pick = <T>(items: T[]) => items[random() % items.length];
const chance = (percent: number) => random() % 100 < percent;

const manager = new AstManager(new ResourceLimit(Number.POSITIVE_INFINITY));
const lines: string[] = [];

const getList = (items: (number | string)[]) => (items.length === 0 ? "-" : items.join(","));
const getSymbolText = (symbol: SmtSymbol) =>
  typeof symbol === "number" ? `n:${symbol}` : `s:${symbol}`;

// One more than the largest handle, since every expression the script makes is described.
let numNodes = 2;

// An expression as the table records it, with its text when it is shallow.
const describe = (expr: number) => {
  numNodes = Math.max(numNodes, expr + 1);
  const fields = `${expr}:${manager.ids[expr]}:${manager.hashes[expr]}`;
  return manager.depths[expr] <= 5 ? `${fields} | ${manager.toString(expr)}` : fields;
};

const record = (operation: string, result: string) =>
  lines.push(`${operation} => ${result} steps=${manager.limit.count} asts=${manager.getNumAsts()}`);

const recordExpr = (operation: string, make: () => number) => {
  const expr = make();
  record(operation, describe(expr));
  return expr;
};

// Records a result that comes with a reference, and releases it.
const recordOwned = (operation: string, make: () => number) => {
  const expr = recordExpr(operation, make);
  manager.decRef(expr);
  return expr;
};

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

// The terms the script holds a reference to, by sort, and in the order it took them.
const held: number[] = [];
const pools = new Map<number, number[]>();
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

const sortU = mkSort("U");
const declF = mkDecl("f", [sortU], sortU);
const declG = mkDecl("g", [sortU, sortU], SORT_BOOL);
const declH = mkDecl("h", [SORT_INT], SORT_INT);
const declSk = mkDecl("sk", [sortU], SORT_INT, true);
// The macros of the test configuration.
const declM1 = mkDecl("m1", [sortU], sortU);
const declM2 = mkDecl("m2", [SORT_INT], SORT_INT);
const declM3 = mkDecl("m3", [SORT_INT], SORT_INT);
const declC = mkDecl("c", [], sortU);
const declD = mkDecl("d", [], sortU);
const declP = mkDecl("p", [], SORT_BOOL);
const declQ = mkDecl("q", [], SORT_BOOL);
const declX = mkDecl("x", [], SORT_INT);
const declY = mkDecl("y", [], SORT_INT);
const declZ = mkDecl("z", [], SORT_REAL);
const constC = hold(mkApp(declC, [], sortU));
const constD = hold(mkApp(declD, [], sortU));
const constP = hold(mkApp(declP, [], SORT_BOOL));
const constQ = hold(mkApp(declQ, [], SORT_BOOL));
const constX = hold(mkApp(declX, [], SORT_INT));
const constY = hold(mkApp(declY, [], SORT_INT));
const constZ = hold(mkApp(declZ, [], SORT_REAL));
// m1(u) = f(f(u)), m2(i) = 7, a ground definition, and m3(i) = i, a definition that is a variable.
const defM1 = hold(mkApp(declF, [mkApp(declF, [mkVar(0, sortU)], sortU)], sortU));
const defM2 = hold(mkInt(7n));
const defM3 = hold(mkVar(0, SORT_INT));
// The handles the test configuration reads.
record(
  `config ${getList([declG, declH, declM1, declM2, declP, declQ, declX, constC, constD, constP, constY, defM1, defM2, declM3, defM3])}`,
  "-",
);

// The sorts of the free variables of a top-level term, by de Bruijn index.
const FREE = [sortU, SORT_INT, sortU, SORT_BOOL];

// The terms built in the current temporaries, by sort, which later terms may share.
let locals = new Map<number, number[]>();
const share = (expr: number) => {
  const local = locals.get(manager.sorts[expr]) ?? [];
  locals.set(manager.sorts[expr], local);
  local.push(expr);
  return expr;
};

const getLeaf = (sort: number, env: number[]): number => {
  const indexes = env.flatMap((varSort, index) => (varSort === sort ? [index] : []));
  if (indexes.length > 0 && chance(45)) return mkVar(pick(indexes), sort);
  if (sort === sortU)
    return chance(80) ? pick([constC, constD]) : mkModelValue(random() % 3, sortU);
  if (sort === SORT_INT)
    return chance(50) ? pick([constX, constY]) : mkInt(BigInt(random() % 5) - 1n);
  if (sort === SORT_REAL) return chance(50) ? constZ : mkReal(BigInt(random() % 7) - 3n, 2n);
  return pick([constP, constQ, manager.trueExpr, manager.falseExpr]);
};

const gen = (sort: number, env: number[], depth: number): number => {
  if (depth === 0 || chance(25)) return getLeaf(sort, env);
  const shared = [...getPool(sort), ...(locals.get(sort) ?? [])];
  if (shared.length > 0 && chance(15)) return pick(shared);
  const next = depth - 1;
  if (sort === sortU) {
    const choice = random() % 3;
    if (choice === 0) return share(mkApp(declF, [gen(sortU, env, next)], sortU));
    if (choice === 1) return share(mkApp(declM1, [gen(sortU, env, next)], sortU));
    return share(
      mkApp(
        OP_ITE,
        [gen(SORT_BOOL, env, next), gen(sortU, env, next), gen(sortU, env, next)],
        sortU,
      ),
    );
  }
  if (sort === SORT_INT) {
    const choice = random() % 6;
    if (choice === 5) return share(mkApp(declM3, [gen(SORT_INT, env, next)], SORT_INT));
    if (choice === 0) return share(mkApp(declH, [gen(SORT_INT, env, next)], SORT_INT));
    if (choice === 1) return share(mkApp(declM2, [gen(SORT_INT, env, next)], SORT_INT));
    if (choice === 2) return share(mkApp(declSk, [gen(sortU, env, next)], SORT_INT));
    if (choice === 3)
      return share(mkApp(OP_ADD, [gen(SORT_INT, env, next), gen(SORT_INT, env, next)], SORT_INT));
    return share(
      mkApp(
        OP_ITE,
        [gen(SORT_BOOL, env, next), gen(SORT_INT, env, next), gen(SORT_INT, env, next)],
        SORT_INT,
      ),
    );
  }
  if (sort === SORT_REAL)
    return share(mkApp(OP_ADD, [gen(SORT_REAL, env, next), gen(SORT_REAL, env, next)], SORT_REAL));
  const choice = random() % 9;
  if (choice === 0)
    return share(mkApp(declG, [gen(sortU, env, next), gen(sortU, env, next)], SORT_BOOL));
  if (choice === 1 || choice === 2) {
    const op = choice === 1 ? OP_AND : OP_OR;
    const args = Array.from({ length: 2 + (random() % 3) }, () => gen(SORT_BOOL, env, next));
    return share(mkApp(op, args, SORT_BOOL));
  }
  if (choice === 3) return share(mkApp(OP_NOT, [gen(SORT_BOOL, env, next)], SORT_BOOL));
  if (choice === 4)
    return share(
      mkApp(pick([OP_EQ, OP_LE]), [gen(SORT_INT, env, next), gen(SORT_INT, env, next)], SORT_BOOL),
    );
  if (choice === 5)
    return share(
      mkApp(OP_IMPLIES, [gen(SORT_BOOL, env, next), gen(SORT_BOOL, env, next)], SORT_BOOL),
    );
  if (choice === 6)
    return share(
      mkApp(
        OP_ITE,
        [gen(SORT_BOOL, env, next), gen(SORT_BOOL, env, next), gen(SORT_BOOL, env, next)],
        SORT_BOOL,
      ),
    );
  // A quantifier over one or two variables, whose first variable in Z3's order is var 0.
  const sorts = Array.from({ length: 1 + (random() % 2) }, () => pick([sortU, SORT_INT]));
  const inner = [...sorts].reverse().concat(env);
  const body = gen(SORT_BOOL, inner, next);
  const names: SmtSymbol[] = sorts.map((_, index) => (chance(50) ? `v${index}` : index));
  const patterns: number[] = [];
  const index = inner.slice(0, sorts.length).indexOf(sortU);
  if (index !== -1 && chance(60))
    patterns.push(mkPattern([mkApp(declF, [mkVar(index, sortU)], sortU)]));
  return share(mkQuantifier(chance(70), sorts, names, body, patterns));
};

// Builds a term inside temporaries, so that its subterms are held only by their parents.
const build = (sort: number) => {
  const outer = manager.beginTemporaries();
  record("begin", `${outer}`);
  locals = new Map();
  const expr = gen(sort, FREE, 1 + (random() % 5));
  hold(expr);
  manager.endTemporaries(outer);
  record(`end ${outer}`, "-");
  return expr;
};

const pickTerm = (sort?: number) =>
  sort === undefined ? pick(held) : pick(getPool(sort).length > 0 ? getPool(sort) : held);

// The test configurations: they flatten and and or, reduce some applications and constants,
// expand m1, m2 and m3, and reduce a quantifier with a constant body. TestRewriter also
// substitutes c for d, and the base, which substitutes nothing, rewrites the arguments of a result
// to depth 0 as they are.
class TestRewriterBase extends RewriterTpl {
  constructor(
    manager: AstManager,
    protected isPatterns: boolean,
  ) {
    super(manager);
  }

  isFlatAssoc(decl: number) {
    const op = this.manager.funcDecls[decl].op;
    return op === OP_AND || op === OP_OR;
  }

  isRewritingPatterns() {
    return this.isPatterns;
  }

  reduceApp(decl: number, args: number[]): number | Rewrite {
    const manager = this.manager;
    const op = manager.funcDecls[decl].op;
    if (op === OP_NOT && manager.isNot(args[0])) {
      const result = manager.getArg(args[0], 0);
      manager.incRef(result);
      return result;
    }
    if (op === OP_AND && args.some((arg) => manager.isFalse(arg))) {
      manager.incRef(manager.falseExpr);
      return manager.falseExpr;
    }
    if (op === OP_AND && args.some((arg) => manager.isTrue(arg))) {
      const rest = args.filter((arg) => !manager.isTrue(arg));
      return { expr: manager.withTemporaries(() => manager.mkAnd(rest)), depth: 1 };
    }
    if (op === OP_OR && args.some((arg) => manager.isFalse(arg))) {
      const rest = args.filter((arg) => !manager.isFalse(arg));
      return { expr: manager.withTemporaries(() => manager.mkOr(rest)), depth: 1 };
    }
    if (decl === declP)
      return {
        expr: manager.withTemporaries(() =>
          manager.mkApp(
            OP_OR,
            [constP, manager.mkApp(declG, [constC, constD], SORT_BOOL)],
            SORT_BOOL,
          ),
        ),
        depth: 3,
      };
    if (decl === declQ) {
      manager.incRef(constP);
      return { expr: constP, depth: 2 };
    }
    if (decl === declX) {
      manager.incRef(constY);
      return constY;
    }
    if (decl === declH && manager.isNumeral(args[0])) {
      const result = manager.mkNumeral(manager.getNumeralValue(args[0]) + 1n);
      manager.incRef(result);
      return result;
    }
    return -1;
  }

  getMacro(decl: number) {
    return decl === declM1 ? defM1 : decl === declM2 ? defM2 : decl === declM3 ? defM3 : -1;
  }

  isReducingMacro() {
    return this.isPatterns;
  }

  reduceQuantifier(_expr: number, body: number) {
    if (!this.manager.isTrue(body) && !this.manager.isFalse(body)) return -1;
    this.manager.incRef(body);
    return body;
  }

  mkNested() {
    return new TestRewriterBase(this.manager, this.isPatterns);
  }
}

class TestRewriter extends TestRewriterBase {
  getSubst(expr: number) {
    return expr === constD ? constC : undefined;
  }

  mkNested() {
    return new TestRewriter(this.manager, this.isPatterns);
  }
}

const rewriters: Record<string, RewriterTpl> = {
  default: new RewriterTpl(manager),
  test: new TestRewriter(manager, true),
  "test-np": new TestRewriterBase(manager, false),
};
const substs = { std: new VarSubst(manager, true), ns: new VarSubst(manager, false) };
const shifter = new VarShifter(manager);
const invShifter = new InvVarShifter(manager);
const reducer = new BetaReducer(manager);
const eliminator = new UnusedVarsEliminator(manager);

// Arguments for the free variables of a term: a term of each variable's sort, or -1.
const getArgs = (isStdOrder: boolean) => {
  const sorts = FREE.slice(0, 1 + (random() % FREE.length));
  const args = sorts.map((sort) => (chance(15) ? -1 : pickTerm(sort)));
  return isStdOrder ? args.reverse() : args;
};

// The subterms of a term, with the terms under its quantifiers.
const getSubterms = (expr: number) => {
  const subterms: number[] = [];
  const todo = [expr];
  for (let current = todo.pop(); current !== undefined; current = todo.pop()) {
    subterms.push(current);
    if (manager.kinds[current] === KIND_APP) todo.push(...manager.getArgs(current));
    else if (manager.kinds[current] === KIND_QUANTIFIER)
      todo.push(manager.getQuantifier(current).body);
  }
  return subterms;
};

const dumpRefs = () => {
  const handles = Array.from({ length: numNodes }, (_, index) => index);
  record(
    "refs",
    getList(handles.map((handle) => `${manager.ids[handle]}/${manager.getRefCount(handle)}`)),
  );
};

for (let index = 0; index < 40; index++) build(pick([SORT_BOOL, SORT_BOOL, SORT_INT, sortU]));
dumpRefs();

for (let step = 0; step < 1500; step++) {
  const choice = random() % 100;
  if (choice < 8) build(pick([SORT_BOOL, SORT_BOOL, SORT_INT, sortU]));
  else if (choice < 18) {
    const name = pick(["std", "ns"] as const);
    const expr = pickTerm();
    const args = getArgs(name === "std");
    recordOwned(`subst ${name} ${expr} ${getList(args)}`, () => substs[name].apply(expr, args));
  } else if (choice < 24) {
    const expr = pickTerm();
    const bound = random() % 3;
    const shift1 = random() % 3;
    const shift2 = random() % 2;
    const shifted = recordExpr(`shift ${expr} ${bound} ${shift1} ${shift2}`, () =>
      shifter.shift(expr, bound, shift1, shift2),
    );
    if (bound === 0)
      recordOwned(`inv-shift ${shifted} ${shift1}`, () => invShifter.shift(shifted, shift1));
    manager.decRef(shifted);
  } else if (choice < 34) {
    const expr = pickTerm();
    const bindings = getArgs(true);
    const kind = random() % 3;
    if (kind === 0)
      recordOwned(`beta ${expr} ${getList(bindings)}`, () =>
        reducer.rewriteWithBindings(expr, bindings),
      );
    else if (kind === 1)
      recordOwned(`beta-set ${expr} ${getList(bindings)}`, () => {
        reducer.reset();
        reducer.setBindings(bindings);
        return reducer.rewrite(expr);
      });
    else {
      const position = random() % bindings.length;
      const binding = pickTerm(FREE[bindings.length - 1 - position]);
      recordOwned(`beta-update ${expr} ${getList(bindings)} ${position} ${binding}`, () => {
        manager.decRef(reducer.rewriteWithBindings(expr, bindings));
        reducer.updateInvBindingAt(position, binding);
        return reducer.rewrite(expr);
      });
    }
  } else if (choice < 42) {
    const expr = pickTerm();
    const subterms = getSubterms(expr);
    const sources: number[] = [];
    const targets: number[] = [];
    for (let count = 1 + (random() % 3); count > 0; count--) {
      const source = chance(70) ? pick(subterms) : mkVar(random() % 4, pick(FREE));
      sources.push(source);
      targets.push(
        chance(20) ? mkVar(random() % 4, manager.sorts[source]) : pickTerm(manager.sorts[source]),
      );
    }
    recordOwned(`replace ${expr} ${getList(sources)} ${getList(targets)}`, () => {
      const replace = new ExprSafeReplace(manager);
      sources.forEach((source, index) => replace.insert(source, targets[index]));
      const result = replace.apply(expr);
      replace.release();
      return result;
    });
  } else if (choice < 52) {
    const first = pickTerm();
    const sort = manager.sorts[first];
    const second = chance(10)
      ? first
      : chance(50)
        ? pickTerm(sort)
        : pick([...getSubterms(pickTerm(sort)), pickTerm(sort)]);
    record(`lt ${first} ${second}`, isAstLess(manager, first, second) ? "1" : "0");
  } else if (choice < 54) {
    const sort = pick([SORT_INT, SORT_REAL]);
    const first =
      sort === SORT_INT
        ? mkInt(BigInt(random() % 9) - 4n)
        : mkReal(BigInt(random() % 9) - 4n, BigInt(1 + (random() % 3)));
    const second =
      sort === SORT_INT
        ? mkInt(BigInt(random() % 9) - 4n)
        : mkReal(BigInt(random() % 9) - 4n, BigInt(1 + (random() % 3)));
    record(`lt ${first} ${second}`, isAstLess(manager, first, second) ? "1" : "0");
  } else if (choice < 57) {
    const expr = pickTerm(SORT_BOOL);
    recordExpr(`mk-not ${expr}`, () => mkNot(manager, expr));
  } else if (choice < 63) {
    const isAnd = chance(50);
    const items = Array.from({ length: 1 + (random() % 4) }, () => pickTerm(SORT_BOOL));
    const vector = new RefVector(manager);
    for (const item of items) vector.push(item);
    if (isAnd) flattenAndVector(manager, vector);
    else flattenOrVector(manager, vector);
    record(
      `${isAnd ? "flatten-and" : "flatten-or"} ${getList(items)}`,
      getList(vector.items.map(describe)),
    );
    vector.reset();
  } else if (choice < 66) {
    const expr = pickTerm(SORT_BOOL);
    recordOwned(`push-not ${expr}`, () => pushNotOwned(manager, expr));
  } else if (choice < 82) {
    const name = pick(["default", "test", "test", "test-np"]);
    const expr = pickTerm();
    recordOwned(`rewrite ${name} ${expr}`, () => rewriters[name].rewrite(expr));
  } else if (choice < 85) {
    const expr = pickTerm();
    const bindings = getArgs(true);
    recordOwned(`rewrite-bind ${expr} ${getList(bindings)}`, () =>
      rewriters.default.rewriteWithBindings(expr, bindings),
    );
  } else if (choice < 86) {
    const name = pick(["default", "test", "test-np"]);
    const isCleanup = chance(30);
    if (isCleanup) rewriters[name].cleanup();
    else rewriters[name].reset();
    record(`${isCleanup ? "cleanup" : "reset"} ${name}`, "-");
  } else if (choice < 91) {
    const expr = pickTerm(SORT_BOOL);
    if (chance(50))
      recordOwned(`elim-unused ${expr}`, () =>
        manager.withTemporaries(() => elimUnusedVars(manager, expr)),
      );
    else recordOwned(`elim-unused-p ${expr}`, () => eliminator.apply(expr));
  } else if (choice < 95) {
    const expr = pickTerm();
    const count = random() % 6;
    if (chance(50))
      record(
        `free-var-sorts ${expr} ${count}`,
        getList(getFreeVarSorts(manager, expr, count).map((sort) => sort ?? "-")),
      );
    else
      record(
        `collect-used ${expr} ${count}`,
        getList(collectUsedVars(manager, expr, count).map((isUsed) => (isUsed ? 1 : 0))),
      );
  } else {
    const expr = pickTerm();
    recordOwned(`replace-free ${expr}`, () =>
      manager.withTemporaries(() =>
        replaceFreeVars(manager, expr, (variable, index, shift) =>
          index % 2 === 0
            ? manager.mkVar(index + shift + 1, manager.sorts[variable])
            : manager.mkVar(manager.values[variable], manager.sorts[variable]),
        ),
      ),
    );
  }
  if (step % 100 === 0) dumpRefs();
}
dumpRefs();

// A deep term with many shared subterms, whose rewrites leave more unused entries in a cache than
// it keeps, so that act_cache deletes the oldest, and expand its table many times.
const outer = manager.beginTemporaries();
record("begin", `${outer}`);
let chain = mkApp(declF, [mkVar(0, sortU)], sortU);
for (let index = 0; index < 300; index++)
  chain = mkApp(OP_ITE, [constP, chain, mkApp(declF, [chain], sortU)], sortU);
// The terms of the chain that a conjunction outside it shares are cached and never looked up.
const sides: number[] = [];
for (let index = 0; index < 1300; index++) {
  chain = mkApp(declF, [chain], sortU);
  sides.push(mkApp(declG, [chain, constC], SORT_BOOL));
}
hold(chain);
hold(mkApp(OP_AND, sides, SORT_BOOL));
manager.endTemporaries(outer);
record(`end ${outer}`, "-");
for (const name of ["default", "test", "test-np", "default"])
  recordOwned(`rewrite ${name} ${chain}`, () => rewriters[name].rewrite(chain));
recordOwned(`subst std ${chain} ${constD}`, () => substs.std.apply(chain, [constD]));
// Results that the main loop rewrites again to depth 1, whose arguments a configuration that
// substitutes nothing keeps as they are.
const shallowOuter = manager.beginTemporaries();
record("begin", `${shallowOuter}`);
const appliedC = mkApp(declG, [mkApp(declF, [constC], sortU), constC], SORT_BOOL);
const shallow = [
  mkApp(
    OP_AND,
    [
      manager.trueExpr,
      constQ,
      appliedC,
      mkApp(OP_NOT, [mkApp(OP_NOT, [constQ], SORT_BOOL)], SORT_BOOL),
    ],
    SORT_BOOL,
  ),
  mkApp(
    OP_OR,
    [
      manager.falseExpr,
      mkApp(OP_EQ, [mkApp(declH, [mkInt(1n)], SORT_INT), constX], SORT_BOOL),
      mkApp(declG, [mkVar(0, sortU), constD], SORT_BOOL),
    ],
    SORT_BOOL,
  ),
];
shallow.push(mkApp(OP_AND, [manager.trueExpr, shallow[0], shallow[1]], SORT_BOOL));
for (const expr of shallow) hold(expr);
manager.endTemporaries(shallowOuter);
record(`end ${shallowOuter}`, "-");
for (const expr of shallow)
  for (const name of ["default", "test", "test-np"])
    recordOwned(`rewrite ${name} ${expr}`, () => rewriters[name].rewrite(expr));

const deepBinding = pickTerm(sortU);
recordOwned(`beta ${chain} ${deepBinding}`, () =>
  reducer.rewriteWithBindings(chain, [deepBinding]),
);
recordOwned(`shift ${chain} 0 2 0`, () => shifter.shift(chain, 0, 2, 0));
recordOwned(`replace ${chain} ${constP} ${constQ}`, () => {
  const replace = new ExprSafeReplace(manager);
  replace.insert(constP, constQ);
  const result = replace.apply(chain);
  replace.release();
  return result;
});
for (const name of Object.keys(rewriters)) {
  rewriters[name].release();
  record(`release ${name}`, "-");
}
substs.std.release();
substs.ns.release();
shifter.release();
invShifter.release();
reducer.release();
eliminator.release();
record("release-rest", "-");
dumpRefs();
for (const expr of held.splice(0)) {
  manager.decRef(expr);
  record(`dec ${expr}`, `${manager.getRefCount(expr)}`);
}
dumpRefs();

const directory = join(import.meta.dir, "../native/crates/prover/smt/tests/tables");
mkdirSync(directory, { recursive: true });
writeFileSync(join(directory, "rewriter.txt"), `${lines.join("\n")}\n`);

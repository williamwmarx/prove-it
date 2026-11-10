// Writes the tables the Rust port of the SMT core (design/smt-core.md) is tested against, from the
// TypeScript it ports. ast.txt is a seeded sequence of operations on ast.ts's AstManager, each with
// what it returned: the handle, Z3 id, hash, sort and declaration small id of each expression, the
// number of ASTs, and the ids and reference counts of every expression at checkpoints. It builds
// and releases expressions inside temporaries, so that ids, small ids and deleted expressions are
// recycled. prove-smt's tests/ast.rs replays the operations:
//   bun scripts/smt-core-tables.ts

import { mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import {
  AstManager,
  FAMILY_USER,
  KIND_APP,
  OP_ABS,
  OP_ADD,
  OP_DISTINCT,
  OP_DIV,
  OP_DIV0,
  OP_GE,
  OP_GT,
  OP_IDIV,
  OP_IDIV0,
  OP_IMPLIES,
  OP_IS_INT,
  OP_ITE,
  OP_LE,
  OP_LT,
  OP_MOD,
  OP_MOD0,
  OP_MUL,
  OP_NUM,
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
import { Rational } from "../src/prover/smt/solver/rational";
import { ResourceLimit } from "../src/prover/smt/solver/rlimit";

// xorshift32, seeded, so that the tables don't change between runs.
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

const random = createRandom(0x5eed_a57);
const pick = <T>(items: T[]) => items[random() % items.length];
const chance = (percent: number) => random() % 100 < percent;

const manager = new AstManager(new ResourceLimit(Number.POSITIVE_INFINITY));
const lines: string[] = [];

const getList = (items: (number | string)[]) => (items.length === 0 ? "-" : items.join(","));
const getSymbolText = (symbol: SmtSymbol | null) =>
  symbol === null ? "-" : typeof symbol === "number" ? `n:${symbol}` : `s:${symbol}`;

// One more than the largest handle, since every expression the script makes is described.
let numNodes = 2;

// An expression as the table records it, with its text when it is shallow.
const describe = (expr: number) => {
  numNodes = Math.max(numNodes, expr + 1);
  // mkAnd and mkOr return their one argument as it is, so it may be deleted.
  const declId =
    manager.kinds[expr] === KIND_APP && manager.ids[expr] !== -1 ? manager.getDeclId(expr) : "-";
  const fields = `${expr}:${manager.ids[expr]}:${manager.hashes[expr]}:${manager.sorts[expr]}:${declId}`;
  return manager.depths[expr] <= 4 ? `${fields} | ${manager.toString(expr)}` : fields;
};

const getDeclText = (decl: number) =>
  `${decl}:${manager.funcDecls[decl].smallId}:${manager.getDeclHash(decl) ?? 0}`;

const record = (operation: string, result: string) =>
  lines.push(`${operation} => ${result} asts=${manager.getNumAsts()}`);

const recordExpr = (operation: string, make: () => number) => {
  const expr = make();
  record(operation, describe(expr));
  return expr;
};

const recordError = (operation: string, make: () => unknown) => {
  try {
    make();
  } catch {
    record(operation, "error");
    return;
  }
  throw new Error(`${operation} did not fail`);
};

// The expressions made so far by sort, live or deleted: a deleted one is revived when an
// application of it is made.
const pools = new Map<number, number[]>();
const getPool = (sort: number) => {
  const pool = pools.get(sort) ?? [];
  pools.set(sort, pool);
  return pool;
};
const add = (expr: number) => {
  getPool(manager.sorts[expr]).push(expr);
  return expr;
};
const pickOf = (sort: number) => pick(getPool(sort));

const mkSort = (name: string) => {
  const sort = manager.mkSort(name);
  record(`sort ${name}`, `${sort}`);
  return sort;
};

const mkDecl = (name: SmtSymbol, domain: number[], range: number, isSkolem = false) => {
  const decl = manager.mkFuncDecl(name, domain, range, isSkolem);
  record(
    `decl ${getSymbolText(name)} ${getList(domain)} ${range} ${isSkolem ? 1 : 0}`,
    getDeclText(decl),
  );
  return decl;
};

const mkApp = (decl: number, args: number[], sort: number) =>
  add(recordExpr(`app ${decl} ${getList(args)} ${sort}`, () => manager.mkApp(decl, args, sort)));

const mkInt = (value: bigint) => add(recordExpr(`int ${value}`, () => manager.mkNumeral(value)));

const mkReal = (num: bigint, den: bigint) => {
  const value = Rational.of(num, den);
  return add(recordExpr(`real ${value.num} ${value.den}`, () => manager.mkRealNumeral(value)));
};

const mkAnd = (args: number[]) =>
  add(recordExpr(`and ${getList(args)}`, () => manager.mkAnd(args)));

const mkVar = (index: number, sort: number) =>
  recordExpr(`var ${index} ${sort}`, () => manager.mkVar(index, sort));

const mkFreshConst = (prefix: SmtSymbol | null, sort: number) =>
  add(
    recordExpr(`fresh-const ${getSymbolText(prefix)} ${sort}`, () =>
      manager.mkFreshConst(prefix, sort),
    ),
  );

// The script holds no reference to a model value's declaration until it takes one.
const mkModelValue = (index: number, sort: number) => {
  const expr = add(
    recordExpr(`model-value ${index} ${sort}`, () => manager.mkModelValue(index, sort)),
  );
  declRefs.set(manager.decls[expr], declRefs.get(manager.decls[expr]) ?? 0);
  return expr;
};

// The references to declarations the script holds: one to each it declares.
const declRefs = new Map<number, number>();

const sortU = mkSort("U");
const sortV = mkSort("V");
const sorts = [SORT_BOOL, SORT_INT, SORT_REAL, sortU, sortV];

const declF = mkDecl("f", [sortU], sortU);
const declG = mkDecl("g", [sortU, sortU], SORT_BOOL);
const declH = mkDecl("h", [SORT_INT], SORT_INT);
const declK = mkDecl("k", [SORT_INT, SORT_REAL], SORT_REAL);
const declL = mkDecl("l", [sortV, sortU], sortV);
const declSk = mkDecl("sk", [sortU], SORT_INT, true);
const constants = [
  mkDecl("c", [], sortU),
  mkDecl("d", [], sortU),
  mkDecl("p", [], SORT_BOOL),
  mkDecl("q", [], SORT_BOOL),
  mkDecl("x", [], SORT_INT),
  mkDecl("y", [], SORT_INT),
  mkDecl("z", [], SORT_REAL),
  mkDecl("w", [], SORT_REAL),
  mkDecl("v", [], sortV),
  mkDecl(7, [], SORT_INT),
];
for (const decl of [declF, declG, declH, declK, declL, declSk, ...constants]) declRefs.set(decl, 1);
for (const decl of constants) mkApp(decl, [], manager.funcDecls[decl].range);

for (const value of [0n, 1n, 2n, 3n, 15n, 16n, -1n, -3n, 2n ** 32n - 1n, 2n ** 32n, 2n ** 40n])
  mkInt(value);
mkInt(-(2n ** 70n));
mkInt(10n ** 30n);
for (const [num, den] of [
  [1n, 2n],
  [-7n, 3n],
  [5n, 1n],
  [0n, 1n],
  [2n ** 80n, 3n],
  [-(10n ** 20n), 7n],
])
  mkReal(num, den);
recordError(`app ${OP_NUM} - ${SORT_INT}`, () => manager.mkApp(OP_NUM, [], SORT_INT));

const builders: Record<number, (() => number)[]> = {
  [SORT_BOOL]: [
    () => mkAnd(Array.from({ length: 2 + (random() % 12) }, () => pickOf(SORT_BOOL))),
    () => {
      const args = Array.from({ length: random() % 14 }, () => pickOf(SORT_BOOL));
      return add(recordExpr(`or ${getList(args)}`, () => manager.mkOr(args)));
    },
    () => {
      const arg = pickOf(SORT_BOOL);
      return add(recordExpr(`not ${arg}`, () => manager.mkNot(arg)));
    },
    () => {
      const sort = pick(sorts);
      const [left, right] = [pickOf(sort), pickOf(sort)];
      return add(recordExpr(`eq ${left} ${right}`, () => manager.mkEq(left, right)));
    },
    () => {
      const sort = pick(sorts);
      return mkApp(
        OP_DISTINCT,
        Array.from({ length: 2 + (random() % 16) }, () => pickOf(sort)),
        SORT_BOOL,
      );
    },
    () => {
      const sort = pick([SORT_INT, SORT_REAL]);
      return mkApp(pick([OP_LE, OP_LT, OP_GE, OP_GT]), [pickOf(sort), pickOf(sort)], SORT_BOOL);
    },
    () => mkApp(OP_IS_INT, [pickOf(SORT_REAL)], SORT_BOOL),
    () => mkApp(declG, [pickOf(sortU), pickOf(sortU)], SORT_BOOL),
    () => mkApp(pick([OP_XOR, OP_IMPLIES]), [pickOf(SORT_BOOL), pickOf(SORT_BOOL)], SORT_BOOL),
  ],
  [SORT_INT]: [
    () =>
      mkApp(
        pick([OP_ADD, OP_SUB, OP_MUL, OP_IDIV, OP_MOD, OP_IDIV0, OP_MOD0]),
        [pickOf(SORT_INT), pickOf(SORT_INT)],
        SORT_INT,
      ),
    () =>
      mkApp(
        pick([OP_ADD, OP_MUL]),
        Array.from({ length: 2 + (random() % 13) }, () => pickOf(SORT_INT)),
        SORT_INT,
      ),
    () => mkApp(pick([OP_UMINUS, OP_ABS]), [pickOf(SORT_INT)], SORT_INT),
    () => mkApp(OP_TO_INT, [pickOf(SORT_REAL)], SORT_INT),
    () => mkApp(declH, [pickOf(SORT_INT)], SORT_INT),
    () => mkApp(declSk, [pickOf(sortU)], SORT_INT),
    () => mkApp(OP_ITE, [pickOf(SORT_BOOL), pickOf(SORT_INT), pickOf(SORT_INT)], SORT_INT),
    () => mkInt(BigInt(random() % 40) - 10n),
    () => mkInt(BigInt(random()) * BigInt(random()) * BigInt(random())),
  ],
  [SORT_REAL]: [
    () =>
      mkApp(
        pick([OP_ADD, OP_MUL, OP_DIV, OP_DIV0]),
        [pickOf(SORT_REAL), pickOf(SORT_REAL)],
        SORT_REAL,
      ),
    () =>
      mkApp(
        pick([OP_ADD, OP_MUL]),
        Array.from({ length: 2 + (random() % 13) }, () => pickOf(SORT_REAL)),
        SORT_REAL,
      ),
    () => mkApp(OP_TO_REAL, [pickOf(SORT_INT)], SORT_REAL),
    () => mkApp(declK, [pickOf(SORT_INT), pickOf(SORT_REAL)], SORT_REAL),
    () => mkReal(BigInt(random() % 30) - 10n, BigInt(1 + (random() % 6))),
    () => mkApp(OP_ITE, [pickOf(SORT_BOOL), pickOf(SORT_REAL), pickOf(SORT_REAL)], SORT_REAL),
  ],
  [sortU]: [
    () => mkApp(declF, [pickOf(sortU)], sortU),
    () => mkApp(OP_ITE, [pickOf(SORT_BOOL), pickOf(sortU), pickOf(sortU)], sortU),
    () => mkFreshConst(pick<SmtSymbol | null>([null, "sk", 3]), sortU),
    () => mkModelValue(random() % 4, sortU),
  ],
  [sortV]: [
    () => mkApp(declL, [pickOf(sortV), pickOf(sortU)], sortV),
    () => mkModelValue(random() % 3, sortV),
  ],
};
const build = (sort: number) => pick(builders[sort])();

// A quantifier over one or two variables whose body and pattern apply f and g to them.
const mkQuantifier = (step: number) => {
  const isPair = chance(50);
  const quantifiedSorts = isPair ? [SORT_INT, sortU] : [sortU];
  const names: SmtSymbol[] = isPair ? ["i", chance(50) ? "u" : 0] : [chance(50) ? "u" : "x"];
  const first = mkVar(0, sortU);
  const applied = mkApp(declF, [first], sortU);
  const body = chance(50)
    ? mkApp(declG, [first, applied], SORT_BOOL)
    : mkAnd([mkApp(declG, [applied, pickOf(sortU)], SORT_BOOL), pickOf(SORT_BOOL)]);
  const patterns = chance(70)
    ? [recordExpr(`pattern ${applied}`, () => manager.mkPattern([applied]))]
    : [];
  const isForall = chance(70);
  const weight = chance(70) ? 0 : 5;
  const qid = `q${step % 3}`;
  return add(
    recordExpr(
      `quant ${isForall ? 1 : 0} ${getList(quantifiedSorts)} ${getList(names.map(getSymbolText))} ${body} ${getList(patterns)} ${weight} ${qid}`,
      () =>
        manager.mkQuantifier({
          isForall,
          sorts: quantifiedSorts,
          names,
          body,
          patterns,
          weight,
          qid,
        }),
    ),
  );
};

// The expressions the script holds a reference to.
const held: number[] = [];
const outers: number[] = [];

const dumpIds = () => {
  const handles = Array.from({ length: numNodes }, (_, index) => index);
  record("ids", getList(handles.map((handle) => manager.ids[handle])));
  record("refs", getList(handles.map((handle) => manager.getRefCount(handle))));
};

for (let step = 0; step < 3000; step++) {
  const choice = random() % 100;
  if (choice < 5 && outers.length < 3) {
    const outer = manager.beginTemporaries();
    outers.push(outer);
    record("begin", `${outer}`);
  } else if (choice < 10 && outers.length > 0) {
    const outer = outers.pop() as number;
    manager.endTemporaries(outer);
    record(`end ${outer}`, "-");
  } else if (choice < 16) {
    const live = [...pools.values()].flat().filter((expr) => manager.ids[expr] !== -1);
    if (live.length === 0) continue;
    const expr = pick(live);
    manager.incRef(expr);
    held.push(expr);
    record(`inc ${expr}`, `${manager.getRefCount(expr)}`);
  } else if (choice < 22 && held.length > 0) {
    const expr = held.splice(random() % held.length, 1)[0];
    manager.decRef(expr);
    record(`dec ${expr}`, `${manager.getRefCount(expr)}`);
  } else if (choice < 24 && held.length > 0) {
    const expr = held.splice(random() % held.length, 1)[0];
    manager.releaseLater(expr);
    record(`release-later ${expr}`, `${manager.getRefCount(expr)}`);
  } else if (choice < 26) {
    const decl = pick([...declRefs.keys()]);
    const count = declRefs.get(decl) ?? 0;
    if (count > 0 && chance(60)) {
      manager.decDeclRef(decl);
      declRefs.set(decl, count - 1);
      record(`dec-decl ${decl}`, getDeclText(decl));
    } else {
      manager.incDeclRef(decl);
      declRefs.set(decl, count + 1);
      record(`inc-decl ${decl}`, getDeclText(decl));
    }
  } else if (choice < 29) {
    mkQuantifier(step);
  } else if (choice < 30) {
    const left = pick([...pools.values()].flat());
    const right = pick([...pools.values()].flat());
    const decl = pick([declF, declH, declSk, ...constants]);
    record(
      `query ${left} ${right} ${decl}`,
      [
        manager.isComplement(left, right),
        manager.areDistinct(left, right),
        manager.getTimesMinusOneArg(left) ?? "-",
        manager.isUniqueValue(left),
        manager.isOccurring(decl, left),
        manager.containsModelValue(left),
        manager.isGroundApp(left),
        manager.isGround(left),
        manager.getNumeral(left) ?? "-",
        manager.isUninterpretedConst(left),
      ].join(","),
    );
  } else if (choice < 31) {
    const prefix = pick([null, "t"]);
    record(`fresh-var-name ${prefix ?? "-"}`, manager.mkFreshVarName(prefix));
  } else if (choice < 32) {
    // (* -1 t), which getTimesMinusOneArg finds.
    mkApp(OP_MUL, [mkInt(-1n), pickOf(SORT_INT)], SORT_INT);
  } else if (choice < 33) {
    const decl = pick(
      [...declRefs.keys()].filter(
        (innerDecl) =>
          manager.funcDecls[innerDecl].family === FAMILY_USER &&
          manager.funcDecls[innerDecl].domain.length === 0,
      ),
    );
    mkApp(decl, [], manager.funcDecls[decl].range);
  } else build(pick(sorts));
  if (step === 1000) {
    manager.initFiniteSetPlugin();
    record("finite-set", "-");
  }
  if (step === 1500) {
    const expr = pickOf(SORT_INT);
    manager.mkMacro("m", expr);
    record(`macro m ${expr}`, getDeclText(manager.funcDecls.length - 1));
  }
  if (step % 100 === 0) dumpIds();
}
while (outers.length > 0) {
  const outer = outers.pop() as number;
  manager.endTemporaries(outer);
  record(`end ${outer}`, "-");
}
for (const expr of held.splice(0)) {
  manager.decRef(expr);
  record(`dec ${expr}`, `${manager.getRefCount(expr)}`);
}
dumpIds();
const quantifier = mkQuantifier(0);
recordError(`quant-mismatch ${quantifier}`, () =>
  manager.mkQuantifier({
    ...manager.getQuantifier(quantifier),
    names: [],
  }),
);

const directory = join(import.meta.dir, "../native/crates/prover/smt/tests/tables");
mkdirSync(directory, { recursive: true });
writeFileSync(join(directory, "ast.txt"), `${lines.join("\n")}\n`);

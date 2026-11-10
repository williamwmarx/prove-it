// Writes the tables the Rust SMT foundation (design/prover.md, stage P3a) is tested against, from
// the TypeScript it ports: JavaScript bigint arithmetic and rational.ts in prove-num's tests, and
// Z3's hashes and the slot order of hashtable.ts in prove-smt's. The operands come from a seeded
// generator, so the tables are the same on every run:
//   bun scripts/smt-foundation-tables.ts

import { mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import {
  astArrayHash,
  combineHash,
  getCompositeHash,
  hashU,
  mkMix,
  stringHash,
} from "../src/prover/smt/solver/hash";
import { getIdentityHash, ObjMap } from "../src/prover/smt/solver/hashtable";
import { RandomGen } from "../src/prover/smt/solver/random-gen";
import {
  getEuclideanDiv,
  getEuclideanMod,
  getGcd,
  getLcm,
  Rational,
} from "../src/prover/smt/solver/rational";

const native = join(import.meta.dir, "../native/crates/prover");

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

const random = createRandom(0x2545f491);
const pick = <T>(items: T[]) => items[random() % items.length];

// Limbs that reach the corners of Knuth's division: zero, one, the halves and all ones.
const getLimb = () =>
  random() % 3 === 0 ? pick([0, 1, 0x7fffffff, 0x80000000, 0xfffffffe, 0xffffffff]) : random();

const getOperand = (limbs: number) => {
  let value = 0n;
  for (let index = 0; index < limbs; index++) value = (value << 32n) | BigInt(getLimb());
  return random() % 2 === 0 ? -value : value;
};

const edges = [0n, 1n, 2n, 3n, 10n, 2n ** 31n, 2n ** 32n, 2n ** 53n, 2n ** 63n, 2n ** 64n]
  .flatMap((value) => [value - 1n, value, value + 1n])
  .concat([2n ** 96n - 1n, 2n ** 128n, 10n ** 18n, 10n ** 19n, 10n ** 40n, 3n ** 70n])
  .flatMap((value) => [value, -value]);

const operands = [...new Set([...edges, ...Array.from({ length: 200 }, () => getOperand(1 + (random() % 8)))])];

const pairs = [
  ...edges.flatMap((left, index) =>
    edges.filter((_, other) => (index + other) % 3 === 0).map((right) => [left, right] as const),
  ),
  ...Array.from({ length: 1200 }, () => [pick(operands), pick(operands)] as const),
  ...Array.from({ length: 600 }, () => {
    // A dividend made from the divisor, so that quotients have many limbs.
    const divisor = getOperand(1 + (random() % 4));
    return [divisor * getOperand(1 + (random() % 4)) + getOperand(1 + (random() % 3)), divisor] as const;
  }),
];

const getF64Bits = (value: number) => {
  const view = new DataView(new ArrayBuffer(8));
  view.setFloat64(0, value);
  return view.getBigUint64(0).toString(16);
};

const intLines = [
  ...operands.map(
    (value) =>
      `unary ${value} ${-value} ${value < 0n ? -value : value} ${getF64Bits(Number(value))} ${(value < 0n ? -value : value).toString(2).length}`,
  ),
  ...pairs.map(([left, right]) =>
    [
      "binary",
      left,
      right,
      left + right,
      left - right,
      left * right,
      right === 0n ? "-" : left / right,
      right === 0n ? "-" : left % right,
      left & right,
      getGcd(left, right),
      right === 0n ? "-" : getEuclideanDiv(left, right),
      right === 0n ? "-" : getEuclideanMod(left, right),
      left === 0n && right === 0n ? "-" : getLcm(left, right),
    ].join(" "),
  ),
  ...operands.flatMap((value) =>
    [0, 1, 31, 32, 33, 63, 64, 65, 200].map(
      (shift) => `shift ${value} ${shift} ${value << BigInt(shift)} ${value >> BigInt(shift)}`,
    ),
  ),
  ...operands
    .slice(0, 120)
    .flatMap((value) => [0, 1, 2, 3, 7].map((exponent) => `pow ${value} ${exponent} ${value ** BigInt(exponent)}`)),
];

const getRational = () => {
  const den = getOperand(1 + (random() % 3));
  return Rational.of(getOperand(1 + (random() % 3)), den === 0n ? 1n : den);
};

const rationals = [
  Rational.zero,
  Rational.one,
  Rational.minusOne,
  Rational.of(1n, 2n),
  Rational.of(-7n, 3n),
  Rational.of(4n, 9n),
  Rational.of(-27n, 8n),
  Rational.of(2n ** 40n, 3n ** 20n),
  ...Array.from({ length: 300 }, getRational),
];

const rationalLines = [
  ...rationals.map((value) =>
    [
      "unary",
      value.num,
      value.den,
      value,
      value.neg(),
      value.abs(),
      value.floor(),
      value.ceil(),
      value.isBig(),
      ...[2, 3].map((degree) => value.root(degree) ?? "-"),
      value.pow(3),
    ].join(" "),
  ),
  ...Array.from({ length: 800 }, () => {
    const left = pick(rationals);
    const right = pick(rationals);
    return [
      "binary",
      left.num,
      left.den,
      right.num,
      right.den,
      left.add(right),
      left.sub(right),
      left.mul(right),
      right.isZero() ? "-" : left.div(right),
      left.compare(right),
    ].join(" ");
  }),
];

const keys = Array.from({ length: 300 }, (_, index) => (index < 40 ? index : random()));
const strings = [
  "",
  "a",
  "abc",
  "Idv",
  "tla__in",
  "smt__TLAunderscore__underscore__a",
  "an exactly twelve",
  "ünïcödé",
  ...Array.from({ length: 200 }, () =>
    Array.from({ length: random() % 40 }, () => String.fromCharCode(32 + (random() % 95))).join(""),
  ),
];

const hashLines = [
  ...keys.map((key) => `u ${key} ${hashU(key)}`),
  ...keys.map((key, index) => {
    const other = keys[(index * 7 + 3) % keys.length];
    return `combine ${key} ${other} ${combineHash(key, other)}`;
  }),
  ...keys.map((key, index) => {
    const [b, c] = [keys[(index + 1) % keys.length], keys[(index + 2) % keys.length]];
    return `mix ${key} ${b} ${c} ${mkMix(key, b, c)}`;
  }),
  ...strings.flatMap((text) =>
    [0, 17, 0xffffffff].map((init) => `string ${init} ${stringHash(text, init)} ${JSON.stringify(text)}`),
  ),
  ...Array.from({ length: 200 }, (_, index) => {
    const children = keys.slice(index % 50, (index % 50) + (index % 9));
    const kind = index % 3 === 0 ? 17 : keys[index];
    return `composite ${kind} ${getCompositeHash(children, kind)} ${children.join(",")}`;
  }),
  ...Array.from({ length: 200 }, (_, index) => {
    const items = Array.from({ length: index % 9 }, () => random() % keys.length);
    const init = keys[(index * 13) % keys.length];
    return `array ${init} ${astArrayHash(items, keys, init)} ${items.join(",")}`;
  }),
];

// A seeded sequence of operations on a table: inserts, overwrites, deletes that leave tombstones,
// growth, resets, and then many inserts and deletes, which rehash the table in place. The
// operations are one table, and the table's entries in slot order every 15th step another.
const getTableLines = (getHash: (key: number) => number, label: string) => {
  const map = new ObjMap<number>(getHash);
  const operations: string[] = [];
  const snapshots: string[] = [];
  const pool = Array.from({ length: 160 }, (_, index) => (index < 60 ? index * 8 : random()));
  const bulk = Array.from({ length: 700 }, () => random());
  const order = bulk.map((_, index) => (index * 337) % bulk.length);
  for (let step = 0; step < 2900; step++) {
    const key = step < 1500 ? pick(pool) : bulk[step < 2200 ? step - 1500 : order[step - 2200]];
    const choice = random() % 100;
    const operation =
      step >= 1500
        ? step < 2200
          ? "set"
          : "delete"
        : step % 500 === 499
          ? "clear"
          : choice < 55
            ? "set"
            : choice < 90
              ? "delete"
              : "replace";
    if (operation === "set") map.set(key, step);
    else if (operation === "delete") map.delete(key);
    else if (operation === "replace") map.replace(key, step);
    else map.clear();
    operations.push(`${label} ${operation} ${key} ${step}`);
    if (step % (step < 1500 ? 15 : 50) === 0 || operation === "clear")
      snapshots.push(
        `${label} ${step} ${[...map.entries()].map(([entryKey, value]) => `${entryKey}:${value}`).join(",")}`,
      );
  }
  return { operations, snapshots };
};

const randomGen = new RandomGen(0);
const seeded = new RandomGen(123456789);
const randomLines = Array.from(
  { length: 200 },
  () => `${randomGen.next()} ${seeded.next()}`,
);

const write = (crate: string, name: string, lines: string[]) => {
  const directory = join(native, crate, "tests/tables");
  mkdirSync(directory, { recursive: true });
  writeFileSync(join(directory, name), `${lines.join("\n")}\n`);
};

write("num", "int.txt", intLines);
write("num", "rational.txt", rationalLines);
write("smt", "hash.txt", hashLines);
const tables = [getTableLines(getIdentityHash, "identity"), getTableLines(hashU, "hashed")];
write("smt", "hashtable.txt", tables.flatMap((table) => table.snapshots));
write("smt", "hashtable-operations.txt", tables.flatMap((table) => table.operations));
write("smt", "random-gen.txt", randomLines);

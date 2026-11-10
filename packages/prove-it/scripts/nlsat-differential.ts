// Writes the differential the Rust port of nlsat is tested against, the same search step for step:
// random small problems, each decided by the TypeScript NlsatSolver, the oracle, under a step
// budget, and checked at random rational points. The problems come from a seeded generator, so the
// fixture is the same on every run. Without --record it checks that the TypeScript reproduces the
// fixture.
//   bun scripts/nlsat-differential.ts --record [--count N] [--seed S]
//
// A problem's text, which prove-smt's differential_tests.rs parses too, is one item per line:
//   vars n                      n variables
//   int f0 f1 ...               1 for an integer variable
//   budget steps                the step budget of check
//   conflicts n|none            maxConflicts
//   a KIND e|o poly | e|o poly  an atom, KIND EQ, LT or GT of the product of the factors, each
//                               even (e) or odd (o), a poly as in smt-nlsat.test.ts
//   cl assumption ref ...       a clause, assumption -1 for none, ref a signed 1-based atom number
//   point v0 v1 ...             a point for checkAssignment, each value n, n/d or _ for none,
//                               the values that are there first

import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import { SmtCanceledError } from "../src/errors";
import { L_FALSE, L_TRUE } from "../src/prover/smt/solver/lbool";
import { type AlgebraicManager, Anum } from "../src/prover/smt/solver/nlsat/algebraic";
import type { Polynomial, PolynomialManager } from "../src/prover/smt/solver/nlsat/polynomial";
import { NlsatSolver } from "../src/prover/smt/solver/nlsat/solver";
import { type Atom, isIneqAtom } from "../src/prover/smt/solver/nlsat/types";
import { Rational } from "../src/prover/smt/solver/rational";
import { getOption } from "./corpora";

const FIXTURE_PATH = join(import.meta.dir, "../tests/fixtures/nlsat/differential.json");

const MAX_DEGREE = 3;

// xorshift32, seeded, so that the problems don't change between runs.
const createRandom = (seed: number) => {
  let state = seed >>> 0 || 1;
  return () => {
    state ^= state << 13;
    state >>>= 0;
    state ^= state >>> 17;
    state ^= state << 5;
    state >>>= 0;
    return state;
  };
};

const random = createRandom(Number(getOption("--seed") ?? 0x6e6c7361));
const getBelow = (bound: number) => random() % bound;
const isChance = (percent: number) => getBelow(100) < percent;
const pick = <T>(items: readonly T[]) => items[getBelow(items.length)];
const getCoeff = (bound: number) => BigInt((1 + getBelow(bound)) * (isChance(50) ? -1 : 1));

// A polynomial of the generator: the coefficient of each exponent vector, keyed by the vector.
type Terms = Map<string, bigint>;

const getTotalDegree = (key: string) =>
  key.split(",").reduce((total, exponent) => total + Number(exponent), 0);

const addTerm = (terms: Terms, key: string, coeff: bigint) => {
  const sum = (terms.get(key) ?? 0n) + coeff;
  if (sum === 0n) terms.delete(key);
  else terms.set(key, sum);
};

const multiply = (first: Terms, second: Terms) => {
  const product: Terms = new Map();
  for (const [firstKey, firstCoeff] of first)
    for (const [secondKey, secondCoeff] of second) {
      const secondExponents = secondKey.split(",").map(Number);
      const key = firstKey
        .split(",")
        .map((exponent, variable) => Number(exponent) + secondExponents[variable])
        .join(",");
      addTerm(product, key, firstCoeff * secondCoeff);
    }
  return product;
};

const getSquare = (terms: Terms) => multiply(terms, terms);

const getMonomialKey = (count: number, degree: number) => {
  const exponents = Array.from({ length: count }, () => 0);
  for (let index = 0; index < degree; index++) exponents[getBelow(count)]++;
  return exponents.join(",");
};

// Terms of total degree at most degree, a constant term among them now and then.
const getSum = (count: number, degree: number, size: number) => {
  const terms: Terms = new Map();
  for (let index = 0; index < size; index++)
    addTerm(terms, getMonomialKey(count, 1 + getBelow(degree)), getCoeff(4));
  if (isChance(60)) addTerm(terms, getMonomialKey(count, 0), getCoeff(6));
  return terms;
};

// A random sum, a product of two or a square, of total degree at most MAX_DEGREE.
const getTerms = (count: number): Terms => {
  const shape = getBelow(10);
  const terms =
    shape < 5
      ? getSum(count, MAX_DEGREE, 1 + getBelow(4))
      : shape < 8
        ? multiply(getSum(count, 1, 1 + getBelow(2)), getSum(count, 2, 1 + getBelow(2)))
        : getSquare(getSum(count, 1, 1 + getBelow(2)));
  if (
    terms.size === 0 ||
    [...terms.keys()].some((key) => getTotalDegree(key) > MAX_DEGREE) ||
    [...terms.keys()].every((key) => getTotalDegree(key) === 0 && !isChance(30))
  )
    return getTerms(count);
  return terms;
};

const showTerms = (terms: Terms) =>
  [...terms]
    .map(
      ([key, coeff]) =>
        `${coeff}:${key
          .split(",")
          .flatMap((exponent, variable) => (exponent === "0" ? [] : [`${variable}^${exponent}`]))
          .join(",")}`,
    )
    .join(" ");

const getValueText = () =>
  `${getCoeff(6) * BigInt(isChance(15) ? 0 : 1)}${isChance(40) ? `/${2 + getBelow(3)}` : ""}`;

// A value for each variable, or now and then for those below some variable only, as checkAssignment
// evaluates an atom only once its maximal variable has a value.
const getPoint = (count: number) => {
  const assigned = isChance(85) ? count : getBelow(count);
  return Array.from({ length: count }, (_value, variable) =>
    variable < assigned ? getValueText() : "_",
  ).join(" ");
};

const getProblem = () => {
  const count = 1 + getBelow(4);
  const atomCount = 1 + getBelow(7);
  const lines = [
    `vars ${count}`,
    `int ${Array.from({ length: count }, () => (isChance(30) ? 1 : 0)).join(" ")}`,
    `budget ${pick([40, 150, 400, 1500, 6000, 30000, 30000, 30000])}`,
    `conflicts ${isChance(25) ? 1 + getBelow(8) : "none"}`,
    ...Array.from({ length: atomCount }, () => {
      const factors = Array.from({ length: isChance(80) ? 1 : 2 }, () =>
        isChance(25) ? `e ${showTerms(getTerms(count))}` : `o ${showTerms(getTerms(count))}`,
      );
      return `a ${pick(["EQ", "LT", "LT", "GT", "GT"])} ${factors.join(" | ")}`;
    }),
    ...Array.from({ length: 1 + getBelow(8) }, () => {
      const refs = Array.from(
        { length: 1 + getBelow(3) },
        () => (1 + getBelow(atomCount)) * (isChance(40) ? -1 : 1),
      );
      return `cl ${isChance(30) ? getBelow(4) : -1} ${refs.join(" ")}`;
    }),
    ...Array.from({ length: 1 + getBelow(3) }, () => `point ${getPoint(count)}`),
  ];
  return lines.join("\n");
};

// The harness syntax of smt-nlsat.test.ts: terms separated by spaces, each coeff:var^degree,....
const parsePolynomial = (pm: PolynomialManager, text: string) => {
  const terms = text.trim() === "" ? [] : text.trim().split(/\s+/);
  return pm.mkPolynomial(
    terms.map((term) => BigInt(term.slice(0, term.indexOf(":")))),
    terms.map((term) => {
      const powers = term
        .slice(term.indexOf(":") + 1)
        .split(",")
        .filter((power) => power !== "")
        .map((power) => power.split("^").map(Number));
      return pm.mkMonomial(
        powers.map((power) => power[0]),
        powers.map((power) => power[1]),
      );
    }),
  );
};

const showPolynomial = (polynomial: Polynomial) =>
  `[${polynomial.ms
    .map(
      (monomial, index) =>
        `${polynomial.as[index]}:${monomial.vars.map((variable, power) => `${variable}^${monomial.degrees[power]}`).join(",")}`,
    )
    .join(" ")}]`;

const showAnum = (am: AlgebraicManager, anum: Anum) =>
  anum.value instanceof Rational
    ? ` q${anum.value}`
    : ` r[${anum.value.p.join(" ")}]#${am.getRootIndex(anum)}(${anum.value.lower},${anum.value.upper})`;

const showAtom = (atom: Atom | null) => {
  if (atom === null) return "none";
  if (!isIneqAtom(atom))
    return `${atom.kind} x${atom.maxVar} #${atom.index} ${showPolynomial(atom.polynomial)}`;
  const factors = atom.polynomials.map(
    (polynomial, index) => `${atom.isEven[index] ? "e" : "o"}${showPolynomial(polynomial)}`,
  );
  return `${atom.kind} ${factors.join(" ")}`;
};

const showError = (error: unknown) =>
  error instanceof SmtCanceledError
    ? "error SmtCanceledError"
    : error instanceof Error
      ? `error ${error.name}: ${error.message}`
      : `error ${String(error)}`;

const showResult = (result: number) =>
  result === L_TRUE ? "sat" : result === L_FALSE ? "unsat" : "undef";

// The solver of a problem's text, with its atoms and clauses, the literal of each atom, and the
// text's other lines.
const mkSolver = (input: string, budget: number) => {
  const solver = new NlsatSolver(null, budget);
  const literals: number[] = [];
  for (const line of input.split("\n")) {
    const words = line.split(" ");
    if (words[0] === "int") for (const flag of words.slice(1)) solver.mkVar(flag === "1");
    if (words[0] === "a") {
      const factors = words.slice(2).join(" ").split(" | ");
      literals.push(
        solver.mkIneqLiteral(
          words[1] === "EQ" ? "EQ" : words[1] === "LT" ? "LT" : "GT",
          factors.map((factor) => parsePolynomial(solver.pm, factor.slice(2))),
          factors.map((factor) => factor[0] === "e"),
        ),
      );
    }
    if (words[0] !== "cl") continue;
    solver.mkExternalClause(
      words
        .slice(2)
        .map(Number)
        .map((ref) => (ref > 0 ? literals[ref - 1] : literals[-ref - 1] ^ 1)),
      words[1] === "-1" ? null : Number(words[1]),
    );
  }
  return { solver, literals };
};

const getLine = (input: string, name: string) =>
  input
    .split("\n")
    .find((line) => line.startsWith(`${name} `))!
    .slice(name.length + 1);

const runCheck = (input: string) => {
  const created = mkSolver(input, Number(getLine(input, "budget")));
  const solver = created.solver;
  const conflicts = getLine(input, "conflicts");
  if (conflicts !== "none") solver.maxConflicts = Number(conflicts);
  const output = [`literals ${created.literals.join(" ")}`];
  try {
    const result = solver.check();
    output.push(`check ${showResult(result)}`);
    if (result === L_TRUE)
      output.push(
        `model${Array.from({ length: Number(getLine(input, "vars")) }, (_value, variable) => showAnum(solver.am, solver.getValue(variable))).join("")}`,
      );
    if (result === L_FALSE)
      output.push(
        `core${solver
          .getCore()
          .map((assumption) => ` ${assumption}`)
          .join("")}`,
      );
  } catch (error) {
    output.push(`check ${showError(error)}`);
  }
  const stats = solver.stats;
  output.push(
    `steps ${solver.steps} conflicts=${stats.conflicts} restarts=${stats.restarts} propagations=${stats.propagations} decisions=${stats.decisions} stages=${stats.stages} irrational_assignments=${stats.irrationalAssignments}`,
  );
  return output;
};

// checkAssignment at each point in turn, on one solver of the problem, until one throws.
const runCheckAssignment = (input: string) => {
  const solver = mkSolver(input, Infinity).solver;
  const output: string[] = [];
  for (const line of input.split("\n").filter((innerLine) => innerLine.startsWith("point "))) {
    const values = line
      .split(" ")
      .slice(1)
      .map((text) => {
        if (text === "_") return undefined;
        const parts = text.split("/");
        return new Anum(Rational.of(BigInt(parts[0]), BigInt(parts[1] ?? "1")));
      });
    try {
      const result = solver.checkAssignment(values);
      const literals = result.clause.map(
        (literal) =>
          ` ${literal} ${(literal & 1) === 1 ? "!" : "+"}${showAtom(solver.getAtom(literal))}`,
      );
      output.push(
        result.result === L_FALSE
          ? `${line}: lemma${literals.join("")}`
          : `${line}: ${showResult(result.result)}`,
      );
    } catch (error) {
      output.push(`${line}: ${showError(error)}`);
      break;
    }
  }
  return output;
};

const run = (input: string) => [...runCheck(input), ...runCheckAssignment(input)].join("\n");

if (process.argv.includes("--record")) {
  const count = Number(getOption("--count") ?? 500);
  const cases = Array.from({ length: count }, () => {
    const input = getProblem();
    return [input, run(input)];
  });
  writeFileSync(FIXTURE_PATH, `${JSON.stringify(cases)}\n`);
  const verdicts = new Map<string, number>();
  for (const pair of cases) {
    const verdict = pair[1].split("\n")[1].replace(/:.*/, "");
    verdicts.set(verdict, (verdicts.get(verdict) ?? 0) + 1);
  }
  console.log(`${count} problems:`, Object.fromEntries(verdicts));
} else {
  const cases: [string, string][] = JSON.parse(readFileSync(FIXTURE_PATH, "utf8"));
  const differences = cases.filter((pair) => run(pair[0]) !== pair[1]);
  for (const pair of differences) console.log(`${pair[0]}\nexpected:\n${pair[1]}\n`);
  console.log(`${cases.length - differences.length} of ${cases.length} reproduce`);
  process.exitCode = differences.length === 0 ? 0 : 1;
}

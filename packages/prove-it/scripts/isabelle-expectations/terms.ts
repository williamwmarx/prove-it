// What the expectations share: the text form of terms, types and theorems that the Rust tests
// parse back, and the errors a problem may end in.
// Types are `name`, `name(arg,...)`, `'a` (TFree) and `?'a.0` (TVar); terms `name::T` (Const),
// `name:T` (Free), `?name.0:T` (Var), `B0` (Bound), `(%name:T body)` (Abs) and `(f a)` (App).
import { readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { TlaIsabelleError } from "../../src/errors";
import { readStatement } from "../../src/prover/isabelle/isar/statement";
import { parseTheory } from "../../src/prover/isabelle/isar/theory";
import { listImplies } from "../../src/prover/isabelle/pure/logic";
import type { Seq } from "../../src/prover/isabelle/pure/seq";
import {
  mkAbs,
  mkApp,
  mkBound,
  mkConst,
  mkFree,
  mkTFree,
  mkTVar,
  mkType,
  mkVar,
  type Term,
  type Typ,
} from "../../src/prover/isabelle/pure/term";
import type { Thm } from "../../src/prover/isabelle/pure/thm";
import type { TlaLogic } from "../../src/prover/isabelle/tla/logic";

const FIXTURE_DIRECTORY = join(import.meta.dirname, "../../tests/fixtures/isabelle");

// The fixture theories' names, without `.thy`.
export const getFixtureNames = () =>
  readdirSync(FIXTURE_DIRECTORY)
    .filter((name) => name.endsWith(".thy"))
    .sort()
    .map((name) => name.slice(0, -".thy".length));

export const readFixture = (name: string) =>
  readFileSync(join(FIXTURE_DIRECTORY, `${name}.thy`), "utf8");

export const escape = (text: string) =>
  text
    .replaceAll("\\", "\\\\")
    .replaceAll("\n", "\\n")
    .replaceAll("\t", "\\t")
    .replaceAll("\r", "\\r");

// The kernel's tests reject sorts, which Isabelle/TLA+ never has.
export const showTyp = (type: Typ): string => {
  if (type.kind !== "Type" && type.sort.length > 0) throw new Error("sorted type");
  if (type.kind === "Type")
    return type.args.length === 0 ? type.name : `${type.name}(${type.args.map(showTyp).join(",")})`;
  return type.kind === "TFree" ? type.name : `?${type.name}.${type.index}`;
};

// The parsers' tests write `(%name:T. body)`, with `binder` ". " in place of " ".
export const showTerm = (term: Term, binder = " "): string => {
  switch (term.kind) {
    case "Const":
      return `${term.name}::${showTyp(term.type)}`;
    case "Free":
      return `${term.name}:${showTyp(term.type)}`;
    case "Var":
      return `?${term.name}.${term.index}:${showTyp(term.type)}`;
    case "Bound":
      return `B${term.index}`;
    case "Abs":
      return `(%${term.name}:${showTyp(term.type)}${binder}${showTerm(term.body, binder)})`;
    case "App":
      return `(${showTerm(term.fun, binder)} ${showTerm(term.arg, binder)})`;
  }
};

const isNameChar = (char: string | undefined) => char !== undefined && /[A-Za-z0-9_.'?]/.test(char);

const getParser = (text: string) => {
  let position = 0;
  const expect = (char: string) => {
    if (text[position] !== char) throw new Error(`expected ${char} at ${position} in ${text}`);
    position += 1;
  };
  const name = () => {
    const start = position;
    while (isNameChar(text[position])) position += 1;
    return text.slice(start, position);
  };
  const indexed = (token: string): [string, number] => {
    const dot = token.lastIndexOf(".");
    return [token.slice(1, dot), Number(token.slice(dot + 1))];
  };
  const typ = (): Typ => {
    const token = name();
    if (token.startsWith("?")) return mkTVar(...indexed(token));
    if (token.startsWith("'")) return mkTFree(token);
    if (text[position] !== "(") return mkType(token);
    position += 1;
    const args = [typ()];
    while (text[position] === ",") {
      position += 1;
      args.push(typ());
    }
    expect(")");
    return mkType(token, args);
  };
  const term = (): Term => {
    if (text[position] === "(") {
      position += 1;
      if (text[position] === "%") {
        position += 1;
        const binder = name();
        expect(":");
        const type = typ();
        expect(" ");
        const body = term();
        expect(")");
        return mkAbs(binder, type, body);
      }
      const fun = term();
      expect(" ");
      const arg = term();
      expect(")");
      return mkApp(fun, arg);
    }
    const token = name();
    if (text[position] !== ":") {
      if (!/^B[0-9]+$/.test(token)) throw new Error(`bad atom ${token}`);
      return mkBound(Number(token.slice(1)));
    }
    position += 1;
    if (text[position] === ":") {
      position += 1;
      return mkConst(token, typ());
    }
    const type = typ();
    if (token.startsWith("?")) return mkVar(...indexed(token), type);
    return mkFree(token, type);
  };
  const whole =
    <Result>(parse: () => Result) =>
    () => {
      const result = parse();
      if (position !== text.length) throw new Error(`trailing text in ${text}`);
      return result;
    };
  return { term: whole(term), typ: whole(typ) };
};

export const parseTerm = (text: string) => getParser(text).term();

export const parseTyp = (text: string) => getParser(text).typ();

// A goal is a term's text, or `@name`: the statement of a fixture, as the Rust tests read it.
export const readGoal = (logic: TlaLogic, field: string) => {
  if (!field.startsWith("@")) return parseTerm(field);
  const statement = readStatement(logic, parseTheory(readFixture(field.slice(1))));
  return listImplies(statement.assumptions, statement.conclusion);
};

// A term in an expectation: its text, or past 160 characters its length and FNV-1a hash.
export const digest = (term: Term) => {
  const text = showTerm(term);
  if (text.length <= 160) return text;
  let hash = 0x811c9dc5;
  for (let index = 0; index < text.length; index += 1)
    hash = Math.imul(hash ^ text.charCodeAt(index), 0x01000193) >>> 0;
  return `#${text.length}:${hash.toString(16)}`;
};

export const showThm = (thm: Thm) => [
  `maxidx ${thm.maxidx}`,
  ...thm.hyps.map((hyp) => `hyp ${digest(hyp)}`),
  ...thm.tpairs.map((pair) => `tpair ${digest(pair[0])} =?= ${digest(pair[1])}`),
  `prop ${digest(thm.prop)}`,
];

// The local exceptions of pattern, unify, thm, rewriter and hypsubst, which the Rust port names
// the same.
const LOCAL_EXCEPTIONS = new Set([
  "Unif",
  "NotPattern",
  "Match",
  "CantUnify",
  "ChangeFail",
  "Compose",
  "MatchFailure",
  "NoMatch",
  "EqVar",
]);

const getExceptionName = (error: unknown) =>
  error instanceof Object ? error.constructor.name : undefined;

const showError = (error: unknown) => {
  if (error instanceof TlaIsabelleError) return `error ${error.exception}: ${error.message}`;
  const name = getExceptionName(error);
  if (name !== undefined && LOCAL_EXCEPTIONS.has(name)) return `error ${name}`;
  throw error;
};

// Runs a computation that prints lines, ending at the first exception, which it prints.
export const attempt = (lines: string[], run: () => void, show = showError) => {
  try {
    run();
  } catch (error) {
    lines.push(show(error));
  }
};

export const one = (lines: string[], label: string, run: () => Thm) => {
  lines.push(label);
  attempt(lines, () => lines.push(...showThm(run())));
};

// The first `count` theorems of a sequence, and whether it ends there.
export const many = (
  lines: string[],
  label: string,
  count: number,
  run: () => Seq<Thm>,
  show = showError,
) => {
  lines.push(label);
  attempt(
    lines,
    () => {
      let seq = run();
      for (let index = 0; ; index += 1) {
        if (index === count) {
          lines.push("stop");
          return;
        }
        const cell = seq.pull();
        if (cell === undefined) {
          lines.push("end");
          return;
        }
        lines.push(`result ${index}`, ...showThm(cell[0]));
        seq = cell[1];
      }
    },
    show,
  );
};

export const joinLines = (lines: readonly string[]) => `${lines.join("\n")}\n`;

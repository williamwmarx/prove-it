// The cases of the enumeration oracle (native/DESIGN.md 6.8): sets TLC keeps lazy, written in
// native/oracle/ValueOracle.java's tokens, and the interpreter's answers for them. The interpreter
// builds each set: a set enumeration as the normalized set an id converts to, SUBSET, [S -> T], a
// set of records with its fields in TLC's order, a product, and \cup, \cap and \ through the
// interpreter's builtins, which combine a set enumeration with the other set at once. It answers the elements in the order a quantifier binds
// them (getQuantifierElements) and the order x' \in S assigns them (getStreamedElements), as
// their TLC fingerprints, which TLC (enumerate q and s) and the native engine (replay enumerate)
// answer too.

import type { Expression } from "../src/ast";
import { TlaEvaluationError } from "../src/errors";
import { getQuantifierElements } from "../src/evaluate";
import { CORE_OPERATORS } from "../src/standard-modules";
import { getTlcFingerprint } from "../src/tlc/fingerprint";
import {
  createEnumeratedSet,
  createModelValue,
  createTuple,
  getStreamedElements,
  getStringRank,
  toFiniteSet,
  type Value,
} from "../src/values";

// The strings the cases use, which every side interns first, in this order.
export const CASE_STRINGS = ["a", "b", "c"];

const decode = (hex: string) =>
  String.fromCharCode(
    ...Array.from({ length: hex.length / 4 }, (_, index) =>
      Number.parseInt(hex.slice(index * 4, index * 4 + 4), 16),
    ),
  );

export const encodeText = (text: string) =>
  Array.from(text, (character) => character.charCodeAt(0).toString(16).padStart(4, "0")).join("");

const QUANTIFIED: Expression = { kind: "Identifier", name: "S", location: { line: 1, column: 1 } };

const getBuiltin = (name: string) => {
  const builtin = CORE_OPERATORS.find((operator) => operator.name === name);
  if (!builtin) throw new Error(`no builtin ${name}`);
  return builtin;
};

// Reads the value the tokens from position next on write.
const createReader = (tokens: string[]) => {
  let next = 0;
  const read = (): Value => {
    const token = tokens[next++];
    const rest = token.slice(1);
    switch (token[0]) {
      case "T":
        return true;
      case "F":
        return false;
      case "i":
        return Number(rest);
      case "s":
        return decode(rest);
      case "m":
        return createModelValue(decode(rest));
      case "S":
        return toFiniteSet(createEnumeratedSet(readMany(Number(rest))));
      case "U":
        return createTuple(readMany(Number(rest)));
      case "L":
        return readLazy(rest);
      default:
        throw new Error(`unknown token ${token}`);
    }
  };
  const readMany = (count: number) => Array.from({ length: count }, read);
  const readLazy = (kind: string): Value => {
    switch (kind[0]) {
      case "p":
        return { kind: "Subset", base: read() };
      case "f": {
        const domain = read();
        return { kind: "FunctionSet", domain, range: read() };
      }
      case "r": {
        const fields = Array.from({ length: Number(kind.slice(1)) }, () => {
          const name = decode(tokens[next++].slice(1));
          return { name, set: read() };
        });
        fields.sort((left, right) => getStringRank(left.name) - getStringRank(right.name));
        return {
          kind: "RecordSet",
          names: fields.map((field) => field.name),
          sets: fields.map((field) => field.set),
        };
      }
      case "x":
        return { kind: "ProductSet", factors: readMany(Number(kind.slice(1))) };
      default: {
        const name = kind[0] === "u" ? "\\cup" : kind[0] === "i" ? "\\cap" : "\\";
        const left = read();
        return getBuiltin(name).evaluate([left, read()]);
      }
    }
  };
  return read;
};

const toAnswer = (elements: Value[]) =>
  [
    "elements",
    ...elements.map((element) => String(BigInt.asIntN(64, getTlcFingerprint([element])))),
  ].join(" ");

const answerSafely = (compute: () => string) => {
  try {
    return compute();
  } catch (error) {
    if (error instanceof TlaEvaluationError) return `!${error.message.split("\n")[0]}`;
    throw error;
  }
};

// The interpreter's answers to a case: its elements as a quantifier binds them, then as
// x' \in S assigns them, each "elements" and fingerprints, or "!" and why it failed.
export const answerCase = (tokens: string): [string, string] => {
  const build = () => createReader(tokens.split(" "))();
  return [
    answerSafely(() => {
      const elements = getQuantifierElements(build(), QUANTIFIED, "master");
      if (Array.isArray(elements)) return toAnswer(elements);
      return toAnswer(
        Array.from(
          { length: elements.high - elements.low + 1 },
          (_, index) => elements.low + index,
        ),
      );
    }),
    answerSafely(() => toAnswer(getStreamedElements(build()))),
  ];
};

// The requests ValueOracle.java and replay enumerate answer for the cases, after the strings.
export const toRequests = (cases: string[]) => [
  `strings ${CASE_STRINGS.map((text) => `s${encodeText(text)}`).join(" ")}`,
  ...cases.flatMap((tokens, index) => [
    `value ${tokens}`,
    `enumerate q ${index}`,
    `enumerate s ${index}`,
  ]),
];

// The answers to the enumerate requests of toRequests, two a case.
export const toCaseAnswers = (lines: string[]) =>
  lines.slice(1).filter((_, index) => index % 3 !== 0);

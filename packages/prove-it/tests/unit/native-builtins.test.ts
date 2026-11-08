// The builtins the TypeScript engine runs in the interpreter, which the native engine computes on
// ids: on seeded generated arguments, each must give the TypeScript engine's states and the
// interpreter's result, and stop wherever the interpreter fails, which then reports TLC's error.

import { afterEach, describe, expect, it } from "bun:test";

import {
  ADDON,
  compareStateLogs,
  compareWithInterpreter,
  COMPLETE,
  restoreSettings,
} from "./native-runs";

afterEach(restoreSettings);

const createRandom = (seed: number) => {
  let state = seed;
  return () => {
    state = (state + 0x6d2b79f5) | 0;
    let mixed = Math.imul(state ^ (state >>> 15), 1 | state);
    mixed = (mixed + Math.imul(mixed ^ (mixed >>> 7), 61 | mixed)) ^ mixed;
    return ((mixed ^ (mixed >>> 14)) >>> 0) / 4294967296;
  };
};

type Random = () => number;

const pick = <Item>(random: Random, items: Item[]) => items[Math.floor(random() * items.length)];
const getInteger = (random: Random, low: number, high: number) =>
  low + Math.floor(random() * (high - low + 1));
const listOf = (random: Random, maximum: number, item: () => string) =>
  Array.from({ length: getInteger(random, 0, maximum) }, item);

const getSequence = (random: Random) =>
  `<<${listOf(random, 4, () => String(getInteger(random, -2, 4))).join(", ")}>>`;
const getText = (random: Random) =>
  `"${listOf(random, 4, () => pick(random, ["a", "b", "c"])).join("")}"`;
const getSet = (random: Random) =>
  `{${listOf(random, 4, () => String(getInteger(random, 0, 5))).join(", ")}}`;
// A bag over a few strings, with counts from 1 to 3.
const getBag = (random: Random) => {
  const keys = [...new Set(listOf(random, 3, () => pick(random, ["a", "b", "c", "d"])))];
  return keys.length === 0
    ? "EmptyBag"
    : keys.map((key) => `("${key}" :> ${getInteger(random, 1, 3)})`).join(" @@ ");
};

interface Case {
  name: string;
  // Writes the application to random arguments TLC computes.
  valid: (random: Random) => string;
  // Applications the interpreter fails on.
  invalid: string[];
}

const CASES: Case[] = [
  {
    name: "SubSeq",
    valid: (random) => {
      const isText = random() < 0.3;
      const sequence = isText ? getText(random) : getSequence(random);
      const length = isText ? sequence.length - 2 : (sequence.match(/,/g)?.length ?? 0) + 1;
      const start = getInteger(random, 1, Math.max(length, 1));
      const end = random() < 0.2 ? start - 1 : getInteger(random, start, Math.max(length, start));
      return length === 0 || sequence === "<<>>"
        ? `SubSeq(${sequence}, 2, 1)`
        : `SubSeq(${sequence}, ${start}, ${end})`;
    },
    invalid: ["SubSeq(<<1, 2>>, 0, 1)", "SubSeq(<<1, 2>>, 1, 3)", "SubSeq({1}, 1, 1)"],
  },
  {
    name: "SelectSeq",
    valid: (random) =>
      random() < 0.5
        ? `SelectSeq(${getSequence(random)}, LAMBDA e : e > 1)`
        : `SelectSeq(<<${getBag(random)}, ${getSet(random)}>>, IsABag)`,
    invalid: ["SelectSeq(<<1, 2>>, LAMBDA e : e)", 'SelectSeq("ab", LAMBDA e : TRUE)'],
  },
  {
    name: "SortSeq",
    valid: (random) =>
      `SortSeq(${getSequence(random)}, LAMBDA u, v : ${pick(random, ["u < v", "u > v", "u = v", "u # v"])})`,
    invalid: ['SortSeq(<<1, "a">>, LAMBDA u, v : u < v)', "SortSeq({1}, LAMBDA u, v : TRUE)"],
  },
  {
    name: "Permutations",
    valid: (random) => `Permutations(${getSet(random)})`,
    invalid: ["Permutations(3)", "Permutations(<<1, 2>>)"],
  },
  {
    name: "IsFiniteSet",
    valid: (random) =>
      `IsFiniteSet(${pick(random, [getSet(random), getSequence(random), getBag(random)])})`,
    invalid: ["IsFiniteSet(3)", 'IsFiniteSet("a")'],
  },
  {
    name: "IsABag",
    valid: (random) =>
      `IsABag(${pick(random, [getBag(random), getSequence(random), getSet(random), '("a" :> "b")'])})`,
    invalid: [],
  },
  {
    name: "BagCardinality",
    valid: (random) => `BagCardinality(${getBag(random)})`,
    invalid: ['BagCardinality("a" :> 0)', 'BagCardinality("a" :> "b")', "BagCardinality(3)"],
  },
  {
    name: "BagIn and CopiesIn",
    valid: (random) =>
      `${pick(random, ["BagIn", "CopiesIn"])}("${pick(random, ["a", "b", "e"])}", ${getBag(random)})`,
    invalid: ['BagIn(1, "a" :> 1)', 'CopiesIn("a", "a" :> "b")', 'BagIn("a", {1})'],
  },
  {
    name: "the bag operators",
    valid: (random) =>
      `${getBag(random)} ${pick(random, ["(+)", "(-)", "\\sqsubseteq"])} ${getBag(random)}`,
    invalid: [
      '("a" :> 1) (+) ("a" :> 0)',
      '("a" :> "b") (-) ("a" :> 1)',
      '{1} \\sqsubseteq ("a" :> 1)',
    ],
  },
  {
    name: "BagUnion",
    valid: (random) => `BagUnion({${listOf(random, 3, () => getBag(random)).join(", ")}})`,
    invalid: ['BagUnion({"a" :> 1, {2}})', "BagUnion(3)"],
  },
  {
    name: "BagOfAll",
    valid: (random) =>
      `BagOfAll(LAMBDA e : ${pick(random, ["e", "<<e>>", 'e = "a"'])}, ${getBag(random)})`,
    invalid: ['BagOfAll(LAMBDA e : 1, "a" :> 1)', "BagOfAll(LAMBDA e : e, 3)"],
  },
  {
    name: "SubBag",
    valid: (random) => `SubBag(${getBag(random)})`,
    invalid: ['SubBag("a" :> 0)', 'SubBag("a" :> "b")', "SubBag({1})"],
  },
  {
    name: "BagToSet and SetToBag",
    valid: (random) =>
      random() < 0.5 ? `BagToSet(${getBag(random)})` : `SetToBag(${getSet(random)})`,
    invalid: ["BagToSet({1})", "SetToBag(3)"],
  },
];

// A spec with an initial state for each application, whose value r holds.
const toSpec = (applications: string[]) => [
  "EXTENDS Integers, Sequences, TLC, FiniteSets, Bags",
  "VARIABLES i, r",
  ...applications.map((application, position) => `A${position} == ${application}`),
  `Inputs == <<${applications.map((_, position) => `A${position}`).join(", ")}>>`,
  `Init == i \\in 1..${applications.length} /\\ r = Inputs[i]`,
  "Next == UNCHANGED <<i, r>>",
];

const CONFIG = "INIT Init\nNEXT Next";

describe.if(ADDON !== undefined)("the native engine's bridged builtins", () => {
  for (const [index, item] of CASES.entries()) {
    it(`computes ${item.name} as the interpreter does`, async () => {
      const random = createRandom(index + 1);
      const applications = Array.from({ length: 40 }, () => item.valid(random));
      const body = toSpec(applications);
      expect(await compareWithInterpreter(body, CONFIG)).toContainEqual(
        expect.stringMatching(COMPLETE),
      );
      await compareStateLogs(body, CONFIG, false);
    });

    if (item.invalid.length > 0) {
      it(`stops on ${item.name} where the interpreter fails`, async () => {
        for (const application of item.invalid) {
          const lines = await compareWithInterpreter(toSpec([application]), CONFIG);
          expect(lines).toContainEqual(expect.stringMatching(/^\[engine\] native: stopped: /));
        }
      });
    }
  }
});

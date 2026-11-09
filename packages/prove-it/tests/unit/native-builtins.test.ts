// The builtins the TypeScript engine runs in the interpreter, which the native engine computes on
// ids: on seeded generated arguments, each must give the TypeScript engine's states and the
// interpreter's result, and stop wherever the interpreter fails, which then reports TLC's error.

import { afterEach, describe, expect, it } from "bun:test";

import {
  ADDON,
  compareStateLogs,
  compareWithInterpreter,
  COMPLETE,
  declined,
  restoreSettings,
  stopped,
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

// A value whose text doesn't depend on how TLC built it: no set of consecutive integers, which
// may be an interval, and no record of several fields, whose order may be as written.
const getPrintable = (random: Random, depth = 0): string => {
  const choice = getInteger(random, 0, depth > 1 ? 2 : 6);
  if (choice === 0) return String(getInteger(random, -3, 12));
  if (choice === 1) {
    return `"${listOf(random, 3, () => pick(random, ["a", "é", '\\"', "\\\\", "\\n", "\\t"])).join("")}"`;
  }
  if (choice === 2) return pick(random, ["TRUE", "FALSE"]);
  if (choice === 3) {
    return `<<${listOf(random, 3, () => getPrintable(random, depth + 1)).join(", ")}>>`;
  }
  if (choice === 4)
    return pick(random, ["{}", "{0, 2}", "{-1, 3, 4}", '{"b", "a"}', "{{}, {1, 5}}"]);
  if (choice === 5)
    return `[${pick(random, ["a", "f1", "x_y"])} |-> ${getPrintable(random, depth + 1)}]`;
  return `(0 :> ${getPrintable(random, depth + 1)} @@ 2 :> ${getPrintable(random, depth + 1)})`;
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
    name: "ToString",
    valid: (random) => `ToString(${getPrintable(random)})`,
    invalid: [],
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

  it("stops on ToString of a value whose text depends on how TLC built it", async () => {
    for (const application of [
      "ToString(1..3)",
      "ToString({2})",
      "ToString([a |-> 1, b |-> 2])",
      'ToString(("a b" :> 1))',
      'ToString(SUBSET {"a", "b", "c", "d", "e", "f", "g"})',
      "ToString([1..3 -> 1..17])",
    ]) {
      const lines = await compareWithInterpreter(toSpec([application]), CONFIG);
      expect(lines).toContainEqual(
        expect.stringMatching(
          stopped("ToString of a value whose text depends on how TLC built it"),
        ),
      );
    }
  });

  // The search ranks ToString's strings as it makes them, which may be in another order than
  // TLC's: across successors, where it builds a function's entries TLC doesn't read, or ranking a
  // text \o made. So it stops where it would order them, and the interpreter makes them again.
  it("stops where it would order the strings ToString made", async () => {
    const config = "INIT Init\nNEXT Next\nINVARIANT First\nCHECK_DEADLOCK FALSE";
    for (const body of [
      [
        "VARIABLES n, s",
        "Init == n = 0 /\\ s = {}",
        "Next == n = 0 /\\ \\E i \\in 1..2 : n' = i /\\ s' = {ToString(100 + i), ToString(149 + i)}",
        "First == n # 2 \\/ (CHOOSE x \\in s : ToString(150 + n) # x) = ToString(150 + 1)",
      ],
      [
        "VARIABLE n",
        "Init == n = 0",
        "Next == UNCHANGED n",
        "First == (CHOOSE x \\in {[i \\in 1..2 |-> ToString(100 + i + n)][2], ToString(100 + 1 + n)} : TRUE) = ToString(100 + 2 + n)",
      ],
      [
        "VARIABLES n, s",
        'Init == n = 0 /\\ s = "1" \\o ToString(n + 2)',
        "Next == UNCHANGED <<n, s>>",
        "First == (CHOOSE x \\in {ToString(6 + 6 + n), ToString(6 + 7 + n)} : TRUE) = ToString(6 + 6 + n)",
      ],
    ]) {
      expect(
        await compareWithInterpreter(["EXTENDS Integers, Sequences, TLC", ...body], config),
      ).toContainEqual(
        expect.stringMatching(
          stopped(
            "(an order of strings the search ranked|ToString of a text the engine made unranked)",
          ),
        ),
      );
    }
  });

  // From TLC's Github696: TLCModelValue makes the model value of a name once, ranking the name.
  // The literal "A_7" ranks before the names the spec builds, so it comes first.
  it("makes the model values TLCModelValue names, as TLC does", async () => {
    const body = [
      "EXTENDS Integers, Sequences, TLC, TLCExt",
      "VARIABLE v",
      'MVS == {TLCModelValue("A_" \\o ToString(n)) : n \\in 0..12}',
      "Init == v = [mv \\in MVS |-> ToString(mv)]",
      "Next == UNCHANGED v",
      'Inv == /\\ v[TLCModelValue("A_7")] = "A_7"',
      '       /\\ (CHOOSE mv \\in MVS : TRUE) = TLCModelValue("A_7")',
    ];
    expect(await compareWithInterpreter(body, `${CONFIG}\nINVARIANT Inv`)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    // The search may rank names in another order than TLC's, so it stops where it would order
    // them: here it builds both entries of the function, where TLC applies it lazily.
    const ranked = [
      "EXTENDS Integers, Sequences, TLC, TLCExt",
      "VARIABLE n",
      'MV(i) == TLCModelValue("A_" \\o ToString(100 + i + n))',
      "Init == n = 0",
      "Next == UNCHANGED n",
      "First == (CHOOSE x \\in {[i \\in 1..2 |-> MV(i)][2], MV(1)} : TRUE) = MV(1)",
    ];
    expect(await compareWithInterpreter(ranked, `${CONFIG}\nINVARIANT First`)).toContainEqual(
      expect.stringMatching(stopped("an order of model values the search ranked")),
    );
    for (const [init, reason] of [
      ['v = {TLCModelValue("A_a"), TLCModelValue("B_a")}', "differently typed model values"],
      ["v = TLCModelValue(1)", "TLCModelValue of a value that isn't a string"],
    ]) {
      const lines = await compareWithInterpreter(
        ["EXTENDS TLCExt", "VARIABLE v", `Init == ${init}`, "Next == UNCHANGED v"],
        CONFIG,
      );
      expect(lines).toContainEqual(expect.stringMatching(stopped(reason)));
    }
  });

  // From TLC's RandomElement: the initial states draw from the generator the assumptions drew
  // from, and each expansion from one seeded with the fingerprint of the state it expands.
  it("draws RandomElement and RandomSubset as TLC does", async () => {
    const body = [
      "EXTENDS Integers, TLC, Randomization",
      "VARIABLES x, y",
      "ASSUME RandomElement(1..10) \\in 1..10",
      "Init == x \\in RandomSubset(3, 1..1000) /\\ y = 0",
      "Next == /\\ y < 3",
      "        /\\ \\/ x' = RandomElement(1..1000)",
      "           \\/ x' \\in RandomSubset(2, {x, x + 1, x + 2})",
      "        /\\ y' = y + 1",
    ];
    expect(await compareWithInterpreter(body, `${CONFIG}\nCHECK_DEADLOCK FALSE`)).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
    // Each component of a set of functions, records or tuples, and the elements of a product
    // by their index, of one with more elements than an int holds too.
    for (const draw of [
      "x = RandomElement([{1, 2} -> 1..5])",
      'x = RandomElement([a : 1..5, b : {"p", "q"}])',
      "x = RandomElement((1..5) \\X {7, 8})",
      "x = RandomElement(SUBSET {1, 2, 3})",
      "x \\in RandomSubset(4, [{1, 2, 3} -> 1..10])",
      "x \\in RandomSubset(4, [a : 1..5, b : 1..6])",
      "x \\in RandomSubset(4, (1..200) \\X (1..200) \\X (1..200))",
      "x \\in RandomSubset(4, (1..4000) \\X (1..4000) \\X (1..4000))",
      "x \\in RandomSubset(4, SUBSET {1, 2, 3})",
    ]) {
      const drawn = [
        "EXTENDS Integers, TLC, Randomization",
        "VARIABLES x, y",
        `Init == ${draw} /\\ y = 0`,
        "Next == UNCHANGED <<x, y>>",
      ];
      expect(await compareWithInterpreter(drawn, CONFIG)).toContainEqual(
        expect.stringMatching(COMPLETE),
      );
    }
  });

  it("stops drawing from a product too large to index", async () => {
    const body = [
      "EXTENDS Integers, Randomization",
      "VARIABLE x",
      "Init == x \\in RandomSubset(1, [1..128 -> BOOLEAN])",
      "Next == UNCHANGED x",
    ];
    expect(await compareWithInterpreter(body, CONFIG)).toContainEqual(
      expect.stringMatching(stopped("RandomSubset of a product too large to index")),
    );
    // TLC draws the first index of an interval with nextInt, whose bound is an int.
    const interval = [
      "EXTENDS Integers, Randomization",
      "VARIABLE x",
      "Init == x \\in RandomSubset(1, (-2147483647 - 1)..2147483647)",
      "Next == UNCHANGED x",
      "Inv == x # -1870019805",
    ];
    expect(await compareWithInterpreter(interval, `${CONFIG}\nINVARIANT Inv`)).toContainEqual(
      expect.stringMatching(stopped("RandomSubset of an interval too large to draw from")),
    );
  });

  // A variable holds a set of functions as its elements, which TLC may keep lazy and draw from
  // component by component.
  it("stops drawing from a set of functions a variable holds", async () => {
    const body = [
      "EXTENDS Integers, TLC",
      "VARIABLES s, x, y",
      "Init == s = [1..3 -> 1..5] /\\ x = 0 /\\ y = 0",
      "Next == y = 0 /\\ x' = RandomElement(s) /\\ y' = y + 1 /\\ UNCHANGED s",
      "Inv == y = 0 \\/ x[3] # 2",
    ];
    expect(
      await compareWithInterpreter(body, `${CONFIG}\nINVARIANT Inv\nCHECK_DEADLOCK FALSE`),
    ).toContainEqual(
      expect.stringMatching(stopped("drew from a set whose shape the engine forgets")),
    );
  });

  // The interpreter rebuilds the trace from the initial predicate, as TLC does, so it draws again.
  it("hands over a violation whose trace drew at random", async () => {
    const body = [
      "EXTENDS Integers, TLC",
      "VARIABLES x, y",
      "Init == x = RandomElement(1..1000) /\\ y = 0",
      "Next == (x' = RandomElement(1..1000) \\/ x' = x) /\\ y' = y + 1",
      "Inv == y < 3",
    ];
    expect(await compareWithInterpreter(body, `${CONFIG}\nINVARIANT Inv`)).toContainEqual(
      expect.stringMatching(stopped("an invariant violated")),
    );
  });

  // A search that ranked strings hands over none of its states, so the interpreter ranks them
  // again from the start.
  it("hands over a search that ranked strings from the start", async () => {
    const body = [
      "EXTENDS Integers, TLC",
      "VARIABLES n, s",
      'Init == n = 0 /\\ s = "a"',
      "Next == n < 3 /\\ ToString(n + 1003 + 1003) # \"q\" /\\ n' = n + 1 /\\ s' = ToString(1003 + 1004 - n)",
    ];
    const config = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE";
    for (const stop of ["1", "2"]) {
      expect(await compareWithInterpreter(body, config, { PROVE_IT_STOP_AT: stop })).toContainEqual(
        expect.stringMatching(stopped("stopped where PROVE_IT_STOP_AT asked")),
      );
    }
  });
  // The temporal atoms the search answers rank strings too, which never order them.
  it("checks a property whose atoms use ToString", async () => {
    const body = [
      "EXTENDS Integers, TLC",
      "VARIABLE n",
      "Init == n = 0",
      "Next == n' = (n + 1) % 3",
      "Spec == Init /\\ [][Next]_n /\\ WF_n(Next)",
      'Live == []<>(ToString(n + 1000 + 7) = "1007")',
    ];
    expect(await compareWithInterpreter(body, "SPECIFICATION Spec\nPROPERTY Live")).toContainEqual(
      expect.stringMatching(COMPLETE),
    );
  });
  // A search that ranked strings may start over, which would print again what it printed.
  it("leaves a model that prints and uses ToString", async () => {
    const body = [
      "EXTENDS Integers, TLC",
      "VARIABLE n",
      "Init == n = 0",
      'Next == n < 3 /\\ PrintT(n) /\\ ToString(100 + n) # "q" /\\ n\' = n + 1',
    ];
    const config = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE";
    expect(await compareWithInterpreter(body, config, { PROVE_IT_STOP_AT: "1" })).toContainEqual(
      expect.stringMatching(declined("unsupported: Print with ToString")),
    );
  });
  // The engine builds every entry of the function, making "12" and "13" with \o before
  // ToString does, where the interpreter makes neither.
  it("stops on ToString of a text the engine made unranked", async () => {
    const body = [
      "EXTENDS Integers, Sequences, TLC",
      "VARIABLES n, s",
      'Init == n = 0 /\\ s = [i \\in 1..3 |-> IF i = 3 THEN "q" ELSE "1" \\o ToString(n + i + 1)][3]',
      "Next == UNCHANGED <<n, s>>",
      "First == (CHOOSE x \\in {ToString(6 + 7 + n), ToString(6 + 6 + n)} : TRUE) = ToString(6 + 6 + n)",
    ];
    expect(
      await compareWithInterpreter(body, "INIT Init\nNEXT Next\nINVARIANT First"),
    ).toContainEqual(expect.stringMatching(stopped("ToString of a text the engine made unranked")));
  });
});

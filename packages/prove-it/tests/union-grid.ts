// A grid of memberships in a union of two operands, each of a kind TLC holds its own way: built
// fine, failing to build, holding values that fail to compare, or with effects (a print and a
// count in TLC's register 1, which the module prints after), with an element in the left
// operand, in the right one, in neither, or of another kind. scripts/record-union-grid.ts records
// TLC's answer to each in tests/fixtures/union-grid/tlc.json, which unit/union-grid.test.ts
// checks the native check against.

interface OperandKind {
  name: string;
  fine: string;
  failing?: string;
  mixed?: string;
  effect?: string;
  member: string;
  other: string;
}

export interface GridCell {
  id: string;
  source: string;
  config: string;
}

// A 1 that prints and counts as TLC evaluates it.
const COUNTED = '(IF PrintT("e") /\\ TLCSet(1, TLCGet(1) + 1) THEN 1 ELSE 1)';

const KINDS: OperandKind[] = [
  {
    name: "enumeration",
    fine: "{1, 2}",
    failing: "{1, 1 \\div 0}",
    mixed: '{1, "a"}',
    effect: `{${COUNTED}, 2}`,
    member: "1",
    other: "3",
  },
  {
    name: "interval",
    fine: "1..2",
    failing: "1..(1 \\div 0)",
    effect: `${COUNTED}..2`,
    member: "1",
    other: "3",
  },
  {
    name: "Nat",
    fine: "Nat",
    failing: "IF 1 \\div 0 = 0 THEN Nat ELSE Nat",
    effect: 'IF PrintT("e") /\\ TLCSet(1, TLCGet(1) + 1) THEN Nat ELSE Nat',
    member: "1",
    other: "-1",
  },
  {
    name: "SUBSET",
    fine: "SUBSET {1, 2}",
    failing: "SUBSET {1 \\div 0}",
    mixed: 'SUBSET {1, "a"}',
    effect: `SUBSET {${COUNTED}, 2}`,
    member: "{1}",
    other: "{3}",
  },
  {
    name: "functions",
    fine: "[{1} -> {1, 2}]",
    failing: "[{1} -> {1 \\div 0}]",
    mixed: '[{1} -> {1, "a"}]',
    effect: `[{1} -> {${COUNTED}, 2}]`,
    member: "(1 :> 1)",
    other: "(1 :> 3)",
  },
  {
    name: "records",
    fine: "[a : {1, 2}]",
    failing: "[a : {1 \\div 0}]",
    mixed: '[a : {1, "a"}]',
    effect: `[a : {${COUNTED}, 2}]`,
    member: "[a |-> 1]",
    other: "[a |-> 3]",
  },
  {
    name: "product",
    fine: "{1, 2} \\X {1}",
    failing: "{1} \\X {1 \\div 0}",
    mixed: '{1, "a"} \\X {1}',
    effect: `{${COUNTED}, 2} \\X {1}`,
    member: "<<1, 1>>",
    other: "<<3, 1>>",
  },
  {
    name: "DOMAIN",
    fine: "DOMAIN (1 :> 0 @@ 2 :> 0)",
    failing: "DOMAIN ((1 \\div 0) :> 0)",
    mixed: 'DOMAIN (1 :> 0 @@ "a" :> 0)',
    effect: `DOMAIN (${COUNTED} :> 0 @@ 2 :> 0)`,
    member: "1",
    other: "3",
  },
  {
    name: "filter",
    fine: "{x \\in {1, 2, 3} : x < 3}",
    failing: "{x \\in {1, 2} : x \\div 0 = 0}",
    mixed: '{x \\in {1, "a"} : TRUE}',
    effect: `{x \\in {${COUNTED}, 2, 3} : x < 3}`,
    member: "1",
    other: "3",
  },
  {
    name: "map",
    fine: "{x + 0 : x \\in {1, 2}}",
    failing: "{x \\div 0 : x \\in {1}}",
    mixed: '{IF x = 1 THEN 1 ELSE "a" : x \\in {1, 2}}',
    effect: `{x + 0 : x \\in {${COUNTED}, 2}}`,
    member: "1",
    other: "3",
  },
  {
    name: "union",
    fine: "{1} \\cup {2}",
    failing: "{1} \\cup {1 \\div 0}",
    mixed: '{1} \\cup {"a"}',
    effect: `{${COUNTED}} \\cup {2}`,
    member: "1",
    other: "3",
  },
  {
    name: "intersection",
    fine: "{1, 2, 3} \\cap {1, 2}",
    failing: "{1} \\cap {1 \\div 0}",
    mixed: '{1, "a"} \\cap {1, "a"}',
    effect: `{${COUNTED}, 2, 3} \\cap {1, 2}`,
    member: "1",
    other: "3",
  },
  // Constants the configuration binds: a set, an integer, a model value, and a function.
  { name: "constant-set", fine: "KS", member: "1", other: "3" },
  { name: "constant-integer", fine: "KI", member: "1", other: "3" },
  { name: "constant-model", fine: "KM", member: "KM", other: "3" },
  { name: "constant-function", fine: "KF", member: "<<1, 1>>", other: "3" },
];

const CONFIG = "CONSTANT KS = {1, 2}\nCONSTANT KI = 42\nCONSTANT KM = KM\nCONSTANT KF <- F\n";

export const getUnionGrid = (): GridCell[] =>
  KINDS.flatMap((left) =>
    KINDS.flatMap((right) => {
      const builds = [
        ["fine", left.fine, right.fine],
        ...(left.failing === undefined ? [] : [["left-fails", left.failing, right.fine]]),
        ...(right.failing === undefined ? [] : [["right-fails", left.fine, right.failing]]),
        ...(left.mixed === undefined ? [] : [["left-mixed", left.mixed, right.fine]]),
        ...(right.mixed === undefined ? [] : [["right-mixed", left.fine, right.mixed]]),
        ...(left.effect === undefined ? [] : [["left-effect", left.effect, right.fine]]),
        ...(right.effect === undefined ? [] : [["right-effect", left.fine, right.effect]]),
        ...(left.effect === undefined || right.effect === undefined
          ? []
          : [["both-effect", left.effect, right.effect]]),
      ];
      const elements = [...new Set([left.member, right.member, left.other, '"z"'])];
      return builds.flatMap((build) =>
        elements.flatMap((element) =>
          ["\\in", "\\notin"].map((operator) => ({
            id: `${left.name} ${right.name} ${build[0]} ${element} ${operator}`,
            source: [
              "---- MODULE M ----",
              "EXTENDS Integers, Sequences, FiniteSets, TLC",
              "CONSTANT KS, KI, KM, KF",
              "F == 1 :> 1 @@ 2 :> 2",
              "ASSUME TLCSet(1, 0)",
              `ASSUME ${element} ${operator} (${build[1]}) \\cup (${build[2]})`,
              "ASSUME PrintT(TLCGet(1))",
              "====",
              "",
            ].join("\n"),
            config: CONFIG,
          })),
        ),
      );
    }),
  );

// Operands of an inner set operation, each of a kind TLC reduces or keeps lazy: set enumerations
// in and out of order, an interval, the empty set, a set TLC only tests, a power set, a set of
// another kind of value, a domain, and a constant the configuration binds to a set.
const REDUCED_OPERANDS = [
  "{1}",
  "{2, 1}",
  "1..2",
  "{}",
  "Nat",
  "SUBSET {1}",
  '{"a"}',
  "DOMAIN [a |-> 0]",
  "KS",
];

// What holds the inner operation: nothing, or unions that could answer from another operand
// without making it.
const REDUCTION_HOLDERS: [string, (inner: string) => string][] = [
  ["alone", (inner) => inner],
  ["before-Nat", (inner) => `(${inner}) \\cup Nat`],
  ["after-Nat", (inner) => `Nat \\cup (${inner})`],
  ["under-two", (inner) => `((${inner}) \\cup Nat) \\cup {1}`],
];

// Memberships in a set operation on an operand with effects that a name around it binds: a LET
// definition, an operator's argument, a bound name, and a name of one of those. TLC evaluates the
// operand once.
const BOUND_EFFECTS = [
  'LET S == {Print("L", <<1, 1>>)} IN <<1, 1>> \\in S \\cup ({1} \\X {1})',
  'LET S == {Print("L", <<1, 1>>)} IN <<1, 1>> \\in ({1} \\X {1}) \\cup S',
  "LET S == {IF TLCSet(1, TLCGet(1) + 1) THEN <<1, 1>> ELSE <<0, 0>>} IN <<1, 1>> \\in S \\cup ({1} \\X {1})",
  'LET S == {Print("L", 1)} IN 1 \\in S \\cap Nat',
  'LET S == {Print("L", 1)} IN 1 \\in (S \\cap Nat) \\cup Nat',
  'LET S == {Print("L", 1)} IN 1 \\in Nat \\ S',
  'LET S == {Print("L", 1)} IN 1 \\in S \\cup {2}',
  'LET S == {Print("L", 1)} IN LET T == S IN 1 \\in T \\cup Nat',
  'LET S == {Print("L", 1)} T == S \\cup Nat IN 1 \\in T',
  'LET S == {Print("L", 1)} IN 1 \\in (LET T == S IN T) \\cup Nat',
  'LET S == {Print("L", 1)} IN <<1>> \\in Seq(S \\cup Nat)',
  'LET S == {Print("L", 1)} IN {1} \\in SUBSET (S \\cup Nat)',
  'LET S(x) == {Print("L", x)} IN 1 \\in S(1) \\cup Nat',
  'LET Op(S) == 1 \\in S \\cup Nat IN Op({Print("L", 1)})',
  'LET Op(S) == 1 \\in (S \\cap Nat) \\cup Nat IN Op({Print("L", 1)})',
  'LET Op(S, T) == 1 \\in S \\cup T IN Op({Print("L", 1)}, Nat)',
  '\\A s \\in {{Print("L", 1)}} : 1 \\in s \\cup Nat',
  'LET f == [x \\in {1} |-> Print("L", x)] IN 1 \\in DOMAIN f \\cup Nat',
  'LET f == [x \\in {1} |-> Print("L", x)] IN 1 \\in {f[1]} \\cup Nat',
];

const getBoundEffects = (): GridCell[] =>
  BOUND_EFFECTS.map((assumption) => ({
    id: `bound ${assumption}`,
    source: [
      "---- MODULE M ----",
      "EXTENDS Integers, Sequences, FiniteSets, TLC",
      "CONSTANT KS, KI, KM, KF",
      "F == 1 :> 1 @@ 2 :> 2",
      "ASSUME TLCSet(1, 0)",
      `ASSUME ${assumption}`,
      "ASSUME PrintT(TLCGet(1))",
      "====",
      "",
    ].join("\n"),
    config: CONFIG,
  }));

/**
 * A grid of memberships in a union, an intersection or a difference TLC may reduce as it
 * evaluates it (`Reducible.cup`, `cap` and `diff`), alone and held in unions that another operand
 * answers, then memberships in an operation on an operand with effects that a name binds.
 * scripts/record-union-grid.ts records TLC's answer to each in
 * tests/fixtures/union-grid/reductions.json.
 */
export const getReductionGrid = (): GridCell[] => [...getReducedOperations(), ...getBoundEffects()];

const getReducedOperations = (): GridCell[] =>
  ["\\cup", "\\cap", "\\"].flatMap((operator) =>
    REDUCED_OPERANDS.flatMap((left) =>
      REDUCED_OPERANDS.flatMap((right) =>
        REDUCTION_HOLDERS.flatMap(([holder, hold]) =>
          ["1", "3"].map((element) => ({
            id: `(${left}) ${operator} (${right}) ${holder} ${element}`,
            source: [
              "---- MODULE M ----",
              "EXTENDS Integers, Sequences, FiniteSets, TLC",
              "CONSTANT KS, KI, KM, KF",
              "F == 1 :> 1 @@ 2 :> 2",
              `ASSUME ${element} \\in ${hold(`(${left}) ${operator} (${right})`)}`,
              "====",
              "",
            ].join("\n"),
            config: CONFIG,
          })),
        ),
      ),
    ),
  );

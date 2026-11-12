// Records what TLC prints where it fails to fingerprint a state or a value, for the cells the
// binary's test `fingerprint_exceptions` runs: memberships of values in sets TLC tests by their own
// methods, searches of a constant definition's sorted set whose comparison fails, in it or in a set
// nested in it, constant definitions TLC can't normalize at startup, functions whose body fails as
// TLC builds them and applications of tuples and records, failures in a value TLC gives no source,
// comparisons TLC can't make in the next-state relation or of an initial state's value with a set,
// initial states that hold values TLC can't fingerprint, temporal properties that fail on the
// initial state with an EvalException, function definitions that fail as TLC builds them,
// ALIASes TLC holds as values, state checks that fail after the initial predicate's last
// enumeration, and sets of functions over Nat. Each cell runs at -workers 1 and 4 and writes TLC's exit code and
// its output without the lines that differ from run to run, which the test drops from the binary's
// too.
// Usage: TLA2TOOLS_JAR=path bun scripts/record-fingerprint-exceptions.ts
// TLA2TOOLS_JAR is a classpath for java -cp: a tla2tools.jar, or a build's classes and libraries.

import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const jarPath = process.env.TLA2TOOLS_JAR;
if (!jarPath) {
  console.error("Set TLA2TOOLS_JAR to the path of tla2tools.jar");
  process.exit(1);
}

const OUTPUT_PATH = join(
  import.meta.dirname,
  "../native/crates/prove-it-cli/tests/fingerprint-exceptions.txt",
);

// The lines that differ from run to run or between TLC and the binary: the banner, the files
// parsed, the times.
const VARYING = [
  "TLC2 Version",
  "Running ",
  "Parsing file",
  "Semantic processing",
  "Linting of module",
  "Starting...",
  "Computing initial states",
  "Finished computing initial states",
  "Finished in",
  "Picked up JAVA_TOOL_OPTIONS",
];

interface Cell {
  name: string;
  spec: string;
  config: string;
}

const SETS = [
  "[{1} -> {1}]",
  '[{"a"} -> {1}]',
  "[a : {1}]",
  "{1} \\X {1}",
  "SUBSET {1}",
  "Seq({1})",
  "UNION {[{1} -> Nat]}",
  "UNION {[a : Nat]}",
  "UNION {Seq({1})}",
];
const VALUES = ["3", '"s"', "{1}", "<<1>>", "[a |-> 1]", "[b |-> 1]", "M", "A_m"];

const memberships: Cell[] = SETS.flatMap((set) =>
  VALUES.map((value) => ({
    name: `${value} \\in ${set}`,
    spec: [
      "---- MODULE M ----",
      "EXTENDS Naturals, Sequences",
      "CONSTANT M, A_m",
      "VARIABLE x",
      "Init == x = 0",
      "Next == x < 2 /\\ x' = x + 1",
      `Inv == x >= 0 => ~(${value} \\in ${set})`,
      "====",
    ].join("\n"),
    config:
      "CONSTANT M = M\nCONSTANT A_m = A_m\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
  })),
);

const comparisons: Cell[] = [
  ["S == {<<1>>, <<2>>}", "[a |-> x] \\notin S"],
  ["S == {<<[a |-> 1]>>, <<[a |-> 2]>>}", "<<<<x>>>> \\notin S"],
  ["S == {<<i>> : i \\in 1..40}", "[a |-> x] \\notin S"],
  ["S == {[i \\in 0..1 |-> 5]}", "[a |-> x] \\notin S"],
].map(([definition, invariant]) => ({
  name: `${definition}: ${invariant}`,
  spec: [
    "---- MODULE M ----",
    "EXTENDS Naturals",
    "VARIABLE x",
    definition,
    `Inv == ${invariant}`,
    "Init == x = 0",
    "Next == x < 2 /\\ x' = x + 1",
    "====",
  ].join("\n"),
  config: "INIT Init\nNEXT Next\nINVARIANT Inv",
}));

// Constant definitions TLC can't normalize as it computes them at startup, which it evaluates
// again where they are used.
const startup: Cell[] = ["x = S", "x \\in {S}"].map((init) => ({
  name: `S == {A_a, B_b}: ${init}`,
  spec: [
    "---- MODULE M ----",
    "EXTENDS Naturals",
    "CONSTANT A_a, B_b",
    "VARIABLE x",
    "S == {A_a, B_b}",
    `Init == ${init}`,
    "Next == x' = x",
    "Inv == x # S",
    "====",
  ].join("\n"),
  config: "CONSTANT A_a = A_a\nCONSTANT B_b = B_b\nINIT Init\nNEXT Next\nINVARIANT Inv",
}));

// Memberships whose failing comparison is in a set nested in the one tested, which TLC reports
// with the sources of the values whose `compareTo` fails there.
const nestedComparisons: Cell[] = [
  "[a |-> [b |-> x]] \\in [a : S]",
  "<<[b |-> x]>> \\in S \\X S",
  "[a |-> [b |-> x]] \\in [a : SUBSET S]",
  "{[b |-> x]} \\in SUBSET S",
  "{{[b |-> x]}} \\in SUBSET SUBSET S",
  "[k \\in {1} |-> [b |-> x]] \\in [{1} -> S]",
  "<<[b |-> x]>> \\in Seq(S)",
  "[a |-> <<[b |-> x]>>] \\in [a : S \\X S]",
  "[a |-> [b |-> x]] \\in [a : S] \\cup {1}",
  "[a |-> [b |-> x]] \\in {1} \\cup [a : S]",
  "[a |-> [b |-> x]] \\in [a : S] \\cup [a : {2}]",
  "[a |-> [b |-> x]] \\in UNION {[a : S]}",
  "<<[b |-> x]>> \\in Seq(S) \\cup {1}",
  "[a |-> x] \\in S \\cup {1}",
  "x \\in SUBSET {1}",
].map((membership) => ({
  name: `S == {<<1>>, <<2>>}: ${membership}`,
  spec: [
    "---- MODULE M ----",
    "EXTENDS Naturals, Sequences",
    "VARIABLE x",
    "S == {<<1>>, <<2>>}",
    `Inv == ${membership}`,
    "Init == x = 0",
    "Next == x < 2 /\\ x' = x + 1",
    "====",
  ].join("\n"),
  config: "INIT Init\nNEXT Next\nINVARIANT Inv",
}));

// Functions whose body fails as TLC builds them with a source, and applications TLC fails in a
// tuple's or a record's method, in the initial and next states.
const functions: Cell[] = [
  ["x = [k \\in {1, 2} |-> k \\div 0]", "x' = x"],
  ["x = [k \\in {1, 2} |-> <<1, 2>>[k + 1]]", "x' = x"],
  ["x = 0", "x' = [k \\in 1..2 |-> k \\div 0]"],
  ["x = 0", "x' = [j \\in {1} |-> [k \\in {1, 2} |-> k \\div 0]]"],
  ["x = 0", "x' = [j \\in {1}, k \\in {1, 2} |-> k \\div 0]"],
  ["x = 0", "x' = [k \\in {1, 2} |-> <<1, 2>>[k + 1]]"],
  ["x = 0", "x' = [k \\in Nat |-> k \\div 0][1]"],
  ["x = 0", "x' = [a |-> 1][1]"],
  ["x = 0", 'x\' = <<1, 2>>["a"]'],
].map(([init, next]) => ({
  name: `Init == ${init}: Next == ${next}`,
  spec: [
    "---- MODULE M ----",
    "EXTENDS Naturals",
    "VARIABLE x",
    `Init == ${init}`,
    `Next == ${next}`,
    "====",
  ].join("\n"),
  config: "INIT Init\nNEXT Next",
}));

// Failures in a value with no source, which TLC reports with the nested expressions instead: a
// set filter, which `CallStackTool.eval` copies without its source.
const unsourced: Cell[] = ["{n \\in Nat : n > 2}"].map((set) => ({
  name: `Init == x \\in ${set}`,
  spec: [
    "---- MODULE M ----",
    "EXTENDS Naturals",
    "VARIABLE x",
    `Init == x \\in ${set}`,
    "Next == UNCHANGED x",
    "====",
  ].join("\n"),
  config: "INIT Init\nNEXT Next",
}));

// A state check that fails as the initial predicate's last conjunct enumerates its set: TLC
// checks the state from `Tool.getInitStates`, after the set's enumerator returned, so the failure
// is in no method of the set and TLC reports the nested expressions.
const continued: Cell[] = [
  ["x \\in 0..1 /\\ y \\in {0}", "INVARIANT Inv", "Inv == 1"],
  ["x = 0 /\\ y \\in {0, 1}", "INVARIANT Inv", "Inv == 1"],
  ["y \\in {0} /\\ x \\in 0..1", "INVARIANT Inv", "Inv == 1"],
  ["x = 0 /\\ y \\in {0}", "CONSTRAINT Con", "Con == 1"],
].map(([init, section, check]) => ({
  name: `Init == ${init}: ${check}`,
  spec: [
    "---- MODULE M ----",
    "EXTENDS Integers",
    "VARIABLES x, y",
    `Init == ${init}`,
    "Next == x' = x /\\ y' = y",
    check,
    "====",
  ].join("\n"),
  config: `INIT Init\nNEXT Next\n${section}`,
}));

// A set of functions over Nat, which TLC enumerates by its own method wherever it enumerates it:
// as the set of a quantifier, a CHOOSE or a set map, and as the base of a set filter TLC keeps
// lazy, which another value's method enumerates. Cardinality, a Java method, reports the
// FingerprintException as its failure.
const functionSets: Cell[] = [
  "{f \\in [Nat -> {0}] : TRUE} = {}",
  "\\E f \\in [Nat -> {0}] : TRUE",
  "\\A f \\in [Nat -> {0}] : TRUE",
  "\\A f \\in {g \\in [Nat -> {0}] : TRUE} : TRUE",
  "CHOOSE f \\in [Nat -> {0}] : TRUE",
  "{f : f \\in [Nat -> {0}]} = {}",
  "Cardinality({f \\in [Nat -> {0}] : TRUE}) = 1",
  "Cardinality([Nat -> {0}]) = 1",
].map((test) => ({
  name: `Init == x = ${test}`,
  spec: [
    "---- MODULE M ----",
    "EXTENDS Integers, FiniteSets",
    "VARIABLE x",
    `Test == ${test}`,
    "Init == x = Test",
    "Next == x' = x",
    "====",
  ].join("\n"),
  config: "INIT Init\nNEXT Next",
}));

const steps: Cell[] = [
  "({<<1>>} \\cup {2}) = {}",
  "({[a |-> 1]} \\cap {{1}}) = {}",
  "2 \\in {<<1>>}",
  '{("a" :> 1), <<2>>} = {}',
  "({<<1>>} \\cap {2}) = {}",
  "({<<1>>} \\ {2}) = {}",
  "({2} \\cup {<<1>>}) = {}",
  "({<<1>>} \\cup {<<2>>, 3}) = {}",
  "<<{<<1>>, 2}>> = <<{}>>",
  "2 \\in {{<<1>>}}",
].map((predicate) => ({
  name: predicate,
  spec: [
    "---- MODULE M ----",
    "EXTENDS Naturals, TLC",
    "VARIABLE x",
    "Init == x = 0",
    `Next == x' = x /\\ ${predicate}`,
    "====",
  ].join("\n"),
  config: "INIT Init\nNEXT Next",
}));

const initialComparisons: Cell[] = ["[a |-> 1]", '"a" :> 1', '"a b" :> 1'].map((value) => ({
  name: `Init == x = ${value}: x = {}`,
  spec: [
    "---- MODULE M ----",
    "EXTENDS TLC",
    "VARIABLE x",
    `Init == x = ${value}`,
    "Next == UNCHANGED x",
    "Inv == x = {}",
    "====",
  ].join("\n"),
  config: "INIT Init\nNEXT Next\nINVARIANT Inv",
}));

// Initial states TLC's replay fails to fingerprint: a filter, whose source `CallStackTool` drops,
// a state the constraints hold of or exclude, and states past the one that fails.
const initialStates: Cell[] = [
  ["x = {n \\in Nat : n > 1} /\\ y = 0", ""],
  ["x = {{n \\in Nat : n > 1}} /\\ y = 0", ""],
  ["\\/ (x = {n \\in Nat : n > 1} /\\ y = 0) \\/ (x = 0 /\\ y = 1)", ""],
  ["\\/ (x = {n \\in Nat : n > 1} /\\ y = 0) \\/ (x = 0 /\\ y = 1)", "y = 0"],
  ["\\/ (x = SUBSET (1..31) /\\ y = 0) \\/ (x = 0 /\\ y = 1)", ""],
  ["\\/ (x = SUBSET (1..31) /\\ y = 0) \\/ (x = 0 /\\ y = 1)", "y \\in {0, 1}"],
  ["\\/ (x = 0 /\\ y = 1) \\/ (x = SUBSET (1..31) /\\ y = 0)", "y = 0"],
].map(([init, constraint]) => ({
  name: constraint ? `Init == ${init} with C == ${constraint}` : `Init == ${init}`,
  spec: [
    "---- MODULE M ----",
    "EXTENDS Integers",
    "VARIABLES x, y",
    `Init == ${init}`,
    "Next == UNCHANGED <<x, y>>",
    ...(constraint ? [`C == ${constraint}`] : []),
    "====",
  ].join("\n"),
  config: `INIT Init\nNEXT Next${constraint ? "\nCONSTRAINT C" : ""}`,
}));

// Temporal properties whose atoms fail with an EvalException as TLC adds the initial state to the
// behavior graphs, which escapes `doInit` without the state.
const initialAtoms: Cell[] = [
  "<>(1 \\div 0 = x)",
  '<>(Assert(x > 0, "no") /\\ x = 2)',
  "<>(1 \\div 0 = x) /\\ <>(<<1>>[2] = x)",
  "<>(x % 0 = 1) \\/ <>(1 \\div 0 = x)",
].map((property) => ({
  name: `Prop == ${property}`,
  spec: [
    "---- MODULE M ----",
    "EXTENDS Naturals, TLC",
    "VARIABLE x",
    "Init == x = 0",
    "Next == x < 2 /\\ x' = x + 1",
    "Spec == Init /\\ [][Next]_x /\\ WF_x(Next)",
    `Prop == ${property}`,
    "====",
  ].join("\n"),
  config: "SPECIFICATION Spec\nPROPERTY Prop",
}));

// Function definitions that fail as TLC builds them, in the frame of the function constructor
// SANY makes of the definition, which `FcnLambdaValue` raises as a FingerprintException.
const functionDefinitions: Cell[] = [
  ["F[k \\in {1}] == 1 \\div (x - 1)\nStep == x' = (x + 1 + 0 * F[1]) % 3", "INIT Init\nNEXT Step"],
  ["F[k \\in {1}] == 1 \\div x\nInv == F[1] = 0", "INIT Init\nNEXT Next\nINVARIANT Inv"],
  [
    "F[n \\in 0..3] == IF n = 0 THEN 1 \\div x ELSE F[n - 1]\nStep == x' = F[3]",
    "INIT Init\nNEXT Step",
  ],
  ["F[k \\in {1}] == 1 \\div 0\nStart == x = F[1]", "INIT Start\nNEXT Next"],
  ["F[k \\in {1}] == <<1>>[x + 2]\nStart == x = 0 /\\ F[1] = 1", "INIT Start\nNEXT Next"],
  ["F[k \\in {1}] == {1} \\in x\nStart == x = 0 /\\ F[1]", "INIT Start\nNEXT Next"],
  ["G[k \\in {1}] == x = 0\nF == G\nStart == F[1]", "INIT Start\nNEXT Next"],
].map(([definitions, config]) => ({
  name: definitions.replaceAll("\n", "; "),
  spec: [
    "---- MODULE M ----",
    "EXTENDS Integers, TLC",
    "VARIABLE x",
    "Init == x = 0",
    "Next == x < 3 /\\ x' = x + 1",
    definitions,
    "====",
  ].join("\n"),
  config,
}));

// An ALIAS TLC holds as a value rather than the definition it names: a definition TLC computes as
// it starts, which a numeral or a string isn't, and a name the configuration assigns, beside an
// ALIAS that takes an argument, one the configuration substitutes and state functions.
const constantAliases: Cell[] = [
  ["Alias == 3", ""],
  ['Alias == "a"', ""],
  ["Alias == (3)", ""],
  ["Alias == -3", ""],
  ["Alias == 1 + 2", ""],
  ["Alias == LET a == 3 IN a", ""],
  ["Alias == TRUE", ""],
  ["Alias == [a |-> 1]", ""],
  ["Alias == [x |-> 1, y |-> 2]", ""],
  ["Alias == {1, 2}", ""],
  ["Alias(p) == [x |-> p]", ""],
  ["Alias == x + 1", ""],
  ["Alias == {x}", ""],
  ["Alias == x > 0", ""],
  ["Alias == [y |-> x]", "CONSTANT Alias = 3"],
  ["Alias == [y |-> x]", "CONSTANT Alias = {1, 2}"],
  ["Alias == [y |-> x]", "CONSTANT Alias = Alias"],
  ["", "CONSTANT Alias = 3"],
  ["CONSTANT Alias", "CONSTANT Alias = 3"],
  ["Alias == [y |-> x]\nQ == [x |-> x + 10, y |-> y]", "CONSTANT Alias <- Q"],
  ["Alias == [y |-> x]\nQ == 3", "CONSTANT Alias <- Q"],
  ["Q == [x |-> x + 10, y |-> y]\nAlias == 3", "CONSTANT Alias <- Q"],
  ["Alias == [y |-> x]\nQ == {1, 2}", "CONSTANT Alias <- Q"],
  ["Alias == [z |-> x]\nQ == [y |-> x]", "CONSTANT Alias = 3\nCONSTANT Alias <- Q"],
  ["Alias == [z |-> x]\nQ == [y |-> x]", "CONSTANT Alias <- Q\nCONSTANT Alias = Alias"],
].flatMap(([definitions, constants]) =>
  ["INVARIANT Inv\n", ""].map((invariant) => ({
    name: `${definitions.replaceAll("\n", "; ") || "no ALIAS definition"}${constants ? `, ${constants.replaceAll("\n", ", ")}` : ""}${invariant ? "" : ", deadlock"}`,
    spec: [
      "---- MODULE M ----",
      "EXTENDS Naturals",
      "VARIABLES x, y",
      "Init == x = 0 /\\ y = 0",
      "Next == x < 2 /\\ x' = x + 1 /\\ y' = y",
      "Inv == x < 2",
      ...(definitions ? [definitions] : []),
      "====",
    ].join("\n"),
    config: `${constants ? `${constants}\n` : ""}INIT Init\nNEXT Next\n${invariant}ALIAS Alias`,
  })),
);

// An ALIAS the configuration assigns a value the front end can't normalize, on a run that prints
// no trace, where TLC never reads the ALIAS.
const unprintedAliases: Cell[] = ["", "\nCONSTANT Alias <- Q"].map((substitution) => ({
  name: `CONSTANT Alias = {1, "a"}${substitution.replaceAll("\n", ", ")}, no trace`,
  spec: [
    "---- MODULE M ----",
    "EXTENDS Naturals",
    "VARIABLE x",
    "Init == x = 0",
    "Next == x' = (x + 1) % 3",
    "Inv == x < 5",
    "Q == [y |-> x]",
    "Alias == [z |-> x]",
    "====",
  ].join("\n"),
  config: `INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias\nCONSTANT Alias = {1, "a"}${substitution}`,
}));

// A literal definition TLC computes as it starts after all: one the configuration substitutes for
// another definition, which TLC computes in that one's name, an INSTANCE's copy whose literal is a
// substitution, and a function whose body is a literal.
const substitutedLiterals: Cell[] = [
  {
    name: "Alias == 3, CONSTANT X <- Alias",
    spec: "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == x < 2\nX == 0\nAlias == 3\n\n====",
    config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias\nCONSTANT X <- Alias",
  },
  {
    name: 'Alias == "a", CONSTANT X <- Alias',
    spec: '---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x\' = x + 1\nInv == x < 2\nAlias == "a"\nX == 0\n\n====',
    config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias\nCONSTANT X <- Alias",
  },
  {
    name: "Alias == 3, CONSTANT X <- [M] Alias",
    spec: "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == x < 2\nX == 0\nAlias == 3\n\n====",
    config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias\nCONSTANT X <- [M] Alias",
  },
  {
    name: "Alias == c, INSTANCE N WITH c <- 3",
    spec: "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == x < 2\n---- MODULE N ----\nCONSTANT c\nAlias == c\n====\nINSTANCE N WITH c <- 3\n====",
    config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias",
  },
  {
    name: "PC == 3, CONSTANT X <- PC",
    spec: "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 3\nX == 0\nPC == 3\n\n====",
    config: "INIT Init\nNEXT Next\nPOSTCONDITION PC\nCONSTANT X <- PC",
  },
  {
    name: "PC == c, INSTANCE N WITH c <- 3",
    spec: "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 3\n---- MODULE N ----\nCONSTANT c\nPC == c\n====\nINSTANCE N WITH c <- 3\n====",
    config: "INIT Init\nNEXT Next\nPOSTCONDITION PC",
  },
  {
    name: "Alias == 3 in an INSTANCE'd module, CONSTANT X <- Alias",
    spec: "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == x < 2\n---- MODULE Inner ----\nAlias == 3\n====\nINSTANCE Inner\nX == 0\n\n====",
    config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias\nCONSTANT X <- Alias",
  },
  {
    name: "PC == 3 in an INSTANCE'd module, CONSTANT X <- PC",
    spec: "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 3\n---- MODULE Inner ----\nPC == 3\n====\nINSTANCE Inner\nX == 0\n====",
    config: "INIT Init\nNEXT Next\nPOSTCONDITION PC\nCONSTANT X <- PC",
  },
  {
    name: "Alias[i \\in {1}] == 3, a function",
    spec: "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == x < 2\nAlias[i \\in {1}] == 3\n\n====",
    config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias",
  },
  {
    name: 'Alias[i \\in {1, 2}] == "s", a function',
    spec: '---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x\' = x + 1\nInv == x < 2\nAlias[i \\in {1, 2}] == "s"\n\n====',
    config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias",
  },
];

// An ALIAS the spec also reads that the configuration assigns and substitutes for, which TLC holds
// as the substituted definition, a theorem's name, which isn't one of TLC's definitions, and an
// assignment scoped to a module that defines no such name, which TLC applies to nothing.
const reviewedAliases: Cell[] = [
  {
    name: "Alias == 1 read by the invariant, CONSTANT Alias = 1, CONSTANT Alias <- Q",
    spec: "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nAlias == 1\nQ == [y |-> x]\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == x < 2 /\\ Alias = Alias\n\n====",
    config:
      "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias\nCONSTANT Alias = 1\nCONSTANT Alias <- Q",
  },
  {
    name: "THEOREM Alias == 3",
    spec: "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == x < 2\nTHEOREM Alias == 3\n\n====",
    config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias",
  },
  {
    name: 'THEOREM Alias == "a"',
    spec: '---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x\' = x + 1\nInv == x < 2\nTHEOREM Alias == "a"\n\n====',
    config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias",
  },
  {
    name: "THEOREM Alias == 3, CONSTANT Alias = 4",
    spec: "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == x < 2\nTHEOREM Alias == 3\n\n====",
    config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias\nCONSTANT Alias = 4",
  },
  {
    name: "CONSTANT Alias = [Inner] 3, Inner defining no Alias",
    spec: "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\n---- MODULE Inner ----\nFoo == 1\n====\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == x < 2\nAlias == [z |-> x]\n\n====",
    config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias\nCONSTANT Alias = [Inner] 3",
  },
  {
    name: "CONSTANT Alias = [Nope] 3, no module Nope",
    spec: "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == x < 2\nAlias == [z |-> x]\n\n====",
    config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias\nCONSTANT Alias = [Nope] 3",
  },
];

const record = (cell: Cell, workers: number) => {
  const directory = mkdtempSync(join(tmpdir(), "prove-it-fingerprint-"));
  writeFileSync(join(directory, "M.tla"), `${cell.spec}\n`);
  writeFileSync(join(directory, "M.cfg"), `${cell.config}\n`);
  const result = spawnSync(
    "java",
    [
      "-cp",
      jarPath,
      "tlc2.TLC",
      "-workers",
      String(workers),
      "-nowarning",
      "-fp",
      "0",
      "-lncheck",
      "final",
      "-noGenerateSpecTE",
      "-config",
      "M.cfg",
      "M.tla",
    ],
    { cwd: directory, encoding: "utf8" },
  );
  rmSync(directory, { recursive: true, force: true });
  const lines = `${result.stdout}${result.stderr}`
    .split("\n")
    .filter((line) => !VARYING.some((prefix) => line.startsWith(prefix)));
  return { exit: result.status, output: lines.join("\n").trimEnd() };
};

const blocks = [
  ...memberships,
  ...comparisons,
  ...startup,
  ...nestedComparisons,
  ...functions,
  ...unsourced,
  ...continued,
  ...functionSets,
  ...steps,
  ...initialComparisons,
  ...initialStates,
  ...initialAtoms,
  ...functionDefinitions,
  ...constantAliases,
  ...unprintedAliases,
  ...substitutedLiterals,
  ...reviewedAliases,
].flatMap((cell) => [
  `### ${cell.name}`,
  "--- spec",
  cell.spec,
  "--- config",
  cell.config,
  ...[1, 4].flatMap((workers) => {
    const recorded = record(cell, workers);
    return [`--- workers ${workers} exit ${recorded.exit}`, recorded.output];
  }),
]);
writeFileSync(OUTPUT_PATH, `${blocks.join("\n")}\n### end\n`);
console.log(`Wrote ${OUTPUT_PATH}`);

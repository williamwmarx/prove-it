// Records what TLC prints where it fails to fingerprint a state or a value, for the cells the
// binary's test `fingerprint_exceptions` runs: memberships of values in sets TLC tests by their own
// methods, searches of a constant definition's sorted set whose comparison fails, in it or in a set
// nested in it, constant definitions TLC can't normalize at startup, functions whose body fails as
// TLC builds them and applications of tuples and records, failures in a value TLC gives no source,
// comparisons TLC can't make in the next-state relation or of an initial state's value with a set,
// initial states that hold values TLC can't fingerprint, temporal properties that fail on the
// initial state with an EvalException, function definitions that fail as TLC builds them, and
// ALIAS values TLC can't print. Each cell runs at -workers 1 and 4 and writes TLC's exit code and
// its output without the lines that differ from run to run, which the test drops from the
// binary's too.
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

// ALIAS values TLC normalizes as it prints a trace's states, where a set it can't normalize stops
// the trace with its unexpected-exception report.
const aliases: Cell[] = ["{1, TRUE}", "SUBSET {1, TRUE}", "{1, 2}", "SUBSET {1, 2}"].map(
  (value) => ({
    name: `Alias == [x |-> x, v |-> ${value}]`,
    spec: [
      "---- MODULE M ----",
      "EXTENDS Naturals",
      "VARIABLE x",
      "Init == x = 0",
      "Next == x' = x + 1",
      "Inv == x < 1",
      `Alias == [x |-> x, v |-> ${value}]`,
      "====",
    ].join("\n"),
    config: "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias",
  }),
);

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
  ...steps,
  ...initialComparisons,
  ...initialStates,
  ...initialAtoms,
  ...functionDefinitions,
  ...aliases,
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

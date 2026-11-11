// Records what TLC prints where it fails to fingerprint a state as it checks an invariant on an
// initial state, for the cells the binary's test `fingerprint_exceptions` runs: memberships of
// values in sets TLC tests by their own methods, searches of a constant definition's sorted set
// whose comparison fails, in it or in a set nested in it, and constant definitions TLC can't
// normalize at startup. Each cell runs at -workers 1 and 4 and writes TLC's exit code and its
// output without the lines that differ from run to run, which the test drops from the binary's too.
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

const blocks = [...memberships, ...comparisons, ...startup, ...nestedComparisons].flatMap(
  (cell) => [
    `### ${cell.name}`,
    "--- spec",
    cell.spec,
    "--- config",
    cell.config,
    ...[1, 4].flatMap((workers) => {
      const recorded = record(cell, workers);
      return [`--- workers ${workers} exit ${recorded.exit}`, recorded.output];
    }),
  ],
);
writeFileSync(OUTPUT_PATH, `${blocks.join("\n")}\n### end\n`);
console.log(`Wrote ${OUTPUT_PATH}`);

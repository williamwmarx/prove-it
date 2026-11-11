// Records what TLC prints for the cells the binary's test `startup_texts` runs: models whose
// constant definitions TLC computes as it starts, one of them a CHOOSE that takes TLC seconds
// and makes no string, as the ring of nodes of tlaplus/Examples' EWD998ChanID does, beside ones
// that make strings TLC orders by when it made them. Each cell runs at -workers 1 and 4 and
// writes TLC's exit code and its output without the lines that differ from run to run, which the
// test drops from the binary's too.
// Usage: TLA2TOOLS_JAR=path bun scripts/record-startup-texts.ts
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
  "../native/crates/prove-it-cli/tests/startup-texts.txt",
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

// EWD998ChanID's RingOfNodes, with Utils' IsSimpleCycle and Functions' Range, over six nodes.
const RING = [
  "Range(f) == {f[x] : x \\in DOMAIN f}",
  "IsSimpleCycle(S, r) ==",
  "  LET F[i \\in 1..Cardinality(S)] ==",
  "        IF i = 1 THEN << CHOOSE s \\in S : TRUE >>",
  "        ELSE LET seq == F[i-1]",
  "                 head == Head(seq)",
  "             IN << r[head] >> \\o F[i-1]",
  "  IN Range(F[Cardinality(S)]) = S",
  "RingOfNodes == CHOOSE r \\in [Node -> Node] : IsSimpleCycle(Node, r)",
];

// The strings TLC makes as it computes a definition before the ring and one after it, which it
// orders by when it made them.
const BEFORE = 'Before == {"b" \\o "x", "a" \\o "x"}';
const AFTER = 'After == {"d" \\o "x", "c" \\o "x"}';

const getCell = (name: string, definitions: string[], prints: string[]) => ({
  name,
  spec: [
    "---- MODULE M ----",
    "EXTENDS Naturals, Sequences, FiniteSets, TLC",
    "CONSTANT Node",
    "VARIABLE ring",
    ...definitions,
    ...prints.map((print) => `ASSUME PrintT(${print})`),
    "Init == ring = RingOfNodes",
    "Next == ring' = ring",
    "====",
  ].join("\n"),
  config: "CONSTANT Node = {n1, n2, n3, n4, n5, n6}\nINIT Init\nNEXT Next",
});

const cells: Cell[] = [
  getCell("ring", RING, ["RingOfNodes"]),
  getCell("ring between strings", [BEFORE, ...RING, AFTER], ["RingOfNodes", "Before", "After"]),
];

const record = (cell: Cell, workers: number) => {
  const directory = mkdtempSync(join(tmpdir(), "prove-it-startup-"));
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

const blocks = cells.flatMap((cell) => [
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

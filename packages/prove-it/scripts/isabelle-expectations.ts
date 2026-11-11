// Regenerates the expectations of prove-isabelle's tests, native/crates/prover/isabelle/testdata,
// from the TypeScript Isabelle back end that the crate ports. Each group writes its own files:
//   isar       isar/*: the outer and inner syntax parsers
//   statement  statement/*: the statements read from the fixture theories
//   kernel     kernel/{envir,pattern,unify}.txt
//   thm        kernel/{thm,resolve,tactic,rules}.txt: theorems, resolution and tactics
//   simp       kernel/{simp,simp-tac}.txt: the simplifier
//   blast      blast/term.txt: blast's terms
//   hypsubst   provers/hypsubst.txt
//   provers    provers/{classical,blast,iprover}.txt: the classical reasoner, blast and iprover
//   decide     decide.txt: decideIsabelle under step limits
// Each group runs in a process of its own, as each was recorded, and the provers group runs one
// process per kind of problem, in parallel. Under Bun, as recorded: where JavaScript's stack
// overflows, the outcome depends on the runtime (decide.txt's Paxos-109 lines vary from run to run).
//
// Usage: bun scripts/isabelle-expectations.ts [group...]   (every group by default)
import { mkdirSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";

import { getBlastTermExpectations } from "./isabelle-expectations/blast-term";
import { getDecideExpectations } from "./isabelle-expectations/decide";
import { getHypsubstExpectations } from "./isabelle-expectations/hypsubst";
import { getIsarExpectations } from "./isabelle-expectations/isar";
import { getKernelExpectations } from "./isabelle-expectations/kernel";
import { getProverExpectations, PROVER_KINDS } from "./isabelle-expectations/provers";
import { getSimpExpectations } from "./isabelle-expectations/simp";
import { getStatementExpectations } from "./isabelle-expectations/statement";
import { getThmExpectations } from "./isabelle-expectations/thm";

const TESTDATA_DIRECTORY = join(import.meta.dirname, "../native/crates/prover/isabelle/testdata");

// Each job's files, by their path in testdata.
const JOBS: Record<string, () => Record<string, string>> = {
  isar: getIsarExpectations,
  statement: getStatementExpectations,
  kernel: getKernelExpectations,
  thm: getThmExpectations,
  simp: getSimpExpectations,
  blast: getBlastTermExpectations,
  hypsubst: getHypsubstExpectations,
  decide: getDecideExpectations,
  ...Object.fromEntries(
    PROVER_KINDS.map(([kind]) => [`provers:${kind}`, () => getProverExpectations(kind)]),
  ),
};

const GROUPS = [
  "isar",
  "statement",
  "kernel",
  "thm",
  "simp",
  "blast",
  "hypsubst",
  "provers",
  "decide",
];

// A child process runs one job and prints its files as JSON.
if (process.argv[2] === "--job") {
  process.stdout.write(JSON.stringify(JOBS[process.argv[3]]()));
} else {
  const groups = process.argv.length > 2 ? process.argv.slice(2) : GROUPS;
  const unknown = groups.filter((group) => !GROUPS.includes(group));
  if (unknown.length > 0) {
    console.error(`Unknown groups: ${unknown.join(", ")}. The groups: ${GROUPS.join(", ")}`);
    process.exit(1);
  }
  for (const group of groups) {
    const jobs = group === "provers" ? PROVER_KINDS.map(([kind]) => `provers:${kind}`) : [group];
    const outputs = await Promise.all(
      jobs.map(async (job) => {
        const child = Bun.spawn([process.execPath, import.meta.path, "--job", job], {
          stdout: "pipe",
          stderr: "inherit",
        });
        const output = await new Response(child.stdout).text();
        if ((await child.exited) !== 0) throw new Error(`${job} failed`);
        const files: Record<string, string> = JSON.parse(output);
        return files;
      }),
    );
    // A file several jobs write is their parts in the order of the jobs.
    const files = new Map<string, string>();
    for (const output of outputs)
      for (const [path, text] of Object.entries(output))
        files.set(path, (files.get(path) ?? "") + text);
    for (const [path, text] of files) {
      const target = join(TESTDATA_DIRECTORY, path);
      mkdirSync(dirname(target), { recursive: true });
      writeFileSync(target, text);
    }
    console.error(`${group}: ${[...files.keys()].join(" ")}`);
  }
}

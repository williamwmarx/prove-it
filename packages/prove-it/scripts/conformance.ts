import { spawn } from "node:child_process";
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import type { ModelOutcome } from "./check-model";
import { compareOutcome } from "./compare-outcome";
import { CONFORMANCE_DIRECTORY, type CorpusModel, EXPECTED_PATH, findModels } from "./corpora";
import { classifyEngineLine, getEngineEnvironment, getEngineLine } from "./engine-runs";
import type { ExpectedResult } from "./record-tlc";

type Verdict = "match" | "mismatch" | "unsupported" | "crash";

interface ConformanceResult {
  id: string;
  verdict: Verdict;
  expected: ExpectedResult;
  actual: ModelOutcome | undefined;
  detail: string | undefined;
  // What the engine did, as its [engine] line says: completed, skipped or handed over.
  engine: string;
  engineLine: string | undefined;
}

interface ModelRun {
  outcome: ModelOutcome | undefined;
  engineLine: string | undefined;
}

const PASSING_PATH = join(CONFORMANCE_DIRECTORY, "passing.json");
const RESULTS_PATH = join(CONFORMANCE_DIRECTORY, ".results.json");

const getArgument = (name: string) => {
  const index = process.argv.indexOf(name);
  return index === -1 ? undefined : process.argv[index + 1];
};

const maximumTlcMilliseconds = Number(getArgument("--max-tlc-ms") ?? 20000);
const filter = getArgument("--filter");
const isUpdate = process.argv.includes("--update");
const concurrency = Number(getArgument("--concurrency") ?? 4);
// With --check, every model passing.json lists must still match TLC, or the run fails.
const isChecked = process.argv.includes("--check");

const runModel = (specPath: string, configPath: string) =>
  new Promise<ModelRun>((resolve) => {
    const child = spawn(
      process.execPath,
      [
        "--stack-size=8000",
        "--max-old-space-size=6144",
        join(import.meta.dirname, "check-model.js"),
        specPath,
        configPath,
      ],
      { stdio: ["ignore", "pipe", "pipe"], env: getEngineEnvironment() },
    );
    const stdout: Buffer[] = [];
    const stderr: Buffer[] = [];
    child.stdout.on("data", (chunk: Buffer) => stdout.push(chunk));
    child.stderr.on("data", (chunk: Buffer) => stderr.push(chunk));
    child.on("close", () => {
      const output = Buffer.concat(stdout).toString("utf8");
      resolve({
        outcome: output.startsWith("{") ? JSON.parse(output) : undefined,
        engineLine: getEngineLine(Buffer.concat(stderr).toString("utf8")),
      });
    });
  });

const expectedResults: ExpectedResult[] = JSON.parse(readFileSync(EXPECTED_PATH, "utf8"));
const expectedById = new Map(expectedResults.map((result) => [result.id, result]));
const isLarge = (model: CorpusModel) =>
  (expectedById.get(model.id)?.tlcMilliseconds ?? 0) > maximumTlcMilliseconds;

// TLC only errors after the time limit when it runs out of memory or disk on an unbounded state
// space, so those runs have no verdict to compare.
const models = findModels().filter((model) => {
  const expected = expectedById.get(model.id);
  return (
    expected !== undefined &&
    (expected.status !== "error" || !isLarge(model)) &&
    (filter === undefined || model.id.includes(filter))
  );
});

const results: ConformanceResult[] = [];

const work = async (queue: CorpusModel[]) => {
  for (let model = queue.shift(); model; model = queue.shift()) {
    const expected = expectedById.get(model.id);
    if (!expected) continue;
    const run = await runModel(model.specPath, model.configPath);
    const actual = run.outcome;
    const detail = actual ? compareOutcome(expected, actual) : "the checker crashed";
    const verdict: Verdict = !actual
      ? "crash"
      : actual.status === "unsupported"
        ? "unsupported"
        : detail
          ? "mismatch"
          : "match";
    results.push({
      id: model.id,
      verdict,
      expected,
      actual,
      detail: detail ?? actual?.error,
      engine: classifyEngineLine(run.engineLine).engine,
      engineLine: run.engineLine,
    });
    console.log(
      `[${results.length}/${models.length}] ${verdict.padEnd(11)} ${model.id}${verdict === "match" ? "" : `  ${detail ?? actual?.error ?? ""}`}`,
    );
  }
};

const smallModels = models.filter((model) => !isLarge(model));
await Promise.all(Array.from({ length: concurrency }, () => work(smallModels)));
await work(models.filter(isLarge));
results.sort((left, right) => (left.id < right.id ? -1 : 1));
writeFileSync(RESULTS_PATH, `${JSON.stringify(results, null, 2)}\n`);

const counts = results.reduce<Record<string, number>>((tally, result) => {
  tally[result.verdict] = (tally[result.verdict] ?? 0) + 1;
  return tally;
}, {});
console.log(
  `\n${Object.entries(counts)
    .map(([verdict, count]) => `${verdict}: ${count}`)
    .join(", ")}`,
);

if (isUpdate) {
  const passing = results.filter((result) => result.verdict === "match").map((result) => result.id);
  writeFileSync(PASSING_PATH, `${JSON.stringify(passing, null, 2)}\n`);
  console.log(`Wrote ${passing.length} passing models to ${PASSING_PATH}`);
}

if (isChecked) {
  if (!existsSync(PASSING_PATH)) {
    console.error(
      `\n--check compares with ${PASSING_PATH}, which doesn't exist. Record it with --update.`,
    );
    process.exit(1);
  }
  const passing = new Set<string>(JSON.parse(readFileSync(PASSING_PATH, "utf8")));
  const matches = new Set(
    results.filter((result) => result.verdict === "match").map((result) => result.id),
  );
  const getVerdict = (id: string) =>
    results.find((result) => result.id === id)?.verdict ?? "not found";
  // A listed model the run's options leave out is skipped; one the run didn't find, such as when
  // the corpora weren't fetched, fails the run.
  const isSelected = (id: string) => {
    const expected = expectedById.get(id);
    return (
      expected !== undefined &&
      (expected.status !== "error" || (expected.tlcMilliseconds ?? 0) <= maximumTlcMilliseconds) &&
      (filter === undefined || id.includes(filter))
    );
  };
  const regressed = [...passing].filter((id) => isSelected(id) && !matches.has(id));
  const gained = [...matches].filter((id) => !passing.has(id));
  if (gained.length > 0) {
    console.log(`\n${gained.length} models match that passing.json doesn't list:`);
    for (const id of gained) console.log(`  ${id}`);
  }
  if (regressed.length > 0) {
    console.log(`\n${regressed.length} models listed in passing.json no longer match:`);
    for (const id of regressed) console.log(`  ${id}: ${getVerdict(id)}`);
    process.exitCode = 1;
  }
}

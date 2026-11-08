import { spawn } from "node:child_process";
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import type { ModelOutcome } from "./check-model";
import { compareOutcome, OUTCOME_FIELDS } from "./compare-outcome";
import { CONFORMANCE_DIRECTORY, type CorpusModel, EXPECTED_PATH, findModels } from "./corpora";
import {
  classifyEngineLine,
  getBackendEnvironment,
  getBackends,
  getEngineLine,
} from "./engine-runs";
import type { ExpectedResult } from "./record-tlc";

type Verdict = "match" | "mismatch" | "unsupported" | "crash";

interface ConformanceResult {
  id: string;
  backend: string;
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
// --backend runs the engine with that backend; --compare-backends runs each model with each one, and
// fails if any two reach different outcomes, whether or not TLC's recording has the counts.
const backends = getBackends();

const runModel = (specPath: string, configPath: string, backend: string) =>
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
      { stdio: ["ignore", "pipe", "pipe"], env: getBackendEnvironment(backend) },
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
// The models whose outcome differs between backends, with how.
const backendDifferences: string[] = [];

const work = async (queue: CorpusModel[]) => {
  for (let model = queue.shift(); model; model = queue.shift()) {
    const expected = expectedById.get(model.id);
    if (!expected) continue;
    const modelResults: ConformanceResult[] = [];
    for (const backend of backends) {
      const run = await runModel(model.specPath, model.configPath, backend);
      const actual = run.outcome;
      const detail = actual ? compareOutcome(expected, actual) : "the checker crashed";
      const verdict: Verdict = !actual
        ? "crash"
        : actual.status === "unsupported"
          ? "unsupported"
          : detail
            ? "mismatch"
            : "match";
      modelResults.push({
        id: model.id,
        backend,
        verdict,
        expected,
        actual,
        detail: detail ?? actual?.error,
        engine: classifyEngineLine(run.engineLine).engine,
        engineLine: run.engineLine,
      });
      console.log(
        `[${results.length + modelResults.length}/${models.length * backends.length}] ${verdict.padEnd(11)} ${backends.length > 1 ? `${backend} ` : ""}${model.id}${verdict === "match" ? "" : `  ${detail ?? actual?.error ?? ""}`}`,
      );
    }
    const differences = modelResults
      .slice(1)
      .flatMap((result) =>
        OUTCOME_FIELDS.filter(
          (field) => result.actual?.[field] !== modelResults[0].actual?.[field],
        ).map(
          (field) =>
            `${field}: ${modelResults[0].backend} ${modelResults[0].actual?.[field]}, ${result.backend} ${result.actual?.[field]}`,
        ),
      );
    if (differences.length > 0) backendDifferences.push(`${model.id}: ${differences.join("; ")}`);
    results.push(...modelResults);
  }
};

const smallModels = models.filter((model) => !isLarge(model));
await Promise.all(Array.from({ length: concurrency }, () => work(smallModels)));
await work(models.filter(isLarge));
results.sort((left, right) =>
  left.id === right.id
    ? backends.indexOf(left.backend) - backends.indexOf(right.backend)
    : left.id < right.id
      ? -1
      : 1,
);
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
  const passing = [
    ...new Set(results.filter((result) => result.verdict === "match").map((result) => result.id)),
  ].filter((id) => results.every((result) => result.id !== id || result.verdict === "match"));
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
  // The backends a listed model must match with: every one the run tested.
  const matches = new Set(
    results
      .filter((result) => result.verdict === "match")
      .map((result) => `${result.backend} ${result.id}`),
  );
  const getVerdicts = (id: string) =>
    results
      .filter((result) => result.id === id)
      .map((result) => `${backends.length > 1 ? `${result.backend} ` : ""}${result.verdict}`)
      .join(", ") || "not found";
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
  const regressed = [...passing].filter(
    (id) => isSelected(id) && !backends.every((backend) => matches.has(`${backend} ${id}`)),
  );
  const gained = [
    ...new Set(
      results
        .filter((result) => result.verdict === "match" && !passing.has(result.id))
        .map((result) => result.id),
    ),
  ];
  if (gained.length > 0) {
    console.log(`\n${gained.length} models match that passing.json doesn't list:`);
    for (const id of gained) console.log(`  ${id}`);
  }
  if (regressed.length > 0) {
    console.log(`\n${regressed.length} models listed in passing.json no longer match:`);
    for (const id of regressed) console.log(`  ${id}: ${getVerdicts(id)}`);
    process.exitCode = 1;
  }
}

if (process.argv.includes("--compare-backends")) {
  console.log(
    backendDifferences.length === 0
      ? `\nThe backends ${backends.join(", ")} reached the same outcome on every model.`
      : `\n${backendDifferences.length} models differ between backends:\n${backendDifferences.map((difference) => `  ${difference}`).join("\n")}`,
  );
  if (backendDifferences.length > 0) process.exitCode = 1;
}

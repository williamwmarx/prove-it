// Runs every check of the library's tests through the native binary: the tests write each check to
// PROVE_IT_CHECK_LOG (src/parallel.ts), and each distinct check runs as TLC's command line would
// run it, on one thread and with every level shared between four. Prints how many the binary
// checks natively, and each reason it gives for the rest with the tests that reach it, as
// native/design/fallback.md records them. --log reads a log a run wrote before instead of running
// the tests; --json writes each check with its answers.
// Usage: bun scripts/run.ts check-log [--binary path] [--log path] [--json path]

import { spawn, spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { availableParallelism, tmpdir } from "node:os";
import { join, relative } from "node:path";

interface LoggedCheck {
  id: string;
  source: string;
  config: string;
  seed?: string;
  livenessCheck?: "default" | "final";
  isTool: boolean;
  isDumped: boolean;
  isContinued: boolean;
  version?: string;
  caller?: string;
}

interface LoggedModule {
  id: string;
  module: string;
  source: string;
}

interface Run {
  key: string;
  check: LoggedCheck;
  modules: Map<string, string>;
  test: string;
}

interface Answer {
  key: string;
  test: string;
  options: string[];
  modules: string[];
  isTemporal: boolean;
  answers: Record<string, string>;
}

const PACKAGE_DIRECTORY = join(import.meta.dirname, "..");
const NOT_NATIVE = "prove-it: not native yet: ";
const THREADS = ["1", "4"];

const getArgument = (name: string) => {
  const index = process.argv.indexOf(name);
  return index === -1 ? undefined : process.argv[index + 1];
};

const workDirectory = mkdtempSync(join(tmpdir(), "check-log-"));
const binary =
  getArgument("--binary") ?? join(PACKAGE_DIRECTORY, "native", "target", "release", "prove-it");
const logPath = getArgument("--log") ?? join(workDirectory, "checks.jsonl");
if (!getArgument("--log")) {
  // The tests run in Bun, which this script, run under Node, spawns by name.
  const tests = spawnSync("bun", ["test", "--parallel"], {
    cwd: PACKAGE_DIRECTORY,
    env: { ...process.env, PROVE_IT_CHECK_LOG: logPath },
    stdio: "inherit",
  });
  if (tests.status !== 0) process.exit(tests.status ?? 1);
}

const lines = readFileSync(logPath, "utf8").split("\n").filter(Boolean);
const entries: (LoggedCheck | LoggedModule)[] = lines.map((line) => JSON.parse(line));
const modulesById = new Map<string, Map<string, string>>();
for (const entry of entries) {
  if (!("module" in entry)) continue;
  const modules = modulesById.get(entry.id) ?? new Map<string, string>();
  modules.set(entry.module, entry.source);
  modulesById.set(entry.id, modules);
}

// The test a check comes from: the first frame of its caller in a test file.
const getTest = (caller: string | undefined) => {
  const frame = caller?.split("\n").find((line) => /\/tests\/.*\.test\.ts:/.test(line));
  const location = frame?.match(/\(?([^()\s]+\/tests\/[^()\s]+):\d+\)?$/)?.[1];
  return location ? relative(join(PACKAGE_DIRECTORY, "tests"), location) : "?";
};

// TLC's command line, but the spec, for a check's options: Java's properties, then TLC's options.
const getOptions = (check: LoggedCheck) => [
  ...(check.version === "1.7.4" ? ["-Dtla-ts.tlc=1.7.4"] : []),
  "tlc2.TLC",
  "-fp",
  "0",
  "-noGenerateSpecTE",
  ...(check.seed ? ["-seed", check.seed] : []),
  ...(check.livenessCheck === "final" ? ["-lncheck", "final"] : []),
  ...(check.isTool ? ["-tool"] : []),
  ...(check.isDumped ? ["-dump", "states"] : []),
  ...(check.isContinued ? ["-continue"] : []),
];

const runs = new Map<string, Run>();
for (const entry of entries) {
  if ("module" in entry) continue;
  const modules = modulesById.get(entry.id) ?? new Map<string, string>();
  const key = createHash("sha256")
    .update(JSON.stringify([entry.source, entry.config, getOptions(entry), [...modules].sort()]))
    .digest("hex")
    .slice(0, 16);
  if (!runs.has(key)) runs.set(key, { key, check: entry, modules, test: getTest(entry.caller) });
}

const runBinary = (directory: string, name: string, options: string[], threads: string) =>
  new Promise<string>((resolve) => {
    const child = spawn(binary, [...options, name], {
      cwd: directory,
      env: { ...process.env, PROVE_IT_WORKERS: threads, PROVE_IT_SHARED_LEVEL: "1" },
    });
    const stderr: Buffer[] = [];
    child.stderr.on("data", (chunk: Buffer) => stderr.push(chunk));
    child.stdout.resume();
    child.on("close", (code) => {
      const declined = Buffer.concat(stderr)
        .toString()
        .split("\n")
        .find((line) => line.startsWith(NOT_NATIVE));
      resolve(declined ? declined.slice(NOT_NATIVE.length) : `exit ${code}`);
    });
  });

const answer = async (run: Run): Promise<Answer> => {
  const name = run.check.source.match(/MODULE\s+(\w+)/)?.[1] ?? "Spec";
  const directory = join(workDirectory, run.key);
  mkdirSync(directory, { recursive: true });
  for (const [module, source] of run.modules)
    writeFileSync(join(directory, `${module}.tla`), source);
  writeFileSync(join(directory, `${name}.tla`), run.check.source);
  writeFileSync(join(directory, `${name}.cfg`), run.check.config);
  const options = getOptions(run.check);
  const answers: Record<string, string> = {};
  for (const threads of THREADS)
    answers[threads] = await runBinary(directory, name, options, threads);
  return {
    key: run.key,
    test: run.test,
    options,
    modules: [...run.modules.keys()],
    isTemporal: /PROPERT/i.test(run.check.config),
    answers,
  };
};

const pending = [...runs.values()];
const answers: Answer[] = [];
const work = async () => {
  for (let run = pending.shift(); run; run = pending.shift()) answers.push(await answer(run));
};
await Promise.all(Array.from({ length: Math.max(1, availableParallelism() >> 1) }, work));
answers.sort((left, right) => left.key.localeCompare(right.key));

const jsonPath = getArgument("--json");
if (jsonPath) writeFileSync(jsonPath, `${JSON.stringify(answers, undefined, 1)}\n`);

const isNative = (text: string) => text.startsWith("exit ");
const differing = answers.filter((entry) => entry.answers["1"] !== entry.answers["4"]);
const declined = answers.filter((entry) => !isNative(entry.answers["1"]));
const exits = new Map<string, number>();
for (const entry of answers.filter((innerEntry) => isNative(innerEntry.answers["1"]))) {
  exits.set(entry.answers["1"], (exits.get(entry.answers["1"]) ?? 0) + 1);
}
const reasons = new Map<string, Answer[]>();
for (const entry of declined) {
  const reason = entry.answers["1"].replace(/state \d+/g, "state N");
  reasons.set(reason, [...(reasons.get(reason) ?? []), entry]);
}
console.log(
  `${answers.length} checks: ${answers.length - declined.length} native, ${declined.length} not native yet, ${differing.length} answered differently on 1 and 4 threads.`,
);
console.log(
  [...exits]
    .sort((left, right) => right[1] - left[1])
    .map(([exit, count]) => `${exit} (${count})`)
    .join(", "),
);
console.log("\n| Runs | Reason | Tests |\n|---:|---|---|");
for (const [reason, entries] of [...reasons].sort(
  (left, right) => right[1].length - left[1].length || left[0].localeCompare(right[0]),
)) {
  const tests = new Map<string, number>();
  for (const entry of entries) tests.set(entry.test, (tests.get(entry.test) ?? 0) + 1);
  const named = [...tests]
    .sort((left, right) => right[1] - left[1])
    .map(([test, count]) => `\`${test}\`${count > 1 ? ` ×${count}` : ""}`);
  console.log(`| ${entries.length} | ${reason.replaceAll("|", "\\|")} | ${named.join(", ")} |`);
}
for (const entry of differing) {
  console.log(`differs on 1 and 4 threads: ${entry.test} ${JSON.stringify(entry.answers)}`);
}

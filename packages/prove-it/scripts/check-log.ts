// Runs every check of the library's tests through the native binary: the tests write each check to
// PROVE_IT_CHECK_LOG (src/parallel.ts), and each distinct check runs as TLC's command line would
// run it, on one thread and with every level shared between four. Prints how many the binary
// checks natively, and each reason it gives for the rest with the tests that reach it, as
// native/design/fallback.md records them, with what of a check the log keeps, and how many it
// checks natively in TLC's default mode, which generates the trace exploration spec. A check of TLC
// 1.7.4 is counted apart, retired with the interpreter, and not run. --log reads a log a run wrote
// before instead of running the tests; --json writes each check with its answers.
// Usage: bun scripts/run.ts check-log [--binary path] [--log path] [--json path]

import { spawn, spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { availableParallelism, tmpdir } from "node:os";
import { dirname, isAbsolute, join, relative } from "node:path";

interface LoggedCheck {
  id: string;
  source: string;
  config: string;
  seed?: string;
  livenessCheck?: "default" | "final";
  workers?: number;
  systemProperties?: [string, string][];
  dump?: { dot?: boolean; colorize?: boolean; actionLabels?: boolean; snapshot?: boolean };
  isTool: boolean;
  isContinued: boolean;
  isWarningEnabled: boolean;
  version?: string;
  // PROVE_IT_TEST_LIVE_CHECK_AT, which has the search check the temporal properties at that state.
  testLiveCheckAt: number;
  caller?: string;
}

interface LoggedModule {
  id: string;
  module: string;
  source: string;
}

interface LoggedClass {
  id: string;
  class: string;
  bytes: string;
}

interface LoggedFile {
  id: string;
  file: string;
  text: string;
}

interface Run {
  key: string;
  check: LoggedCheck;
  modules: Map<string, string>;
  classes: Map<string, string>;
  files: Map<string, string>;
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
const entries: (LoggedCheck | LoggedModule | LoggedClass | LoggedFile)[] = lines.map((line) =>
  JSON.parse(line),
);
// The modules each check loaded, by name, its classes in base64, and the files it read, by path.
const modulesById = new Map<string, Map<string, string>>();
const classesById = new Map<string, Map<string, string>>();
const filesById = new Map<string, Map<string, string>>();
for (const entry of entries) {
  if ("module" in entry) {
    modulesById.set(
      entry.id,
      (modulesById.get(entry.id) ?? new Map()).set(entry.module, entry.source),
    );
  } else if ("class" in entry) {
    classesById.set(
      entry.id,
      (classesById.get(entry.id) ?? new Map()).set(entry.class, entry.bytes),
    );
  } else if ("file" in entry) {
    filesById.set(entry.id, (filesById.get(entry.id) ?? new Map()).set(entry.file, entry.text));
  }
}

// The test a check comes from: the first frame of its caller in a test file.
const getTest = (caller: string | undefined) => {
  const frame = caller?.split("\n").find((line) => /\/tests\/.*\.test\.ts:/.test(line));
  const location = frame?.match(/\(?([^()\s]+\/tests\/[^()\s]+):\d+\)?$/)?.[1];
  return location ? relative(join(PACKAGE_DIRECTORY, "tests"), location) : "?";
};

// TLC's command line, but the spec, for a check's options: Java's properties, then TLC's options.
const getOptions = (check: LoggedCheck) => [
  ...(check.systemProperties ?? []).map(([name, value]) => `-D${name}=${value}`),
  "tlc2.TLC",
  "-fp",
  "0",
  "-noGenerateSpecTE",
  ...(check.seed ? ["-seed", check.seed] : []),
  ...(check.livenessCheck === "final" ? ["-lncheck", "final"] : []),
  ...(check.workers === undefined ? [] : ["-workers", String(check.workers)]),
  ...(check.isTool ? ["-tool"] : []),
  ...(check.isWarningEnabled ? [] : ["-nowarning"]),
  ...(check.dump
    ? [
        "-dump",
        ...(check.dump.dot
          ? [
              [
                "dot",
                check.dump.colorize && "colorize",
                check.dump.actionLabels && "actionlabels",
                check.dump.snapshot && "snapshot",
              ]
                .filter(Boolean)
                .join(","),
            ]
          : []),
        "states",
      ]
    : []),
  ...(check.isContinued ? ["-continue"] : []),
];

const runs = new Map<string, Run>();
for (const entry of entries) {
  if ("module" in entry || "class" in entry || "file" in entry) continue;
  const modules = modulesById.get(entry.id) ?? new Map<string, string>();
  const classes = classesById.get(entry.id) ?? new Map<string, string>();
  const files = filesById.get(entry.id) ?? new Map<string, string>();
  const key = createHash("sha256")
    .update(
      JSON.stringify([
        entry.source,
        entry.config,
        getOptions(entry),
        entry.version,
        entry.testLiveCheckAt,
        [...modules].sort(),
        [...classes].sort(),
        [...files].sort(),
      ]),
    )
    .digest("hex")
    .slice(0, 16);
  if (!runs.has(key)) {
    runs.set(key, { key, check: entry, modules, classes, files, test: getTest(entry.caller) });
  }
}

const runBinary = (run: Run, directory: string, name: string, options: string[], threads: string) =>
  new Promise<string>((resolve) => {
    // Node leaves out a variable whose value is undefined.
    const child = spawn(binary, [...options, name], {
      cwd: directory,
      env: {
        ...process.env,
        PROVE_IT_WORKERS: threads,
        PROVE_IT_SHARED_LEVEL: "1",
        PROVE_IT_TEST_LIVE_CHECK_AT:
          run.check.testLiveCheckAt > 0 ? String(run.check.testLiveCheckAt) : undefined,
      },
    });
    const stderr: Buffer[] = [];
    child.stderr.on("data", (chunk: Buffer) => stderr.push(chunk));
    child.stdout.resume();
    // A run a signal ends checked nothing, whatever it printed.
    child.on("close", (code, signal) => {
      const declined = Buffer.concat(stderr)
        .toString()
        .split("\n")
        .find((line) => line.startsWith(NOT_NATIVE));
      if (signal) resolve(`ended by ${signal}`);
      else resolve(declined ? declined.slice(NOT_NATIVE.length) : `exit ${code}`);
    });
  });

const answer = async (run: Run): Promise<Answer> => {
  const name = run.check.source.match(/MODULE\s+(\w+)/)?.[1] ?? "Spec";
  const directory = join(workDirectory, run.key);
  mkdirSync(directory, { recursive: true });
  for (const [module, source] of run.modules) {
    writeFileSync(join(directory, `${module}.tla`), source);
  }
  for (const [className, bytes] of run.classes) {
    writeFileSync(join(directory, `${className}.class`), Buffer.from(bytes, "base64"));
  }
  // The binary reads a file outside the check's directory where it is, if the test left it there.
  for (const [path, text] of run.files) {
    if (isAbsolute(path) || path.startsWith("..")) continue;
    mkdirSync(dirname(join(directory, path)), { recursive: true });
    writeFileSync(join(directory, path), text);
  }
  writeFileSync(join(directory, `${name}.tla`), run.check.source);
  writeFileSync(join(directory, `${name}.cfg`), run.check.config);
  const options = getOptions(run.check);
  const answers: Record<string, string> = {};
  for (const threads of THREADS)
    answers[threads] = await runBinary(run, directory, name, options, threads);
  answers.default = await runBinary(
    run,
    directory,
    name,
    options.filter((option) => option !== "-noGenerateSpecTE"),
    "1",
  );
  return {
    key: run.key,
    test: run.test,
    options,
    modules: [...run.modules.keys()],
    isTemporal: /PROPERT/i.test(run.check.config),
    answers,
  };
};

// The binary declines TLC 1.7.4, which leaves with the interpreter rather than becoming native.
const retired = [...runs.values()].filter((run) => run.check.version === "1.7.4");
const pending = [...runs.values()].filter((run) => run.check.version !== "1.7.4");
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
console.log(`${retired.length} more are TLC 1.7.4's, retired with the interpreter.`);
console.log(
  `In TLC's default mode, which generates the trace exploration spec: ${answers.filter((entry) => isNative(entry.answers.default)).length} native.`,
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

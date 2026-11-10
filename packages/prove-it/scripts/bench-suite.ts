// Times TLA+ model checkers on the models in bench-suite.json and writes the medians as JSON (and,
// with --markdown, a table): Java TLC on one worker and on every core, tla-ts under Node, tla-rs, and
// Prove It as its compiled binary and under Bun and Node. Every run is a fresh process, so wall time
// includes startup; CPU time is the user and system time of the process and its children, which a
// loaded machine stretches less than wall time. The checkers take turns in each round, so a burst
// of load spreads over all of them.
//
// Each checker's verdict and distinct states, and its depth and generated states where it counts
// them as TLC does, must match TLC's on one worker; a checker that disagrees, fails or times out on a model
// is reported as such, takes no further runs there and is left out of the speedups. TLC's recording
// in expected.json stands in where TLC fails. Only Prove It failing or disagreeing, or a model with
// nothing to check against, makes the run fail.
//
// Usage: bun scripts/bench-suite.ts [--runs 3] [--filter text] [--checkers tlc,tlc-auto,...]
//        [--timeout seconds] [--out path] [--markdown path] [--suite bench-liveness.json]
// TLA2TOOLS_JAR names tla2tools.jar, TLA_TS_CLI tla-ts's dist/cli.js and TLA_RS_BIN tla-rs's tla
// binary, and PROVE_IT_BASE_BINARY another build's dist/prove-it (prove-it-base); the Prove It binary
// is dist/prove-it (bun run build:binary), and the one Bun compiled ahead of time dist/prove-it-aot
// (build-binary.ts --aot, prove-it-aot). prove-it-rust, prove-it-rust-aot and prove-it-base-rust run
// those binaries with PROVE_IT_ENGINE_BACKEND=rust, where the binary embeds the native engine
// (scripts/platform-packages.ts build, before build-binary.ts). native and native-auto run the
// native binary (cargo build --release -p prove-it-cli in native) on one worker and on every core,
// and native-base PROVE_IT_BASE_NATIVE, another build of it, on one worker. A checker whose file is
// missing is left out.

import { spawnSync } from "node:child_process";
import {
  appendFileSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  rmSync,
  statSync,
  symlinkSync,
  writeFileSync,
} from "node:fs";
import { availableParallelism, cpus, loadavg, release, tmpdir, totalmem } from "node:os";
import { dirname, join } from "node:path";

import { ADDON_FILE } from "../src/engine/native";
import { EXPECTED_PATH, getOption, LIBRARY_PATH, linkLibraryModules } from "./corpora";

interface SuiteModel {
  id: string;
  directory: string;
  spec: string;
  config: string;
  style: string;
  isUsingLibrary?: boolean;
  // TLC's result on a model outside the conformance corpora, which expected.json doesn't hold.
  expected?: ExpectedResult;
}

interface Outcome {
  // "success", "deadlock", "invariant <name>", "temporal <name>", "action property <name>", or
  // "error" and "timeout", which carry no counts.
  verdict: string;
  // Why a checker failed, when it says.
  message?: string;
  generatedStates?: number;
  distinctStates?: number;
  depth?: number;
}

interface Checker {
  name: string;
  getCommand: (model: SuiteModel, metadataDirectory: string) => string[];
  // The directory the checker runs in, when it isn't the model's.
  getDirectory?: (model: SuiteModel) => string;
  parse: (stdout: string, stderr: string) => Outcome;
  // What the checker's runs set in the environment besides it.
  environment?: Record<string, string>;
  // tla-rs counts transitions where TLC counts generated states, which differ by the initial states.
  isCountingGenerated: boolean;
  // TLC on several workers can report a depth past the search's, as its workers don't keep to levels.
  isDepthExact: boolean;
}

interface Measurement extends Outcome {
  wallMilliseconds: number;
  cpuMilliseconds: number;
  maxRssMegabytes: number;
  exitCode: number | null;
}

interface ExpectedResult {
  id: string;
  status?: string;
  generatedStates?: number;
  distinctStates?: number;
  depth?: number;
  tlcMilliseconds?: number;
}

type Verdict = "agrees" | "disagrees" | "unchecked" | "fails" | "times out";

const PACKAGE_DIRECTORY = join(import.meta.dirname, "..");
const CLI_PATH = join(PACKAGE_DIRECTORY, "dist/cli.js");
const BINARY_PATH = join(PACKAGE_DIRECTORY, "dist/prove-it");
const AOT_BINARY_PATH = join(PACKAGE_DIRECTORY, "dist/prove-it-aot");
// PROVE_IT_NATIVE names another native binary, such as a build with symbols for perf.
const NATIVE_PATH =
  process.env.PROVE_IT_NATIVE ?? join(PACKAGE_DIRECTORY, "native/target/release/prove-it");
// build-binary.ts embeds the native engine from beside the binary, when it was built for this
// platform.
const getAddonPath = (binaryPath: string) => join(dirname(binaryPath), "embedded", ADDON_FILE);
const RUST_BACKEND = { PROVE_IT_ENGINE_BACKEND: "rust" };
// --suite names another list of models beside this script, such as bench-liveness.json.
const MODELS: SuiteModel[] = JSON.parse(
  readFileSync(join(import.meta.dirname, getOption("--suite") ?? "bench-suite.json"), "utf8"),
);
const runs = Number(getOption("--runs") ?? 3);
const filter = getOption("--filter");
// No deadline unless --timeout asks for one.
const timeoutOption = getOption("--timeout");
const timeoutSeconds = timeoutOption === undefined ? undefined : Number(timeoutOption);
const outPath = getOption("--out") ?? join(PACKAGE_DIRECTORY, ".bench-suite.json");
const markdownPath = getOption("--markdown");
const jarPath = process.env.TLA2TOOLS_JAR ?? "";
const tlaTsPath = process.env.TLA_TS_CLI ?? "";
const tlaRsPath = process.env.TLA_RS_BIN ?? "";
// Another build of Prove It's binary, such as main's, to time a change against.
const baseBinaryPath = process.env.PROVE_IT_BASE_BINARY ?? "";
// And that build's ahead-of-time binary.
const baseAotBinaryPath = process.env.PROVE_IT_BASE_AOT_BINARY ?? "";
// And another build's native binary.
const baseNativePath = process.env.PROVE_IT_BASE_NATIVE ?? "";

if (
  !Number.isInteger(runs) ||
  runs < 1 ||
  (timeoutSeconds !== undefined && !(timeoutSeconds > 0))
) {
  console.error("--runs takes a whole number from 1, and --timeout a number of seconds above 0");
  process.exit(1);
}

if (!existsSync(CLI_PATH)) {
  console.error("Build the package first with bun run build");
  process.exit(1);
}

// A model that extends a module of TLAPS or the Community Modules finds it on TLC's library path,
// which tla-ts and Prove It take in the form of a java command line.
const LIBRARY_OPTION = `-DTLA-Library=${LIBRARY_PATH}`;

const getCliArguments = (model: SuiteModel) =>
  model.isUsingLibrary
    ? [LIBRARY_OPTION, "tlc2.TLC", "-config", model.config, model.spec]
    : [model.spec, "-config", model.config];

// The lines that say why a checker failed, or its last ones.
const getFailureLines = (output: string) => {
  const lines = output
    .split("\n")
    .map((line) => line.trim())
    .filter((line) => line !== "" && !line.startsWith("Picked up"));
  const errors = lines.filter((line) => /error|exception|unsupported|not supported/i.test(line));
  return (errors.length > 0 ? errors : lines.slice(-3)).slice(0, 3).join(" | ").slice(0, 300);
};

const readNumber = (text: string | undefined) =>
  text === undefined ? undefined : Number(text.replaceAll(",", ""));

// TLC's messages, which tla-ts and Prove It print as TLC does.
const parseTlcOutput = (stdout: string, stderr: string): Outcome => {
  const output = `${stdout}${stderr}`;
  const statistics = [
    ...output.matchAll(/([\d,]+) states? generated, ([\d,]+) distinct states? found/g),
  ].at(-1);
  const counts = {
    generatedStates: readNumber(statistics?.[1]),
    distinctStates: readNumber(statistics?.[2]),
    depth: readNumber(/The depth of the complete state graph search is (\d+)/.exec(output)?.[1]),
  };
  const violation =
    /Error: Invariant (\S+) is violated/.exec(output) ??
    /Error: Action property (\S+) is violated/.exec(output) ??
    /Error: Temporal properties were violated/.exec(output) ??
    /Error: Temporal property (\S+) was violated/.exec(output) ??
    /Error: Deadlock reached/.exec(output);
  if (output.includes("No error has been found")) return { verdict: "success", ...counts };
  if (violation === null) return { verdict: "error", message: getFailureLines(output) };
  const kind = violation[0].includes("Invariant")
    ? "invariant"
    : violation[0].includes("Action")
      ? "action property"
      : violation[0].includes("Temporal")
        ? "temporal"
        : "deadlock";
  return { verdict: violation[1] ? `${kind} ${violation[1]}` : kind, ...counts };
};

// tla-rs's --json report, which it prints to stdout after a summary of the spec; its progress goes
// to stderr.
const parseTlaRsOutput = (stdout: string, stderr: string): Outcome => {
  const parse = (text: string): Record<string, unknown> | undefined => {
    try {
      return JSON.parse(text);
    } catch {
      return undefined;
    }
  };
  const start = stdout.search(/^\{/m);
  const report = start === -1 ? undefined : parse(stdout.slice(start));
  if (report === undefined)
    return { verdict: "error", message: getFailureLines(`${stdout}${stderr}`) };
  const statistics = (report.stats ?? {}) as Record<string, number | undefined>;
  const counts = {
    generatedStates: statistics.transitions,
    distinctStates: statistics.states_explored,
    depth: statistics.max_depth,
  };
  switch (report.status) {
    case "ok":
    case "success":
    case "passed":
    case "no_violation":
      return { verdict: "success", ...counts };
    case "invariant_violation":
      return { verdict: `invariant ${report.invariant_name}`, ...counts };
    case "deadlock":
      return { verdict: "deadlock", ...counts };
    case "liveness_violation":
      return { verdict: "temporal", ...counts };
    default:
      return { verdict: "error", message: `${report.status}: ${report.error ?? ""}`.slice(0, 300) };
  }
};

// TLC's options, which the native binary takes too: the differential's, so the binary prints what
// TLC prints, without its seed.
const getTlcOptions = (workers: string, model: SuiteModel, metadataDirectory: string) => [
  "-workers",
  workers,
  "-nowarning",
  "-fp",
  "0",
  "-lncheck",
  "final",
  "-noGenerateSpecTE",
  "-metadir",
  metadataDirectory,
  "-config",
  model.config,
  model.spec,
];

const getNativeCommand =
  (binaryPath: string, workers: string) => (model: SuiteModel, metadataDirectory: string) => [
    binaryPath,
    ...(model.isUsingLibrary ? [LIBRARY_OPTION, "tlc2.TLC"] : []),
    ...getTlcOptions(workers, model, metadataDirectory),
  ];

const getTlcCommand = (workers: string) => (model: SuiteModel, metadataDirectory: string) => [
  "java",
  ...(model.isUsingLibrary ? [LIBRARY_OPTION] : []),
  "-XX:+UseParallelGC",
  "-Xmx4g",
  "-cp",
  jarPath,
  "tlc2.TLC",
  ...getTlcOptions(workers, model, metadataDirectory),
];

// tla-ts's own benchmark runs both checkers under Node with this heap.
const getNodeCommand = (cliPath: string) => (model: SuiteModel) => [
  "node",
  "--max-old-space-size=6144",
  cliPath,
  ...getCliArguments(model),
];

const getBunCommand = (model: SuiteModel) => [
  process.execPath,
  CLI_PATH,
  ...getCliArguments(model),
];

// tla-rs reads modules only from the spec's directory, so a model that uses the library runs in a
// directory of links to its own files and the library's.
const TLA_RS_DIRECTORY = mkdtempSync(join(tmpdir(), "prove-it-bench-tla-rs-"));
const linkFiles = (source: string, target: string) =>
  readdirSync(source)
    .filter((name) => statSync(join(source, name)).isFile() && !existsSync(join(target, name)))
    .forEach((name) => symlinkSync(join(source, name), join(target, name)));
const getTlaRsDirectory = (model: SuiteModel) => {
  if (!model.isUsingLibrary) return model.directory;
  const directory = join(TLA_RS_DIRECTORY, model.id.replaceAll(/[^A-Za-z0-9_.-]/g, "_"));
  if (!existsSync(directory)) {
    mkdirSync(directory);
    linkFiles(model.directory, directory);
    linkFiles(LIBRARY_PATH, directory);
  }
  return directory;
};
const getTlaRsCommand = (model: SuiteModel) => [
  tlaRsPath,
  model.spec,
  "--config",
  model.config,
  "--json",
  "--max-states",
  "2000000000",
  "--max-depth",
  "100000000",
];

const TLC_STYLE = { parse: parseTlcOutput, isCountingGenerated: true, isDepthExact: true };
const ALL_CHECKERS: (Checker & { isAvailable: boolean })[] = [
  { name: "tlc", getCommand: getTlcCommand("1"), ...TLC_STYLE, isAvailable: existsSync(jarPath) },
  {
    name: "tlc-auto",
    getCommand: getTlcCommand("auto"),
    ...TLC_STYLE,
    isDepthExact: false,
    isAvailable: existsSync(jarPath),
  },
  {
    name: "tla-ts",
    getCommand: getNodeCommand(tlaTsPath),
    ...TLC_STYLE,
    isAvailable: existsSync(tlaTsPath),
  },
  {
    name: "tla-rs",
    getCommand: getTlaRsCommand,
    getDirectory: getTlaRsDirectory,
    parse: parseTlaRsOutput,
    isCountingGenerated: false,
    isDepthExact: true,
    isAvailable: existsSync(tlaRsPath),
  },
  {
    name: "prove-it",
    getCommand: (model) => [BINARY_PATH, ...getCliArguments(model)],
    ...TLC_STYLE,
    isAvailable: existsSync(BINARY_PATH),
  },
  {
    name: "prove-it-aot",
    getCommand: (model) => [AOT_BINARY_PATH, ...getCliArguments(model)],
    ...TLC_STYLE,
    isAvailable: existsSync(AOT_BINARY_PATH),
  },
  {
    name: "prove-it-rust",
    getCommand: (model) => [BINARY_PATH, ...getCliArguments(model)],
    ...TLC_STYLE,
    environment: RUST_BACKEND,
    isAvailable: existsSync(BINARY_PATH) && existsSync(getAddonPath(BINARY_PATH)),
  },
  {
    name: "prove-it-rust-aot",
    getCommand: (model) => [AOT_BINARY_PATH, ...getCliArguments(model)],
    ...TLC_STYLE,
    environment: RUST_BACKEND,
    isAvailable: existsSync(AOT_BINARY_PATH) && existsSync(getAddonPath(AOT_BINARY_PATH)),
  },
  {
    name: "prove-it-base",
    getCommand: (model) => [baseBinaryPath, ...getCliArguments(model)],
    ...TLC_STYLE,
    isAvailable: baseBinaryPath !== "" && existsSync(baseBinaryPath),
  },
  {
    name: "prove-it-base-rust",
    getCommand: (model) => [baseBinaryPath, ...getCliArguments(model)],
    ...TLC_STYLE,
    environment: RUST_BACKEND,
    isAvailable:
      baseBinaryPath !== "" &&
      existsSync(baseBinaryPath) &&
      existsSync(getAddonPath(baseBinaryPath)),
  },
  {
    name: "prove-it-base-aot",
    getCommand: (model) => [baseAotBinaryPath, ...getCliArguments(model)],
    ...TLC_STYLE,
    isAvailable: baseAotBinaryPath !== "" && existsSync(baseAotBinaryPath),
  },
  {
    name: "native",
    getCommand: getNativeCommand(NATIVE_PATH, "1"),
    ...TLC_STYLE,
    isAvailable: existsSync(NATIVE_PATH),
  },
  {
    name: "native-auto",
    getCommand: getNativeCommand(NATIVE_PATH, "auto"),
    ...TLC_STYLE,
    isDepthExact: false,
    isAvailable: existsSync(NATIVE_PATH),
  },
  {
    name: "native-base",
    getCommand: getNativeCommand(baseNativePath, "1"),
    ...TLC_STYLE,
    isAvailable: baseNativePath !== "" && existsSync(baseNativePath),
  },
  { name: "prove-it-bun", getCommand: getBunCommand, ...TLC_STYLE, isAvailable: true },
  {
    name: "prove-it-node",
    getCommand: getNodeCommand(CLI_PATH),
    ...TLC_STYLE,
    isAvailable: true,
  },
];
const requested = getOption("--checkers")?.split(",");
const unknown = requested?.filter((name) => !ALL_CHECKERS.some((checker) => checker.name === name));
if (unknown !== undefined && unknown.length > 0) {
  console.error(`Unknown checkers: ${unknown.join(", ")}`);
  process.exit(1);
}
// A checker asked for by name must run; with no --checkers, the ones missing are left out.
const missing = ALL_CHECKERS.filter(
  (checker) =>
    !checker.isAvailable && (requested === undefined || requested.includes(checker.name)),
);
missing.forEach((checker) =>
  console.warn(
    `Leaving out ${checker.name}: set TLA2TOOLS_JAR, TLA_TS_CLI, TLA_RS_BIN, PROVE_IT_BASE_BINARY, PROVE_IT_BASE_AOT_BINARY and PROVE_IT_BASE_NATIVE, and build dist/prove-it and dist/prove-it-aot, with the native engine for the -rust ones, and the native binary`,
  ),
);
if (requested !== undefined && missing.length > 0) process.exit(1);
const checkers = ALL_CHECKERS.filter(
  (checker) => checker.isAvailable && (requested === undefined || requested.includes(checker.name)),
);
// The speedups are over this Prove It, and the counts are checked against TLC on one worker, or
// against TLC's recording in expected.json when TLC isn't run.
const baseline = ["native", "prove-it", "prove-it-bun", "prove-it-node", "prove-it-rust"].find(
  (name) => checkers.some((checker) => checker.name === name),
);
const isProveIt = (name: string) => name.startsWith("prove-it") || name.startsWith("native");

// The engine is on, on its default backend, unless a checker says otherwise, so the runs don't
// inherit a setting from the shell.
const environment = Object.fromEntries(
  Object.entries(process.env).filter(
    (entry) => entry[0] !== "PROVE_IT_ENGINE" && entry[0] !== "PROVE_IT_ENGINE_BACKEND",
  ),
);

const run = (command: string[], cwd: string, settings: Record<string, string> = {}) => {
  const result = Bun.spawnSync({
    cmd: command,
    cwd,
    env: { ...environment, ...settings },
    stdout: "pipe",
    stderr: "pipe",
    ...(timeoutSeconds === undefined
      ? {}
      : { timeout: timeoutSeconds * 1000, killSignal: "SIGKILL" }),
  });
  return {
    result,
    stdout: result.stdout.toString(),
    stderr: result.stderr.toString(),
    output: `${result.stdout.toString()}${result.stderr.toString()}`,
  };
};

const measure = (checker: Checker, model: SuiteModel): Measurement => {
  const metadataDirectory = mkdtempSync(join(tmpdir(), "prove-it-bench-"));
  // Built before the clock starts, so the first run doesn't pay for a working directory.
  const command = checker.getCommand(model, metadataDirectory);
  const directory = checker.getDirectory?.(model) ?? model.directory;
  const startedAt = performance.now();
  let execution: ReturnType<typeof run>;
  try {
    execution = run(command, directory, checker.environment);
  } catch (error) {
    // A checker that can't start fails its cell rather than the whole benchmark.
    rmSync(metadataDirectory, { recursive: true, force: true });
    return {
      verdict: "error",
      message: `could not start: ${error instanceof Error ? error.message : String(error)}`,
      wallMilliseconds: 0,
      cpuMilliseconds: 0,
      maxRssMegabytes: 0,
      exitCode: null,
    };
  }
  const wallMilliseconds = performance.now() - startedAt;
  rmSync(metadataDirectory, { recursive: true, force: true });
  const isTimedOut = execution.result.exitedDueToTimeout === true;
  const parsed: Outcome = isTimedOut
    ? { verdict: "timeout", message: `timed out after ${timeoutSeconds} s` }
    : checker.parse(execution.stdout, execution.stderr);
  // A process the kernel stopped, such as for running out of memory, reports no error of its own.
  const exitCode = execution.result.exitCode;
  // Success only counts from a process that also exited cleanly; a violation exits non-zero on purpose.
  const checked: Outcome =
    parsed.verdict === "success" && exitCode !== 0
      ? {
          verdict: "error",
          message: `reported success, then exited with ${exitCode ?? execution.result.signalCode}`,
        }
      : parsed;
  const outcome =
    checked.verdict === "error" && execution.result.signalCode
      ? {
          ...checked,
          message: `stopped by ${execution.result.signalCode} at ${Math.round(execution.result.resourceUsage.maxRSS / 1024 / 1024)} MB resident`,
        }
      : checked;
  return {
    ...outcome,
    wallMilliseconds,
    cpuMilliseconds: Number(execution.result.resourceUsage.cpuTime.total) / 1000,
    maxRssMegabytes: execution.result.resourceUsage.maxRSS / 1024 / 1024,
    exitCode,
  };
};

const getMedian = (values: number[]) => {
  const sorted = [...values].sort((left, right) => left - right);
  const middle = Math.floor(sorted.length / 2);
  return sorted.length % 2 === 1 ? sorted[middle] : (sorted[middle - 1] + sorted[middle]) / 2;
};

const getVersion = (command: string[]) => {
  const result = spawnSync(command[0], command.slice(1), { encoding: "utf8" });
  return `${result.stdout}${result.stderr}`
    .split("\n")
    .find((line) => line.trim() !== "" && !line.startsWith("Picked up"))
    ?.trim();
};

// The commit a checkout is at, and +local when its files differ from it, as they do in a run of
// local changes that depot ci run applies as a patch.
const getCommit = (path: string) => {
  const git = (args: string[]) =>
    spawnSync("git", ["-C", path, ...args], { encoding: "utf8" }).stdout.trim();
  const commit = git(["rev-parse", "--short", "HEAD"]);
  return git(["status", "--porcelain", "--untracked-files=no"]) === "" ? commit : `${commit}+local`;
};

const getPackageVersion = (cliPath: string) => {
  const manifest = join(dirname(cliPath), "..", "package.json");
  return existsSync(manifest) ? JSON.parse(readFileSync(manifest, "utf8")).version : undefined;
};

const expectedById = new Map(
  (JSON.parse(readFileSync(EXPECTED_PATH, "utf8")) as ExpectedResult[]).map((result) => [
    result.id,
    result,
  ]),
);

const machine = {
  date: new Date().toISOString(),
  cores: availableParallelism(),
  cpu: cpus()[0]?.model,
  memoryGigabytes: Math.round(totalmem() / 1024 ** 3),
  kernel: release(),
  bun: Bun.version,
  node: getVersion(["node", "--version"]),
  java: jarPath ? getVersion(["java", "-version"]) : undefined,
  // A jar built without its git history names its commit through TLC_COMMIT.
  tlc:
    jarPath &&
    /TLC2 Version [^\n]*/
      .exec(run(["java", "-cp", jarPath, "tlc2.TLC"], tmpdir()).output)?.[0]
      .replace(/\$\{git\.shortRevision\}/, process.env.TLC_COMMIT?.slice(0, 7) ?? "?"),
  tlaTs: tlaTsPath ? getPackageVersion(tlaTsPath) : undefined,
  tlaRs: tlaRsPath ? getVersion([tlaRsPath, "--version"]) : undefined,
  proveIt: getCommit(PACKAGE_DIRECTORY),
  // The commit of the checkout PROVE_IT_BASE_BINARY was built in.
  proveItBase: baseBinaryPath ? getCommit(dirname(baseBinaryPath)) : undefined,
  timeoutSeconds,
  loadAverageAtStart: loadavg(),
};
console.log(machine);

if (MODELS.some((model) => model.isUsingLibrary)) linkLibraryModules();

// A config named by a path, such as a scaled model's in benchmarks/liveness, is the package's.
const models = MODELS.filter((model) => filter === undefined || model.id.includes(filter)).map(
  (model) => ({
    ...model,
    directory: join(PACKAGE_DIRECTORY, model.directory),
    config: model.config.includes("/") ? join(PACKAGE_DIRECTORY, model.config) : model.config,
  }),
);

const describeOutcome = (outcome: Outcome | undefined, isCountingGenerated = true) =>
  outcome === undefined
    ? "?"
    : `${outcome.verdict} ${isCountingGenerated ? (outcome.generatedStates ?? "?") : "-"}/${outcome.distinctStates ?? "?"} depth ${outcome.depth ?? "?"}`;

const VERDICT_KINDS = [
  "success",
  "deadlock",
  "temporal",
  "invariant",
  "action property",
  "assumption",
];

// "invariant TypeOK" is the kind "invariant" and the name "TypeOK"; a recording gives the kind alone.
const splitVerdict = (verdict: string) => {
  const kind = VERDICT_KINDS.find((each) => verdict === each || verdict.startsWith(`${each} `));
  return { kind: kind ?? verdict, name: kind === undefined ? "" : verdict.slice(kind.length + 1) };
};

const isSameVerdict = (left: string, right: string) => {
  const [first, second] = [splitVerdict(left), splitVerdict(right)];
  return first.kind === second.kind && (!first.name || !second.name || first.name === second.name);
};

const isMatching = (outcome: Outcome, reference: Outcome | undefined, checker: Checker) =>
  reference !== undefined &&
  isSameVerdict(outcome.verdict, reference.verdict) &&
  outcome.distinctStates === reference.distinctStates &&
  (!checker.isDepthExact ||
    outcome.depth === undefined ||
    reference.depth === undefined ||
    outcome.depth === reference.depth) &&
  (!checker.isCountingGenerated || outcome.generatedStates === reference.generatedStates);

// expected.json's statuses, in the words the parsers use.
const RECORDED_VERDICTS: Record<string, string> = {
  success: "success",
  deadlock: "deadlock",
  "invariant-violation": "invariant",
  "liveness-violation": "temporal",
  "property-violation": "action property",
  "assumption-violation": "assumption",
};

const isTlcRequested = checkers.some((checker) => checker.name === "tlc");

const results = models.map((model, index) => {
  const expected = expectedById.get(model.id) ?? model.expected;
  const recorded: Outcome | undefined =
    expected?.distinctStates === undefined
      ? undefined
      : {
          verdict: RECORDED_VERDICTS[expected.status ?? ""] ?? expected.status ?? "?",
          generatedStates: expected.generatedStates,
          distinctStates: expected.distinctStates,
          depth: expected.depth,
        };
  // One round runs every checker still in the race once, so a burst of load lands on all of them.
  const measurementsByChecker = new Map<string, Measurement[]>(
    checkers.map((checker) => [checker.name, []]),
  );
  const stopped = new Set<string>();
  let reference = recorded;
  for (let round = 0; round < runs; round++) {
    checkers
      .filter((checker) => !stopped.has(checker.name))
      .forEach((checker) => {
        const measurement = measure(checker, model);
        measurementsByChecker.get(checker.name)?.push(measurement);
        if (checker.name === "tlc" && round === 0 && measurement.verdict !== "error") {
          reference = measurement.verdict === "timeout" ? reference : measurement;
        }
        if (
          measurement.verdict === "error" ||
          measurement.verdict === "timeout" ||
          (checker.name !== "tlc" &&
            reference !== undefined &&
            !isMatching(measurement, reference, checker))
        ) {
          stopped.add(checker.name);
        }
      });
  }
  // The baseline Prove It's engine, as it ran: the last line it reports says what it did. The
  // native binary has one engine and reports none.
  const prober = checkers.find((checker) => checker.name === baseline);
  const engineLine =
    baseline === "native"
      ? undefined
      : run(prober?.getCommand(model, tmpdir()) ?? getBunCommand(model), model.directory, {
          ...prober?.environment,
          PROVE_IT_ENGINE: "debug",
        })
          .output.match(/^\[engine\] .*$/gm)
          ?.at(-1);
  const measurements = Object.fromEntries(
    checkers.map((checker) => {
      const all = measurementsByChecker.get(checker.name) ?? [];
      const failure = all.find(
        (measurement) => measurement.verdict === "error" || measurement.verdict === "timeout",
      );
      const verdict: Verdict =
        failure?.verdict === "timeout"
          ? "times out"
          : failure !== undefined
            ? "fails"
            : reference === undefined
              ? "unchecked"
              : all.every((measurement) => isMatching(measurement, reference, checker))
                ? "agrees"
                : "disagrees";
      // The run that disagrees, which stopped the checker, explains the cell.
      const shown =
        all.find(
          (measurement) =>
            measurement.verdict !== "timeout" && !isMatching(measurement, reference, checker),
        ) ??
        all.find((measurement) => measurement.verdict !== "timeout") ??
        all[0];
      const walls = all.map((measurement) => measurement.wallMilliseconds);
      return [
        checker.name,
        {
          verdict,
          outcome: describeOutcome(shown, checker.isCountingGenerated),
          message: failure?.message,
          wallMilliseconds: Math.round(getMedian(walls)),
          minimumWallMilliseconds: Math.round(Math.min(...walls)),
          maximumWallMilliseconds: Math.round(Math.max(...walls)),
          cpuMilliseconds: Math.round(
            getMedian(all.map((measurement) => measurement.cpuMilliseconds)),
          ),
          maxRssMegabytes: Math.round(
            getMedian(all.map((measurement) => measurement.maxRssMegabytes)),
          ),
          runs: all,
        },
      ];
    }),
  );
  // TLC failing leaves its recording in expected.json to check Prove It against.
  const problems = [
    // Without TLC asked for, a model with no recording is only unchecked.
    ...(reference === undefined && isTlcRequested
      ? ["no run or recording of TLC to check against"]
      : []),
    ...checkers
      .filter(
        (checker) =>
          isProveIt(checker.name) &&
          measurements[checker.name].verdict !== "agrees" &&
          measurements[checker.name].verdict !== "unchecked",
      )
      .map((checker) => `${checker.name} ${measurements[checker.name].verdict}`),
  ];
  console.log(
    `[${index + 1}/${models.length}] ${model.id}  reference ${describeOutcome(reference)}\n  ${checkers
      .map(
        (checker) =>
          `${checker.name} ${measurements[checker.name].wallMilliseconds}ms/${measurements[checker.name].cpuMilliseconds}ms cpu ${measurements[checker.name].verdict}${measurements[checker.name].verdict === "agrees" ? "" : ` (${measurements[checker.name].message ?? measurements[checker.name].outcome})`}`,
      )
      .join("\n  ")}\n  ${engineLine ?? "[engine] no report"}`,
  );
  if (problems.length > 0) console.error(`!!! ${model.id}: ${problems.join(", ")}`);
  return {
    id: model.id,
    style: model.style,
    expectedTlcMilliseconds: expected?.tlcMilliseconds,
    reference: reference && describeOutcome(reference),
    distinctStates: reference?.distinctStates,
    problems,
    engine: engineLine?.replace(/^\[engine\] /, ""),
    measurements,
  };
});

rmSync(TLA_RS_DIRECTORY, { recursive: true, force: true });
writeFileSync(
  outPath,
  `${JSON.stringify({ machine: { ...machine, loadAverageAtEnd: loadavg() }, runs, baseline, checkers: checkers.map((checker) => checker.name), results }, null, 2)}\n`,
);

type Result = (typeof results)[number];
const formatSeconds = (milliseconds: number | undefined) =>
  milliseconds === undefined ? "-" : (milliseconds / 1000).toFixed(2);
const getRatio = (
  result: Result,
  numerator: string,
  metric: "wallMilliseconds" | "cpuMilliseconds",
) => {
  const top = result.measurements[numerator];
  const bottom = baseline === undefined ? undefined : result.measurements[baseline];
  // Two times compare when both checkers agree with TLC, or when no TLC result checks either.
  const isComparable =
    top !== undefined &&
    bottom !== undefined &&
    (top.verdict === "agrees" || top.verdict === "unchecked") &&
    top.verdict === bottom.verdict;
  return isComparable ? top[metric] / bottom[metric] : undefined;
};
const formatRatio = (ratio: number | undefined) =>
  ratio === undefined ? "-" : `${ratio.toFixed(2)}x`;
const getGeometricMean = (ratios: (number | undefined)[]) => {
  const defined = ratios.filter((ratio) => ratio !== undefined);
  return defined.length === 0
    ? undefined
    : Math.exp(defined.reduce((sum, ratio) => sum + Math.log(ratio), 0) / defined.length);
};
const getEngineLabel = (engine: string | undefined) =>
  engine === undefined
    ? "?"
    : engine.startsWith("checked")
      ? "ran"
      : engine.startsWith("found")
        ? "searched"
        : engine.replace(/ after \d+ ms/, "").split(":")[0];
const formatCell = (result: Result, name: string) => {
  const measurement = result.measurements[name];
  const time = `${formatSeconds(measurement.wallMilliseconds)} (${formatSeconds(measurement.cpuMilliseconds)})`;
  return measurement.verdict === "agrees"
    ? time
    : measurement.verdict === "unchecked"
      ? `${time} unchecked`
      : measurement.verdict;
};
const competitors = checkers.filter((checker) => checker.name !== baseline);

console.log(
  `\nMedian of ${runs} runs; wall seconds (CPU seconds); speedups over ${baseline ?? "nothing"}`,
);
console.table(
  results.map((result) => ({
    model: result.id.length > 40 ? `…${result.id.slice(-39)}` : result.id,
    distinct: result.distinctStates,
    ...Object.fromEntries(
      checkers.map((checker) => [checker.name, formatCell(result, checker.name)]),
    ),
    engine: getEngineLabel(result.engine),
  })),
);
const summary = competitors.map((checker) => ({
  name: checker.name,
  wall: getGeometricMean(
    results.map((result) => getRatio(result, checker.name, "wallMilliseconds")),
  ),
  cpu: getGeometricMean(results.map((result) => getRatio(result, checker.name, "cpuMilliseconds"))),
  agreeing: results.filter((result) => result.measurements[checker.name].verdict === "agrees")
    .length,
}));
console.log(`Geometric mean speedup of ${baseline} (wall, CPU) on the models both finish:`);
summary.forEach((row) =>
  console.log(
    `  over ${row.name.padEnd(13)} ${formatRatio(row.wall)}, ${formatRatio(row.cpu)} (${row.agreeing}/${results.length} models)`,
  ),
);
console.log(
  `Load average at start ${machine.loadAverageAtStart.map((load) => load.toFixed(2)).join(" ")}, at end ${loadavg()
    .map((load) => load.toFixed(2))
    .join(" ")}`,
);
console.log(`Wrote ${outPath}`);

if (markdownPath !== undefined) {
  const row = (cells: (string | number | undefined)[]) =>
    `| ${cells.map((cell) => String(cell ?? "-").replaceAll("|", "\\|")).join(" | ")} |`;
  const spread = (result: Result, name: string) => {
    const measurement = result.measurements[name];
    const wall =
      measurement.runs.length > 1
        ? ` ${formatSeconds(measurement.minimumWallMilliseconds)}–${formatSeconds(measurement.maximumWallMilliseconds)}`
        : "";
    return measurement.verdict === "agrees" ? `${wall}, ${measurement.maxRssMegabytes} MB` : "";
  };
  const lines = [
    "## Checker benchmark",
    "",
    `Median wall seconds of ${runs} interleaved runs (CPU seconds; min–max wall, median peak resident memory), startup included, on ${machine.cores} cores (${machine.cpu}, ${machine.memoryGigabytes} GB). Speedups are over \`${baseline}\` at ${machine.proveIt}, on the models where both agree with TLC on one worker. A checker that fails${timeoutSeconds === undefined ? "" : `, times out (${timeoutSeconds} s)`} or disagrees with TLC on a model says so instead of a time and takes no more runs there.`,
    "",
    row(["Checker", "Version", `${baseline} is faster (wall)`, "(CPU)", "Models agreeing"]),
    row(["---", "---", "---:", "---:", "---:"]),
    row([
      baseline,
      machine.proveIt,
      "",
      "",
      `${results.filter((result) => baseline !== undefined && result.measurements[baseline].verdict === "agrees").length}/${results.length}`,
    ]),
    ...summary.map((entry) =>
      row([
        entry.name,
        entry.name.startsWith("tlc")
          ? machine.tlc
          : entry.name === "tla-ts"
            ? machine.tlaTs
            : entry.name === "tla-rs"
              ? machine.tlaRs
              : entry.name.startsWith("prove-it-base")
                ? machine.proveItBase
                : machine.proveIt,
        formatRatio(entry.wall),
        formatRatio(entry.cpu),
        `${entry.agreeing}/${results.length}`,
      ]),
    ),
    "",
    row(["Model", "Distinct states", ...checkers.map((checker) => checker.name), "Engine"]),
    row(["---", "---:", ...checkers.map(() => "---:"), "---"]),
    ...results.map((result) =>
      row([
        result.id,
        result.distinctStates?.toLocaleString("en-US"),
        ...checkers.map(
          (checker) => `${formatCell(result, checker.name)}${spread(result, checker.name)}`,
        ),
        getEngineLabel(result.engine),
      ]),
    ),
    "",
    ...results.flatMap((result) =>
      checkers
        .filter((checker) => result.measurements[checker.name].verdict !== "agrees")
        .map(
          (checker) =>
            `- ${result.id}, ${checker.name} ${result.measurements[checker.name].verdict}: ${result.measurements[checker.name].message ?? (result.reference === undefined ? `${result.measurements[checker.name].outcome}, with no TLC result to check against` : `${result.measurements[checker.name].outcome}, where TLC gives ${result.reference}`)}`,
        ),
    ),
    "",
    `Machine: ${machine.kernel}, Bun ${machine.bun}, Node ${machine.node}, ${machine.java ?? "no Java"}; load average ${machine.loadAverageAtStart.map((load) => load.toFixed(2)).join(" ")} at start, ${loadavg()
      .map((load) => load.toFixed(2))
      .join(" ")} at end.`,
    "",
  ];
  appendFileSync(markdownPath, lines.join("\n"));
}

const failing = results.filter((result) => result.problems.length > 0);
if (failing.length > 0) {
  console.error(
    `!!! Prove It failed or disagreed, or nothing checked it, on ${failing.map((result) => result.id).join(", ")}`,
  );
}
process.exit(failing.length > 0 ? 1 : 0);

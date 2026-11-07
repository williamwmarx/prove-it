// Times Java TLC (one worker and all cores), the original tla-ts under Node, and Prove It under Bun
// and Node on the models in bench-suite.json, and writes the medians as JSON. Every run is a fresh
// process, so wall time includes startup; CPU time is the user and system time of the process and
// its children, which a loaded machine stretches less than wall time. The checkers take turns in
// each round, so a burst of load spreads over all of them.
// Usage: bun scripts/bench-suite.ts [--runs 3] [--filter text] [--checkers tlc,tlc-auto,...]
//        [--out path]
// TLA2TOOLS_JAR names tla2tools.jar and TLA_TS_CLI names tla-ts's dist/cli.js; a checker whose
// file is missing is left out.

import { spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { availableParallelism, cpus, loadavg, release, tmpdir, totalmem } from "node:os";
import { join } from "node:path";

import { EXPECTED_PATH, getOption, LIBRARY_PATH, linkLibraryModules } from "./corpora";

interface SuiteModel {
  id: string;
  directory: string;
  spec: string;
  config: string;
  style: string;
  isUsingLibrary?: boolean;
}

interface Checker {
  name: string;
  getCommand: (model: SuiteModel, metadataDirectory: string) => string[];
}

interface Measurement {
  wallMilliseconds: number;
  cpuMilliseconds: number;
  maxRssMegabytes: number;
  exitCode: number;
  generatedStates: number | undefined;
  distinctStates: number | undefined;
}

interface ExpectedResult {
  id: string;
  generatedStates?: number;
  distinctStates?: number;
  tlcMilliseconds: number;
}

const PACKAGE_DIRECTORY = join(import.meta.dirname, "..");
const CLI_PATH = join(PACKAGE_DIRECTORY, "dist/cli.js");
const MODELS: SuiteModel[] = JSON.parse(
  readFileSync(join(import.meta.dirname, "bench-suite.json"), "utf8"),
);
const runs = Number(getOption("--runs") ?? 3);
const filter = getOption("--filter");
const outPath = getOption("--out") ?? join(PACKAGE_DIRECTORY, ".bench-suite.json");
const jarPath = process.env.TLA2TOOLS_JAR ?? "";
const tlaTsPath = process.env.TLA_TS_CLI ?? "";

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

const getTlcCommand = (workers: string) => (model: SuiteModel, metadataDirectory: string) => [
  "java",
  ...(model.isUsingLibrary ? [LIBRARY_OPTION] : []),
  "-XX:+UseParallelGC",
  "-Xmx4g",
  "-cp",
  jarPath,
  "tlc2.TLC",
  "-workers",
  workers,
  "-nowarning",
  "-noGenerateSpecTE",
  "-metadir",
  metadataDirectory,
  "-config",
  model.config,
  model.spec,
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

const ALL_CHECKERS: (Checker & { isAvailable: boolean })[] = [
  { name: "tlc", getCommand: getTlcCommand("1"), isAvailable: existsSync(jarPath) },
  { name: "tlc-auto", getCommand: getTlcCommand("auto"), isAvailable: existsSync(jarPath) },
  { name: "tla-ts", getCommand: getNodeCommand(tlaTsPath), isAvailable: existsSync(tlaTsPath) },
  {
    name: "prove-it-bun",
    getCommand: getBunCommand,
    isAvailable: true,
  },
  { name: "prove-it-node", getCommand: getNodeCommand(CLI_PATH), isAvailable: true },
];
const requested = getOption("--checkers")?.split(",");
ALL_CHECKERS.filter((checker) => !checker.isAvailable).forEach((checker) =>
  console.warn(`Leaving out ${checker.name}: set TLA2TOOLS_JAR and TLA_TS_CLI to run it`),
);
const checkers = ALL_CHECKERS.filter(
  (checker) => checker.isAvailable && (requested === undefined || requested.includes(checker.name)),
);

// The engine is on unless this says otherwise, so the runs don't inherit a setting from the shell.
const environment = Object.fromEntries(
  Object.entries(process.env).filter((entry) => entry[0] !== "PROVE_IT_ENGINE"),
);

const run = (command: string[], cwd: string, engineSetting?: string) => {
  const result = Bun.spawnSync({
    cmd: command,
    cwd,
    env:
      engineSetting === undefined
        ? environment
        : { ...environment, PROVE_IT_ENGINE: engineSetting },
    stdout: "pipe",
    stderr: "pipe",
  });
  return { result, output: `${result.stdout.toString()}${result.stderr.toString()}` };
};

const measure = (checker: Checker, model: SuiteModel): Measurement => {
  const metadataDirectory = mkdtempSync(join(tmpdir(), "prove-it-bench-"));
  const startedAt = performance.now();
  const execution = run(checker.getCommand(model, metadataDirectory), model.directory);
  const wallMilliseconds = performance.now() - startedAt;
  rmSync(metadataDirectory, { recursive: true, force: true });
  const statistics = [
    ...execution.output.matchAll(/(\d+) states generated, (\d+) distinct states found/g),
  ].at(-1);
  return {
    wallMilliseconds,
    cpuMilliseconds: Number(execution.result.resourceUsage.cpuTime.total) / 1000,
    maxRssMegabytes: execution.result.resourceUsage.maxRSS / 1024 / 1024,
    exitCode: execution.result.exitCode,
    generatedStates: statistics ? Number(statistics[1]) : undefined,
    distinctStates: statistics ? Number(statistics[2]) : undefined,
  };
};

const getMedian = (values: number[]) =>
  [...values].sort((left, right) => left - right)[Math.floor(values.length / 2)];

const getVersion = (command: string[]) => {
  const result = spawnSync(command[0], command.slice(1), { encoding: "utf8" });
  return `${result.stdout}${result.stderr}`
    .split("\n")
    .find((line) => line.trim() !== "" && !line.startsWith("Picked up"))
    ?.trim();
};

const getCommit = (path: string) =>
  spawnSync("git", ["-C", path, "rev-parse", "--short", "HEAD"], {
    encoding: "utf8",
  }).stdout.trim();

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
  java: getVersion(["java", "-version"]),
  tlc:
    jarPath &&
    /TLC2 Version [^\n]*/.exec(run(["java", "-cp", jarPath, "tlc2.TLC"], tmpdir()).output)?.[0],
  tlaTs: tlaTsPath && getCommit(join(tlaTsPath, "..")),
  proveIt: getCommit(PACKAGE_DIRECTORY),
  loadAverageAtStart: loadavg(),
};
console.log(machine);

if (MODELS.some((model) => model.isUsingLibrary)) linkLibraryModules();

const models = MODELS.filter((model) => filter === undefined || model.id.includes(filter)).map(
  (model) => ({ ...model, directory: join(PACKAGE_DIRECTORY, model.directory) }),
);

const results = models.map((model, index) => {
  // One round runs every checker once, so a burst of load lands on all of them.
  const rounds = Array.from({ length: runs }, () =>
    checkers.map((checker) => measure(checker, model)),
  );
  const engineLine = /^\[engine\] .*$/m.exec(
    run(getBunCommand(model), model.directory, "debug").output,
  )?.[0];
  const expected = expectedById.get(model.id);
  const measurements = Object.fromEntries(
    checkers.map((checker, checkerIndex) => {
      const all = rounds.map((round) => round[checkerIndex]);
      return [
        checker.name,
        {
          wallMilliseconds: Math.round(
            getMedian(all.map((measurement) => measurement.wallMilliseconds)),
          ),
          cpuMilliseconds: Math.round(
            getMedian(all.map((measurement) => measurement.cpuMilliseconds)),
          ),
          maxRssMegabytes: Math.round(
            getMedian(all.map((measurement) => measurement.maxRssMegabytes)),
          ),
          generatedStates: all[0].generatedStates,
          distinctStates: all[0].distinctStates,
          runs: all,
        },
      ];
    }),
  );
  // Every run of every checker, and TLC's recording, must count the same states.
  const counts = [
    ...(expected?.distinctStates === undefined
      ? []
      : [`expected ${expected.generatedStates}/${expected.distinctStates}`]),
    ...checkers.flatMap((checker, checkerIndex) =>
      rounds.map(
        (round) =>
          `${checker.name} ${round[checkerIndex].generatedStates}/${round[checkerIndex].distinctStates}`,
      ),
    ),
  ];
  const isAgreeing = new Set(counts.map((count) => count.split(" ")[1])).size === 1;
  const failed = checkers.filter((_checker, checkerIndex) =>
    rounds.some((round) => round[checkerIndex].exitCode !== 0),
  );
  console.log(
    `[${index + 1}/${models.length}] ${model.id}  ${checkers.map((checker) => `${checker.name} ${measurements[checker.name].wallMilliseconds}ms/${measurements[checker.name].cpuMilliseconds}ms cpu`).join(", ")}  ${engineLine ?? "[engine] no report"}`,
  );
  if (!isAgreeing)
    console.error(`!!! STATE COUNTS DISAGREE on ${model.id}: ${[...new Set(counts)].join(", ")}`);
  if (failed.length > 0)
    console.error(
      `!!! NONZERO EXIT on ${model.id}: ${failed.map((checker) => checker.name).join(", ")}`,
    );
  return {
    id: model.id,
    style: model.style,
    expectedTlcMilliseconds: expected?.tlcMilliseconds,
    generatedStates: measurements[checkers[0].name]?.generatedStates,
    distinctStates: measurements[checkers[0].name]?.distinctStates,
    isAgreeing,
    counts: [...new Set(counts)],
    failed: failed.map((checker) => checker.name),
    engine: engineLine?.replace(/^\[engine\] /, ""),
    measurements,
  };
});

writeFileSync(
  outPath,
  `${JSON.stringify({ machine: { ...machine, loadAverageAtEnd: loadavg() }, runs, checkers: checkers.map((checker) => checker.name), results }, null, 2)}\n`,
);

const formatSeconds = (milliseconds: number | undefined) =>
  milliseconds === undefined ? "-" : (milliseconds / 1000).toFixed(2);
const getRatio = (
  result: (typeof results)[number],
  numerator: string,
  denominator: string,
  metric: "wallMilliseconds" | "cpuMilliseconds",
) => {
  const top = result.measurements[numerator]?.[metric];
  const bottom = result.measurements[denominator]?.[metric];
  return top === undefined || bottom === undefined ? undefined : top / bottom;
};
const formatRatio = (ratio: number | undefined) =>
  ratio === undefined ? "-" : `${ratio.toFixed(2)}x`;

const getEngineLabel = (engine: string | undefined) =>
  engine === undefined
    ? "?"
    : engine.startsWith("checked")
      ? "ran"
      : engine.replace(/ after \d+ ms/, "").split(":")[0];

console.log(`\nMedian of ${runs} runs; wall seconds (CPU seconds); speedups of Prove It under Bun`);
console.table(
  results.map((result) => ({
    model: result.id.length > 40 ? `…${result.id.slice(-39)}` : result.id,
    distinct: result.distinctStates,
    ...Object.fromEntries(
      checkers.map((checker) => [
        checker.name,
        `${formatSeconds(result.measurements[checker.name].wallMilliseconds)} (${formatSeconds(result.measurements[checker.name].cpuMilliseconds)})`,
      ]),
    ),
    "vs tlc": formatRatio(getRatio(result, "tlc", "prove-it-bun", "wallMilliseconds")),
    "vs tlc cpu": formatRatio(getRatio(result, "tlc", "prove-it-bun", "cpuMilliseconds")),
    "vs tla-ts": formatRatio(getRatio(result, "tla-ts", "prove-it-bun", "wallMilliseconds")),
    engine: getEngineLabel(result.engine),
    counts: result.isAgreeing ? "agree" : "DISAGREE",
  })),
);

const getGeometricMean = (ratios: (number | undefined)[]) => {
  const defined = ratios.filter((ratio) => ratio !== undefined);
  return defined.length === 0
    ? undefined
    : Math.exp(defined.reduce((sum, ratio) => sum + Math.log(ratio), 0) / defined.length);
};
console.log("Geometric mean speedup of Prove It under Bun (wall, CPU):");
checkers
  .filter((checker) => checker.name !== "prove-it-bun")
  .forEach((checker) =>
    console.log(
      `  over ${checker.name.padEnd(13)} ${formatRatio(getGeometricMean(results.map((result) => getRatio(result, checker.name, "prove-it-bun", "wallMilliseconds"))))}, ${formatRatio(getGeometricMean(results.map((result) => getRatio(result, checker.name, "prove-it-bun", "cpuMilliseconds"))))}`,
    ),
  );
console.log(
  `Load average at start ${machine.loadAverageAtStart.map((load) => load.toFixed(2)).join(" ")}, at end ${loadavg()
    .map((load) => load.toFixed(2))
    .join(" ")}`,
);
console.log(`Wrote ${outPath}`);
const isFailing = results.some((result) => !result.isAgreeing || result.failed.length > 0);
if (isFailing) console.error("!!! Some checkers disagree on state counts or exited with an error");
process.exit(isFailing ? 1 : 0);

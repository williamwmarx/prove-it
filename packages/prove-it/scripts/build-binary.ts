// Compiles the CLI and its workers into a standalone Bun executable, dist/prove-it, whose code Bun
// has compiled to bytecode ahead of time, so a run neither parses nor compiles the bundle first.
// With --aot, Bun compiles it to machine code instead (Bun's ahead-of-time compiler, in its canary
// builds: scripts/ci/bootstrap.sh bun-canary), as dist/prove-it-aot. Then it runs the executable
// on models that need what it embeds.
// Usage: bun scripts/build-binary.ts [--aot]

import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";

import { createSanySnapshot } from "../src/sany/snapshot";

const PACKAGE_DIRECTORY = join(import.meta.dirname, "..");
// The ahead-of-time executable embeds a file at its path from the package, and fails to build
// (CorruptedCompiledProgram) when an entry it embeds there is also on disk, as dist's are, so the
// snapshot and the entries go in a directory of their own.
const EMBEDDED_DIRECTORY = "dist/embedded";
const SNAPSHOT_PATH = join(PACKAGE_DIRECTORY, EMBEDDED_DIRECTORY, "sany-snapshot.json");

mkdirSync(dirname(SNAPSHOT_PATH), { recursive: true });
writeFileSync(SNAPSHOT_PATH, JSON.stringify(createSanySnapshot()));

const isAheadOfTime = process.argv.includes("--aot");
const outfile = join(PACKAGE_DIRECTORY, isAheadOfTime ? "dist/prove-it-aot" : "dist/prove-it");

const result = await Bun.build({
  entrypoints: [
    "src/cli.ts",
    "src/parallel-worker.ts",
    "src/engine-worker.ts",
    "src/prover/prove-worker.ts",
  ].map((entry) => join(PACKAGE_DIRECTORY, entry)),
  compile: {
    outfile,
    // Bun 1.4.4 doesn't know aot yet; its canary does.
    ...(isAheadOfTime ? ({ aot: true } as object) : {}),
    // The CLI reads the snapshot from beside itself, where the executable embeds it.
    assets: [SNAPSHOT_PATH],
    autoloadDotenv: false,
    autoloadBunfig: false,
  },
  // The library finds its workers and the snapshot beside itself, as dist does. The bytecode
  // executable embeds the entries and the snapshot side by side at its root, and the ahead-of-time
  // one the snapshot at its path from the package, so the entries go beside it.
  naming: isAheadOfTime ? `${EMBEDDED_DIRECTORY}/[name].[ext]` : "[name].[ext]",
  // An ahead-of-time binary holds machine code rather than bytecode, and runs its actions as closures.
  bytecode: !isAheadOfTime,
  define: {
    PROVE_IT_BINARY: "true",
    // HACK: the bytecode executable bundles each entry into one module, whose URL every module it
    // holds shares, while the ahead-of-time one keeps a module for each source file, at its path
    // from the package in Bun's embedded file system, /$bunfs/root. Each module would look for the
    // workers and the snapshot beside its own source file, so they all take the URL of the CLI's
    // entry instead.
    ...(isAheadOfTime && {
      "import.meta.url": JSON.stringify(`file:///$bunfs/root/${EMBEDDED_DIRECTORY}/cli.js`),
      PROVE_IT_AOT: "true",
    }),
  },
  target: "bun",
  format: "esm",
  throw: false,
});

result.logs.forEach((log) => console.error(log));
if (!result.success) process.exit(1);

// The executable throws a MissingBuildFileError for the snapshot or a worker it can't find: every
// check reads the snapshot, the engine starts its workers with PROVE_IT_WORKERS once a search runs
// long enough, the interpreter starts its own with -workers when the engine is off, and tlapm starts
// the prover's with --threads.
const cacheDirectory = mkdtempSync(join(tmpdir(), "prove-it-binary-"));
const checks = [
  {
    directory: "benchmarks/commit",
    args: ["Commit.cfg"],
    env: { PROVE_IT_ENGINE: "debug", PROVE_IT_WORKERS: "2" },
    expected: " on 2 threads ",
  },
  {
    directory: "tests/fixtures/commit",
    args: ["-workers", "2", "Commit.cfg"],
    env: { PROVE_IT_ENGINE: "0" },
  },
  {
    directory: "tests/fixtures/obligations",
    args: ["tlapm", "--threads", "2", "--cache-dir", cacheDirectory, "Proofs.tla"],
    env: {},
  },
];
const failures = checks.flatMap((check) => {
  const run = spawnSync(outfile, check.args, {
    cwd: join(PACKAGE_DIRECTORY, check.directory),
    env: { ...process.env, ...check.env },
    encoding: "utf8",
  });
  const isPassed =
    run.status === 0 && (check.expected === undefined || run.stderr.includes(check.expected));
  return isPassed ? [] : [`${check.args.join(" ")} in ${check.directory}:\n${run.stderr}`];
});
rmSync(cacheDirectory, { recursive: true, force: true });
if (failures.length > 0) {
  console.error(`${outfile} failed:\n${failures.join("\n")}`);
  process.exit(1);
}

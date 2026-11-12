// Compiles the CLI and its workers into a standalone Bun executable, dist/prove-it, whose code Bun
// has compiled to bytecode ahead of time, so a run neither parses nor compiles the bundle first.
// With --aot, Bun compiles it to machine code instead (Bun's ahead-of-time compiler, in its canary
// builds: scripts/ci/bootstrap.sh bun-canary), as dist/prove-it-aot. Then it runs the executable
// on models that need what it embeds. It embeds the native engine too when
// scripts/platform-packages.ts has built it for this platform, and checks that the executable loads
// it.
// Usage: bun scripts/build-binary.ts [--aot]

import { spawnSync } from "node:child_process";
import { copyFileSync, existsSync, mkdirSync, mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";

import { ADDON_FILE } from "../src/engine/native";
import { NPM_DIRECTORY, PLATFORMS } from "./platform-packages";

const PACKAGE_DIRECTORY = join(import.meta.dirname, "..");
// The ahead-of-time executable embeds a file at its path from the package, and fails to build
// (CorruptedCompiledProgram) when an entry it embeds there is also on disk, as dist's are, so the
// addon and the entries go in a directory of their own.
const EMBEDDED_DIRECTORY = "dist/embedded";

// The addon goes beside the CLI's entry, where the loader looks for it.
const addonPath = join(PACKAGE_DIRECTORY, EMBEDDED_DIRECTORY, ADDON_FILE);
mkdirSync(dirname(addonPath), { recursive: true });
const builtAddon = PLATFORMS.filter(
  (platform) => platform.os === process.platform && platform.cpu === process.arch,
)
  .map((platform) => join(NPM_DIRECTORY, platform.name, ADDON_FILE))
  .find((path) => existsSync(path));
rmSync(addonPath, { force: true });
if (builtAddon === undefined) {
  console.error("No native engine is built for this platform, so the executable goes without it");
} else {
  copyFileSync(builtAddon, addonPath);
}

const isAheadOfTime = process.argv.includes("--aot");
const outfile = join(PACKAGE_DIRECTORY, isAheadOfTime ? "dist/prove-it-aot" : "dist/prove-it");

const result = await Bun.build({
  entrypoints: ["src/cli.ts", "src/parallel-worker.ts", "src/prover/prove-worker.ts"].map((entry) =>
    join(PACKAGE_DIRECTORY, entry),
  ),
  compile: {
    outfile,
    // Bun 1.4.4 doesn't know aot yet; its canary does.
    ...(isAheadOfTime ? ({ aot: true } as object) : {}),
    assets: builtAddon === undefined ? [] : [addonPath],
    autoloadDotenv: false,
    autoloadBunfig: false,
  },
  // The library finds its workers and the addon beside itself, as dist does. The bytecode
  // executable embeds the entries and the addon side by side at its root, and the ahead-of-time
  // one the addon at its path from the package, so the entries go beside it.
  naming: isAheadOfTime ? `${EMBEDDED_DIRECTORY}/[name].[ext]` : "[name].[ext]",
  // An ahead-of-time binary holds machine code rather than bytecode.
  bytecode: !isAheadOfTime,
  define: {
    PROVE_IT_BINARY: "true",
    // HACK: the bytecode executable bundles each entry into one module, whose URL every module it
    // holds shares, while the ahead-of-time one keeps a module for each source file, at its path
    // from the package in Bun's embedded file system, /$bunfs/root. Each module would look for the
    // workers and the addon beside its own source file, so they all take the URL of the CLI's
    // entry instead.
    ...(isAheadOfTime && {
      "import.meta.url": JSON.stringify(`file:///$bunfs/root/${EMBEDDED_DIRECTORY}/cli.js`),
    }),
  },
  target: "bun",
  format: "esm",
  throw: false,
});

result.logs.forEach((log) => console.error(log));
if (!result.success) process.exit(1);

// The executable throws a MissingBuildFileError for a worker it can't find: the interpreter starts
// its workers with -workers when the engine is off, and tlapm starts the prover's with --threads.
const cacheDirectory = mkdtempSync(join(tmpdir(), "prove-it-binary-"));
// SANY's report needs the engine, so a check of a model needs the embedded addon.
const checks = [
  ...(builtAddon === undefined
    ? []
    : [
        {
          directory: "tests/fixtures/commit",
          args: ["-workers", "2", "Commit.cfg"],
          env: { PROVE_IT_ENGINE: "0" },
        },
        {
          directory: "tests/fixtures/commit",
          args: ["Commit.cfg"],
          // A state log leaves the check to the TypeScript check, which searches the engine IR
          // past the binary's own check; where the log can't be created, the engine writes none.
          env: {
            PROVE_IT_ENGINE: "debug",
            PROVE_IT_ENGINE_ADDON: undefined,
            PROVE_IT_STATE_LOG: join("missing", "states.jsonl"),
          },
          expected: ["[engine] native: complete: ", " on 1 thread "],
        },
      ]),
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
    run.status === 0 && (check.expected ?? []).every((expected) => run.stderr.includes(expected));
  return isPassed ? [] : [`${check.args.join(" ")} in ${check.directory}:\n${run.stderr}`];
});
rmSync(cacheDirectory, { recursive: true, force: true });
if (failures.length > 0) {
  console.error(`${outfile} failed:\n${failures.join("\n")}`);
  process.exit(1);
}

// Compiles the CLI and its workers into a standalone Bun executable, dist/prove-it, whose code Bun
// has compiled to bytecode ahead of time, so a run neither parses nor compiles the bundle first.
// With --aot, Bun compiles it to machine code instead (Bun's ahead-of-time compiler, in its canary
// builds: scripts/ci/bootstrap.sh bun-canary), as dist/prove-it-aot.
// Usage: bun scripts/build-binary.ts [--aot]

import { mkdirSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";

import { createSanySnapshot } from "../src/sany/snapshot";

const PACKAGE_DIRECTORY = join(import.meta.dirname, "..");
const SNAPSHOT_PATH = join(PACKAGE_DIRECTORY, "dist/sany-snapshot.json");

mkdirSync(dirname(SNAPSHOT_PATH), { recursive: true });
writeFileSync(SNAPSHOT_PATH, JSON.stringify(createSanySnapshot()));

const isAheadOfTime = process.argv.includes("--aot");

const result = await Bun.build({
  entrypoints: [
    "src/cli.ts",
    "src/parallel-worker.ts",
    "src/engine-worker.ts",
    "src/prover/prove-worker.ts",
  ].map((entry) => join(PACKAGE_DIRECTORY, entry)),
  compile: {
    outfile: join(PACKAGE_DIRECTORY, isAheadOfTime ? "dist/prove-it-aot" : "dist/prove-it"),
    // Bun 1.4.4 doesn't know aot yet; its canary does.
    ...(isAheadOfTime ? ({ aot: true } as object) : {}),
    // The CLI reads the snapshot from beside itself, where the executable embeds it.
    assets: [SNAPSHOT_PATH],
    autoloadDotenv: false,
    autoloadBunfig: false,
  },
  // The library finds its workers beside itself, as dist does.
  naming: "[name].[ext]",
  // An ahead-of-time binary holds machine code rather than bytecode, and runs its actions as closures.
  bytecode: !isAheadOfTime,
  define: isAheadOfTime ? { PROVE_IT_AOT: "true" } : {},
  target: "bun",
  format: "esm",
  throw: false,
});

result.logs.forEach((log) => console.error(log));
if (!result.success) process.exit(1);

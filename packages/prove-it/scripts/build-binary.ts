// Compiles the CLI and its workers into a standalone Bun executable, dist/prove-it, whose code Bun
// has compiled to bytecode ahead of time, so a run neither parses nor compiles the bundle first.
// Usage: bun scripts/build-binary.ts

import { mkdirSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";

import { createSanySnapshot } from "../src/sany/snapshot";

const PACKAGE_DIRECTORY = join(import.meta.dirname, "..");
const SNAPSHOT_PATH = join(PACKAGE_DIRECTORY, "dist/sany-snapshot.json");

mkdirSync(dirname(SNAPSHOT_PATH), { recursive: true });
writeFileSync(SNAPSHOT_PATH, JSON.stringify(createSanySnapshot()));

const result = await Bun.build({
  entrypoints: [
    "src/cli.ts",
    "src/parallel-worker.ts",
    "src/engine-worker.ts",
    "src/prover/prove-worker.ts",
  ].map((entry) => join(PACKAGE_DIRECTORY, entry)),
  compile: {
    outfile: join(PACKAGE_DIRECTORY, "dist/prove-it"),
    // The CLI reads the snapshot from beside itself, where the executable embeds it.
    assets: [SNAPSHOT_PATH],
    autoloadDotenv: false,
    autoloadBunfig: false,
  },
  // The library finds its workers beside itself, as dist does.
  naming: "[name].[ext]",
  bytecode: true,
  target: "bun",
  format: "esm",
  throw: false,
});

result.logs.forEach((log) => console.error(log));
if (!result.success) process.exit(1);

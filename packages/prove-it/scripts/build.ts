// Bundles each entry into dist on its own, without shared chunks. The library finds its workers as
// new URL("./parallel-worker.js", import.meta.url), so all four entries sit side by side in dist.
// Usage: bun scripts/build.ts

import { rmSync } from "node:fs";
import { join } from "node:path";

const PACKAGE_DIRECTORY = join(import.meta.dirname, "..");
const OUT_DIRECTORY = join(PACKAGE_DIRECTORY, "dist");

const LICENSE_BANNER = `/**
 * @license prove-it
 *
 * Copyright (c) Aiden Bai and Prove It contributors
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */`;

rmSync(OUT_DIRECTORY, { recursive: true, force: true });

const result = await Bun.build({
  entrypoints: [
    "src/index.ts",
    "src/cli.ts",
    "src/parallel-worker.ts",
    "src/prover/prove-worker.ts",
  ].map((entry) => join(PACKAGE_DIRECTORY, entry)),
  outdir: OUT_DIRECTORY,
  naming: "[name].[ext]",
  target: "node",
  format: "esm",
  banner: LICENSE_BANNER,
  throw: false,
});

result.logs.forEach((log) => console.error(log));
if (!result.success) process.exit(1);

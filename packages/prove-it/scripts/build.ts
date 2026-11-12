// Bundles the entries into dist, splitting the code they share and the code they import dynamically
// into chunks, so the CLI loads the prover, the XML exporter and tlapm only for the commands that
// run them. The prover finds its workers as new URL("./prove-worker.js", import.meta.url), so the
// entries and the chunks sit side by side in dist.
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
  entrypoints: ["src/index.ts", "src/cli.ts", "src/prover/prove-worker.ts"].map((entry) =>
    join(PACKAGE_DIRECTORY, entry),
  ),
  outdir: OUT_DIRECTORY,
  naming: { entry: "[name].[ext]", chunk: "[name]-[hash].[ext]" },
  splitting: true,
  target: "node",
  format: "esm",
  banner: LICENSE_BANNER,
  throw: false,
});

result.logs.forEach((log) => console.error(log));
if (!result.success) process.exit(1);

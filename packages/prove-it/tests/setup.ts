// Every check needs the native engine, so bun test points PROVE_IT_ENGINE_ADDON at the addon
// `bun scripts/platform-packages.ts build` built for this system, unless it or PROVE_IT_ENGINE_WASM
// already names one. A test that runs without the engine says so in its own environment.

import { existsSync } from "node:fs";
import { join } from "node:path";

import { NPM_DIRECTORY, PLATFORMS } from "../scripts/platform-packages";
import { ADDON_FILE } from "../src/engine/native";

const addon = PLATFORMS.filter(
  (platform) => platform.os === process.platform && platform.cpu === process.arch,
)
  .map((platform) => join(NPM_DIRECTORY, platform.name, ADDON_FILE))
  .find(existsSync);
if (
  addon !== undefined &&
  process.env.PROVE_IT_ENGINE_ADDON === undefined &&
  process.env.PROVE_IT_ENGINE_WASM === undefined
) {
  process.env.PROVE_IT_ENGINE_ADDON = addon;
}

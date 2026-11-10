// Every check needs the native engine, so bun test points PROVE_IT_ENGINE_ADDON at the addon
// `bun scripts/platform-packages.ts build` built for this system, unless it or PROVE_IT_ENGINE_WASM
// already names one. A test that runs without the engine says so in its own environment.

import { useBuiltAddon } from "../scripts/platform-packages";

useBuiltAddon();

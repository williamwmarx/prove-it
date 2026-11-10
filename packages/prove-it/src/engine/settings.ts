// PROVE_IT_ENGINE=0 turns the engine off, and PROVE_IT_ENGINE=debug reports what it did on stderr.
const getEnvironment = () =>
  (globalThis as { process?: { env?: Record<string, string | undefined> } }).process?.env;

export const getEngineSetting = () => getEnvironment()?.PROVE_IT_ENGINE;

export const reportEngine = (message: string) => {
  if (getEngineSetting() === "debug") console.error(`[engine] ${message}`);
};

// PROVE_IT_FINGERPRINT=reference fingerprints each state from scratch instead of from its parent's,
// and =check does both and throws where they differ.
export const getFingerprintSetting = () => getEnvironment()?.PROVE_IT_FINGERPRINT;

// PROVE_IT_ENGINE_ADDON loads the native engine from that path rather than its platform's package.
export const getEngineAddon = () => getEnvironment()?.PROVE_IT_ENGINE_ADDON;

// PROVE_IT_ENGINE_WASM loads the native engine from that WebAssembly module rather than the addon,
// as where there is no process.dlopen.
export const getEngineWasm = () => getEnvironment()?.PROVE_IT_ENGINE_WASM;

// PROVE_IT_IR_DUMP names the file the engine IR of the model is written to.
export const isIrDumped = () => Boolean(getEnvironment()?.PROVE_IT_IR_DUMP);

export const getEnvironmentFlag = (name: string) => getEnvironment()?.[name] === "1";

// The state PROVE_IT_STOP_AT names, before whose expansion the engine's search stops, or -1.
export const getStopAt = () => {
  const stopAt = Number(getEnvironment()?.PROVE_IT_STOP_AT ?? -1);
  return Number.isInteger(stopAt) && stopAt >= 0 ? stopAt : -1;
};

// PROVE_IT_TEST_LIVE_CHECK_AT: after how many expanded states the search checks the temporal
// properties the first time, rather than after three seconds, so that a test sees the check TLC
// makes part way through the search. -1 without it.
export const getTestLiveCheckAt = () => {
  const testLiveCheckAt = Number(getEnvironment()?.PROVE_IT_TEST_LIVE_CHECK_AT ?? -1);
  return Number.isInteger(testLiveCheckAt) && testLiveCheckAt > 0 ? testLiveCheckAt : -1;
};

// How many threads the native engine searches with: PROVE_IT_WORKERS, else one. TLC's -workers doesn't change it, since a model tuned for TLC's workers is
// usually faster on one engine thread; the engine keeps TLC's order whatever the number.
export const getEngineThreads = () => {
  const configured = Number(getEnvironment()?.PROVE_IT_WORKERS);
  return Number.isInteger(configured) && configured > 0 ? configured : 1;
};

// PROVE_IT_SHARED_LEVEL: the fewest states a level of the native search shares between its
// threads, or -1 for the engine's own threshold. A test sets it low to share every level.
export const getMinimumSharedLevel = () => {
  const configured = Number(getEnvironment()?.PROVE_IT_SHARED_LEVEL ?? -1);
  return Number.isInteger(configured) && configured >= 0 ? configured : -1;
};

// The file system and whether this is the main thread, on a host that has them. The debug logs
// below are written only from the main thread, since a worker sees the same settings.
const getMainThreadFileSystem = () => {
  const getBuiltinModule = (
    globalThis as { process?: { getBuiltinModule?: (name: string) => unknown } }
  ).process?.getBuiltinModule;
  const threads = getBuiltinModule?.("node:worker_threads") as
    { isMainThread: boolean } | undefined;
  return threads?.isMainThread
    ? (getBuiltinModule?.("node:fs") as
        | {
            writeFileSync: (path: string, data: string | Uint8Array) => void;
            appendFileSync: (path: string, text: string) => void;
          }
        | undefined)
    : undefined;
};

// Writes bytes to the file the setting `name` names, if it names one: PROVE_IT_IR_DUMP names the
// file the engine IR is written to.
export const writeDebugBytes = (name: string, bytes: Uint8Array) => {
  const path = getEnvironment()?.[name];
  if (path) getMainThreadFileSystem()?.writeFileSync(path, bytes);
};

// PROVE_IT_CHECK_LOG names a file each check appends lines of JSON to, which
// scripts/check-log.ts reads: the check's source, configuration, options and caller, then each
// module, class and file it reads.
export const getCheckLog = () => {
  const path = getEnvironment()?.PROVE_IT_CHECK_LOG;
  const fileSystem = path ? getMainThreadFileSystem() : undefined;
  return path && fileSystem
    ? (entry: object) => fileSystem.appendFileSync(path, `${JSON.stringify(entry)}\n`)
    : undefined;
};

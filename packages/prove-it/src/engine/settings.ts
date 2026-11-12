// PROVE_IT_ENGINE=debug reports what the engine did on stderr.
const getEnvironment = () =>
  (globalThis as { process?: { env?: Record<string, string | undefined> } }).process?.env;

export const reportEngine = (message: string) => {
  if (getEnvironment()?.PROVE_IT_ENGINE === "debug") console.error(`[engine] ${message}`);
};

// PROVE_IT_ENGINE_ADDON loads the native engine from that path rather than its platform's package.
export const getEngineAddon = () => getEnvironment()?.PROVE_IT_ENGINE_ADDON;

// PROVE_IT_ENGINE_WASM loads the native engine from that WebAssembly module rather than the addon,
// as where there is no process.dlopen.
export const getEngineWasm = () => getEnvironment()?.PROVE_IT_ENGINE_WASM;

export const getEnvironmentSetting = (name: string) => getEnvironment()?.[name];

// The PROVE_IT_ settings, which the native check reads as the binary reads its environment.
export const getEngineVariables = () =>
  Object.entries(getEnvironment() ?? {}).filter(
    (entry): entry is [string, string] =>
      entry[0].startsWith("PROVE_IT_") && entry[1] !== undefined,
  );

// The file system and whether this is the main thread, on a host that has them. The check log is
// written only from the main thread, since a worker sees the same settings.
const getMainThreadFileSystem = () => {
  const getBuiltinModule = (
    globalThis as { process?: { getBuiltinModule?: (name: string) => unknown } }
  ).process?.getBuiltinModule;
  const threads = getBuiltinModule?.("node:worker_threads") as
    { isMainThread: boolean } | undefined;
  return threads?.isMainThread
    ? (getBuiltinModule?.("node:fs") as
        | {
            appendFileSync: (path: string, text: string) => void;
          }
        | undefined)
    : undefined;
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

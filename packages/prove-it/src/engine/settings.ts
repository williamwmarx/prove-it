// PROVE_IT_ENGINE=0 turns the engine off, and PROVE_IT_ENGINE=debug reports what it did on stderr.
const getEnvironment = () =>
  (globalThis as { process?: { env?: Record<string, string | undefined> } }).process?.env;

export const getEngineSetting = () => getEnvironment()?.PROVE_IT_ENGINE;

export const reportEngine = (message: string) => {
  if (getEngineSetting() === "debug") console.error(`[engine] ${message}`);
};

// The binary Bun compiles to machine code ahead of time (build-binary.ts --aot) defines
// PROVE_IT_AOT. It runs code made with new Function in an interpreter, so it runs actions as
// closures unless PROVE_IT_CODEGEN says otherwise.
declare const PROVE_IT_AOT: boolean | undefined;
const isAheadOfTime = typeof PROVE_IT_AOT === "boolean" && PROVE_IT_AOT;

// PROVE_IT_CODEGEN=0 runs actions as closures instead of generated code, =1 generates code even in
// the ahead-of-time binary, =dump prints the code, =share writes the code a large action gets,
// with each branch point's continuation shared, and =hoist puts every step in a function of its own.
export const getCodegenSetting = () =>
  getEnvironment()?.PROVE_IT_CODEGEN ?? (isAheadOfTime ? "0" : undefined);

// PROVE_IT_FINGERPRINT=reference fingerprints each state from scratch instead of from its parent's,
// and =check does both and throws where they differ.
export const getFingerprintSetting = () => getEnvironment()?.PROVE_IT_FINGERPRINT;

// PROVE_IT_ENGINE_BACKEND=auto, the default, or =rust tries the native engine before the TypeScript
// one, which checks whatever the native engine declines and everything where its platform package
// isn't installed; auto doesn't when PROVE_IT_WORKERS asks for more than one thread, since the
// native search runs on one. ts goes straight to the TypeScript one. PROVE_IT_ENGINE_ADDON loads the native
// engine from that path rather than its platform's package.
export const getEngineBackend = () => getEnvironment()?.PROVE_IT_ENGINE_BACKEND ?? "auto";

export const getEngineAddon = () => getEnvironment()?.PROVE_IT_ENGINE_ADDON;

// PROVE_IT_IR_DUMP names the file the engine IR of the model is written to, with any backend.
export const isIrDumped = () => Boolean(getEnvironment()?.PROVE_IT_IR_DUMP);

export const getEnvironmentFlag = (name: string) => getEnvironment()?.[name] === "1";

// The state PROVE_IT_STOP_AT names, before whose expansion the engine's search stops, or -1.
export const getStopAt = () => {
  const stopAt = Number(getEnvironment()?.PROVE_IT_STOP_AT ?? -1);
  return Number.isInteger(stopAt) && stopAt >= 0 ? stopAt : -1;
};

// Whether PROVE_IT_STORE_TRACE asks for the store's operations, which only a search on one thread
// records whole: the workers' operations go to the shared store and not to the trace.
export const isStoreTraced = () => Boolean(getEnvironment()?.PROVE_IT_STORE_TRACE);

// How many threads the engine searches with: PROVE_IT_WORKERS, else one. TLC's -workers doesn't
// change it, since a model tuned for TLC's workers is usually faster on one engine thread; the
// engine keeps TLC's order whatever the number.
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

// Writes lines to the file the setting `name` names, if it names one, a batch at a time, since a
// file may be longer than a string can be: PROVE_IT_STATE_LOG names the file a search writes its
// states to.
export const writeDebugFile = (name: string, getLines: () => Iterable<string>) => {
  const path = getEnvironment()?.[name];
  const fileSystem = path ? getMainThreadFileSystem() : undefined;
  if (!path || !fileSystem) return;
  fileSystem.writeFileSync(path, "");
  const batch: string[] = [];
  for (const line of getLines()) {
    batch.push(line);
    if (batch.length < 8192) continue;
    fileSystem.appendFileSync(path, `${batch.join("\n")}\n`);
    batch.length = 0;
  }
  if (batch.length > 0) fileSystem.appendFileSync(path, `${batch.join("\n")}\n`);
};

// Writes bytes to the file the setting `name` names, if it names one: PROVE_IT_IR_DUMP names the
// file the engine IR is written to.
export const writeDebugBytes = (name: string, bytes: Uint8Array) => {
  const path = getEnvironment()?.[name];
  if (path) getMainThreadFileSystem()?.writeFileSync(path, bytes);
};

// Appends lines to the file the setting `name` names, from empty, keeping them until there are
// many or the process exits: PROVE_IT_STORE_TRACE names the file the store writes its operations
// to.
export const openDebugLog = (name: string) => {
  const path = getEnvironment()?.[name];
  const fileSystem = path ? getMainThreadFileSystem() : undefined;
  if (!path || !fileSystem) return undefined;
  fileSystem.writeFileSync(path, "");
  const lines: string[] = [];
  const flush = () => {
    if (lines.length === 0) return;
    fileSystem.appendFileSync(path, `${lines.join("\n")}\n`);
    lines.length = 0;
  };
  (globalThis as { process?: { on: (event: string, listener: () => void) => void } }).process?.on(
    "exit",
    flush,
  );
  return (line: string) => {
    lines.push(line);
    if (lines.length >= 8192) flush();
  };
};

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

// PROVE_IT_ENGINE_BACKEND=rust or =auto tries the native engine before the TypeScript one, which
// checks whatever the native engine declines; ts, the default, goes straight to the TypeScript one.
// PROVE_IT_ENGINE_ADDON loads the native engine from that path rather than its platform's package.
export const getEngineBackend = () => getEnvironment()?.PROVE_IT_ENGINE_BACKEND ?? "ts";

export const getEngineAddon = () => getEnvironment()?.PROVE_IT_ENGINE_ADDON;

export const getEnvironmentFlag = (name: string) => getEnvironment()?.[name] === "1";

// How many threads the engine searches with: PROVE_IT_WORKERS, else one. TLC's -workers doesn't
// change it, since a model tuned for TLC's workers is usually faster on one engine thread; the
// engine keeps TLC's order whatever the number.
export const getEngineThreads = () => {
  const configured = Number(getEnvironment()?.PROVE_IT_WORKERS);
  return Number.isInteger(configured) && configured > 0 ? configured : 1;
};

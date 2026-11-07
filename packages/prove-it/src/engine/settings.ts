// PROVE_IT_ENGINE=0 turns the engine off, and PROVE_IT_ENGINE=debug reports what it did on stderr.
const getEnvironment = () =>
  (globalThis as { process?: { env?: Record<string, string | undefined> } }).process?.env;

export const getEngineSetting = () => getEnvironment()?.PROVE_IT_ENGINE;

export const reportEngine = (message: string) => {
  if (getEngineSetting() === "debug") console.error(`[engine] ${message}`);
};

// PROVE_IT_CODEGEN=0 runs actions as closures instead of generated code, =dump prints the code,
// =share writes the code a large action gets, with each branch point's continuation shared, and
// =hoist puts every step in a function of its own.
export const getCodegenSetting = () => getEnvironment()?.PROVE_IT_CODEGEN;

// PROVE_IT_FINGERPRINT=reference fingerprints each state from scratch instead of from its parent's,
// and =check does both and throws where they differ.
export const getFingerprintSetting = () => getEnvironment()?.PROVE_IT_FINGERPRINT;

export const getEnvironmentFlag = (name: string) => getEnvironment()?.[name] === "1";

// How many threads the engine searches with: PROVE_IT_WORKERS, else one. TLC's -workers doesn't
// change it, since a model tuned for TLC's workers is usually faster on one engine thread; the
// engine keeps TLC's order whatever the number.
export const getEngineThreads = () => {
  const configured = Number(getEnvironment()?.PROVE_IT_WORKERS);
  return Number.isInteger(configured) && configured > 0 ? configured : 1;
};

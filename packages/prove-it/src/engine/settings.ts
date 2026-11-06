// PROVE_IT_ENGINE=0 turns the engine off, and PROVE_IT_ENGINE=debug reports what it did on stderr.
const getEnvironment = () =>
  (globalThis as { process?: { env?: Record<string, string | undefined> } }).process?.env;

export const getEngineSetting = () => getEnvironment()?.PROVE_IT_ENGINE;

export const reportEngine = (message: string) => {
  if (getEngineSetting() === "debug") console.error(`[engine] ${message}`);
};

// PROVE_IT_CODEGEN=0 runs actions as closures instead of generated code.
export const getCodegenSetting = () => getEnvironment()?.PROVE_IT_CODEGEN;

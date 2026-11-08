// What the conformance scripts share about the engine: the backends they can run it with, and how
// they read what it did from the [engine] lines PROVE_IT_ENGINE=debug prints on stderr.

import { getOption } from "./corpora";

// The engine's implementations, which PROVE_IT_ENGINE_BACKEND picks. Only the TypeScript engine
// exists yet.
export const BACKENDS = ["ts"];

// The backend --backend names, or every backend with --compare-backends. A name that isn't a
// backend ends the run.
export const getBackends = () => {
  const backend = getOption("--backend") ?? BACKENDS[0];
  if (!BACKENDS.includes(backend)) {
    console.error(`--backend takes one of ${BACKENDS.join(", ")}, not ${backend}`);
    process.exit(2);
  }
  return process.argv.includes("--compare-backends") ? BACKENDS : [backend];
};

export const getBackendEnvironment = (backend: string) => ({
  ...process.env,
  PROVE_IT_ENGINE: process.env.PROVE_IT_ENGINE ?? "debug",
  PROVE_IT_ENGINE_BACKEND: backend,
});

// Notes on how the engine runs, such as closures standing in for generated code or what the workers
// did with a level, aren't outcomes.
export const getEngineLine = (stderr: string) =>
  [...stderr.matchAll(/^\[engine\] (.*)$/gm)]
    .map((match) => match[1])
    .find((line) => !line.endsWith(" runs as closures") && !line.startsWith("level of "));

export const classifyEngineLine = (engineLine: string | undefined) => {
  if (engineLine === undefined) return { engine: "not reached", reason: undefined };
  if (engineLine.startsWith("checked ")) return { engine: "completed", reason: undefined };
  const skipped = /^skipped: (.*)$/.exec(engineLine);
  if (skipped) return { engine: "skipped", reason: skipped[1] };
  const handedOver = /^handed over after (\d+) ms: (.*)$/.exec(engineLine);
  return {
    engine: "handed over",
    reason: handedOver?.[2] ?? engineLine,
    engineMilliseconds: handedOver ? Number(handedOver[1]) : undefined,
  };
};

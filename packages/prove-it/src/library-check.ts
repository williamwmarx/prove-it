// The library's check: the native binary's check, run in-process through checkSources as the CLI
// runs it, which reads the spec, its configuration and its modules from the options rather than
// files. Where it declines the model, or the options ask for what only the TypeScript check does,
// the TypeScript check checks it and its result converts.

import type { CheckOptions as SearchOptions } from "./check";
import {
  type CheckProgress,
  type CheckResult,
  fromNativeOutcome,
  fromSearchResult,
  toContinuedViolation,
  type Violation,
} from "./check-result";
import { checkAllSources, getNativeAddon, loadWasmEngine } from "./engine/native";
import { getEngineVariables, isTypeScriptCheckAsked, reportEngine } from "./engine/settings";
import { checkUnlogged, logCheck } from "./parallel";

export interface CheckOptions extends Omit<SearchOptions, "onProgress"> {
  // Reports the points of the search at which TLC prints a message. Only the TypeScript check
  // reports them as it goes, so the check takes this path where it's given.
  onProgress?: (progress: CheckProgress) => void;
}

// The standard modules the TypeScript check reads as its own, never asking loadModule for them.
const BUILT_IN_MODULES = new Set(["Naturals", "Integers", "Sequences", "FiniteSets", "TLC"]);

// TLC's file name for the spec: its module's.
const getModuleName = (source: string) => /^\s*-{4,}\s*MODULE\s+(\w+)\s*-{4,}/m.exec(source)?.[1];

// Why the native check doesn't take these options, if it doesn't.
const getDeclined = (options: CheckOptions) =>
  (
    [
      [isTypeScriptCheckAsked(), "a setting only the TypeScript check honours"],
      [options.version === "1.7.4", "TLC 1.7.4"],
      [options.dump !== undefined, "-dump"],
      [options.systemProperties !== undefined, "system properties"],
      [options.onProgress !== undefined, "onProgress"],
      [options.onPause !== undefined, "onPause"],
    ] as const
  ).find((entry) => entry[0])?.[1];

// The native check's result, or undefined where it declines.
const checkWithEngine = (options: CheckOptions) => {
  const declined = getDeclined(options);
  const name = getModuleName(options.source);
  const config = options.config;
  if (declined !== undefined || name === undefined || typeof config !== "string") {
    reportEngine(
      `native: check takes the TypeScript path: ${declined ?? (name === undefined ? "a spec without a module header" : "a configuration given as a ModelConfig")}`,
    );
    return undefined;
  }
  const addon = getNativeAddon();
  if (typeof addon === "string") return undefined;
  const args = [
    ...(options.isTraceRecorded ? [] : ["-noGenerateSpecTE"]),
    ...(options.seed === undefined ? [] : ["-seed", String(options.seed)]),
    ...(options.workers === undefined ? [] : ["-workers", String(options.workers)]),
    ...(options.livenessCheck === "final" ? ["-lncheck", "final"] : []),
    ...(options.isTool ? ["-tool"] : []),
    ...(options.isWarningEnabled === false ? ["-nowarning"] : []),
    ...(options.isContinued ? ["-continue"] : []),
    `${name}.tla`,
  ];
  const texts = new Map([
    [`${name}.tla`, options.source],
    [`${name}.cfg`, config],
  ]);
  const read = (key: string) => {
    const [kind, ...rest] = key.split(":");
    const path = rest.join(":");
    return kind === "text"
      ? texts.get(path)
      : // The bytes of a tla2tools.jar a Java launch names, which the library's command line,
        // with no launch, never does.
        kind === "bytes"
        ? undefined
        : kind === "module"
          ? BUILT_IN_MODULES.has(path)
            ? undefined
            : options.loadModule?.(path)
          : kind === "class"
            ? options.loadClass?.(path)
            : // SANY's report names the file of each module it parses, which the result doesn't hold.
              kind === "file"
              ? ""
              : undefined;
  };
  const result = checkAllSources(
    addon,
    args,
    [
      "",
      "",
      "",
      globalThis.navigator?.hardwareConcurrency ?? 1,
      0,
      0,
      Date.now(),
      "UTC0",
      getEngineVariables(),
      true,
    ],
    read,
  );
  if (result.kind === "declined") {
    reportEngine(`native: check declined: ${result.reason}`);
    return undefined;
  }
  // The check stops before it searches at a spec or a configuration TLC rejects, for which the
  // TypeScript check throws its error.
  if (result.outcome === undefined) {
    reportEngine(
      `native: check takes the TypeScript path: the engine stopped before it searched (exit ${result.exitCode})`,
    );
    return undefined;
  }
  const print = options.onPrint ?? console.log;
  result.outcome.prints.forEach((text) => print(text));
  return fromNativeOutcome(result.outcome);
};

// What the TypeScript check finds, converted. With -continue it reports each violation it goes on
// past as it finds it.
const checkWithInterpreter = async (options: CheckOptions) => {
  const isTool = options.isTool ?? false;
  const version = options.version ?? "master";
  const continued: Violation[] = [];
  const onProgress = options.onProgress;
  const result = await checkUnlogged({
    ...options,
    onProgress:
      onProgress || options.isContinued
        ? (progress) => {
            if (progress.kind !== "violation") return onProgress?.(progress);
            const reported = toContinuedViolation(
              progress.status,
              progress.violation,
              isTool,
              version,
            );
            continued.push(...reported);
            onProgress?.({ kind: "violation", status: progress.status, violation: reported[0] });
          }
        : undefined,
  });
  return fromSearchResult(result, continued, isTool, version);
};

export const check = async (options: CheckOptions): Promise<CheckResult> => {
  await loadWasmEngine();
  // PROVE_IT_CHECK_LOG logs the call once, and what either check reads under it.
  const readers = logCheck({ ...options, onProgress: undefined });
  const logged = {
    ...options,
    loadModule: readers.loadModule,
    loadClass: readers.loadClass,
    readFile: readers.readFile,
  };
  return checkWithEngine(logged) ?? checkWithInterpreter(logged);
};

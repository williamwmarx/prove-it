// The library's check: the native binary's check, run in-process through checkSources as the CLI
// runs it, which reads the spec, its configuration and its modules from the options rather than
// files. Where it declines the model, or the options ask for what only the TypeScript check does,
// the TypeScript check checks it and its result converts.

import type {
  CheckOptions as SearchOptions,
  OutputLine,
  SearchStatistics,
  TraceStep,
} from "./check";
import {
  type CheckProgress,
  type CheckResult,
  fromNativeOutcome,
  fromSearchResult,
  toContinuedViolation,
  type Violation,
} from "./check-result";
import { parseConfig } from "./config";
import { checkAllSources, getNativeAddon, loadWasmEngine } from "./engine/native";
import { getEngineVariables, isTypeScriptCheckAsked, reportEngine } from "./engine/settings";
import { WebAssemblyStackError } from "./errors";
import { getNativeProgress } from "./native-progress";
import { checkUnlogged, logCheck } from "./parallel";

export interface CheckOptions extends Omit<SearchOptions, "onProgress"> {
  // Reports the points of the search at which TLC prints a message. The native check reports them
  // once it ends, in order among what the spec printed; the TypeScript check, as it goes.
  onProgress?: (progress: CheckProgress) => void;
}

// The standard modules the TypeScript check reads as its own, never asking loadModule for them.
const BUILT_IN_MODULES = new Set(["Naturals", "Integers", "Sequences", "FiniteSets", "TLC"]);

// Whether the engine as WebAssembly declined a recursion its stack doesn't hold: it trapped
// (src/engine/wasm.ts), or stopped at its bound (WEBASSEMBLY_TOO_DEEP in machine.rs), as it
// searched or as it started.
const isWebAssemblyStack = (reason: string) =>
  reason === "WebAssembly ran out of stack" ||
  reason.endsWith(": recursion deeper than WebAssembly's stack holds");

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
      [options.onPause !== undefined, "onPause"],
    ] as const
  ).find((entry) => entry[0])?.[1];

// The native check's result, why it declined, or undefined where it wasn't run or stopped before
// it searched.
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
    if (isWebAssemblyStack(result.reason)) throw new WebAssemblyStackError();
    reportEngine(`native: check declined: ${result.reason}`);
    return result.reason;
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
  // The TypeScript check prints SANY's warnings as it links the spec, where the caller didn't.
  if (!options.isSanyReported) result.outcome.sanyWarnings.forEach((text) => print(text));
  const prints = result.outcome.prints;
  const checked = fromNativeOutcome(result.outcome);
  const onProgress = options.onProgress;
  const events = onProgress
    ? getNativeProgress(
        result.outcome,
        checked.violations,
        parseConfig(config),
        options.isContinued ?? false,
      )
    : [];
  let printed = 0;
  events.forEach((event) => {
    prints.slice(printed, event.printsBefore).forEach((text) => print(text));
    printed = Math.max(printed, event.printsBefore);
    onProgress?.(event.progress);
  });
  prints.slice(printed).forEach((text) => print(text));
  return checked;
};

const toStatistics = (statistics: SearchStatistics): SearchStatistics => ({
  generatedStates: statistics.generatedStates,
  distinctStates: statistics.distinctStates,
  queuedStates: statistics.queuedStates,
  depth: statistics.depth,
});

// What the TypeScript check finds, converted. With -continue it reports each violation it goes on
// past as it finds it.
// A violation or a failure of the TypeScript check, with its trace.
interface Traced {
  trace: TraceStep[];
  traceOutput?: OutputLine[];
}

// What the spec printed as TLC rebuilt and printed a trace, then after it, as the native check
// reports it.
const getTracePrints = (reported: Traced | undefined) =>
  [
    ...(reported?.trace ?? []).flatMap((step) => step.output ?? []),
    ...(reported?.traceOutput ?? []),
  ].filter((line) => typeof line === "string");

// What the native check declines where the TypeScript check places the trace's prints otherwise
// than TLC, or prints other values in them: a printing ALIAS, a printing temporal property, and
// TLCExt's Trace (native/design/fallback.md, "Interpreter limits").
const MISPLACED_TRACE_PRINTS = [
  "an ALIAS that prints",
  "prints it doesn't place in TLC's order",
  "TLCExt's Trace",
];

// The TypeScript check's result. Where the native check declined for `declined`, the trace's prints
// go to onPrint as the native check reports them, but where the TypeScript check misplaces them;
// where the native check didn't run, as with onProgress, they don't, as before.
const checkWithInterpreter = async (options: CheckOptions, declined: string | undefined) => {
  const isTracePrinted =
    declined !== undefined && !MISPLACED_TRACE_PRINTS.some((reason) => declined.includes(reason));
  const print = (line: string) => {
    if (isTracePrinted) (options.onPrint ?? console.log)(line);
  };
  const isTool = options.isTool ?? false;
  const version = options.version ?? "master";
  const continued: Violation[] = [];
  // The traces -continue reported as the search went on, whose prints went to onPrint then.
  const reportedTraces = new Set<Traced>();
  const onProgress = options.onProgress;
  const result = await checkUnlogged({
    ...options,
    onProgress:
      onProgress || options.isContinued
        ? (progress) => {
            // The search's statistics are its whole result so far, of which the event carries
            // the counts.
            if (progress.kind === "progress" || progress.kind === "liveness-started") {
              return onProgress?.({ ...progress, statistics: toStatistics(progress.statistics) });
            }
            if (progress.kind !== "violation") return onProgress?.(progress);
            // TLC prints each violation's trace as it reports it, without rebuilding it once more
            // after it, and goes on.
            reportedTraces.add(progress.violation);
            getTracePrints({ trace: progress.violation.trace }).forEach((line) => print(line));
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
  // Every trace the result carries but one -continue reported as it went on: the violation, a
  // temporal property the deadlocked state violates too, and a failure.
  [result.violation, result.additionalViolation, result.failure]
    .filter((traced) => traced === undefined || !reportedTraces.has(traced))
    .flatMap(getTracePrints)
    .forEach((line) => print(line));
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
  const native = checkWithEngine(logged);
  return typeof native === "object" ? native : checkWithInterpreter(logged, native);
};

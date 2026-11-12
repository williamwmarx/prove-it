// The library's check: the native binary's check, run in-process through checkSources as the CLI
// runs it, which reads the spec, its configuration and its modules from the options rather than
// files. Where the native check declines the model, check throws TlaUnsupportedError.

import { type CheckProgress, type CheckResult, fromNativeOutcome } from "./check-result";
import { formatConfig, type ModelConfig, parseConfig } from "./config";
import { checkAllSources, getNativeAddon, loadWasmEngine } from "./engine/native";
import { getCheckLog, getEngineVariables, reportEngine } from "./engine/settings";
import {
  createSanyError,
  EngineUnavailableError,
  TlaConfigError,
  TlaEvaluationError,
  TlaStackOverflowError,
  TlaUnsupportedError,
  WebAssemblyStackError,
} from "./errors";
import { getNativeProgress } from "./native-progress";

// TLC's -dump: the reachable states, or with `dot` the state graph, which the native check doesn't
// write yet.
interface StateDump {
  path: string;
  dot?: boolean;
}

export interface CheckOptions {
  // The spec's root module.
  source: string;
  // Its configuration, as TLC reads a .cfg file, or parsed.
  config: string | ModelConfig;
  // The text of a module the spec extends or instantiates, by name, where it isn't a standard one.
  loadModule?: (name: string) => string | undefined;
  // The bytes of a Java class that overrides an operator, by name.
  loadClass?: (name: string) => Uint8Array | undefined;
  // Where TLC prints a line: the spec's prints, and SANY's warnings.
  onPrint?: (line: string) => void;
  // A file the spec reads or writes, as IOUtils does, and the -dump file.
  readFile?: (path: string) => string | undefined;
  writeFile?: (path: string, text: string) => void;
  // The Java system properties TLCGet("-Dname") reads, as a Java launch's -D sets them.
  systemProperties?: ReadonlyMap<string, string>;
  // TLC's -seed, -workers, -lncheck final, -dump, -tool, -continue, -nowarning, and -generateSpecTE.
  seed?: bigint;
  workers?: number;
  livenessCheck?: "default" | "final";
  dump?: StateDump;
  isTool?: boolean;
  isContinued?: boolean;
  isTraceRecorded?: boolean;
  isWarningEnabled?: boolean;
  // Whether the caller reported SANY's warnings, which the check otherwise prints.
  isSanyReported?: boolean;
  // Reports the points of the search at which TLC prints a message, once the check ends, in order
  // among what the spec printed.
  onProgress?: (progress: CheckProgress) => void;
}

// The standard modules the engine reads as its own, never asking loadModule for them.
const BUILT_IN_MODULES = new Set(["Naturals", "Integers", "Sequences", "FiniteSets", "TLC"]);

// Whether the engine as WebAssembly declined a recursion its stack doesn't hold: it trapped
// (src/engine/wasm.ts), or stopped at its bound (WEBASSEMBLY_TOO_DEEP in machine.rs), as it
// searched or as it started.
const isWebAssemblyStack = (reason: string) =>
  reason === "WebAssembly ran out of stack" ||
  reason.endsWith(": recursion deeper than WebAssembly's stack holds");

// The options with the check written to PROVE_IT_CHECK_LOG, and each module, class and file it
// reads as it reads it.
const logCheck = (options: CheckOptions): CheckOptions => {
  const append = getCheckLog();
  if (!append) return options;
  const id = crypto.randomUUID();
  append({
    id,
    source: options.source,
    config: typeof options.config === "string" ? options.config : formatConfig(options.config),
    seed: options.seed?.toString(),
    livenessCheck: options.livenessCheck,
    isTool: options.isTool === true,
    workers: options.workers,
    isContinued: options.isContinued === true,
    isWarningEnabled: options.isWarningEnabled !== false,
    caller: new Error().stack,
  });
  const loadModule = options.loadModule;
  const loadClass = options.loadClass;
  const readFile = options.readFile;
  return {
    ...options,
    loadModule:
      loadModule &&
      ((name) => {
        const text = loadModule(name);
        if (text !== undefined) append({ id, module: name, source: text });
        return text;
      }),
    loadClass:
      loadClass &&
      ((name) => {
        const bytes = loadClass(name);
        if (bytes !== undefined)
          append({
            id,
            class: name,
            bytes: btoa(Array.from(bytes, (byte) => String.fromCharCode(byte)).join("")),
          });
        return bytes;
      }),
    readFile:
      readFile &&
      ((path) => {
        const text = readFile(path);
        if (text !== undefined) append({ id, file: path, text });
        return text;
      }),
  };
};

export const check = async (options: CheckOptions): Promise<CheckResult> => {
  await loadWasmEngine();
  const logged = logCheck(options);
  // TLC's file name for the spec: its module's.
  const name = /^\s*-{4,}\s*MODULE\s+(\w+)\s*-{4,}/m.exec(logged.source)?.[1];
  if (name === undefined)
    throw new TlaUnsupportedError("not native yet: a spec without a module header");
  if (logged.dump?.dot) throw new TlaUnsupportedError("not native yet: -dump dot");
  const config = typeof logged.config === "string" ? logged.config : formatConfig(logged.config);
  if (config === undefined) {
    throw new TlaUnsupportedError("not native yet: a ModelConfig no configuration file holds");
  }
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new EngineUnavailableError(addon);
  // The system properties go in front of TLC's class as a Java launch's -D, as the binary reads
  // them.
  const launch = logged.systemProperties
    ? [
        ...[...logged.systemProperties].map((property) => `-D${property[0]}=${property[1]}`),
        "tlc2.TLC",
      ]
    : [];
  const args = [
    ...launch,
    ...(logged.isTraceRecorded ? [] : ["-noGenerateSpecTE"]),
    ...(logged.seed === undefined ? [] : ["-seed", String(logged.seed)]),
    ...(logged.workers === undefined ? [] : ["-workers", String(logged.workers)]),
    ...(logged.livenessCheck === "final" ? ["-lncheck", "final"] : []),
    ...(logged.isTool ? ["-tool"] : []),
    ...(logged.isWarningEnabled === false ? ["-nowarning"] : []),
    ...(logged.isContinued ? ["-continue"] : []),
    ...(logged.dump ? ["-dump", logged.dump.path] : []),
    `${name}.tla`,
  ];
  const texts = new Map([
    [`${name}.tla`, logged.source],
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
            : logged.loadModule?.(path)
          : kind === "class"
            ? logged.loadClass?.(path)
            : // A file the spec reads, as the Json module's operators do.
              kind === "read"
              ? logged.readFile?.(path)
              : // SANY's report names the file of each module it parses, which the result
                // doesn't hold.
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
    throw new TlaUnsupportedError(`not native yet: ${result.reason}`);
  }
  // The library writes each file the check wrote, with what each write appended, before what it
  // prints or throws, as the CLI does. The check names the -dump file as TLC does, with .dump
  // added, and the library writes it at the path the caller gave; other files, as a trace
  // exploration spec, keep their names.
  const writeFiles = () => {
    const written = new Map<string, string>();
    const decoder = new TextDecoder();
    result.writes.forEach((write) =>
      written.set(
        write.path,
        (write.isAppended ? (written.get(write.path) ?? "") : "") + decoder.decode(write.bytes),
      ),
    );
    const dumpPath = logged.dump?.path;
    written.forEach((text, path) =>
      logged.writeFile?.(
        dumpPath !== undefined && (path === dumpPath || path === `${dumpPath}.dump`)
          ? dumpPath
          : path,
        text,
      ),
    );
  };
  const { outcome, thrown } = result;
  if (outcome === undefined) {
    // The check stopped before it searched, at a spec or a configuration TLC rejects, after what
    // the spec printed as TLC computed its constants.
    if (thrown === undefined)
      throw new TlaUnsupportedError(
        `not native yet: the engine stopped before it searched (exit ${result.exitCode})`,
      );
    // TLC warns of the invariants and properties before it reports an error of the constraints,
    // which onProgress would receive, and the error doesn't carry.
    if (logged.onProgress && /^Warning: /m.test(result.out)) {
      throw new TlaUnsupportedError("not native yet: warnings onProgress receives before an error");
    }
    writeFiles();
    thrown.prints.forEach((text) => (logged.onPrint ?? console.log)(text));
    throw thrown.kind === "syntax"
      ? createSanyError(
          thrown.sany.errors,
          thrown.sany.isFatal,
          thrown.sany.parseError,
          thrown.sany.warnings,
        )
      : thrown.kind === "config"
        ? new TlaConfigError(thrown.message)
        : thrown.kind === "evaluation"
          ? new TlaEvaluationError(thrown.message)
          : new TlaStackOverflowError();
  }
  writeFiles();
  const print = logged.onPrint ?? console.log;
  if (!logged.isSanyReported) outcome.sanyWarnings.forEach((text) => print(text));
  const prints = outcome.prints;
  const checked = fromNativeOutcome(outcome);
  const onProgress = logged.onProgress;
  const events = onProgress
    ? getNativeProgress(
        outcome,
        checked.violations,
        parseConfig(config),
        logged.isContinued ?? false,
      )
    : [];
  const printed = events.reduce((count, event) => {
    prints.slice(count, event.printsBefore).forEach((text) => print(text));
    onProgress?.(event.progress);
    return Math.max(count, event.printsBefore);
  }, 0);
  prints.slice(printed).forEach((text) => print(text));
  return checked;
};

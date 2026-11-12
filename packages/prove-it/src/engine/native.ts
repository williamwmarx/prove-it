// The native engine: the N-API addon that native/crates/prove-it-napi builds. The npm package finds
// it in the optional package for its platform, and the executables embed it; where there is no
// process.dlopen it runs as WebAssembly (wasm.ts).

import type { CheckStatus } from "../check-result";
import type { SanyError } from "../errors";
import type { ProofObligation } from "../prover/prove";
import type { Statistics, Verdict } from "../prover/verdict";
import { getEngineAddon, getEngineWasm } from "./settings";
import { instantiateEngine } from "./wasm";

// What the native binary prints for a TLC command line, its exit code and what it found, the keys
// of what the check still reads, or why the binary declines the model (prove-it-host's check.rs).
export type NativeCheckSources =
  | {
      kind: "checked";
      exitCode: number;
      out: string;
      err: string;
      thrown: NativeThrown | undefined;
      outcome: NativeCheckOutcome | undefined;
      // Each file the check wrote, in order, which the caller writes.
      writes: { path: string; bytes: Uint8Array; isAppended: boolean }[];
    }
  | { kind: "needed"; keys: string[] }
  | { kind: "declined"; reason: string };

// Where the check stops before it searches, the error the TypeScript check throws: the report of
// a TlaSyntaxError, or the message of a TlaConfigError or a TlaEvaluationError.
export type NativeThrown =
  | {
      kind: "syntax";
      sany: {
        errors: SanyError[];
        warnings: SanyError[];
        isFatal: boolean;
        parseError: string | undefined;
      };
    }
  | { kind: "config"; message: string }
  | { kind: "evaluation"; message: string };

// What the check found, where it searched (prove-it-check's outcome.rs): each variable of a state
// as its name, TLC's text of its value, and the value as plain data in JSON.
export interface NativeCheckOutcome {
  status: CheckStatus;
  generatedStates: number;
  distinctStates: number;
  queuedStates: number;
  depth: number;
  prints: string[];
  // SANY's warnings, which the library prints before the prints (`formatSanyWarnings`).
  sanyWarnings: string[];
  // TLC's messages as the check printed them: each one's code, level and text, how many of
  // `prints` came before it, and the search's counts (generated, distinct, queued, depth) where
  // TLC checks the temporal properties part way through the search.
  messages: [
    code: number,
    level: number,
    text: string,
    printsBefore: number,
    counts: [number, number, number, number] | undefined,
  ][];
  violations: {
    code: number;
    headline: string;
    loopStart: number | undefined;
    states: { label: string; variables: [name: string, text: string, data: string][] }[];
  }[];
}

// Runs checkSources to the end: each round, `read` answers the keys it asks for.
export const checkAllSources = (
  addon: NativeAddon,
  args: string[],
  machine: NativeMachine,
  read: (key: string) => string | Uint8Array | undefined,
) => {
  const known = new Map<string, string | Uint8Array | undefined>();
  const check = (): Exclude<NativeCheckSources, { kind: "needed" }> => {
    const result = addon.checkSources(args, [...known], machine);
    if (result.kind !== "needed") return result;
    result.keys.forEach((key) => known.set(key, read(key)));
    return check();
  };
  return check();
};

// What the check prints of the machine it runs on and of the time: `now` in milliseconds since the
// epoch, `zone` a POSIX TZ rule, and the environment variables it reads; and whether the library's
// check runs it, which answers for files itself and reads each printed state's plain data. A tuple,
// since neither binding reads an object.
export type NativeMachine = [
  system: string,
  release: string,
  arch: string,
  cores: number,
  memoryMegabytes: number,
  pid: number,
  now: number,
  zone: string,
  variables: [string, string][],
  isLibrary: boolean,
];

// A prover backend's answer, malformed input, or why the Rust backend doesn't decide the input
// (prove-it-host's prover.rs).
export type NativeDecision =
  | { kind: "decided"; verdict: Verdict; statistics: Statistics }
  | { kind: "error"; message: string }
  | { kind: "declined"; reason: string };

// What the Rust prover driver asks JavaScript to decide, by the key it answers under
// (prove-it-host's prove.rs).
export interface NativeDecideRequest {
  key: string;
  prover: string;
  text: string;
  timeLimitMs: number;
  priority: number;
}

// The obligations proved so far, and the modules and decisions the driver needs, or why it failed.
export type NativeProve =
  | {
      kind: "needed";
      keys: string[];
      requests: NativeDecideRequest[];
      reports: ProofObligation[];
    }
  | {
      kind: "proved";
      reports: ProofObligation[];
      missingProofCount: number;
      omittedProofCount: number;
    }
  | {
      kind: "error";
      name: string;
      message: string;
      failure?: string;
      exception?: string;
      reports?: ProofObligation[];
    };

// An error the obligations throw, by the name of its class in errors.ts (prove-it-host's prove.rs).
export interface NativeObligationError {
  kind: "error";
  name: string;
  message: string;
  failure?: string;
  exception?: string;
}

export interface NativeMethod {
  prover: string;
  timeLimitMs: number;
}

// An obligation as tlapm prints it, with the methods Prep tries on it (prove-it-host's
// obligations.rs).
export interface NativeObligation {
  id: number;
  location: string;
  kind: "Main" | "Support" | "Error" | "Omitted";
  text: string;
  methods: NativeMethod[] | NativeObligationError;
}

// A module's obligations and the text each backend asked for receives, or the modules they need.
export type NativeObligations =
  | { kind: "needed"; keys: string[] }
  | {
      kind: "obligations";
      obligations: NativeObligation[];
      encodings: ({ kind: "text"; text: string } | NativeObligationError)[];
    }
  | NativeObligationError;

// Each obligation's fingerprint as tlapm makes it, or the modules they need.
export type NativeFingerprints =
  | { kind: "needed"; keys: string[] }
  | {
      kind: "fingerprints";
      fingerprints: { id: number; fingerprint: string | NativeObligationError }[];
    }
  | NativeObligationError;

// The addon's hooks into its store, which scripts/value-oracle.ts asks (binding/store.rs).
interface NativeStoreHooks {
  storePerform: (name: string, args: unknown[]) => number | boolean | null | string;
  storeFingerprints: (
    states: Int32Array,
    width: number,
    order: Int32Array,
    parents: Int32Array | undefined,
    isReference: boolean,
    fingerprints: BigInt64Array,
  ) => void;
  storeResetFingerprints: () => void;
}

export interface NativeAddon extends NativeStoreHooks {
  abiVersion: () => number;
  decide: (
    prover: string,
    text: string,
    timeLimitMs: number,
    stepLimit: number | undefined,
    cancel: Int32Array | undefined,
  ) => NativeDecision;
  prove: (file: string, source: string, known: [string, string | undefined][]) => NativeProve;
  obligations: (
    file: string,
    source: string,
    known: [string, string | undefined][],
    encode: [number, string][],
  ) => NativeObligations;
  fingerprint: (
    file: string,
    source: string,
    known: [string, string | undefined][],
  ) => NativeFingerprints;
  checkSources: (
    args: string[],
    known: [string, string | Uint8Array | undefined][],
    machine: NativeMachine,
  ) => NativeCheckSources;
}

// The contract between this loader and the addon, ABI_VERSION in its lib.rs.
const ABI_VERSION = 25;

export const ADDON_FILE = "prove-it-engine.node";
export const WASM_FILE = "prove-it-engine.wasm";

// The executables build-binary.ts compiles define PROVE_IT_BINARY, and embed the addon beside the
// CLI when their build had one.
declare const PROVE_IT_BINARY: boolean | undefined;
const isBinary = typeof PROVE_IT_BINARY === "boolean" && PROVE_IT_BINARY;

// The platform packages scripts/platform-packages.ts packs. Linux has one for glibc and one for
// musl, and a package manager installs only the one for the libc it runs on.
const getPackages = () =>
  (process.platform === "linux"
    ? ["-gnu", "-musl"]
    : process.platform === "win32"
      ? ["-msvc"]
      : [""]
  ).map((suffix) => `@atemp/prove-it-${process.platform}-${process.arch}${suffix}`);

const resolveAddon = (name: string) => {
  try {
    return new URL(import.meta.resolve(`${name}/${ADDON_FILE}`));
  } catch {
    return undefined;
  }
};

const toPath = (url: URL) => {
  const path = decodeURIComponent(url.pathname);
  return process.platform === "win32" ? path.slice(1) : path;
};

// The addon PROVE_IT_ENGINE_ADDON names, the one an executable embeds, or the one in the platform
// package installed. process.getBuiltinModule would take Bun a millisecond or two to load node:url,
// so a file URL becomes a path by hand; on Windows its path starts with a slash before the drive.
const getAddonPath = () => {
  const override = getEngineAddon();
  if (override !== undefined) return override;
  const url = isBinary
    ? new URL(`./${ADDON_FILE}`, import.meta.url)
    : getPackages().reduce<URL | undefined>(
        (found, name) => found ?? resolveAddon(name),
        undefined,
      );
  return url && toPath(url);
};

const getChecked = (addon: NativeAddon, path: string) => {
  const version = addon.abiVersion();
  return version === ABI_VERSION ? addon : `${path} has ABI version ${version}, not ${ABI_VERSION}`;
};

const loadAddon = (): NativeAddon | string => {
  const addonPath = getAddonPath();
  if (addonPath === undefined) return `no ${getPackages().join(" or ")}`;
  const module = { exports: {} };
  try {
    process.dlopen(module, addonPath);
  } catch (error) {
    return `can't load ${addonPath}: ${error instanceof Error ? error.message : String(error)}`;
  }
  return getChecked(module.exports as NativeAddon, addonPath);
};

// The engine compiled to WebAssembly that PROVE_IT_ENGINE_WASM names.
const loadWasm = (wasmPath: string): NativeAddon | string => {
  const fs = process.getBuiltinModule("node:fs");
  try {
    return getChecked(
      instantiateEngine(new WebAssembly.Module(fs.readFileSync(wasmPath))),
      wasmPath,
    );
  } catch (error) {
    return `can't load ${wasmPath}: ${error instanceof Error ? error.message : String(error)}`;
  }
};

const loaded: { addon?: NativeAddon | string } = {};

const isDlopen = () => typeof globalThis.process?.dlopen === "function";

// The addon for this platform, or else the engine as WebAssembly the package ships beside its
// modules, as on a platform no package is built for. An addon PROVE_IT_ENGINE_ADDON names, or one
// an executable embeds, is the only one tried.
const loadAddonOrWasm = () => {
  const addon = loadAddon();
  if (typeof addon !== "string" || isBinary || getEngineAddon() !== undefined) return addon;
  const wasmPath = toPath(new URL(`./${WASM_FILE}`, import.meta.url));
  return process.getBuiltinModule("node:fs").existsSync(wasmPath) ? loadWasm(wasmPath) : addon;
};

// The addon, or the engine compiled to WebAssembly, loaded on first use, or why it can't be loaded.
export const getNativeAddon = () => {
  const wasmPath = getEngineWasm();
  loaded.addon ??=
    wasmPath !== undefined
      ? loadWasm(wasmPath)
      : isDlopen()
        ? loadAddonOrWasm()
        : "no process.dlopen";
  return loaded.addon;
};

// Where there is no process.dlopen, as in a browser, fetches and compiles the engine as WebAssembly,
// which the package ships beside its modules, before getNativeAddon is first called: compiling it
// takes a promise there. The URL is a literal, as WASM_FILE names it, so that a bundler finds the
// file and copies it beside the module it bundles this into.
export const loadWasmEngine = async () => {
  if (loaded.addon !== undefined || isDlopen() || getEngineWasm() !== undefined) return;
  const url = new URL("./prove-it-engine.wasm", import.meta.url);
  try {
    loaded.addon = getChecked(
      instantiateEngine(await WebAssembly.compileStreaming(fetch(url))),
      url.href,
    );
  } catch (error) {
    loaded.addon = `can't load ${url.href}: ${error instanceof Error ? error.message : String(error)}`;
  }
};

// The native engine: the N-API addon that native/crates/prove-it-napi builds. The npm package finds
// it in the optional package for its platform, and the executables embed it. It reads the model
// as the engine IR and searches it as runEngine does, or declines it before producing any state,
// and the TypeScript engine checks what it declines.

import { EngineInvariantError } from "../errors";
import type { LiveExpression } from "../tableau";
import { createStateDecoder, type EncodedStates } from "../transfer";
import { formatPrinted, type Value } from "../values";
import { fromEnumeratedValue, fromValue } from "./convert";
import { resetFingerprints } from "./fingerprint";
import type { IrOutcome } from "./ir";
import type { LiveOracle } from "./live";
import type { EngineCheckpoint, EngineInput, EngineResult } from "./search";
import { getEngineAddon, getEnvironmentFlag, getStopAt, reportEngine } from "./settings";
import { Bailout, resetStore } from "./store";

// The addon's test hooks into its store, which native-store.ts calls (binding/store.rs).
export interface NativeStoreHooks {
  storePerform: (name: string, args: unknown[]) => number | boolean | null | string;
  storeDecode: (
    words: Int32Array,
    strings: string[],
    width: number,
    count: number,
    ids: Int32Array,
  ) => string | null;
  storeEncode: (states: Int32Array, width: number) => EncodedIds;
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

export interface EncodedIds {
  words: Int32Array;
  strings: string[];
  count: number;
}

interface NativeAddon extends NativeStoreHooks {
  abiVersion: () => number;
  check: (
    ir: Uint8Array,
    settings: Int32Array,
    stateLog: string,
    report: (kind: number, a: number, b: number, c: number, d: number) => void,
    print: (width: number, words: Int32Array, strings: string[]) => void,
  ) => NativeOutcome;
}

// The steps of a search the native engine recorded for temporal properties, with its answers to
// each of the liveness checker's atoms (binding/check.rs).
interface NativeGraph {
  expanded: number;
  // Each expanded state's successors, then its new states, then the edge offsets, one more.
  counts: Int32Array;
  edges: Int32Array;
  labels?: Int32Array;
  initialCounts: Float64Array;
  isEnabledExact: number;
  // Per atom: 1 or 0 for each state, or for an action each step and then each state's stuttering
  // step, and 2 where the interpreter answers.
  tables: Uint8Array[];
  fromSteps: Float64Array;
  // Why the engine answers an atom not at all, or "".
  unknown: string[];
}

// The search up to the state the native engine stopped at, or all of it with temporal properties.
interface NativeCheckpoint {
  // The state being expanded, the states before it, the generated and initial generated counts,
  // and the collisions; only the collisions where nothing is handed over.
  counts: Float64Array;
  outDegrees?: Float64Array;
  parents?: Int32Array;
  words?: Int32Array;
  strings?: string[];
  keyWords?: Int32Array;
  keyStrings?: string[];
  keyWidth?: number;
  graph?: NativeGraph;
}

// What the native engine did with a model (binding/check.rs).
export type NativeOutcome =
  | { status: "unavailable" | "declined"; reason: string }
  // A self-check failed.
  | { status: "invariant"; reason: string }
  | {
      status: "complete";
      reason: string;
      // The generated, distinct and initial counts, the depth, the values and the collisions.
      counts: Float64Array;
      outDegrees: Float64Array;
      fingerprints: BigInt64Array;
      checkpoint?: NativeCheckpoint;
    }
  | ({ status: "stopped"; reason: string } & NativeCheckpoint);

// The contract between this loader and the addon, ABI_VERSION in its lib.rs.
const ABI_VERSION = 2;

export const ADDON_FILE = "prove-it-engine.node";

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
  if (url === undefined) return undefined;
  const path = decodeURIComponent(url.pathname);
  return process.platform === "win32" ? path.slice(1) : path;
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
  const addon = module.exports as NativeAddon;
  const version = addon.abiVersion();
  return version === ABI_VERSION
    ? addon
    : `${addonPath} has ABI version ${version}, not ${ABI_VERSION}`;
};

const loaded: { addon?: NativeAddon | string } = {};

// The addon, loaded on first use, or why it can't be loaded.
export const getNativeAddon = () => {
  loaded.addon ??=
    typeof globalThis.process?.dlopen === "function" ? loadAddon() : "no process.dlopen";
  return loaded.addon;
};

type NativeCallbacks = Pick<
  EngineInput,
  "onProgress" | "onInitialStatesStarted" | "onInitialStates" | "onPrint"
>;

// Loads the addon on first use, and lowers the model only once it has. The TypeScript engine checks
// what it declines, and everything when it can't be loaded.
export const checkNatively = (
  lower: () => IrOutcome,
  callbacks: NativeCallbacks,
): NativeOutcome => {
  const addon = getNativeAddon();
  if (typeof addon === "string") return { status: "unavailable", reason: addon };
  const lowered = lower();
  if (!("ir" in lowered)) return { status: "declined", reason: `the engine IR: ${lowered.reason}` };
  const settings = Int32Array.of(
    globalThis.process?.env?.PROVE_IT_MEMO === "off" ? 1 : 0,
    getEnvironmentFlag("PROVE_IT_EPOCH_CHECK") ? 1 : 0,
    getStopAt(),
    getEnvironmentFlag("PROVE_IT_FP_VERIFY") ? 1 : 0,
    getEnvironmentFlag("PROVE_IT_LIVE_CHECK") ? 1 : 0,
  );
  return addon.check(
    lowered.ir,
    settings,
    globalThis.process?.env?.PROVE_IT_STATE_LOG ?? "",
    (kind, a, b, c, d) => {
      if (kind === 0) callbacks.onInitialStatesStarted();
      else if (kind === 1) callbacks.onProgress?.({ kind: "initial-states-progress", count: a });
      else if (kind === 2) callbacks.onInitialStates(a, b);
      else {
        callbacks.onProgress?.({
          kind: "progress",
          statistics: { generatedStates: a, distinctStates: b, queuedStates: c, depth: d },
        });
      }
    },
    // What Print or PrintT printed, written by the interpreter's printer.
    (width, words, strings) => {
      const values = createStateDecoder(width)({ words, strings, count: 1 })[0];
      callbacks.onPrint(values.map(formatPrinted).join("  "));
    },
  );
};

// The states the native engine found, as ids of this process's engine store, which the
// interpreter's hand-over reads.
const decodeStates = (words: Int32Array, strings: string[], width: number, count: number) => {
  const encoded: EncodedStates = { words, strings, count };
  const states = createStateDecoder(width)(encoded);
  const ids = new Int32Array(states.length * width);
  states.forEach((state, index) => {
    state.forEach((value, variable) => {
      ids[index * width + variable] = fromValue(value);
    });
  });
  return ids;
};

// Answers the liveness checker from the native engine's tables, as live.ts's oracle answers it
// from the TypeScript engine's states, and leaves the rest to the interpreter.
const createNativeOracle = (
  graph: NativeGraph,
  edgeOffsets: Int32Array,
  atoms: LiveExpression[],
  getIndex: (state: Value[]) => number | undefined,
): LiveOracle => {
  const positions = new Map(atoms.map((atom, position) => [atom, position]));
  const edgeCount = graph.edges.length;
  const reported = new Set<number>();
  const report = { isReported: false };
  const toAnswer = (answer: number | undefined) =>
    answer === 1 ? true : answer === 0 ? false : undefined;
  return (expression, state, next) => {
    const position = positions.get(expression);
    const index = position === undefined ? undefined : getIndex(state);
    if (position === undefined || index === undefined) return undefined;
    const unknown = graph.unknown[position];
    if (unknown !== "") {
      if (!reported.has(position)) {
        reported.add(position);
        reportEngine(`leaves a temporal predicate to the interpreter: ${unknown}`);
      }
      return undefined;
    }
    const table = graph.tables[position];
    if (expression.kind !== "Action") {
      const isFromSteps = graph.fromSteps[position] === 1;
      if (
        expression.kind === "Enabled" &&
        index < graph.expanded &&
        !report.isReported &&
        (isFromSteps || graph.isEnabledExact === 0)
      ) {
        report.isReported = true;
        reportEngine(
          isFromSteps
            ? "answers ENABLED from the steps its search took"
            : "runs each action ENABLED asks about: its search evaluated conjuncts TLC's ENABLED walks",
        );
      }
      return toAnswer(table[index]);
    }
    const nextIndex = next && getIndex(next);
    if (nextIndex === undefined) return undefined;
    if (nextIndex === index) return toAnswer(table[edgeCount + index]);
    if (index >= graph.expanded) return undefined;
    for (let edge = edgeOffsets[index]; edge < edgeOffsets[index + 1]; edge++) {
      if (graph.edges[edge] === nextIndex) return toAnswer(table[edge]);
    }
    return undefined;
  };
};

// The search the native engine handed over, with the states decoded into the engine's store for
// the interpreter to take over, or undefined when it handed over nothing.
const toCheckpoint = (
  native: NativeCheckpoint,
  width: number,
  atoms: LiveExpression[],
): EngineCheckpoint | undefined => {
  if (!native.parents || !native.words || !native.strings || !native.outDegrees) return undefined;
  resetStore();
  resetFingerprints();
  const counts = native.counts;
  const count = counts[1];
  const states = decodeStates(native.words, native.strings, width, count);
  const base = {
    expanding: counts[0],
    count,
    generated: counts[2],
    initialGenerated: counts[3],
    outDegrees: Array.from(native.outDegrees),
    states,
    parents: native.parents,
    width,
  };
  const graph = native.graph;
  if (graph) {
    const expanded = graph.expanded;
    const edgeOffsets = graph.counts.subarray(2 * expanded);
    return {
      ...base,
      initialCounts: Array.from(graph.initialCounts),
      graph: {
        expanded,
        successorCounts: graph.counts.subarray(0, expanded),
        newCounts: graph.counts.subarray(expanded, 2 * expanded),
        edgeOffsets,
        edges: graph.edges,
        labels: graph.labels,
      },
      createLiveOracle: (getIndex) => createNativeOracle(graph, edgeOffsets, atoms, getIndex),
    };
  }
  const keyWidth = native.keyWidth;
  const keys =
    keyWidth === undefined
      ? undefined
      : decodeStates(native.keyWords!, native.keyStrings!, keyWidth, count);
  const stored = keys ?? states;
  const storedWidth = keyWidth ?? width;
  // The index of each state's key, built when the interpreter first asks whether a successor is
  // among them.
  const lookup: { indices?: Map<string, number> } = {};
  const getIndices = () => {
    if (lookup.indices) return lookup.indices;
    const indices = new Map<string, number>();
    for (let index = 0; index < count; index++) {
      indices.set(stored.subarray(index * storedWidth, (index + 1) * storedWidth).join(), index);
    }
    lookup.indices = indices;
    return indices;
  };
  const findState = (key: Value[]) => {
    const ids: number[] = [];
    for (const value of key) {
      const id = fromEnumeratedValue(value);
      if (id === undefined) return undefined;
      ids.push(id);
    }
    return getIndices().get(ids.join()) ?? -1;
  };
  return {
    ...base,
    ...(keys && { keys, keyWidth }),
    findState: (key) => {
      try {
        return findState(key);
      } catch (error) {
        if (error instanceof Bailout) return undefined;
        throw error;
      }
    },
  };
};

// A search the native engine completed, as runEngine returns one: with temporal properties, the
// whole search for the interpreter to replay.
export const toEngineResult = (
  outcome: Extract<NativeOutcome, { status: "complete" }>,
  width: number,
  atoms: LiveExpression[],
): EngineResult => {
  const counts = outcome.counts;
  return {
    generatedStates: counts[0],
    distinctStates: counts[1],
    initialStates: { generated: counts[2], distinct: counts[3] },
    depth: counts[4],
    valueCount: counts[5],
    outDegrees: Array.from(outcome.outDegrees),
    getFingerprints: () => outcome.fingerprints,
    threads: 1,
    checkpoint: outcome.checkpoint && toCheckpoint(outcome.checkpoint, width, atoms),
  };
};

// What the native engine's search stopping throws, as runEngine throws it: a Bailout with the
// search for the interpreter to go on from, or an EngineInvariantError where a self-check failed.
export const toStop = (
  outcome: Extract<NativeOutcome, { status: "stopped" | "invariant" }>,
  width: number,
  atoms: LiveExpression[],
): Error => {
  if (outcome.status === "invariant") return new EngineInvariantError(outcome.reason);
  const bailout = new Bailout(outcome.reason);
  bailout.checkpoint = toCheckpoint(outcome, width, atoms);
  return bailout;
};

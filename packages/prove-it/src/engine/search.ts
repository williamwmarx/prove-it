// The engine's breadth-first search. It explores states in TLC's order, counts them as TLC does,
// and reports a complete search. Anything else it meets (a violation, an error, a feature it
// doesn't implement) ends the run with a Bailout carrying a checkpoint, from which the reference
// interpreter goes on.
//
// A search that runs long enough hands its levels to worker threads (parallel.ts), which keep TLC's
// order, and takes them back to finish alone if a worker stops.

import type { CheckProgress } from "../check";
import type { ModelConfig } from "../config";
import { EngineInvariantError } from "../errors";
import type { Environment } from "../evaluate";
import type { TlcVersion } from "../tlc/version";
import type { Value } from "../values";
import { resetAssigned, shortcuts } from "./action";
import {
  DISTINCT_SLOT,
  EPOCH,
  LEVEL_SLOT,
  LOC,
  NEXT_LEVEL_SLOT,
  nextEpoch,
  resetCompileState,
  setCurrent,
  setNext,
  tlc,
} from "./compile";
import {
  createEngineContext,
  type EngineProperties,
  type EngineSpec,
  holdsAll,
  holdsAllChanged,
} from "./context";
import { fromEnumeratedValue } from "./convert";
import { getStateFingerprints, resetFingerprints } from "./fingerprint";
import { createLiveOracle, type EnabledActions, type LiveOracle } from "./live";
import {
  createSharedSearch,
  createStorageBlock,
  getReadyCount,
  type GoMessage,
  runLevel,
  type SearchViews,
  seedState,
  stopWorkers,
} from "./parallel";
import { getEnvironmentFlag, getStopAt, isStoreTraced } from "./settings";
import { writeStateLog } from "./state-log";
import { bail, Bailout, freezeTexts, getValueCount, int, resetStore, shareStore } from "./store";
import { createCanonicalizer, type NamedPermutation } from "./symmetry";
import { type EngineWorkers, spawnEngineWorkers } from "./workers";

export type { EngineSpec } from "./context";

export interface EngineInput {
  config: ModelConfig;
  environment: Environment;
  spec: EngineSpec;
  isWarningEnabled: boolean;
  tlcOrder: number[];
  onProgress: ((progress: CheckProgress) => void) | undefined;
  // Called as the engine starts computing the initial states and once it has, so the caller
  // reports them.
  onInitialStatesStarted: () => void;
  onInitialStates: (generated: number, distinct: number) => void;
  // Whether the interpreter's liveness checker takes an initial state, which TLC adds to it as it
  // computes the initial states.
  isLiveInitialState: ((state: Int32Array) => boolean) | undefined;
  // Prints a line the spec prints.
  onPrint: (text: string) => void;
  startedAt: number;
  properties: EngineProperties;
  // The symmetry group, as the model values each permutation moves.
  symmetry: NamedPermutation[] | undefined;
  // Whether to record the state graph, for temporal properties the interpreter checks.
  isRecordingGraph: boolean;
  // How many threads may search, and what a worker needs to build the spec.
  workers: number;
  source: string;
  modules: [string, string | undefined][];
  version: TlcVersion | undefined;
}

// The steps of a search, for the interpreter to check temporal properties on: for each of the first
// `expanded` states, how many successors it generated, how many of them were new, and the states, in
// the model, its steps went to in the order generated, between edgeOffsets[i] and edgeOffsets[i + 1].
// A search of spec.actions labels each step with the position of the action that took it.
export interface EngineGraph {
  expanded: number;
  successorCounts: Int32Array;
  newCounts: Int32Array;
  edgeOffsets: Int32Array;
  edges: Int32Array;
  labels: Int32Array | undefined;
}

// The search up to the state the engine was expanding when it stopped: the states found before
// that expansion, as ids, with their parents and the counts so far. With a graph, the interpreter
// replays the steps of the states the engine expanded rather than expanding them again, answering
// its liveness checker from the engine's states, given the index of each state and the actions
// ENABLED of an action asks about.
export interface EngineCheckpoint {
  graph?: EngineGraph;
  // With a graph, how many initial states the search had generated when it found each initial
  // state it kept, for the counts as the interpreter adds that state to its liveness checker.
  initialCounts?: number[];
  createLiveOracle?: (
    getIndex: (state: Value[]) => number | undefined,
    getEnabledActions: EnabledActions,
  ) => LiveOracle;
  // Without a graph, the index of the state whose key, what TLC fingerprints, has these values, -1
  // for none, or undefined when the engine can't tell.
  findState?: (key: Value[]) => number | undefined;
  // What TLC fingerprints in place of each state, when that isn't the state: its representative
  // under symmetry, or its view, `keyWidth` ids each.
  keys?: Int32Array;
  keyWidth?: number;
  expanding: number;
  count: number;
  generated: number;
  initialGenerated: number;
  outDegrees: number[];
  states: Int32Array;
  parents: Int32Array;
  width: number;
}

export interface EngineResult {
  generatedStates: number;
  distinctStates: number;
  depth: number;
  outDegrees: number[];
  initialStates: { generated: number; distinct: number };
  getFingerprints: () => BigInt64Array;
  valueCount: number;
  threads: number;
  // A complete search the interpreter is to replay, when it checks temporal properties.
  checkpoint: EngineCheckpoint | undefined;
}

const MAXIMUM_GRAPH_STATES = 4_000_000;
const OUT_DEGREE_BUCKETS = 32;
const PROGRESS_INTERVAL = 60_000;
// Workers start once the search has run this long, and take over a level of at least this many
// states, since a worker takes a while to build the spec and a small level isn't worth sharing.
const WORKER_SPAWN_MS = 150;
const MINIMUM_SHARED_LEVEL = 2048;

export const runEngine = (input: EngineInput): EngineResult => {
  const environment = input.environment;
  const config = input.config;
  resetStore();
  resetCompileState();
  if (getEnvironmentFlag("PROVE_IT_SHARED")) shareStore();
  resetFingerprints();
  resetAssigned();
  shortcuts.isPastWalk = false;
  const context = createEngineContext(
    environment,
    config,
    input.spec,
    input.isWarningEnabled,
    input.properties,
    !input.isRecordingGraph,
  );
  const width = context.width;
  const constraints = context.constraints;
  const constraintVars = context.constraintVars;
  const actionConstraints = context.actionConstraints;
  const invariants = context.invariants;
  const invariantVars = context.invariantVars;
  const actionProperties = context.actionProperties;
  const view = context.view;
  const canonicalize = input.symmetry
    ? createCanonicalizer(input.symmetry, input.tlcOrder)
    : undefined;

  // The states found so far, `width` ids each, in TLC's order. The search tells states apart by
  // their key: the state itself, or what TLC fingerprints in its place, kept in separateKeys: with
  // a VIEW the id of the view's value, and under symmetry the state's representative.
  const hasSeparateKeys = view !== undefined || canonicalize !== undefined;
  const keyWidth = view ? 1 : width;
  let states = new Int32Array(Math.max(1, width) * 16384);
  let separateKeys = new Int32Array(hasSeparateKeys ? keyWidth * 1024 : 0);
  let stateCount = 0;
  let parents = new Int32Array(16384);
  // An open-addressing table of [hash, state index] pairs, so that a probe compares hashes without
  // a second random read.
  let table = new Int32Array(2 << 12).fill(-1);
  let tableMask = (1 << 12) - 1;
  const getKeys = () => (hasSeparateKeys ? separateKeys : states);
  const separateKey = new Int32Array(1);

  const hashState = (source: Int32Array, offset: number) => {
    let hash = 0x811c9dc5;
    for (let index = 0; index < keyWidth; index++)
      hash = Math.imul(hash ^ source[offset + index], 0x01000193);
    hash ^= hash >>> 13;
    hash = Math.imul(hash, 0x5bd1e995);
    return hash ^ (hash >>> 15);
  };

  // The hash of the key findSlot looked up last.
  let lastHash = 0;

  const growTable = () => {
    const next = new Int32Array(table.length * 2).fill(-1);
    const mask = table.length - 1;
    for (let slot = 0; slot <= tableMask; slot++) {
      const stored = table[2 * slot + 1];
      if (stored === -1) continue;
      const hash = table[2 * slot];
      let nextSlot = hash & mask;
      while (next[2 * nextSlot + 1] !== -1) nextSlot = (nextSlot + 1) & mask;
      next[2 * nextSlot] = hash;
      next[2 * nextSlot + 1] = stored;
    }
    table = next;
    tableMask = mask;
  };

  // The key of a complete state, which is in the current register.
  // TLC fingerprints the view of the representative when it has both.
  const getKey = (state: Int32Array) => {
    if (!canonicalize) {
      if (!view) return state;
      separateKey[0] = view();
      return separateKey;
    }
    representative.set(state);
    canonicalize(representative);
    if (!view) return representative;
    const epoch = EPOCH;
    setCurrent(representative);
    separateKey[0] = view();
    setCurrent(state, epoch);
    return separateKey;
  };
  const representative = new Int32Array(width);

  // The slot of a key in the table: either the slot that holds it, or the empty one to put it in.
  // It keeps the key's hash for addState, which follows it for a new key.
  const findSlot = (key: Int32Array) => {
    const hash = hashState(key, 0);
    lastHash = hash;
    const keys = getKeys();
    for (let slot = hash & tableMask; ; slot = (slot + 1) & tableMask) {
      const stored = table[2 * slot + 1];
      if (stored === -1) return slot;
      if (table[2 * slot] !== hash) continue;
      const offset = stored * keyWidth;
      let isEqual = true;
      for (let index = 0; index < keyWidth; index++) {
        if (keys[offset + index] !== key[index]) {
          isEqual = false;
          break;
        }
      }
      if (isEqual) return slot;
    }
  };

  const addState = (source: Int32Array, key: Int32Array, slot: number, parent: number) => {
    if ((stateCount + 1) * width > states.length) {
      const next = new Int32Array(states.length * 4);
      next.set(states);
      states = next;
    }
    if (stateCount >= parents.length) {
      const next = new Int32Array(parents.length * 4);
      next.set(parents);
      parents = next;
    }
    if (hasSeparateKeys && (stateCount + 1) * keyWidth > separateKeys.length) {
      const nextKeys = new Int32Array(separateKeys.length * 2);
      nextKeys.set(separateKeys);
      separateKeys = nextKeys;
    }
    states.set(source, stateCount * width);
    if (hasSeparateKeys) separateKeys.set(key, stateCount * keyWidth);
    parents[stateCount] = parent;
    table[2 * slot] = lastHash;
    table[2 * slot + 1] = stateCount;
    stateCount++;
    if (stateCount * 2 > tableMask + 1) growTable();
  };

  let generated = 0;
  let initialGenerated = 0;
  let depth = 0;

  // TLCGet("distinct") counts the states found so far, and a new state before its checks.
  const setDistinct = (count: number) => {
    tlc.distinct = count;
    if (tlc.isDistinctRead) LOC[DISTINCT_SLOT] = int(count);
  };
  // What the spec prints while the engine computes the initial states or expands a state goes out
  // once that's done: if the engine hands over, the interpreter does it again.
  const flushOutput = () => {
    const lines = tlc.output;
    if (lines.length === 0) return;
    tlc.output = [];
    for (const line of lines) {
      if (typeof line === "string") input.onPrint(line);
      else input.onProgress?.({ kind: "initial-states-progress", count: line });
    }
  };

  // --- initial states ---
  const initialCounts: number[] = [];
  const current = new Int32Array(width).fill(-1);
  const next = new Int32Array(width).fill(-1);
  // The initial predicate assigns the current state in place, so nothing caches by its epoch.
  setCurrent(current, 0);
  setNext(next);
  // TLCGet("level") is 0 in the initial predicate and 1 in the checks of an initial state.
  LOC[LEVEL_SLOT] = int(0);
  setDistinct(0);
  input.onInitialStatesStarted();
  context.initStep(() => {
    for (let index = 0; index < width; index++)
      if (current[index] === -1) bail("an initial state that isn't complete");
    LOC[LEVEL_SLOT] = int(1);
    if (initialGenerated > 1 && (initialGenerated & (initialGenerated - 1)) === 0) {
      // A count after what the initial predicate printed waits with it.
      if (tlc.output.length > 0) tlc.output.push(initialGenerated);
      else input.onProgress?.({ kind: "initial-states-progress", count: initialGenerated });
    }
    const state = current;
    generated++;
    initialGenerated++;
    const isInModel = holdsAll(constraints);
    const key = isInModel ? getKey(state) : undefined;
    const slot = key ? findSlot(key) : -1;
    const isSeen = isInModel && table[2 * slot + 1] !== -1;
    if (!isSeen) {
      if (isInModel) setDistinct(stateCount + 1);
      if (isInModel && input.isLiveInitialState?.(state) === false) {
        bail("an initial state the liveness checker fails on");
      }
      if (!holdsAll(context.initialInvariants)) bail("an invariant violated in an initial state");
      if (!holdsAll(context.initialPredicates)) bail("a property violated in an initial state");
      if (isInModel) {
        addState(state, key!, slot, -1);
        if (input.isRecordingGraph) initialCounts.push(initialGenerated);
        depth = 1;
      }
    }
    LOC[LEVEL_SLOT] = int(0);
  });
  flushOutput();
  const initialStates = { generated: initialGenerated, distinct: stateCount };
  input.onInitialStates(initialGenerated, stateCount);

  // --- next states ---
  const outDegrees = new Array<number>(OUT_DEGREE_BUCKETS).fill(0);
  let levelEnd = stateCount;
  let level = 1;
  let newStates = 0;
  let successors = 0;
  let expanding = 0;
  let progressAt = performance.now() + 3000;
  const reportProgress = () => {
    if (!input.onProgress || performance.now() < progressAt) return;
    progressAt = performance.now() + PROGRESS_INTERVAL;
    input.onProgress({
      kind: "progress",
      statistics: {
        generatedStates: generated,
        distinctStates: stateCount,
        queuedStates: stateCount - expanding - 1,
        depth: Math.max(depth, 1),
      },
    });
  };

  const actionSteps = input.isRecordingGraph ? context.actionSteps : undefined;
  const graph = input.isRecordingGraph
    ? {
        successorCounts: new Int32Array(1024),
        newCounts: new Int32Array(1024),
        edgeOffsets: new Int32Array(1025),
        edges: new Int32Array(4096),
        labels: actionSteps && new Int32Array(4096),
        edgeCount: 0,
      }
    : undefined;
  // The position of the action whose steps the search is taking.
  let action = 0;
  const recordEdge = (target: number) => {
    const recording = graph!;
    if (recording.edgeCount === recording.edges.length) {
      const capacity = recording.edges.length * 2;
      const nextEdges = new Int32Array(capacity);
      nextEdges.set(recording.edges);
      recording.edges = nextEdges;
      if (recording.labels) {
        const nextLabels = new Int32Array(capacity);
        nextLabels.set(recording.labels);
        recording.labels = nextLabels;
      }
    }
    if (recording.labels) recording.labels[recording.edgeCount] = action;
    recording.edges[recording.edgeCount++] = target;
  };
  const recordExpansion = (index: number) => {
    const recording = graph!;
    if (index >= recording.successorCounts.length) {
      const capacity = recording.successorCounts.length * 2;
      const grow = (array: Int32Array, length: number) => {
        const nextArray = new Int32Array(length);
        nextArray.set(array);
        return nextArray;
      };
      recording.successorCounts = grow(recording.successorCounts, capacity);
      recording.newCounts = grow(recording.newCounts, capacity);
      recording.edgeOffsets = grow(recording.edgeOffsets, capacity + 1);
    }
    recording.successorCounts[index] = successors;
    recording.newCounts[index] = newStates;
    recording.edgeOffsets[index + 1] = recording.edgeCount;
  };

  // The epoch of the state being expanded, which its successors put back once checked.
  let expansionEpoch = 0;
  // The ids of the level of the state being expanded and of its successors, for TLCGet("level").
  let levelId = 0;
  let nextLevelId = 0;
  const setSuccessorCurrent = (successor: Int32Array, successorEpoch: number) => {
    setCurrent(successor, successorEpoch);
    LOC[LEVEL_SLOT] = nextLevelId;
  };
  const setExpandedCurrent = () => {
    setCurrent(current, expansionEpoch);
    LOC[LEVEL_SLOT] = levelId;
  };
  const visitSuccessor = () => {
    successors++;
    generated++;
    const successor = next;
    const successorEpoch = nextEpoch();
    setSuccessorCurrent(successor, successorEpoch);
    // The state being expanded is in the model, so each constraint and invariant held of it.
    const isStateInModel = holdsAllChanged(constraints, constraintVars, successor, current);
    const key = isStateInModel ? getKey(successor) : undefined;
    setExpandedCurrent();
    const isInModel = isStateInModel && holdsAll(actionConstraints);
    const slot = isInModel ? findSlot(key!) : -1;
    const isNew = isInModel && table[2 * slot + 1] === -1;
    if (isNew) setDistinct(stateCount + 1);
    if (!isInModel || isNew) {
      setSuccessorCurrent(successor, successorEpoch);
      const holds = holdsAllChanged(invariants, invariantVars, successor, current);
      setExpandedCurrent();
      if (!holds) bail("an invariant violated");
    }
    if (graph && isInModel) recordEdge(isNew ? stateCount : table[2 * slot + 1]);
    if (!holdsAll(actionProperties)) bail("an action property violated");
    if (!isNew) return;
    addState(successor, key!, slot, expanding);
    newStates++;
    depth = level + 1;
  };

  // PROVE_IT_LIVE_CHECK=1 takes each state's steps through nextStep too, and throws unless the
  // actions took the same steps in the same order.
  const checkedSuccessors: Int32Array[] | undefined =
    actionSteps && getEnvironmentFlag("PROVE_IT_LIVE_CHECK") ? [] : undefined;
  const collectSuccessor = () => {
    checkedSuccessors!.push(next.slice());
  };

  const onSuccessor = () => {
    for (let index = 0; index < width; index++) {
      if (next[index] === -1) bail("a successor that isn't complete");
    }
    const checked = checkedSuccessors?.[successors];
    if (checkedSuccessors && !checked?.every((id, variable) => id === next[variable])) {
      throw new EngineInvariantError("the actions took other steps than the next-state relation");
    }
    visitSuccessor();
  };

  // PROVE_IT_STOP_AT=k stops the search before it expands state k, as it stops for anything it
  // doesn't handle, so the interpreter goes on from there. It searches on one thread then.
  const stopAt = getStopAt();

  // --- workers ---
  const canShare =
    input.workers > 1 &&
    !input.isRecordingGraph &&
    !view &&
    !canonicalize &&
    typeof SharedArrayBuffer === "function" &&
    typeof Atomics.wait === "function" &&
    !getEnvironmentFlag("PROVE_IT_SERIAL") &&
    stopAt === -1 &&
    !isStoreTraced();
  // How many states the search had found when the workers joined.
  let seeded = 0;
  const parallel: { workers?: EngineWorkers; isSpawned: boolean; threads: number } = {
    isSpawned: false,
    threads: 1,
  };

  // Searches the levels from [levelStart, levelEnd) on with the workers. Returns whether it
  // finished the search; otherwise a worker stopped, and the states and counts are as they were at
  // the start of the level it stopped in, for this thread to go on alone.
  const searchInParallel = (workers: EngineWorkers | undefined): boolean => {
    const store = shareStore();
    freezeTexts();
    const views: SearchViews = createSharedSearch(config, width);
    seeded = stateCount;
    const block = createStorageBlock();
    for (let index = 0; index < stateCount; index++) {
      seedState(views, states.subarray(index * width, (index + 1) * width), index, block);
    }
    const go: GoMessage = { type: "go", store, search: views.buffers };
    workers?.post(go);
    const keys = views.keys;
    tlc.isShared = true;
    try {
      for (;;) {
        const start = expanding;
        const end = levelEnd;
        const outcome = runLevel(context, views, start, end);
        parallel.threads = Math.max(parallel.threads, getReadyCount(views) + 1);
        if (outcome.isAborted) return false;
        const added = outcome.added;
        const childCounts = new Array<number>(end - start).fill(0);
        for (let position = 0; position < added.length; position++) {
          const stored = added[position];
          childCounts[keys[stored * 2] - start]++;
          views.order[end + position] = stored;
        }
        for (const count of childCounts) outDegrees[Math.min(count, OUT_DEGREE_BUCKETS - 1)]++;
        generated += outcome.generated;
        expanding = end;
        stateCount = end + added.length;
        levelEnd = stateCount;
        if (added.length > 0) {
          level++;
          depth = level;
        }
        reportProgress();
        if (added.length === 0) return true;
      }
    } finally {
      tlc.isShared = false;
      stopWorkers(views);
      reloadFrom(views);
      setDistinct(stateCount);
    }
  };

  // Takes the states back from the shared storage in TLC's order, with their parents, for the
  // fingerprints of a finished search or for this thread to go on alone.
  const reloadFrom = (views: SearchViews) => {
    const count = stateCount;
    const storage = views.storage;
    const keys = views.keys;
    const reloaded = new Int32Array(Math.max(1, count * width));
    const reloadedParents = new Int32Array(Math.max(1, count));
    for (let index = 0; index < count; index++) {
      const stored = views.order[index];
      reloaded.set(storage.subarray(stored * width, (stored + 1) * width), index * width);
      reloadedParents[index] = index < seeded ? parents[index] : keys[stored * 2];
    }
    states = reloaded;
    parents = reloadedParents;
    let capacity = 1 << 12;
    while (capacity < count * 2) capacity *= 2;
    table = new Int32Array(2 * capacity).fill(-1);
    tableMask = capacity - 1;
    for (let index = 0; index < count; index++) {
      const hash = hashState(states, index * width);
      let slot = hash & tableMask;
      while (table[2 * slot + 1] !== -1) slot = (slot + 1) & tableMask;
      table[2 * slot] = hash;
      table[2 * slot + 1] = index;
    }
  };

  // The index of the state, among the first `count`, whose key has these values, or -1, or
  // undefined when the engine can't tell, for a value the interpreter holds lazily, or one the
  // engine can't hold.
  const findStateBefore = (key: Value[], count: number) => {
    const ids = new Int32Array(keyWidth);
    try {
      for (let index = 0; index < keyWidth; index++) {
        const id = fromEnumeratedValue(key[index]);
        if (id === undefined) return undefined;
        ids[index] = id;
      }
    } catch (error) {
      if (error instanceof Bailout) return undefined;
      throw error;
    }
    const stored = table[2 * findSlot(ids) + 1];
    return stored < count ? stored : -1;
  };

  // The first `count` states and the steps of the first `expanded` of them, for the interpreter to
  // replay, from the initial states on. It rebuilds the state at `expanding` its own way.
  const getGraphCheckpoint = (
    expanded: number,
    count: number,
    expandingAt: number,
  ): EngineCheckpoint => {
    const recording = graph!;
    const edgeCount = recording.edgeOffsets[expanded];
    const stored = states.slice(0, count * width);
    // TLC's ENABLED walks what the shortcut evaluated, so only a search that took no shortcut past
    // a walk found the successors ENABLED finds.
    const isEnabledExact = !shortcuts.isPastWalk;
    const edges = recording.edges.slice(0, edgeCount);
    const labels = recording.labels?.slice(0, edgeCount);
    return {
      expanding: expandingAt,
      count,
      generated: initialGenerated,
      initialGenerated,
      initialCounts,
      outDegrees: new Array<number>(OUT_DEGREE_BUCKETS).fill(0),
      states: stored,
      parents: parents.slice(0, count),
      width,
      graph: {
        expanded,
        successorCounts: recording.successorCounts,
        newCounts: recording.newCounts,
        edgeOffsets: recording.edgeOffsets,
        edges,
        labels,
      },
      createLiveOracle: (getIndex, getEnabledActions) =>
        createLiveOracle(
          context.compiler,
          {
            states: stored,
            expanded,
            edgeOffsets: recording.edgeOffsets,
            edges,
            labels,
            isEnabledExact,
          },
          getIndex,
          getEnabledActions,
        ),
    };
  };

  // TLC's fingerprints of the first `count` states' keys.
  const getFingerprints = (count: number) =>
    view
      ? getStateFingerprints(separateKeys, count, 1, [0])
      : getStateFingerprints(
          hasSeparateKeys ? separateKeys : states,
          count,
          width,
          input.tlcOrder,
          parents,
        );

  // The counts before the state being expanded, which a bailout hands to the interpreter: it
  // expands that state again from there, finding what the engine stopped at.
  let checkpointCount = 0;
  let checkpointGenerated = 0;
  const startedAt = performance.now();
  try {
    for (expanding = 0; expanding < stateCount; expanding++) {
      if (expanding === levelEnd) {
        level++;
        levelEnd = stateCount;
        if (canShare && !tlc.isUsed) {
          const elapsed = performance.now() - startedAt;
          if (!parallel.isSpawned && elapsed >= WORKER_SPAWN_MS) {
            parallel.isSpawned = true;
            parallel.workers = spawnEngineWorkers(input.workers - 1, {
              source: input.source,
              config,
              modules: input.modules,
              isWarningEnabled: input.isWarningEnabled,
              version: input.version,
            });
          }
          const workers = parallel.workers;
          if (
            workers &&
            workers.getStartedCount() > 0 &&
            levelEnd - expanding >= MINIMUM_SHARED_LEVEL &&
            searchInParallel(workers)
          ) {
            break;
          }
          // A level a worker stopped in runs here from its start, with the states and counts as
          // they were then.
          if (expanding >= stateCount) break;
        }
      }
      checkpointCount = stateCount;
      checkpointGenerated = generated;
      if (expanding === stopAt) bail("stopped where PROVE_IT_STOP_AT asked");
      // The interpreter checks temporal properties on the graph as it grows, so it may find a
      // violation early in a state space the engine would search without end. Past this many
      // states, the engine hands its graph over and the interpreter goes on.
      if (graph && stateCount > MAXIMUM_GRAPH_STATES) bail("a state graph too large to keep");
      const offset = expanding * width;
      for (let variable = 0; variable < width; variable++)
        current[variable] = states[offset + variable];
      next.fill(-1);
      resetAssigned();
      newStates = 0;
      successors = 0;
      expansionEpoch = nextEpoch();
      levelId = int(level);
      nextLevelId = int(level + 1);
      setExpandedCurrent();
      LOC[NEXT_LEVEL_SLOT] = nextLevelId;
      setNext(next);
      if (!actionSteps) context.nextStep(onSuccessor);
      else {
        if (checkedSuccessors) {
          checkedSuccessors.length = 0;
          context.nextStep(collectSuccessor);
        }
        for (action = 0; action < actionSteps.length; action++) actionSteps[action](onSuccessor);
        if (checkedSuccessors && checkedSuccessors.length !== successors) {
          throw new EngineInvariantError(
            "the actions took other steps than the next-state relation",
          );
        }
      }
      if (successors === 0 && config.checkDeadlock) bail("deadlock");
      if (graph) recordExpansion(expanding);
      outDegrees[Math.min(newStates, OUT_DEGREE_BUCKETS - 1)]++;
      flushOutput();
      if ((expanding & 0xff) === 0) reportProgress();
    }
  } catch (error) {
    // With a graph, the interpreter replays the steps of the states before the one the engine was
    // expanding, counting them again. It searches a graph too large to keep from the start, since
    // its liveness checker may stop in the first states, before it has taken all of them over.
    if (error instanceof Bailout && !(graph && checkpointCount > MAXIMUM_GRAPH_STATES)) {
      const checkpoint: EngineCheckpoint = graph
        ? getGraphCheckpoint(expanding, checkpointCount, expanding)
        : {
            expanding,
            count: checkpointCount,
            generated: checkpointGenerated,
            initialGenerated,
            outDegrees: outDegrees.slice(),
            states: states.slice(0, checkpointCount * width),
            parents: parents.slice(0, checkpointCount),
            width,
            ...(hasSeparateKeys && {
              keys: separateKeys.slice(0, checkpointCount * keyWidth),
              keyWidth,
            }),
            findState: (key) => findStateBefore(key, checkpointCount),
          };
      error.checkpoint = checkpoint;
      writeStateLog(() => ({
        variables: environment.variables,
        states: checkpoint.states,
        parents: checkpoint.parents,
        count: checkpointCount,
        fingerprints: getFingerprints(checkpointCount),
        edges: undefined,
        labels: undefined,
        stopped: error.message,
        expanding,
      }));
    }
    throw error;
  } finally {
    parallel.workers?.terminate();
  }
  writeStateLog(() => ({
    variables: environment.variables,
    states,
    parents,
    count: stateCount,
    fingerprints: getFingerprints(stateCount),
    edges: graph?.edges.subarray(0, graph.edgeCount),
    labels: graph?.labels,
    stopped: undefined,
    expanding: stateCount,
  }));

  return {
    generatedStates: generated,
    distinctStates: stateCount,
    depth: generated === 0 ? 0 : Math.max(depth, 1),
    outDegrees,
    initialStates,
    getFingerprints: () => getFingerprints(stateCount),
    valueCount: getValueCount(),
    threads: parallel.threads,
    checkpoint: graph && getGraphCheckpoint(stateCount, stateCount, 0),
  };
};

export const isBailout = (error: unknown): error is Bailout => error instanceof Bailout;

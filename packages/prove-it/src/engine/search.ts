// The engine's breadth-first search. It explores states in TLC's order, counts them as TLC does,
// and reports a complete search. Anything else it meets (a violation, an error, a feature it
// doesn't implement) ends the run with a Bailout carrying a checkpoint, from which the reference
// interpreter goes on.
//
// A search that runs long enough hands its levels to worker threads (parallel.ts), which keep TLC's
// order, and takes them back to finish alone if a worker stops.

import type { CheckProgress } from "../check";
import type { ModelConfig } from "../config";
import type { Environment } from "../evaluate";
import type { TlcVersion } from "../tlc/version";
import { resetAssigned } from "./action";
import { setCurrent, setNext } from "./compile";
import { createEngineContext, type EngineSpec, holdsAll } from "./context";
import { getStateFingerprints, resetFingerprints } from "./fingerprint";
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
import { getEnvironmentFlag } from "./settings";
import { bail, Bailout, freezeTexts, getValueCount, resetStore, shareStore } from "./store";
import { type EngineWorkers, spawnEngineWorkers } from "./workers";

export type { EngineSpec } from "./context";

export interface EngineInput {
  config: ModelConfig;
  environment: Environment;
  spec: EngineSpec;
  isWarningEnabled: boolean;
  tlcOrder: number[];
  onProgress: ((progress: CheckProgress) => void) | undefined;
  // Called once the initial states are computed, so the caller reports them.
  onInitialStates: (generated: number, distinct: number) => void;
  startedAt: number;
  // How many threads may search, and what a worker needs to build the spec.
  workers: number;
  source: string;
  modules: [string, string | undefined][];
  version: TlcVersion | undefined;
}

// The search up to the state the engine was expanding when it stopped: the states found before
// that expansion, as ids, with their parents and the counts so far.
export interface EngineCheckpoint {
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
}

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
  if (getEnvironmentFlag("PROVE_IT_SHARED")) shareStore();
  resetFingerprints();
  resetAssigned();
  const context = createEngineContext(environment, config, input.spec, input.isWarningEnabled);
  const width = context.width;
  const constraints = context.constraints;
  const actionConstraints = context.actionConstraints;
  const invariants = context.invariants;

  // The states found so far, `width` ids each, in TLC's order.
  let states = new Int32Array(Math.max(1, width) * 1024);
  let stateCount = 0;
  let parents = new Int32Array(1024);
  let table = new Int32Array(1 << 12).fill(-1);
  let tableMask = table.length - 1;

  const hashState = (source: Int32Array, offset: number) => {
    let hash = 0x811c9dc5;
    for (let index = 0; index < width; index++)
      hash = Math.imul(hash ^ source[offset + index], 0x01000193);
    hash ^= hash >>> 13;
    hash = Math.imul(hash, 0x5bd1e995);
    return hash ^ (hash >>> 15);
  };

  const growTable = () => {
    const next = new Int32Array(table.length * 2).fill(-1);
    const mask = next.length - 1;
    for (let state = 0; state < stateCount; state++) {
      let slot = hashState(states, state * width) & mask;
      while (next[slot] !== -1) slot = (slot + 1) & mask;
      next[slot] = state;
    }
    table = next;
    tableMask = mask;
  };

  // The slot of a state in the table: either the slot that holds it, or the empty one to put it in.
  const findSlot = (source: Int32Array) => {
    const hash = hashState(source, 0);
    for (let slot = hash & tableMask; ; slot = (slot + 1) & tableMask) {
      const stored = table[slot];
      if (stored === -1) return slot;
      const offset = stored * width;
      let isEqual = true;
      for (let index = 0; index < width; index++) {
        if (states[offset + index] !== source[index]) {
          isEqual = false;
          break;
        }
      }
      if (isEqual) return slot;
    }
  };

  const addState = (source: Int32Array, slot: number, parent: number) => {
    if ((stateCount + 1) * width > states.length) {
      const next = new Int32Array(states.length * 2);
      next.set(states);
      states = next;
    }
    if (stateCount >= parents.length) {
      const next = new Int32Array(parents.length * 2);
      next.set(parents);
      parents = next;
    }
    states.set(source, stateCount * width);
    parents[stateCount] = parent;
    table[slot] = stateCount;
    stateCount++;
    if (stateCount * 2 > table.length) growTable();
  };

  let generated = 0;
  let initialGenerated = 0;
  let depth = 0;

  // --- initial states ---
  const current = new Int32Array(width).fill(-1);
  const next = new Int32Array(width).fill(-1);
  setCurrent(current);
  setNext(next);
  context.initStep(() => {
    for (let index = 0; index < width; index++)
      if (current[index] === -1) bail("an initial state that isn't complete");
    if (initialGenerated > 1 && (initialGenerated & (initialGenerated - 1)) === 0) {
      input.onProgress?.({ kind: "initial-states-progress", count: initialGenerated });
    }
    generated++;
    initialGenerated++;
    const isInModel = holdsAll(constraints);
    const slot = isInModel ? findSlot(current) : -1;
    if (isInModel && table[slot] !== -1) return;
    if (!holdsAll(invariants)) bail("an invariant violated in an initial state");
    if (!isInModel) return;
    addState(current, slot, -1);
    depth = 1;
  });
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

  const visitSuccessor = () => {
    successors++;
    generated++;
    setCurrent(next);
    const isStateInModel = holdsAll(constraints);
    setCurrent(current);
    const isInModel = isStateInModel && holdsAll(actionConstraints);
    const slot = isInModel ? findSlot(next) : -1;
    const isNew = isInModel && table[slot] === -1;
    if (!isInModel || isNew) {
      setCurrent(next);
      const holds = holdsAll(invariants);
      setCurrent(current);
      if (!holds) bail("an invariant violated");
    }
    if (!isNew) return;
    addState(next, slot, expanding);
    newStates++;
    depth = level + 1;
  };

  const onSuccessor = () => {
    for (let index = 0; index < width; index++) {
      if (next[index] === -1) bail("a successor that isn't complete");
    }
    visitSuccessor();
  };

  // --- workers ---
  const canShare =
    input.workers > 1 &&
    typeof SharedArrayBuffer === "function" &&
    typeof Atomics.wait === "function" &&
    !getEnvironmentFlag("PROVE_IT_SERIAL");
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
      stopWorkers(views);
      reloadFrom(views);
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
    table = new Int32Array(capacity).fill(-1);
    tableMask = capacity - 1;
    for (let index = 0; index < count; index++) {
      let slot = hashState(states, index * width) & tableMask;
      while (table[slot] !== -1) slot = (slot + 1) & tableMask;
      table[slot] = index;
    }
  };

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
        if (canShare) {
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
      current.set(states.subarray(expanding * width, (expanding + 1) * width));
      next.fill(-1);
      resetAssigned();
      newStates = 0;
      successors = 0;
      setCurrent(current);
      setNext(next);
      context.nextStep(onSuccessor);
      if (successors === 0 && config.checkDeadlock) bail("deadlock");
      outDegrees[Math.min(newStates, OUT_DEGREE_BUCKETS - 1)]++;
      if ((expanding & 0xff) === 0) reportProgress();
    }
  } catch (error) {
    if (error instanceof Bailout) {
      const checkpoint: EngineCheckpoint = {
        expanding,
        count: checkpointCount,
        generated: checkpointGenerated,
        initialGenerated,
        outDegrees: outDegrees.slice(),
        states: states.slice(0, checkpointCount * width),
        parents: parents.slice(0, checkpointCount),
        width,
      };
      error.checkpoint = checkpoint;
    }
    throw error;
  } finally {
    parallel.workers?.terminate();
  }

  return {
    generatedStates: generated,
    distinctStates: stateCount,
    depth: generated === 0 ? 0 : Math.max(depth, 1),
    outDegrees,
    initialStates,
    getFingerprints: () => getStateFingerprints(states, stateCount, width, input.tlcOrder),
    valueCount: getValueCount(),
    threads: parallel.threads,
  };
};

export const isBailout = (error: unknown): error is Bailout => error instanceof Bailout;

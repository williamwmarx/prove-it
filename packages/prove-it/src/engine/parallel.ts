// The engine's search on several threads, deterministic and in TLC's order.
//
// The search runs level by level. Every thread expands states of the current level and adds the new
// states it finds to a shared table, with the index of the state that found each and the position
// of the step among that state's successors. When two threads find the same state, it keeps the
// smaller of the two, the one TLC's single worker finds first. Once a level is done, the
// coordinator sorts its new states by those keys, which is the order TLC queues them in. So the
// counts, the outdegrees and the parents a trace follows are TLC's whatever the number of threads.
//
// Values live in the store's shared memory (store.ts), so a state crosses threads as its ids, and a
// thread that meets anything the engine doesn't finish stops the level for every thread.

import type { ModelConfig } from "../config";
import { resetAssigned } from "./action";
import { nextEpoch, setCurrent, setNext } from "./compile";
import { type EngineContext, holdsAll, holdsAllChanged } from "./context";
import { reportEngine } from "./settings";
import { Bailout, type SharedStore } from "./store";

// The words of the control block.
const GENERATION = 0;
const COMMAND = 1;
// The words threads update most sit a cache line apart.
const CURSOR = 16;
const LEVEL_START = 3;
const LEVEL_END = 4;
const DONE = 5;
const ABORT = 6;
const STORAGE_COUNT = 32;
const GENERATED = 8;
const ARENA_TOP = 48;
const READY = 10;
const LEVEL_STORAGE = 11;
// How many workers, in the order they got ready, take part in the current level. A worker that gets
// ready while a level runs joins the next one.
const ADMITTED = 12;
const CONTROL_WORDS = 64;
// Each thread takes this many storage slots at a time, so threads write apart.
const STORAGE_BLOCK = 64;
const UNUSED = -2;

export const COMMAND_RUN = 1;
export const COMMAND_STOP = 2;

const CHUNK = 16;
const SEGMENT_BITS = 10;
const SEGMENTS = 1 << SEGMENT_BITS;
const INITIAL_SEGMENT_SLOTS = 256;
const MAXIMUM_BYTES = 1 << 30;
// Locks a cache line apart, so threads taking different segments don't contend for one line.
const LOCK_STRIDE = 16;

export interface SharedSearch {
  width: number;
  checkDeadlock: boolean;
  control: SharedArrayBuffer;
  // Each state the search found, `width` ids, by the order threads stored it in.
  storage: SharedArrayBuffer;
  // For each stored state: the index, in TLC's order, of the state that found it, and the position
  // of the step among that state's successors.
  keys: SharedArrayBuffer;
  // The stored state at each index in TLC's order.
  order: SharedArrayBuffer;
  directory: SharedArrayBuffer;
  locks: SharedArrayBuffer;
  arena: SharedArrayBuffer;
}

export interface SearchViews {
  buffers: SharedSearch;
  width: number;
  control: Int32Array;
  storage: Int32Array;
  keys: Int32Array;
  order: Int32Array;
  directory: Int32Array;
  locks: Int32Array;
  arena: Int32Array;
}

export interface GoMessage {
  type: "go";
  store: SharedStore;
  search: SharedSearch;
}

export const attachSearch = (buffers: SharedSearch): SearchViews => ({
  buffers,
  width: buffers.width,
  control: new Int32Array(buffers.control),
  storage: new Int32Array(buffers.storage),
  keys: new Int32Array(buffers.keys),
  order: new Int32Array(buffers.order),
  directory: new Int32Array(buffers.directory),
  locks: new Int32Array(buffers.locks),
  arena: new Int32Array(buffers.arena),
});

export const createSharedSearch = (config: ModelConfig, width: number): SearchViews => {
  const buffers: SharedSearch = {
    width,
    checkDeadlock: config.checkDeadlock,
    control: new SharedArrayBuffer(CONTROL_WORDS * 4),
    // Each grows only at its end, so the system commits only the pages a search writes.
    storage: new SharedArrayBuffer(MAXIMUM_BYTES),
    keys: new SharedArrayBuffer(MAXIMUM_BYTES),
    order: new SharedArrayBuffer(MAXIMUM_BYTES / 2),
    directory: new SharedArrayBuffer(SEGMENTS * 3 * 4),
    locks: new SharedArrayBuffer(SEGMENTS * LOCK_STRIDE * 4),
    arena: new SharedArrayBuffer(MAXIMUM_BYTES),
  };
  const views = attachSearch(buffers);
  for (let segment = 0; segment < SEGMENTS; segment++) {
    views.directory[segment * 3] = segment * INITIAL_SEGMENT_SLOTS * 2;
    views.directory[segment * 3 + 1] = INITIAL_SEGMENT_SLOTS - 1;
  }
  views.control[ARENA_TOP] = SEGMENTS * INITIAL_SEGMENT_SLOTS * 2;
  return views;
};

export const hashState = (source: Int32Array, offset: number, width: number) => {
  let hash = 0x811c9dc5;
  for (let index = 0; index < width; index++) {
    hash = Math.imul(hash ^ source[offset + index], 0x01000193);
  }
  hash ^= hash >>> 13;
  hash = Math.imul(hash, 0x5bd1e995);
  return hash ^ (hash >>> 15);
};

const isStored = (views: SearchViews, stored: number, source: Int32Array) => {
  const width = views.width;
  const storage = views.storage;
  const offset = stored * width;
  for (let index = 0; index < width; index++) {
    if (storage[offset + index] !== source[index]) return false;
  }
  return true;
};

// Puts a stored state in its segment's table, the segment locked, growing the segment when half
// full. Entries are pairs: the hash, then the stored index + 1.
const insertEntry = (views: SearchViews, segment: number, hash: number, stored: number) => {
  const directory = views.directory;
  const arena = views.arena;
  const offset = directory[segment * 3];
  const mask = directory[segment * 3 + 1];
  let slot = hash & mask;
  while (arena[offset + slot * 2 + 1] !== 0) slot = (slot + 1) & mask;
  arena[offset + slot * 2] = hash;
  arena[offset + slot * 2 + 1] = stored + 1;
  const used = ++directory[segment * 3 + 2];
  if (used * 2 <= mask + 1) return;
  const capacity = (mask + 1) * 2;
  const nextOffset = Atomics.add(views.control, ARENA_TOP, capacity * 2);
  if ((nextOffset + capacity * 2) * 4 > views.buffers.arena.byteLength) {
    throw new Bailout("the shared state table is full");
  }
  const nextMask = capacity - 1;
  for (let index = 0; index <= mask; index++) {
    const entry = arena[offset + index * 2 + 1];
    if (entry === 0) continue;
    const entryHash = arena[offset + index * 2];
    let target = entryHash & nextMask;
    while (arena[nextOffset + target * 2 + 1] !== 0) target = (target + 1) & nextMask;
    arena[nextOffset + target * 2] = entryHash;
    arena[nextOffset + target * 2 + 1] = entry;
  }
  directory[segment * 3] = nextOffset;
  directory[segment * 3 + 1] = nextMask;
};

const lock = (locks: Int32Array, segment: number) => {
  while (Atomics.compareExchange(locks, segment, 0, 1) !== 0) {
    // Spin: a segment is held only while one state is looked up or added.
  }
};

// Stores a state found from the state at TLC index `parent`, as the `ordinal`th step. Returns the
// stored index of a new state, or -1 for one stored before, whose keys it lowers to these when it
// was found in this level by a step TLC takes later.
export interface StorageBlock {
  next: number;
  end: number;
}

export const createStorageBlock = (): StorageBlock => ({ next: 0, end: 0 });

// The next storage slot of this thread's block, taking a new block when it runs out. A block's
// slots start unused, so the coordinator skips the ones a level leaves.
const takeSlot = (views: SearchViews, block: StorageBlock) => {
  if (block.next === block.end) {
    const start = Atomics.add(views.control, STORAGE_COUNT, STORAGE_BLOCK);
    if ((start + STORAGE_BLOCK) * views.width * 4 > views.buffers.storage.byteLength) {
      throw new Bailout("the shared state storage is full");
    }
    for (let stored = start; stored < start + STORAGE_BLOCK; stored++) {
      views.keys[stored * 2] = UNUSED;
    }
    block.next = start;
    block.end = start + STORAGE_BLOCK;
  }
  return block.next++;
};

export const insertState = (
  views: SearchViews,
  source: Int32Array,
  parent: number,
  ordinal: number,
  block: StorageBlock,
) => {
  const width = views.width;
  const hash = hashState(source, 0, width);
  const segment = hash >>> (32 - SEGMENT_BITS);
  const locks = views.locks;
  const lockIndex = segment * LOCK_STRIDE;
  lock(locks, lockIndex);
  const offset = views.directory[segment * 3];
  const mask = views.directory[segment * 3 + 1];
  const arena = views.arena;
  for (let slot = hash & mask; ; slot = (slot + 1) & mask) {
    const entry = arena[offset + slot * 2 + 1];
    if (entry === 0) break;
    if (arena[offset + slot * 2] !== hash || !isStored(views, entry - 1, source)) continue;
    const stored = entry - 1;
    if (stored >= views.control[LEVEL_STORAGE]) {
      const keys = views.keys;
      const storedParent = keys[stored * 2];
      if (parent < storedParent || (parent === storedParent && ordinal < keys[stored * 2 + 1])) {
        keys[stored * 2] = parent;
        keys[stored * 2 + 1] = ordinal;
      }
    }
    Atomics.store(locks, lockIndex, 0);
    return -1;
  }
  let stored: number;
  try {
    stored = takeSlot(views, block);
  } catch (error) {
    Atomics.store(locks, lockIndex, 0);
    throw error;
  }
  views.storage.set(source, stored * width);
  views.keys[stored * 2] = parent;
  views.keys[stored * 2 + 1] = ordinal;
  insertEntry(views, segment, hash, stored);
  Atomics.store(locks, lockIndex, 0);
  return stored;
};

// Expands the states of the current level that this thread claims, until none are left or a
// thread stops the level. Returns how many successors it generated.
export const expandLevel = (context: EngineContext, views: SearchViews) => {
  const control = views.control;
  const width = views.width;
  const current = new Int32Array(width);
  const next = new Int32Array(width);
  const levelEnd = control[LEVEL_END];
  const storage = views.storage;
  const order = views.order;
  const checkDeadlock = views.buffers.checkDeadlock;
  let generated = 0;
  let parent = 0;
  let ordinal = 0;
  const block = createStorageBlock();
  let expansionEpoch = 0;
  const onSuccessor = () => {
    for (let index = 0; index < width; index++) {
      if (next[index] === -1) throw new Bailout("a successor that isn't complete");
    }
    generated++;
    ordinal++;
    const successorEpoch = nextEpoch();
    setCurrent(next, successorEpoch);
    // The state being expanded is in the model, so each constraint and invariant held of it.
    const isStateInModel = holdsAllChanged(
      context.constraints,
      context.constraintVars,
      next,
      current,
    );
    setCurrent(current, expansionEpoch);
    // Every step, to a new state or not, as the search on one thread checks it.
    if (!holdsAll(context.actionProperties)) throw new Bailout("an action property violated");
    const isInModel = isStateInModel && holdsAll(context.actionConstraints);
    const stored = isInModel ? insertState(views, next, parent, ordinal, block) : -1;
    if (isInModel && stored === -1) return;
    setCurrent(next, successorEpoch);
    const holds = holdsAllChanged(context.invariants, context.invariantVars, next, current);
    setCurrent(current, expansionEpoch);
    if (!holds) throw new Bailout("an invariant violated");
  };
  setNext(next);
  try {
    for (;;) {
      if (Atomics.load(control, ABORT) !== 0) break;
      const start = Atomics.add(control, CURSOR, CHUNK);
      if (start >= levelEnd) break;
      const end = Math.min(start + CHUNK, levelEnd);
      for (let index = start; index < end; index++) {
        const offset = order[index] * width;
        for (let variable = 0; variable < width; variable++) {
          current[variable] = storage[offset + variable];
        }
        next.fill(-1);
        resetAssigned();
        parent = index;
        ordinal = 0;
        expansionEpoch = nextEpoch();
        setCurrent(current, expansionEpoch);
        context.nextStep(onSuccessor);
        if (ordinal === 0 && checkDeadlock) throw new Bailout("deadlock");
      }
    }
  } catch (error) {
    Atomics.store(control, ABORT, 1);
    if (!(error instanceof Bailout)) throw error;
  }
  Atomics.add(control, GENERATED, generated);
  return generated;
};

// --- the worker's side ---

// Runs levels as the coordinator starts them, until it says to stop.
export const serveLevels = (context: EngineContext, views: SearchViews) => {
  const control = views.control;
  let generation = Atomics.load(control, GENERATION);
  const index = Atomics.add(control, READY, 1);
  for (;;) {
    Atomics.wait(control, GENERATION, generation);
    generation = Atomics.load(control, GENERATION);
    if (Atomics.load(control, COMMAND) === COMMAND_STOP) return;
    if (index >= Atomics.load(control, ADMITTED)) continue;
    try {
      expandLevel(context, views);
    } finally {
      Atomics.add(control, DONE, 1);
      Atomics.notify(control, DONE);
    }
  }
};

// --- the coordinator's side ---

export const getReadyCount = (views: SearchViews) => Atomics.load(views.control, READY);

export interface LevelOutcome {
  isAborted: boolean;
  generated: number;
  // The stored index of each new state, in TLC's order.
  added: number[];
}

// Runs a level over TLC indices [start, end) with the ready workers, the coordinator taking part,
// and orders the new states TLC's way.
export const runLevel = (
  context: EngineContext,
  views: SearchViews,
  start: number,
  end: number,
): LevelOutcome => {
  const control = views.control;
  const participants = Atomics.load(control, READY);
  Atomics.store(control, ADMITTED, participants);
  const storageStart = Atomics.load(control, STORAGE_COUNT);
  Atomics.store(control, LEVEL_START, start);
  Atomics.store(control, LEVEL_END, end);
  Atomics.store(control, CURSOR, start);
  Atomics.store(control, DONE, 0);
  Atomics.store(control, GENERATED, 0);
  Atomics.store(control, LEVEL_STORAGE, storageStart);
  Atomics.store(control, COMMAND, COMMAND_RUN);
  Atomics.add(control, GENERATION, 1);
  Atomics.notify(control, GENERATION);
  const levelStartedAt = performance.now();
  const ownGenerated = expandLevel(context, views);
  const ownFinishedAt = performance.now();
  for (let done = Atomics.load(control, DONE); done < participants;) {
    Atomics.wait(control, DONE, done);
    done = Atomics.load(control, DONE);
  }
  const isAborted = Atomics.load(control, ABORT) !== 0;
  reportEngine(
    `level of ${end - start} states: ${participants} workers, coordinator generated ${ownGenerated} of ${Atomics.load(control, GENERATED)}, ${(ownFinishedAt - levelStartedAt).toFixed(1)} ms alone, ${(performance.now() - levelStartedAt).toFixed(1)} ms in all`,
  );
  const storageEnd = Atomics.load(control, STORAGE_COUNT);
  const keys = views.keys;
  const added: number[] = [];
  for (let stored = storageStart; stored < storageEnd; stored++) {
    if (keys[stored * 2] !== UNUSED) added.push(stored);
  }
  added.sort(
    (left, right) => keys[left * 2] - keys[right * 2] || keys[left * 2 + 1] - keys[right * 2 + 1],
  );
  return { isAborted, generated: Atomics.load(control, GENERATED), added };
};

export const stopWorkers = (views: SearchViews) => {
  Atomics.store(views.control, COMMAND, COMMAND_STOP);
  Atomics.add(views.control, GENERATION, 1);
  Atomics.notify(views.control, GENERATION);
};

// Stores a state the coordinator found before the workers joined, at the next TLC index.
export const seedState = (
  views: SearchViews,
  source: Int32Array,
  index: number,
  block: StorageBlock,
) => {
  const stored = insertState(views, source, -1, index, block);
  views.order[index] = stored;
  return stored;
};

export const getParentOf = (views: SearchViews, stored: number) => views.keys[stored * 2];

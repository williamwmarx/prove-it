// Caches of pure computations keyed by the ids of what they read. A computation reads a few state
// variables and bound names, and far fewer distinct values flow through those than there are states,
// so most evaluations become a hash lookup.

const EMPTY = -1;
// After this many lookups a table that hits less often than MINIMUM_HIT_RATE turns itself off.
const PROBATION = 1 << 13;
const MINIMUM_HIT_RATE = 0.2;
const MAXIMUM_ENTRIES = 1 << 22;

export class MemoTable {
  readonly width: number;
  keys: Int32Array;
  values: Int32Array;
  mask: number;
  size = 0;
  lookups = 0;
  hits = 0;
  isEnabled = true;

  constructor(width: number) {
    this.width = width;
    const capacity = 64;
    this.keys = new Int32Array(capacity * width);
    this.values = new Int32Array(capacity).fill(EMPTY);
    this.mask = capacity - 1;
  }

  private grow() {
    const width = this.width;
    const oldKeys = this.keys;
    const oldValues = this.values;
    const capacity = oldValues.length * 2;
    this.keys = new Int32Array(capacity * width);
    this.values = new Int32Array(capacity).fill(EMPTY);
    this.mask = capacity - 1;
    for (let entry = 0; entry < oldValues.length; entry++) {
      if (oldValues[entry] === EMPTY) continue;
      let hash = 0x811c9dc5;
      for (let index = 0; index < width; index++) {
        hash = Math.imul(hash ^ oldKeys[entry * width + index], 0x01000193);
      }
      hash ^= hash >>> 15;
      let slot = hash & this.mask;
      while (this.values[slot] !== EMPTY) slot = (slot + 1) & this.mask;
      for (let index = 0; index < width; index++) {
        this.keys[slot * width + index] = oldKeys[entry * width + index];
      }
      this.values[slot] = oldValues[entry];
    }
  }

  // Checks whether the table should stay on, once its probation ends.
  private review() {
    if (this.hits < this.lookups * MINIMUM_HIT_RATE) {
      this.isEnabled = false;
      this.keys = new Int32Array(0);
      this.values = new Int32Array(0);
    }
  }

  get1(first: number) {
    if (++this.lookups === PROBATION) this.review();
    if (!this.isEnabled) return EMPTY;
    const hash = Math.imul(0x811c9dc5 ^ first, 0x01000193);
    const mask = this.mask;
    const values = this.values;
    const keys = this.keys;
    for (let slot = (hash ^ (hash >>> 15)) & mask; ; slot = (slot + 1) & mask) {
      const value = values[slot];
      if (value === EMPTY) return EMPTY;
      if (keys[slot] === first) {
        this.hits++;
        return value;
      }
    }
  }

  set1(first: number, value: number) {
    if (!this.isEnabled || this.size >= MAXIMUM_ENTRIES) return;
    if ((this.size + 1) * 2 > this.values.length) this.grow();
    const hash = Math.imul(0x811c9dc5 ^ first, 0x01000193);
    const mask = this.mask;
    let slot = (hash ^ (hash >>> 15)) & mask;
    while (this.values[slot] !== EMPTY) slot = (slot + 1) & mask;
    this.keys[slot] = first;
    this.values[slot] = value;
    this.size++;
  }

  get2(first: number, second: number) {
    if (++this.lookups === PROBATION) this.review();
    if (!this.isEnabled) return EMPTY;
    const hash = Math.imul(Math.imul(0x811c9dc5 ^ first, 0x01000193) ^ second, 0x01000193);
    const mask = this.mask;
    const values = this.values;
    const keys = this.keys;
    for (let slot = (hash ^ (hash >>> 15)) & mask; ; slot = (slot + 1) & mask) {
      const value = values[slot];
      if (value === EMPTY) return EMPTY;
      if (keys[slot * 2] === first && keys[slot * 2 + 1] === second) {
        this.hits++;
        return value;
      }
    }
  }

  set2(first: number, second: number, value: number) {
    if (!this.isEnabled || this.size >= MAXIMUM_ENTRIES) return;
    if ((this.size + 1) * 2 > this.values.length) this.grow();
    const hash = Math.imul(Math.imul(0x811c9dc5 ^ first, 0x01000193) ^ second, 0x01000193);
    const mask = this.mask;
    let slot = (hash ^ (hash >>> 15)) & mask;
    while (this.values[slot] !== EMPTY) slot = (slot + 1) & mask;
    this.keys[slot * 2] = first;
    this.keys[slot * 2 + 1] = second;
    this.values[slot] = value;
    this.size++;
  }

  // Keys of any width, read from the scratch array.
  getN(scratch: Int32Array) {
    if (++this.lookups === PROBATION) this.review();
    if (!this.isEnabled) return EMPTY;
    const width = this.width;
    let hash = 0x811c9dc5;
    for (let index = 0; index < width; index++) hash = Math.imul(hash ^ scratch[index], 0x01000193);
    const mask = this.mask;
    const values = this.values;
    const keys = this.keys;
    for (let slot = (hash ^ (hash >>> 15)) & mask; ; slot = (slot + 1) & mask) {
      const value = values[slot];
      if (value === EMPTY) return EMPTY;
      let isEqual = true;
      for (let index = 0; index < width; index++) {
        if (keys[slot * width + index] !== scratch[index]) {
          isEqual = false;
          break;
        }
      }
      if (isEqual) {
        this.hits++;
        return value;
      }
    }
  }

  setN(scratch: Int32Array, value: number) {
    if (!this.isEnabled || this.size >= MAXIMUM_ENTRIES) return;
    if ((this.size + 1) * 2 > this.values.length) this.grow();
    const width = this.width;
    let hash = 0x811c9dc5;
    for (let index = 0; index < width; index++) hash = Math.imul(hash ^ scratch[index], 0x01000193);
    const mask = this.mask;
    let slot = (hash ^ (hash >>> 15)) & mask;
    while (this.values[slot] !== EMPTY) slot = (slot + 1) & mask;
    for (let index = 0; index < width; index++) this.keys[slot * width + index] = scratch[index];
    this.values[slot] = value;
    this.size++;
  }
}

// A cache of an expression that reads too many state variables for a memo table, but no primed
// ones, while one state is current. Its value is then a function of the bound names it reads, up
// to four, which key its entries; an entry from an earlier current state doesn't match. Entries
// are direct-mapped: a collision overwrites.
const EPOCH_ENTRIES = 64;
const EPOCH_MINIMUM_HIT_RATE = 0.1;
export const EPOCH_KEYS = 4;

export class EpochCache {
  epochs = new Int32Array(EPOCH_ENTRIES);
  keys = new Int32Array(EPOCH_ENTRIES * EPOCH_KEYS);
  values = new Int32Array(EPOCH_ENTRIES);
  lookups = 0;
  hits = 0;
  isEnabled = true;

  // The entry for the keys, where the keys past the bound names read are 0.
  static entry(first: number, second: number, third: number, fourth: number) {
    let hash = Math.imul(0x811c9dc5 ^ first, 0x01000193);
    hash = Math.imul(hash ^ second, 0x01000193);
    hash = Math.imul(hash ^ third, 0x01000193);
    hash = Math.imul(hash ^ fourth, 0x01000193);
    return (hash ^ (hash >>> 15)) & (EPOCH_ENTRIES - 1);
  }

  get(epoch: number, entry: number, first: number, second: number, third: number, fourth: number) {
    // A cache whose expression is evaluated about once per state only costs.
    if (++this.lookups === PROBATION && this.hits < this.lookups * EPOCH_MINIMUM_HIT_RATE)
      this.isEnabled = false;
    const keys = this.keys;
    const at = entry * EPOCH_KEYS;
    if (
      this.epochs[entry] !== epoch ||
      keys[at] !== first ||
      keys[at + 1] !== second ||
      keys[at + 2] !== third ||
      keys[at + 3] !== fourth
    )
      return EMPTY;
    this.hits++;
    return this.values[entry];
  }

  set(
    epoch: number,
    entry: number,
    first: number,
    second: number,
    third: number,
    fourth: number,
    value: number,
  ) {
    const keys = this.keys;
    const at = entry * EPOCH_KEYS;
    this.epochs[entry] = epoch;
    keys[at] = first;
    keys[at + 1] = second;
    keys[at + 2] = third;
    keys[at + 3] = fourth;
    this.values[entry] = value;
  }
}

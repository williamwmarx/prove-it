// Caches of pure computations keyed by the ids of what they read. A computation reads a few state
// variables and bound names, and far fewer distinct values flow through those than there are states,
// so most evaluations become a hash lookup.

const EMPTY = -1;
// After this many lookups a table that hits less often than MINIMUM_HIT_RATE turns itself off.
const PROBATION = 1 << 13;
const MINIMUM_HIT_RATE = 0.2;
const MAXIMUM_ENTRIES = 1 << 22;
// A table of width 1 indexes its values by its key while it has at least one entry for every
// DIRECT_SPARSITY ids its array spans past the first DIRECT_MINIMUM.
const DIRECT_SPARSITY = 16;
const DIRECT_MINIMUM = 1 << 16;
// And never past this many ids, about what a hash table holding MAXIMUM_ENTRIES takes.
const DIRECT_MAXIMUM = 1 << 23;

const OFFSET_BASIS = 0x811c9dc5;
const fold = (hash: number, key: number) => Math.imul(hash ^ key, 0x01000193);

export class MemoTable {
  readonly width: number;
  keys: Int32Array;
  values: Int32Array;
  mask: number;
  size = 0;
  lookups = 0;
  hits = 0;
  isEnabled = true;
  // A table of width 1 is keyed by one id, so while its keys are dense enough its values are an
  // array indexed by the id, read without hashing or probing. One whose keys turn out too sparse
  // becomes a hash table like the others.
  private isDirect: boolean;

  constructor(width: number) {
    this.width = width;
    this.isDirect = width === 1;
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
      let hash = OFFSET_BASIS;
      for (let index = 0; index < width; index++) hash = fold(hash, oldKeys[entry * width + index]);
      hash ^= hash >>> 15;
      let slot = hash & this.mask;
      while (this.values[slot] !== EMPTY) slot = (slot + 1) & this.mask;
      for (let index = 0; index < width; index++) {
        this.keys[slot * width + index] = oldKeys[entry * width + index];
      }
      this.values[slot] = oldValues[entry];
    }
  }

  // Grows a direct table's array to hold the id, or makes the table a hash table when its keys are
  // too sparse for the array that would take.
  private reserveDirect(id: number) {
    const direct = this.values;
    const capacity = Math.max(2 * direct.length, id + 1);
    if (capacity <= DIRECT_MAXIMUM && capacity <= DIRECT_SPARSITY * this.size + DIRECT_MINIMUM) {
      this.values = new Int32Array(capacity).fill(EMPTY);
      this.values.set(direct);
      return;
    }
    this.isDirect = false;
    this.size = 0;
    this.values = new Int32Array(this.keys.length).fill(EMPTY);
    for (let key = 0; key < direct.length; key++) {
      if (direct[key] !== EMPTY) this.set1(key, direct[key]);
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

  // Counts a lookup, and says whether the table is on.
  private open() {
    if (++this.lookups === PROBATION) this.review();
    return this.isEnabled;
  }

  // The empty slot a new entry with this hash goes in, or -1 when the table takes no more entries.
  private claim(hash: number) {
    if (!this.isEnabled || this.size >= MAXIMUM_ENTRIES) return -1;
    if ((this.size + 1) * 2 > this.values.length) this.grow();
    const mask = this.mask;
    let slot = (hash ^ (hash >>> 15)) & mask;
    while (this.values[slot] !== EMPTY) slot = (slot + 1) & mask;
    this.size++;
    return slot;
  }

  // Each width up to 6 has its own lookup and store, which take the keys as arguments rather than
  // in an array to fill. All hash the keys in order, as getN does.
  get1(a: number) {
    if (!this.open()) return EMPTY;
    const values = this.values;
    if (this.isDirect) {
      const value = a >>> 0 < values.length ? values[a] : EMPTY;
      if (value !== EMPTY) this.hits++;
      return value;
    }
    const hash = fold(OFFSET_BASIS, a);
    const mask = this.mask;
    const keys = this.keys;
    for (let slot = (hash ^ (hash >>> 15)) & mask; ; slot = (slot + 1) & mask) {
      const value = values[slot];
      if (value === EMPTY) return EMPTY;
      if (keys[slot] === a) {
        this.hits++;
        return value;
      }
    }
  }

  set1(a: number, value: number) {
    if (this.isDirect) {
      if (!this.isEnabled || this.size >= MAXIMUM_ENTRIES || a < 0) return;
      if (a >= this.values.length) this.reserveDirect(a);
      if (this.isDirect) {
        if (this.values[a] === EMPTY) this.size++;
        this.values[a] = value;
        return;
      }
    }
    const slot = this.claim(fold(OFFSET_BASIS, a));
    if (slot === -1) return;
    this.keys[slot] = a;
    this.values[slot] = value;
  }

  get2(a: number, b: number) {
    if (!this.open()) return EMPTY;
    const hash = fold(fold(OFFSET_BASIS, a), b);
    const mask = this.mask;
    const values = this.values;
    const keys = this.keys;
    for (let slot = (hash ^ (hash >>> 15)) & mask; ; slot = (slot + 1) & mask) {
      const value = values[slot];
      if (value === EMPTY) return EMPTY;
      const at = slot * 2;
      if (keys[at] === a && keys[at + 1] === b) {
        this.hits++;
        return value;
      }
    }
  }

  set2(a: number, b: number, value: number) {
    const slot = this.claim(fold(fold(OFFSET_BASIS, a), b));
    if (slot === -1) return;
    const keys = this.keys;
    keys[slot * 2] = a;
    keys[slot * 2 + 1] = b;
    this.values[slot] = value;
  }

  get3(a: number, b: number, c: number) {
    if (!this.open()) return EMPTY;
    const hash = fold(fold(fold(OFFSET_BASIS, a), b), c);
    const mask = this.mask;
    const values = this.values;
    const keys = this.keys;
    for (let slot = (hash ^ (hash >>> 15)) & mask; ; slot = (slot + 1) & mask) {
      const value = values[slot];
      if (value === EMPTY) return EMPTY;
      const at = slot * 3;
      if (keys[at] === a && keys[at + 1] === b && keys[at + 2] === c) {
        this.hits++;
        return value;
      }
    }
  }

  set3(a: number, b: number, c: number, value: number) {
    const slot = this.claim(fold(fold(fold(OFFSET_BASIS, a), b), c));
    if (slot === -1) return;
    const keys = this.keys;
    const at = slot * 3;
    keys[at] = a;
    keys[at + 1] = b;
    keys[at + 2] = c;
    this.values[slot] = value;
  }

  get4(a: number, b: number, c: number, d: number) {
    if (!this.open()) return EMPTY;
    const hash = fold(fold(fold(fold(OFFSET_BASIS, a), b), c), d);
    const mask = this.mask;
    const values = this.values;
    const keys = this.keys;
    for (let slot = (hash ^ (hash >>> 15)) & mask; ; slot = (slot + 1) & mask) {
      const value = values[slot];
      if (value === EMPTY) return EMPTY;
      const at = slot * 4;
      if (keys[at] === a && keys[at + 1] === b && keys[at + 2] === c && keys[at + 3] === d) {
        this.hits++;
        return value;
      }
    }
  }

  set4(a: number, b: number, c: number, d: number, value: number) {
    const slot = this.claim(fold(fold(fold(fold(OFFSET_BASIS, a), b), c), d));
    if (slot === -1) return;
    const keys = this.keys;
    const at = slot * 4;
    keys[at] = a;
    keys[at + 1] = b;
    keys[at + 2] = c;
    keys[at + 3] = d;
    this.values[slot] = value;
  }

  get5(a: number, b: number, c: number, d: number, e: number) {
    if (!this.open()) return EMPTY;
    const hash = fold(fold(fold(fold(fold(OFFSET_BASIS, a), b), c), d), e);
    const mask = this.mask;
    const values = this.values;
    const keys = this.keys;
    for (let slot = (hash ^ (hash >>> 15)) & mask; ; slot = (slot + 1) & mask) {
      const value = values[slot];
      if (value === EMPTY) return EMPTY;
      const at = slot * 5;
      if (
        keys[at] === a &&
        keys[at + 1] === b &&
        keys[at + 2] === c &&
        keys[at + 3] === d &&
        keys[at + 4] === e
      ) {
        this.hits++;
        return value;
      }
    }
  }

  set5(a: number, b: number, c: number, d: number, e: number, value: number) {
    const slot = this.claim(fold(fold(fold(fold(fold(OFFSET_BASIS, a), b), c), d), e));
    if (slot === -1) return;
    const keys = this.keys;
    const at = slot * 5;
    keys[at] = a;
    keys[at + 1] = b;
    keys[at + 2] = c;
    keys[at + 3] = d;
    keys[at + 4] = e;
    this.values[slot] = value;
  }

  get6(a: number, b: number, c: number, d: number, e: number, f: number) {
    if (!this.open()) return EMPTY;
    const hash = fold(fold(fold(fold(fold(fold(OFFSET_BASIS, a), b), c), d), e), f);
    const mask = this.mask;
    const values = this.values;
    const keys = this.keys;
    for (let slot = (hash ^ (hash >>> 15)) & mask; ; slot = (slot + 1) & mask) {
      const value = values[slot];
      if (value === EMPTY) return EMPTY;
      const at = slot * 6;
      if (
        keys[at] === a &&
        keys[at + 1] === b &&
        keys[at + 2] === c &&
        keys[at + 3] === d &&
        keys[at + 4] === e &&
        keys[at + 5] === f
      ) {
        this.hits++;
        return value;
      }
    }
  }

  set6(a: number, b: number, c: number, d: number, e: number, f: number, value: number) {
    const slot = this.claim(fold(fold(fold(fold(fold(fold(OFFSET_BASIS, a), b), c), d), e), f));
    if (slot === -1) return;
    const keys = this.keys;
    const at = slot * 6;
    keys[at] = a;
    keys[at + 1] = b;
    keys[at + 2] = c;
    keys[at + 3] = d;
    keys[at + 4] = e;
    keys[at + 5] = f;
    this.values[slot] = value;
  }

  // Keys of any width, read from an array at an offset.
  getN(keys: Int32Array, offset: number) {
    const width = this.width;
    if (width === 1) return this.get1(keys[offset]);
    if (!this.open()) return EMPTY;
    let hash = OFFSET_BASIS;
    for (let index = 0; index < width; index++) hash = fold(hash, keys[offset + index]);
    const mask = this.mask;
    const values = this.values;
    const stored = this.keys;
    for (let slot = (hash ^ (hash >>> 15)) & mask; ; slot = (slot + 1) & mask) {
      const value = values[slot];
      if (value === EMPTY) return EMPTY;
      let isEqual = true;
      for (let index = 0; index < width; index++) {
        if (stored[slot * width + index] !== keys[offset + index]) {
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

  setN(keys: Int32Array, offset: number, value: number) {
    const width = this.width;
    if (width === 1) return this.set1(keys[offset], value);
    let hash = OFFSET_BASIS;
    for (let index = 0; index < width; index++) hash = fold(hash, keys[offset + index]);
    const slot = this.claim(hash);
    if (slot === -1) return;
    for (let index = 0; index < width; index++) {
      this.keys[slot * width + index] = keys[offset + index];
    }
    this.values[slot] = value;
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
  // Epochs count past 2^31, so they don't fit an Int32Array.
  epochs = new Float64Array(EPOCH_ENTRIES);
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

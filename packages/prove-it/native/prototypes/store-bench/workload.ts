// The synthetic store workload, run against Prove It's own store.ts (imported read-only). The Rust
// port in src/main.rs runs the same operations from the same random sequence, so the value counts
// and the checksum of ids must agree.
import {
  appendTuple,
  createRecordShape,
  EMPTY_SET,
  EMPTY_TUPLE,
  except,
  functionOfSorted,
  getValueCount,
  int,
  recordOf,
  resetStore,
  setOf,
  sizeOf,
  str,
  withElement,
} from "/home/user/prove-it/packages/prove-it/src/engine/store";
import { setStringOrder } from "/home/user/prove-it/packages/prove-it/src/values";

const ITERATIONS = Number(process.argv[2] ?? 2_000_000);
const STATE_WIDTH = 4;
const TEXTS = [
  "rm",
  "type",
  "working",
  "prepared",
  "committed",
  "aborted",
  "Prepared",
  "Commit",
  "Abort",
];
const RMS = Array.from({ length: 5 }, (_, index) => `r${index}`);

const run = () => {
  setStringOrder([...TEXTS, ...RMS]);
  resetStore();
  let seed = 0x2545f491;
  const next = () => {
    seed ^= seed << 13;
    seed ^= seed >>> 17;
    seed ^= seed << 5;
    return seed >>> 0;
  };
  const rms = RMS.map(str);
  const states = ["working", "prepared", "committed", "aborted"].map(str);
  const types = ["Prepared", "Commit", "Abort"].map(str);
  const shape = createRecordShape([str("rm"), str("type")]);
  let rmState = functionOfSorted(
    rms,
    rms.map(() => states[0]),
    rms.length,
  );
  let msgs = EMPTY_SET;
  let log = EMPTY_TUPLE;
  let checksum = 0;
  const record = new Int32Array(2);
  // The state table: [hash, index] pairs over states of STATE_WIDTH ids, as search.ts keeps it.
  let stateStore = new Int32Array(STATE_WIDTH * 1024);
  let stateCount = 0;
  let table = new Int32Array(2 << 10).fill(-1);
  let mask = (1 << 10) - 1;
  const state = new Int32Array(STATE_WIDTH);
  const hashState = (source: Int32Array, offset: number) => {
    let hash = 0x811c9dc5;
    for (let index = 0; index < STATE_WIDTH; index++)
      hash = Math.imul(hash ^ source[offset + index], 0x01000193);
    hash ^= hash >>> 13;
    hash = Math.imul(hash, 0x5bd1e995);
    return hash ^ (hash >>> 15);
  };
  const grow = () => {
    const nextTable = new Int32Array(table.length * 2).fill(-1);
    const nextMask = table.length - 1;
    for (let slot = 0; slot <= mask; slot++) {
      const stored = table[2 * slot + 1];
      if (stored === -1) continue;
      let to = table[2 * slot] & nextMask;
      while (nextTable[2 * to + 1] !== -1) to = (to + 1) & nextMask;
      nextTable[2 * to] = table[2 * slot];
      nextTable[2 * to + 1] = stored;
    }
    table = nextTable;
    mask = nextMask;
  };
  const probe = () => {
    const hash = hashState(state, 0);
    for (let slot = hash & mask; ; slot = (slot + 1) & mask) {
      const stored = table[2 * slot + 1];
      if (stored === -1) {
        if ((stateCount + 1) * STATE_WIDTH > stateStore.length) {
          const grown = new Int32Array(stateStore.length * 2);
          grown.set(stateStore);
          stateStore = grown;
        }
        stateStore.set(state, stateCount * STATE_WIDTH);
        table[2 * slot] = hash;
        table[2 * slot + 1] = stateCount++;
        if (stateCount * 2 > mask + 1) grow();
        return 1;
      }
      if (table[2 * slot] !== hash) continue;
      const offset = stored * STATE_WIDTH;
      let index = 0;
      while (index < STATE_WIDTH && stateStore[offset + index] === state[index]) index++;
      if (index === STATE_WIDTH) return 0;
    }
  };
  let fresh = 0;
  const startedAt = performance.now();
  for (let iteration = 0; iteration < ITERATIONS; iteration++) {
    const random = next();
    const rm = random % 5;
    rmState = except(rmState, rms[rm], states[(random >>> 3) & 3]);
    record[0] = rms[rm];
    record[1] = types[(random >>> 5) % 3];
    msgs = withElement(msgs, recordOf(shape, record));
    if (((random >>> 8) & 3) === 0) msgs = EMPTY_SET;
    const small = setOf([
      int((random >>> 12) % 4),
      int((random >>> 16) % 4),
      int((random >>> 20) % 4),
    ]);
    log =
      ((random >>> 24) & 3) === 0 || sizeOf(log) >= 3
        ? EMPTY_TUPLE
        : appendTuple(log, int((random >>> 27) & 1));
    state[0] = rmState;
    state[1] = small;
    state[2] = log;
    state[3] = msgs === EMPTY_SET ? 1 : 0;
    if (process.argv[3] !== "noprobe") fresh += probe();
    checksum = (checksum * 31 + rmState + msgs + small + log) | 0;
  }
  return {
    ms: performance.now() - startedAt,
    values: getValueCount(),
    states: stateCount,
    fresh,
    checksum,
  };
};

for (let round = 0; round < 3; round++) {
  const result = run();
  console.log(
    `ts store: ${ITERATIONS} iterations in ${result.ms.toFixed(1)} ms (${((result.ms * 1e6) / ITERATIONS).toFixed(0)} ns/iteration), ${result.values} values, ${result.states} states, checksum ${result.checksum}`,
  );
}

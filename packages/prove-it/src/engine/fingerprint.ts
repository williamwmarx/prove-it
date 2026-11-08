// TLC's 64-bit fingerprints of the engine's states, which TLC reports the smallest distance between.
//
// TLC fingerprints a state by extending FP64 over the bytes of its values. Extending is linear over
// GF(2), so extending a fingerprint fp by the bytes of a value v is shift(fp, |v|) xor F(v), where F(v)
// extends zero by v and shift extends by |v| zero bytes. F and |v| are computed once per interned
// value, and a state's fingerprint takes one shift and one xor per variable, or, from its parent's,
// per variable that changed.

import { EngineInvariantError } from "../errors";
import { getStringRank } from "../values";
import { getFingerprintSetting } from "./settings";
import {
  elementAt,
  getKey,
  getRangeValue,
  intOf,
  KIND_BOOL,
  KIND_INT,
  KIND_MODEL,
  KIND_SET,
  KIND_STRING,
  kindOf,
  sizeOf,
  textOf,
  TRUE,
} from "./store";

const IRREDUCIBLE_POLYNOMIAL = 0x911498ae0e66bad6n;

const BYTE_MOD_TABLE = (() => {
  const powers: bigint[] = [];
  for (let power = 1n << 63n; powers.length < 72;) {
    powers.push(power);
    power = (power >> 1n) ^ ((power & 1n) === 0n ? 0n : IRREDUCIBLE_POLYNOMIAL);
  }
  return Array.from({ length: 256 }, (_, byte) =>
    powers
      .slice(64, 72)
      .reverse()
      .reduce((value, power, bit) => ((byte >> bit) & 1 ? value ^ power : value), 0n),
  );
})();
const MOD_HIGH = Int32Array.from(BYTE_MOD_TABLE, (entry) =>
  Number(BigInt.asIntN(32, entry >> 32n)),
);
const MOD_LOW = Int32Array.from(BYTE_MOD_TABLE, (entry) => Number(BigInt.asIntN(32, entry)));

const INITIAL_HIGH = Number(BigInt.asIntN(32, IRREDUCIBLE_POLYNOMIAL >> 32n));
const INITIAL_LOW = Number(BigInt.asIntN(32, IRREDUCIBLE_POLYNOMIAL));

// The fingerprint being extended byte by byte.
let high = 0;
let low = 0;

const extendByte = (byte: number) => {
  const index = (byte ^ low) & 0xff;
  low = ((low >>> 8) | (high << 24)) ^ MOD_LOW[index];
  high = (high >>> 8) ^ MOD_HIGH[index];
};

const extendInt = (word: number) => {
  extendByte(word & 0xff);
  extendByte((word >>> 8) & 0xff);
  extendByte((word >>> 16) & 0xff);
  extendByte((word >>> 24) & 0xff);
};

// A table that shifts a fingerprint by a fixed number of zero bytes: entry [8k + i][b] holds the
// shift of the fingerprint whose byte k is b and whose other bytes are zero, high word at 2i.
type ShiftTable = Int32Array;

// The shifted fingerprint, read right after the call, so that callers keep theirs in locals.
let shiftedHigh = 0;
let shiftedLow = 0;

const shiftWithTable = (table: ShiftTable, fingerprintHigh: number, fingerprintLow: number) => {
  const entry0 = (fingerprintLow & 0xff) << 1;
  const entry1 = 512 + ((fingerprintLow >>> 7) & 0x1fe);
  const entry2 = 1024 + ((fingerprintLow >>> 15) & 0x1fe);
  const entry3 = 1536 + ((fingerprintLow >>> 23) & 0x1fe);
  const entry4 = 2048 + ((fingerprintHigh & 0xff) << 1);
  const entry5 = 2560 + ((fingerprintHigh >>> 7) & 0x1fe);
  const entry6 = 3072 + ((fingerprintHigh >>> 15) & 0x1fe);
  const entry7 = 3584 + ((fingerprintHigh >>> 23) & 0x1fe);
  shiftedHigh =
    table[entry0] ^
    table[entry1] ^
    table[entry2] ^
    table[entry3] ^
    table[entry4] ^
    table[entry5] ^
    table[entry6] ^
    table[entry7];
  shiftedLow =
    table[entry0 + 1] ^
    table[entry1 + 1] ^
    table[entry2 + 1] ^
    table[entry3 + 1] ^
    table[entry4 + 1] ^
    table[entry5 + 1] ^
    table[entry6 + 1] ^
    table[entry7 + 1];
};

// Shifting is linear, so the table needs only the shifts of the 64 single bits: every other entry
// is the xor of the entry without its lowest bit and the entry of that bit.
const buildShiftTable = (
  shift: (fingerprintHigh: number, fingerprintLow: number) => void,
): ShiftTable => {
  const savedHigh = high;
  const savedLow = low;
  const table = new Int32Array(8 * 256 * 2);
  for (let byteIndex = 0; byteIndex < 8; byteIndex++) {
    const slot = byteIndex * 512;
    for (let bit = 0; bit < 8; bit++) {
      const word = 1 << (8 * (byteIndex & 3) + bit);
      shift(byteIndex >= 4 ? word : 0, byteIndex < 4 ? word : 0);
      table[slot + (2 << bit)] = shiftedHigh;
      table[slot + (2 << bit) + 1] = shiftedLow;
    }
    for (let byte = 3; byte < 256; byte++) {
      const lowest = byte & -byte;
      if (lowest === byte) continue;
      const entry = slot + 2 * byte;
      table[entry] = table[slot + 2 * lowest] ^ table[slot + 2 * (byte ^ lowest)];
      table[entry + 1] = table[slot + 2 * lowest + 1] ^ table[slot + 2 * (byte ^ lowest) + 1];
    }
  }
  high = savedHigh;
  low = savedLow;
  return table;
};

// Shifts by 2^j zero bytes.
const powerTables: ShiftTable[] = [];
const getPowerTable = (exponent: number) => {
  let table = powerTables[exponent];
  if (table) return table;
  table =
    exponent === 0
      ? buildShiftTable((fingerprintHigh, fingerprintLow) => {
          high = fingerprintHigh;
          low = fingerprintLow;
          extendByte(0);
          shiftedHigh = high;
          shiftedLow = low;
        })
      : ((half) =>
          buildShiftTable((fingerprintHigh, fingerprintLow) => {
            shiftWithTable(half, fingerprintHigh, fingerprintLow);
            shiftWithTable(half, shiftedHigh, shiftedLow);
          }))(getPowerTable(exponent - 1));
  powerTables[exponent] = table;
  return table;
};

const shiftByPowers = (fingerprintHigh: number, fingerprintLow: number, length: number) => {
  for (let exponent = 0; length > 0; exponent++, length = Math.floor(length / 2)) {
    if (length % 2 === 1) {
      // Making the table shifts too, so the result is read only after it.
      const table = getPowerTable(exponent);
      shiftWithTable(table, fingerprintHigh, fingerprintLow);
      fingerprintHigh = shiftedHigh;
      fingerprintLow = shiftedLow;
    }
  }
  shiftedHigh = fingerprintHigh;
  shiftedLow = fingerprintLow;
};

// Tables for the lengths of values and of the tails of states, as far as the cap allows, numbered
// from 1 in the order made.
const lengthTables: ShiftTable[] = [];
const lengthTableNumbers = new Map<number, number>();
const MAXIMUM_LENGTH_TABLES = 1024;

// The number of the table that shifts by a length, or -1 past the cap.
const getLengthTableNumber = (length: number) => {
  const known = lengthTableNumbers.get(length);
  if (known !== undefined) return known;
  if (lengthTables.length >= MAXIMUM_LENGTH_TABLES) return -1;
  lengthTables.push(
    buildShiftTable((fingerprintHigh, fingerprintLow) =>
      shiftByPowers(fingerprintHigh, fingerprintLow, length),
    ),
  );
  lengthTableNumbers.set(length, lengthTables.length);
  return lengthTables.length;
};

// F(v) as high and low words, and |v|, for each value id.
let valueHigh = new Int32Array(0);
let valueLow = new Int32Array(0);
let valueLength = new Float64Array(0);
let computed = new Uint8Array(0);
// The number of the length table for each value id: 0 until looked up, -1 past the cap.
let valueTables = new Int32Array(0);

const ensureCapacity = (id: number) => {
  if (id < computed.length) return;
  const capacity = Math.max(1024, (id + 1) * 2);
  const nextHigh = new Int32Array(capacity);
  nextHigh.set(valueHigh);
  valueHigh = nextHigh;
  const nextLow = new Int32Array(capacity);
  nextLow.set(valueLow);
  valueLow = nextLow;
  const nextLength = new Float64Array(capacity);
  nextLength.set(valueLength);
  valueLength = nextLength;
  const nextComputed = new Uint8Array(capacity);
  nextComputed.set(computed);
  computed = nextComputed;
  const nextTables = new Int32Array(capacity);
  nextTables.set(valueTables);
  valueTables = nextTables;
};

const BOOL_VALUE = 0;
const INT_VALUE = 1;
const STRING_VALUE = 3;
const SET_ENUM_VALUE = 5;
const FCN_RCD_VALUE = 9;
const MODEL_VALUE = 21;

// Shifts a fingerprint by a value's length, with the table found once per value.
const shiftByValue = (id: number, fingerprintHigh: number, fingerprintLow: number) => {
  let number = valueTables[id];
  if (number === 0) {
    number = getLengthTableNumber(valueLength[id]);
    valueTables[id] = number;
  }
  if (number > 0) shiftWithTable(lengthTables[number - 1], fingerprintHigh, fingerprintLow);
  else shiftByPowers(fingerprintHigh, fingerprintLow, valueLength[id]);
};

// Extends the running fingerprint by a value, F and length known.
const extendKnown = (id: number) => {
  shiftByValue(id, high, low);
  high = shiftedHigh ^ valueHigh[id];
  low = shiftedLow ^ valueLow[id];
};

const computeValue = (id: number) => {
  ensureCapacity(id);
  if (computed[id]) return;
  const kind = kindOf(id);
  // Children first, since computing them uses the running fingerprint.
  if (kind === KIND_SET) {
    for (let index = 0; index < sizeOf(id); index++) computeValue(elementAt(id, index));
  } else if (
    kind !== KIND_BOOL &&
    kind !== KIND_INT &&
    kind !== KIND_STRING &&
    kind !== KIND_MODEL
  ) {
    for (let index = 0; index < sizeOf(id); index++) {
      computeValue(getKey(id, index));
      computeValue(getRangeValue(id, index));
    }
  }
  ensureCapacity(id);
  high = 0;
  low = 0;
  let length: number;
  switch (kind) {
    case KIND_BOOL:
      extendByte(BOOL_VALUE);
      extendByte(id === TRUE ? 116 : 102);
      length = 2;
      break;
    case KIND_INT:
      extendByte(INT_VALUE);
      extendInt(intOf(id));
      length = 5;
      break;
    case KIND_STRING: {
      const text = textOf(id);
      extendByte(STRING_VALUE);
      extendInt(text.length);
      for (let index = 0; index < text.length; index++) extendByte(text.charCodeAt(index) & 0xff);
      length = 5 + text.length;
      break;
    }
    case KIND_MODEL:
      extendByte(MODEL_VALUE);
      extendInt(getStringRank(textOf(id)) + 1);
      length = 5;
      break;
    case KIND_SET: {
      extendByte(SET_ENUM_VALUE);
      extendInt(sizeOf(id));
      length = 5;
      for (let index = 0; index < sizeOf(id); index++) {
        const element = elementAt(id, index);
        extendKnown(element);
        length += valueLength[element];
      }
      break;
    }
    default: {
      extendByte(FCN_RCD_VALUE);
      extendInt(sizeOf(id));
      length = 5;
      for (let index = 0; index < sizeOf(id); index++) {
        const key = getKey(id, index);
        const value = getRangeValue(id, index);
        extendKnown(key);
        extendKnown(value);
        length += valueLength[key] + valueLength[value];
      }
    }
  }
  valueHigh[id] = high;
  valueLow[id] = low;
  valueLength[id] = length;
  computed[id] = 1;
};

export const resetFingerprints = () => {
  computed = new Uint8Array(0);
  valueTables = new Int32Array(0);
  valueHigh = new Int32Array(0);
  valueLow = new Int32Array(0);
  valueLength = new Float64Array(0);
};

// The TLC fingerprints of states stored one after another, each `width` ids in the engine's
// variable order, read in TLC's variable order.
//
// A state's fingerprint is shift(INIT, L) xor the xor over its values v_j of shift(F(v_j), S_j),
// where L is the length of all its values and S_j that of the values after v_j. Where a state
// differs from its parent only in values of the same lengths, L and every S_j are the parent's, so
// its fingerprint is the parent's xor shift(F(v_j) xor F(v'_j), S_j) for each value that changed.
export const getStateFingerprints = (
  states: Int32Array,
  count: number,
  width: number,
  order: number[],
  parents?: Int32Array,
) => {
  const setting = getFingerprintSetting();
  if (setting === "reference") return getStateFingerprintsReference(states, count, width, order);
  const fingerprints = new BigInt64Array(count);
  const words = new Int32Array(fingerprints.buffer);
  const variables = order.length;
  // The tail length each position last had and its table, since it seldom changes.
  const tails = new Float64Array(variables).fill(-1);
  const tailTables = new Int32Array(variables);
  // Whether a state's fingerprint follows from that of an earlier one, which then is in
  // shiftedHigh and shiftedLow. Values are computed as they first appear.
  const isFromEarlier = (offset: number, earlier: number) => {
    const earlierOffset = earlier * width;
    let fingerprintHigh = words[2 * earlier + 1];
    let fingerprintLow = words[2 * earlier];
    let tail = 0;
    for (let position = variables - 1; position >= 0; position--) {
      const index = order[position];
      const id = states[offset + index];
      const earlierId = states[earlierOffset + index];
      if (id !== earlierId) {
        if (id >= computed.length || computed[id] === 0) computeValue(id);
        if (valueLength[id] !== valueLength[earlierId]) return false;
        if (tails[position] !== tail) {
          tails[position] = tail;
          tailTables[position] = getLengthTableNumber(tail);
        }
        const changedHigh = valueHigh[id] ^ valueHigh[earlierId];
        const changedLow = valueLow[id] ^ valueLow[earlierId];
        const number = tailTables[position];
        if (number > 0) shiftWithTable(lengthTables[number - 1], changedHigh, changedLow);
        else shiftByPowers(changedHigh, changedLow, tail);
        fingerprintHigh ^= shiftedHigh;
        fingerprintLow ^= shiftedLow;
      }
      tail += valueLength[id];
    }
    shiftedHigh = fingerprintHigh;
    shiftedLow = fingerprintLow;
    return true;
  };
  for (let state = 0; state < count; state++) {
    const offset = state * width;
    const parent = parents === undefined ? -1 : parents[state];
    if (parent >= 0 && parent < state && isFromEarlier(offset, parent)) {
      words[2 * state] = shiftedLow;
      words[2 * state + 1] = shiftedHigh;
      continue;
    }
    let fingerprintHigh = INITIAL_HIGH;
    let fingerprintLow = INITIAL_LOW;
    for (let position = 0; position < variables; position++) {
      const id = states[offset + order[position]];
      if (id >= computed.length || computed[id] === 0) computeValue(id);
      shiftByValue(id, fingerprintHigh, fingerprintLow);
      fingerprintHigh = shiftedHigh ^ valueHigh[id];
      fingerprintLow = shiftedLow ^ valueLow[id];
    }
    words[2 * state] = fingerprintLow;
    words[2 * state + 1] = fingerprintHigh;
  }
  if (setting === "check") {
    const reference = getStateFingerprintsReference(states, count, width, order);
    for (let state = 0; state < count; state++) {
      if (fingerprints[state] !== reference[state]) {
        throw new EngineInvariantError(
          `the fingerprint of state ${state} differs from the reference`,
        );
      }
    }
  }
  return fingerprints;
};

// The fingerprints extended over every value of every state, which PROVE_IT_FINGERPRINT=reference
// takes and =check compares with.
export const getStateFingerprintsReference = (
  states: Int32Array,
  count: number,
  width: number,
  order: number[],
) => {
  const fingerprints = new BigInt64Array(count);
  const words = new Int32Array(fingerprints.buffer);
  for (let state = 0; state < count; state++) {
    for (const index of order) computeValue(states[state * width + index]);
  }
  for (let state = 0; state < count; state++) {
    high = INITIAL_HIGH;
    low = INITIAL_LOW;
    for (const index of order) extendKnown(states[state * width + index]);
    words[2 * state] = low;
    words[2 * state + 1] = high;
  }
  return fingerprints;
};

// TLC's 64-bit fingerprints of the engine's states, which TLC reports the smallest distance between.
//
// TLC fingerprints a state by extending FP64 over the bytes of its values. Extending is linear over
// GF(2), so extending a fingerprint fp by the bytes of a value v is shift(fp, |v|) xor F(v), where F(v)
// extends zero by v and shift extends by |v| zero bytes. F and |v| are computed once per interned
// value, and a state's fingerprint takes one shift and one xor per variable.

import { getStringRank } from "../values";
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

const buildShiftTable = (
  shift: (fingerprintHigh: number, fingerprintLow: number) => void,
): ShiftTable => {
  const savedHigh = high;
  const savedLow = low;
  const table = new Int32Array(8 * 256 * 2);
  for (let byteIndex = 0; byteIndex < 8; byteIndex++) {
    for (let byte = 0; byte < 256; byte++) {
      const fingerprintLow = byteIndex < 4 ? byte << (8 * byteIndex) : 0;
      const fingerprintHigh = byteIndex >= 4 ? byte << (8 * (byteIndex - 4)) : 0;
      shift(fingerprintHigh, fingerprintLow);
      const entry = (byteIndex * 256 + byte) * 2;
      table[entry] = high;
      table[entry + 1] = low;
    }
  }
  high = savedHigh;
  low = savedLow;
  return table;
};

const applyShiftTable = (table: ShiftTable) => {
  const fingerprintHigh = high;
  const fingerprintLow = low;
  let nextHigh = 0;
  let nextLow = 0;
  for (let byteIndex = 0; byteIndex < 8; byteIndex++) {
    const byte =
      byteIndex < 4
        ? (fingerprintLow >>> (8 * byteIndex)) & 0xff
        : (fingerprintHigh >>> (8 * (byteIndex - 4))) & 0xff;
    const entry = (byteIndex * 256 + byte) * 2;
    nextHigh ^= table[entry];
    nextLow ^= table[entry + 1];
  }
  high = nextHigh;
  low = nextLow;
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
        })
      : ((half) =>
          buildShiftTable((fingerprintHigh, fingerprintLow) => {
            high = fingerprintHigh;
            low = fingerprintLow;
            applyShiftTable(half);
            applyShiftTable(half);
          }))(getPowerTable(exponent - 1));
  powerTables[exponent] = table;
  return table;
};

const lengthTables = new Map<number, ShiftTable>();
const MAXIMUM_LENGTH_TABLES = 512;

const shiftBy = (length: number) => {
  let table = lengthTables.get(length);
  if (!table && lengthTables.size < MAXIMUM_LENGTH_TABLES) {
    table = buildShiftTable((fingerprintHigh, fingerprintLow) => {
      high = fingerprintHigh;
      low = fingerprintLow;
      shiftByPowers(length);
    });
    lengthTables.set(length, table);
  }
  if (table) applyShiftTable(table);
  else shiftByPowers(length);
};

const shiftByPowers = (length: number) => {
  for (let exponent = 0; length > 0; exponent++, length = Math.floor(length / 2)) {
    if (length % 2 === 1) applyShiftTable(getPowerTable(exponent));
  }
};

// F(v) as high and low words, and |v|, for each value id.
let valueHigh = new Int32Array(0);
let valueLow = new Int32Array(0);
let valueLength = new Float64Array(0);
let computed = new Uint8Array(0);

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
};

const BOOL_VALUE = 0;
const INT_VALUE = 1;
const STRING_VALUE = 3;
const SET_ENUM_VALUE = 5;
const FCN_RCD_VALUE = 9;
const MODEL_VALUE = 21;

// Extends the running fingerprint by a value, F and length known.
const extendKnown = (id: number) => {
  shiftBy(valueLength[id]);
  high ^= valueHigh[id];
  low ^= valueLow[id];
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
  valueHigh = new Int32Array(0);
  valueLow = new Int32Array(0);
  valueLength = new Float64Array(0);
};

// The TLC fingerprints of states stored one after another, each `width` ids in the engine's
// variable order, read in TLC's variable order.
export const getStateFingerprints = (
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

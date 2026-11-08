import {
  getStringRank,
  isFunctionValue,
  isModelValue,
  type ModelValue,
  toFiniteFunction,
  toFiniteSet,
  type Value,
} from "../values";

// FP64 with TLC's first irreducible polynomial, FP64.Polys[0], which `-fp 0` selects, as its high
// and low 32 bits, which avoids a BigInt operation for every byte. A fingerprint starts as the
// polynomial. The engine's fingerprints share these and the table.
export const INITIAL_HIGH = 0x911498ae | 0;
export const INITIAL_LOW = 0x0e66bad6;

// FP64's ByteModTable: entry b is the fingerprint from zero of byte b, the sum of x^(71 - k) mod the
// polynomial for each bit k of b, with x^0 in a fingerprint's top bit. It is built from 32-bit
// halves, as building it from BigInts took about a millisecond of each run's startup.
const createByteModTable = () => {
  const highs = new Int32Array(256);
  const lows = new Int32Array(256);
  let powerHigh = 1 << 31;
  let powerLow = 0;
  for (let exponent = 1; exponent < 72; exponent++) {
    const isReduced = (powerLow & 1) !== 0;
    powerLow = ((powerLow >>> 1) | (powerHigh << 31)) ^ (isReduced ? INITIAL_LOW : 0);
    powerHigh = (powerHigh >>> 1) ^ (isReduced ? INITIAL_HIGH : 0);
    const bit = exponent < 64 ? 0 : 1 << (71 - exponent);
    for (let byte = 0; byte < 256; byte++) {
      if ((byte & bit) === 0) continue;
      highs[byte] ^= powerHigh;
      lows[byte] ^= powerLow;
    }
  }
  return { highs, lows };
};

const BYTE_MOD_TABLE = createByteModTable();
export const BYTE_MOD_HIGH = BYTE_MOD_TABLE.highs;
export const BYTE_MOD_LOW = BYTE_MOD_TABLE.lows;

// The fingerprint being extended.
let high = INITIAL_HIGH;
let low = INITIAL_LOW;

const extendByte = (byte: number) => {
  const index = (byte ^ low) & 0xff;
  low = ((low >>> 8) | (high << 24)) ^ BYTE_MOD_LOW[index];
  high = (high >>> 8) ^ BYTE_MOD_HIGH[index];
};

// Extending is linear over GF(2), so extending by four bytes at once shifts the fingerprint by a
// word and adds, for each of the four, the fingerprint from zero of that byte followed by the zero
// bytes that come after it: SLICE_HIGH[k] and SLICE_LOW[k] hold them for k zero bytes after.
const createSliceTables = () => {
  const highs = [BYTE_MOD_HIGH];
  const lows = [BYTE_MOD_LOW];
  for (let zeros = 1; zeros < 4; zeros++) {
    const previousHigh = highs[zeros - 1];
    const previousLow = lows[zeros - 1];
    const sliceHigh = new Int32Array(256);
    const sliceLow = new Int32Array(256);
    for (let byte = 0; byte < 256; byte++) {
      const index = previousLow[byte] & 0xff;
      sliceLow[byte] =
        ((previousLow[byte] >>> 8) | (previousHigh[byte] << 24)) ^ BYTE_MOD_LOW[index];
      sliceHigh[byte] = (previousHigh[byte] >>> 8) ^ BYTE_MOD_HIGH[index];
    }
    highs.push(sliceHigh);
    lows.push(sliceLow);
  }
  return { highs, lows };
};

const SLICES = createSliceTables();
const SLICE_HIGH_0 = SLICES.highs[0];
const SLICE_HIGH_1 = SLICES.highs[1];
const SLICE_HIGH_2 = SLICES.highs[2];
const SLICE_HIGH_3 = SLICES.highs[3];
const SLICE_LOW_0 = SLICES.lows[0];
const SLICE_LOW_1 = SLICES.lows[1];
const SLICE_LOW_2 = SLICES.lows[2];
const SLICE_LOW_3 = SLICES.lows[3];

// Extends the fingerprint by the four bytes of a word, lowest first.
const extendInt = (word: number) => {
  const mixed = low ^ word;
  const first = mixed & 0xff;
  const second = (mixed >>> 8) & 0xff;
  const third = (mixed >>> 16) & 0xff;
  const fourth = mixed >>> 24;
  low = high ^ SLICE_LOW_3[first] ^ SLICE_LOW_2[second] ^ SLICE_LOW_1[third] ^ SLICE_LOW_0[fourth];
  high = SLICE_HIGH_3[first] ^ SLICE_HIGH_2[second] ^ SLICE_HIGH_1[third] ^ SLICE_HIGH_0[fourth];
};

const BOOL_VALUE = 0;
const INT_VALUE = 1;
const STRING_VALUE = 3;
const SET_ENUM_VALUE = 5;
const FCN_RCD_VALUE = 9;
const MODEL_VALUE = 21;

// Value#fingerPrint for TLC's booleans, integers, strings, and model values, which returns how
// many bytes it extends the fingerprint by. A model value extends the fingerprint with its
// UniqueString token, and TLC numbers tokens from 1 in intern order.
const extendScalar = (value: boolean | number | string | ModelValue) => {
  if (typeof value === "boolean") {
    extendByte(BOOL_VALUE);
    extendByte(value ? 116 : 102);
    return 2;
  }
  if (typeof value === "number") {
    extendByte(INT_VALUE);
    extendInt(value);
    return 5;
  }
  if (typeof value === "string") {
    extendByte(STRING_VALUE);
    extendInt(value.length);
    const whole = value.length & ~3;
    for (let index = 0; index < whole; index += 4) {
      extendInt(
        (value.charCodeAt(index) & 0xff) |
          ((value.charCodeAt(index + 1) & 0xff) << 8) |
          ((value.charCodeAt(index + 2) & 0xff) << 16) |
          ((value.charCodeAt(index + 3) & 0xff) << 24),
      );
    }
    for (let index = whole; index < value.length; index++) extendByte(value.charCodeAt(index));
    return 5 + value.length;
  }
  extendByte(MODEL_VALUE);
  extendInt(getStringRank(value.name) + 1);
  return 5;
};

// Value#fingerPrint for each of TLC's value classes.
const extendValue = (value: Value) => {
  if (typeof value !== "object" || isModelValue(value)) {
    extendScalar(value);
  } else if (isFunctionValue(value)) {
    const functionValue = toFiniteFunction(value);
    extendByte(FCN_RCD_VALUE);
    extendInt(functionValue.domain.length);
    for (let index = 0; index < functionValue.domain.length; index++) {
      extendValue(functionValue.domain[index]);
      extendValue(functionValue.range[index]);
    }
  } else {
    const elements = toFiniteSet(value).elements;
    extendByte(SET_ENUM_VALUE);
    extendInt(elements.length);
    for (const element of elements) extendValue(element);
  }
};

// TLCStateMut#fingerPrint of variable values in TLC's variable order. Evaluating a lazy value can
// fingerprint another, so this restores the fingerprint it interrupts.
export const getTlcFingerprint = (state: Value[]) => {
  const outer = { high, low };
  high = INITIAL_HIGH;
  low = INITIAL_LOW;
  for (const value of state) extendValue(value);
  const fingerprint = (BigInt(high >>> 0) << 32n) | BigInt(low >>> 0);
  high = outer.high;
  low = outer.low;
  return fingerprint;
};

// TLCStateMut#fingerPrint of each state's variables in TLC's variable order, as the fingerprint
// store reads them.
export const getTlcFingerprints = (states: Value[][], order: number[]) => {
  const fingerprints = new BigInt64Array(states.length);
  // Each fingerprint's low and high words, as a BigInt64Array is little-endian.
  const words = new Int32Array(fingerprints.buffer);
  const outerHigh = high;
  const outerLow = low;
  states.forEach((state, position) => {
    high = INITIAL_HIGH;
    low = INITIAL_LOW;
    for (const index of order) extendValue(state[index]);
    words[2 * position] = low;
    words[2 * position + 1] = high;
  });
  high = outerHigh;
  low = outerLow;
  return fingerprints;
};

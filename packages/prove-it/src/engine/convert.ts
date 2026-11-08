// Conversion between the engine's interned ids and the reference interpreter's values, for
// constants, for operators the engine hands to the reference implementation, and for traces.

import {
  createModelValue,
  createSortedFunction,
  createSortedRecord,
  createSortedSet,
  createTuple,
  isTlcEnumerable,
  toFiniteFunction,
  toFiniteSet,
  type Value,
} from "../values";
import {
  bail,
  bool,
  elementAt,
  functionOf,
  generation,
  getKey,
  getRangeValue,
  int,
  intOf,
  KIND_BOOL,
  KIND_FUNCTION,
  KIND_INT,
  KIND_MODEL,
  KIND_SET,
  KIND_STRING,
  KIND_TUPLE,
  kindOf,
  model,
  setOf,
  sizeOf,
  str,
  textOf,
  TRUE,
  tupleOf,
} from "./store";

const cache = { generation: -1, values: [] as (Value | undefined)[] };

export const toValue = (id: number): Value => {
  if (cache.generation !== generation) {
    cache.generation = generation;
    cache.values = [];
  }
  const known = cache.values[id];
  if (known !== undefined) return known;
  const value = buildValue(id);
  cache.values[id] = value;
  return value;
};

const buildValue = (id: number): Value => {
  switch (kindOf(id)) {
    case KIND_BOOL:
      return id === TRUE;
    case KIND_INT:
      return intOf(id);
    case KIND_STRING:
      return textOf(id);
    case KIND_MODEL:
      return createModelValue(textOf(id));
    case KIND_SET: {
      const size = sizeOf(id);
      const elements: Value[] = new Array(size);
      for (let index = 0; index < size; index++) elements[index] = toValue(elementAt(id, index));
      return createSortedSet(elements);
    }
    case KIND_TUPLE: {
      const size = sizeOf(id);
      const elements: Value[] = new Array(size);
      for (let index = 0; index < size; index++)
        elements[index] = toValue(getRangeValue(id, index));
      return createTuple(elements);
    }
    case KIND_FUNCTION: {
      const size = sizeOf(id);
      const domain: Value[] = new Array(size);
      const range: Value[] = new Array(size);
      let isRecord = true;
      for (let index = 0; index < size; index++) {
        domain[index] = toValue(getKey(id, index));
        range[index] = toValue(getRangeValue(id, index));
        if (typeof domain[index] !== "string") isRecord = false;
      }
      return isRecord ? createSortedRecord(domain, range) : createSortedFunction(domain, range);
    }
    default:
      return bail("unknown value kind");
  }
};

export const fromValue = (value: Value): number => {
  if (typeof value === "boolean") return bool(value);
  if (typeof value === "number") return int(value);
  if (typeof value === "string") return str(value);
  if (value.kind === "ModelValue") return model(value.name);
  if (value.kind === "Function" || value.kind === "LazyFunction") {
    const finite = toFiniteFunction(value);
    const keys = finite.domain.map(fromValue);
    const values = finite.range.map(fromValue);
    return functionOf(keys, values);
  }
  if (value.kind === "Interval") {
    const elements: number[] = [];
    for (let element = value.low; element <= value.high; element++) elements.push(int(element));
    return setOf(elements);
  }
  if (value.kind === "Set") return setOf(value.elements.map(fromValue));
  if (!isTlcEnumerable(value)) return bail(`a value the engine can't hold: ${value.kind}`);
  return setOf(toFiniteSet(value).elements.map(fromValue));
};

// The id of a value the interpreter holds enumerated, or undefined for one it holds lazily, which
// only the interpreter enumerates, or one the engine can't hold.
export const fromEnumeratedValue = (value: Value): number | undefined => {
  if (typeof value === "boolean") return bool(value);
  if (typeof value === "number") return int(value);
  if (typeof value === "string") return str(value);
  if (value.kind === "ModelValue") return model(value.name);
  if (value.kind === "Interval") return fromValue(value);
  if (value.kind === "Function") {
    const keys = fromEnumeratedValues(value.domain);
    const values = keys && fromEnumeratedValues(value.range);
    return keys && values && functionOf(keys, values);
  }
  if (value.kind !== "Set") return undefined;
  const elements = fromEnumeratedValues(value.elements);
  return elements && setOf(elements);
};

const fromEnumeratedValues = (values: Value[]) => {
  const ids: number[] = [];
  for (const value of values) {
    const id = fromEnumeratedValue(value);
    if (id === undefined) return undefined;
    ids.push(id);
  }
  return ids;
};

export const fromTuple = (elements: number[]) => tupleOf(elements, elements.length);

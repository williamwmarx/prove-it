// Conversion between the engine's interned ids and the reference interpreter's values, for
// constants, for operators the engine hands to the reference implementation, and for traces.

import {
  createModelValue,
  createSortedFunction,
  createSortedRecord,
  createSortedSet,
  createTuple,
  formatPrinted,
  isFieldName,
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

// The text Print gives a value whose text TLC doesn't derive from how it was built, which the
// engine forgets: TLC prints an interval as one, such as 1..3, and a record's fields in the order
// they were written.
export const formatPrintedId = (id: number) =>
  isPrintable(id)
    ? formatPrinted(toValue(id))
    : bail("printing a value whose text depends on how TLC built it");

const isPrintable = (id: number): boolean => {
  const kind = kindOf(id);
  if (kind !== KIND_SET && kind !== KIND_TUPLE && kind !== KIND_FUNCTION) return true;
  const size = sizeOf(id);
  for (let index = 0; index < size; index++) {
    if (kind === KIND_TUPLE) {
      if (!isPrintable(getRangeValue(id, index))) return false;
      continue;
    }
    const element = kind === KIND_SET ? elementAt(id, index) : getKey(id, index);
    const first = kind === KIND_SET ? elementAt(id, 0) : getKey(id, 0);
    if (kindOf(element) !== kindOf(first) || !isPrintable(element)) return false;
    if (kind === KIND_FUNCTION) {
      if (kindOf(element) === KIND_STRING && (size > 1 || !isFieldName(textOf(element))))
        return false;
      if (!isPrintable(getRangeValue(id, index))) return false;
    }
  }
  // A set of consecutive integers may be an interval.
  return (
    kind !== KIND_SET ||
    size === 0 ||
    kindOf(elementAt(id, 0)) !== KIND_INT ||
    intOf(elementAt(id, size - 1)) - intOf(elementAt(id, 0)) !== size - 1
  );
};

export const fromTuple = (elements: number[]) => tupleOf(elements, elements.length);

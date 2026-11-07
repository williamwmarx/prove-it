// TLC's symmetry reduction on the engine's states: each state is replaced by its smallest image
// under the symmetry group, compared variable by variable in TLC's variable order, as
// TLCStateMut#fingerPrint picks it. Permuting an interned value is cached per permutation, in an
// array indexed by its id, so a value is permuted once however many states hold it.

import {
  compare,
  elementAt,
  functionOf,
  getKey,
  getRangeValue,
  getValueCount,
  KIND_FUNCTION,
  KIND_MODEL,
  KIND_SET,
  KIND_TUPLE,
  kindOf,
  model,
  setOf,
  sizeOf,
  tupleOf,
} from "./store";

// A permutation as the model values it moves, by name, to their images.
export type NamedPermutation = [string, string][];

export const createCanonicalizer = (group: NamedPermutation[], order: number[]) => {
  const permutations = group.map(
    (pairs) => new Map(pairs.map(([name, image]): [number, number] => [model(name), model(image)])),
  );
  // Each permutation's image of each id permuted so far, or -1.
  const images = permutations.map(() => new Int32Array(0));

  const permute = (id: number, index: number): number => {
    const kind = kindOf(id);
    if (kind === KIND_MODEL) return permutations[index].get(id) ?? id;
    if (kind !== KIND_SET && kind !== KIND_FUNCTION && kind !== KIND_TUPLE) return id;
    const known = id < images[index].length ? images[index][id] : -1;
    if (known !== -1) return known;
    const size = sizeOf(id);
    let isMoved = false;
    let result = id;
    if (kind === KIND_SET) {
      const elements: number[] = new Array(size);
      for (let position = 0; position < size; position++) {
        const element = elementAt(id, position);
        elements[position] = permute(element, index);
        if (elements[position] !== element) isMoved = true;
      }
      if (isMoved) result = setOf(elements);
    } else if (kind === KIND_TUPLE) {
      const elements: number[] = new Array(size);
      for (let position = 0; position < size; position++) {
        const element = getRangeValue(id, position);
        elements[position] = permute(element, index);
        if (elements[position] !== element) isMoved = true;
      }
      if (isMoved) result = tupleOf(elements, size);
    } else {
      const keys: number[] = new Array(size);
      const values: number[] = new Array(size);
      for (let position = 0; position < size; position++) {
        const key = getKey(id, position);
        const value = getRangeValue(id, position);
        keys[position] = permute(key, index);
        values[position] = permute(value, index);
        if (keys[position] !== key || values[position] !== value) isMoved = true;
      }
      if (isMoved) result = functionOf(keys, values);
    }
    if (id >= images[index].length) {
      const grown = new Int32Array(Math.max(1024, getValueCount() * 2)).fill(-1);
      grown.set(images[index]);
      images[index] = grown;
    }
    images[index][id] = result;
    return result;
  };

  const smallest = new Int32Array(order.length);
  const permuted = new Int32Array(order.length);
  // Replaces the state with its representative.
  return (state: Int32Array) => {
    smallest.set(state);
    for (let index = 0; index < permutations.length; index++) {
      let comparison = 0;
      for (const variable of order) {
        permuted[variable] = permute(state[variable], index);
        if (comparison === 0) comparison = compare(permuted[variable], smallest[variable]);
        if (comparison > 0) break;
      }
      if (comparison < 0) smallest.set(permuted);
    }
    state.set(smallest);
  };
};

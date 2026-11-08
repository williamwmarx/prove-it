// TLC's symmetry reduction on the engine's states: each state is replaced by its smallest image
// under the symmetry group, compared variable by variable in TLC's variable order, as
// TLCStateMut#fingerPrint picks it. Permuting an interned value is cached per permutation, in an
// array indexed by its id, so a value is permuted once however many states hold it.
//
// A state's values are mostly new, but their parts mostly aren't, so a permutation's image of a
// state's value is compared with the smallest image so far without building it, from the cached
// images of its parts. Only the image of a permutation that wins is built.

import {
  compare,
  elementAt,
  functionOf,
  getKey,
  getModelType,
  getRangeValue,
  getValueCount,
  KIND_FUNCTION,
  KIND_MODEL,
  KIND_SET,
  KIND_TUPLE,
  kindOf,
  model,
  setOfRange,
  sizeOf,
  tupleOfRange,
} from "./store";

// A permutation as the model values it moves, by name, to their images.
export type NamedPermutation = [string, string][];

export const createCanonicalizer = (group: NamedPermutation[], order: number[]) => {
  const permutations = group.map(
    (pairs) => new Map(pairs.map(([name, image]): [number, number] => [model(name), model(image)])),
  );
  // TLC sorts each image, which fails where it mixes model values of different types; the images
  // of a group that can mix them are built, so that the engine fails there too.
  const isTypePreserving = permutations.every((permutation) =>
    [...permutation].every(([id, image]) => getModelType(id) === getModelType(image)),
  );
  // Each permutation's image of each id permuted so far, or -1.
  const images = permutations.map(() => new Int32Array(0));
  let stack = new Int32Array(256);
  let top = 0;

  const remember = (id: number, index: number, image: number) => {
    if (id >= images[index].length) {
      const grown = new Int32Array(Math.max(1024, getValueCount() * 2)).fill(-1);
      grown.set(images[index]);
      images[index] = grown;
    }
    images[index][id] = image;
  };

  const permute = (id: number, index: number): number => {
    const kind = kindOf(id);
    if (kind === KIND_MODEL) return permutations[index].get(id) ?? id;
    if (kind !== KIND_SET && kind !== KIND_FUNCTION && kind !== KIND_TUPLE) return id;
    const known = id < images[index].length ? images[index][id] : -1;
    if (known !== -1) return known;
    const size = sizeOf(id);
    let isMoved = false;
    let result = id;
    if (kind === KIND_SET || kind === KIND_TUPLE) {
      // The images go on the stack, above those of the values being permuted around this one.
      const at = top;
      top += size;
      if (top > stack.length) {
        const grown = new Int32Array(2 * top);
        grown.set(stack);
        stack = grown;
      }
      for (let position = 0; position < size; position++) {
        const element = kind === KIND_SET ? elementAt(id, position) : getRangeValue(id, position);
        const image = permute(element, index);
        stack[at + position] = image;
        if (image !== element) isMoved = true;
      }
      if (isMoved)
        result = kind === KIND_SET ? setOfRange(stack, at, size) : tupleOfRange(stack, at, size);
      top = at;
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
    remember(id, index, result);
    return result;
  };

  // The ids of the parts of the value being compared, and stamps that mark ids by the comparison
  // that saw them, with the position each key was seen at.
  let parts = new Int32Array(64);
  let marks = new Int32Array(0);
  let positions = new Int32Array(0);
  let stamp = 0;

  const mark = (id: number) => {
    if (id >= marks.length) {
      const capacity = Math.max(1024, Math.max(id + 1, getValueCount()) * 2);
      const grownMarks = new Int32Array(capacity);
      grownMarks.set(marks);
      marks = grownMarks;
      const grownPositions = new Int32Array(capacity);
      grownPositions.set(positions);
      positions = grownPositions;
    }
    marks[id] = stamp;
  };
  const isMarked = (id: number) => id < marks.length && marks[id] === stamp;
  const nextStamp = () => {
    if (stamp === 0x7fffffff) {
      marks.fill(0);
      stamp = 0;
    }
    stamp++;
  };

  // How the parts, once sorted, compare in TLC's order with those of smallest, as many and as
  // distinct: two such sequences first differ where the least of the parts in only one of them
  // stands, so the sequence holding it is the smaller.
  const compareParts = (size: number, smallest: number, getPart: typeof elementAt) => {
    nextStamp();
    for (let position = 0; position < size; position++) mark(getPart(smallest, position));
    let least = -1;
    for (let position = 0; position < size; position++) {
      const part = parts[position];
      if (!isMarked(part) && (least === -1 || compare(part, least) < 0)) least = part;
    }
    if (least === -1) return 0;
    nextStamp();
    for (let position = 0; position < size; position++) mark(parts[position]);
    let position = 0;
    while (isMarked(getPart(smallest, position))) position++;
    return compare(least, getPart(smallest, position));
  };

  // How the image of a composite value compares with smallest, the image of the same value under
  // another permutation, so of its kind and size.
  const compareUnbuilt = (id: number, index: number, smallest: number) => {
    const kind = kindOf(id);
    const size = sizeOf(id);
    if (kind === KIND_TUPLE) {
      for (let position = 0; position < size; position++) {
        const comparison = compare(
          permute(getRangeValue(id, position), index),
          getRangeValue(smallest, position),
        );
        if (comparison !== 0) return comparison;
      }
      return 0;
    }
    if (size > parts.length) parts = new Int32Array(2 * size);
    const getPart = kind === KIND_SET ? elementAt : getKey;
    for (let position = 0; position < size; position++) {
      parts[position] = permute(getPart(id, position), index);
    }
    const comparison = compareParts(size, smallest, getPart);
    if (comparison !== 0 || kind === KIND_SET) return comparison;
    // The domains are the same, so the values compare in the order of its keys, each of which, as
    // a key of smallest, was marked and so has a position.
    for (let position = 0; position < size; position++) positions[parts[position]] = position;
    for (let position = 0; position < size; position++) {
      const comparison = compare(
        permute(getRangeValue(id, positions[getKey(smallest, position)]), index),
        getRangeValue(smallest, position),
      );
      if (comparison !== 0) return comparison;
    }
    return 0;
  };

  // For each permutation and id, the image the id's image last compared larger than, or -1: a
  // state is generated again and again, and an image that compared equal or smaller is known.
  const largerThan = permutations.map(() => new Int32Array(0));

  const compareImage = (id: number, index: number, smallest: number) => {
    const kind = kindOf(id);
    if (
      !isTypePreserving ||
      (kind !== KIND_SET && kind !== KIND_FUNCTION && kind !== KIND_TUPLE) ||
      (id < images[index].length && images[index][id] !== -1)
    ) {
      return compare(permute(id, index), smallest);
    }
    if (id >= largerThan[index].length) {
      const grown = new Int32Array(Math.max(1024, getValueCount() * 2)).fill(-1);
      grown.set(largerThan[index]);
      largerThan[index] = grown;
    }
    const known = largerThan[index][id];
    if (known === smallest) return 1;
    // A value compared again, with another image, is worth building.
    if (known !== -1) return compare(permute(id, index), smallest);
    const comparison = compareUnbuilt(id, index, smallest);
    if (comparison > 0) largerThan[index][id] = smallest;
    if (comparison === 0) remember(id, index, smallest);
    return comparison;
  };

  const smallest = new Int32Array(order.length);
  // Replaces the state with its representative.
  return (state: Int32Array) => {
    // A permutation that bailed out left its images on the stack.
    top = 0;
    smallest.set(state);
    for (let index = 0; index < permutations.length; index++) {
      let comparison = 0;
      let at = 0;
      while (at < order.length && comparison === 0) {
        comparison = compareImage(state[order[at]], index, smallest[order[at]]);
        at++;
      }
      if (comparison >= 0) continue;
      for (let rest = at - 1; rest < order.length; rest++) {
        smallest[order[rest]] = permute(state[order[rest]], index);
      }
    }
    state.set(smallest);
  };
};

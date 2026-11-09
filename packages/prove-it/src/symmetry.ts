import type { Expression, OperatorDefinition } from "./ast";
import type { Substitution } from "./config";
import { TlaConfigError, TlaEvaluationError, UNEXPECTED_EXCEPTION } from "./errors";
import { type Environment, evaluate } from "./evaluate";
import { EXIT_STATUS, setExitCode } from "./exit-codes";
import { MESSAGE_CODE } from "./tlc/messages";
import {
  compareValues,
  createFunction,
  createSet,
  createSortedFunction,
  createSortedSet,
  isEnumerable,
  isFunctionValue,
  isModelValue,
  isSetValue,
  type ModelValue,
  toFiniteFunction,
  toFiniteSet,
  type Value,
} from "./values";

export interface PermutedSet {
  name: string;
  operand: Expression | undefined;
}

// The image of each model value a permutation moves, by name.
type Images = Map<string, ModelValue>;

const getPermutationKey = (permutation: Images) =>
  [...permutation]
    .map(([name, image]) => `${name}>${image.name}`)
    .sort()
    .join(",");

const composePermutations = (first: Images, second: Images) => {
  const composed: Images = new Map();
  const names = new Set([...first.keys(), ...second.keys()]);
  names.forEach((name) => {
    const image = first.get(name);
    const result = image ? (second.get(image.name) ?? image) : second.get(name);
    if (result && result.name !== name) composed.set(name, result);
  });
  return composed;
};

// Tool#getSymmetryPerms fails with a RuntimeException as TLC starts, which TLC reports as one it
// did not expect.
const createSymmetryError = (message: string) =>
  setExitCode(new TlaEvaluationError(`${UNEXPECTED_EXCEPTION}${message}`), EXIT_STATUS.error);

const toImages = (value: Value) => {
  const functionValue = toFiniteFunction(value);
  const permutation: Images = new Map();
  functionValue.domain.forEach((key, index) => {
    const image = functionValue.range[index];
    if (!isModelValue(key) || !isModelValue(image)) {
      throw createSymmetryError("Symmetry function must have model values as domain and range.");
    }
    if (key.name !== image.name) permutation.set(key.name, image);
  });
  return permutation;
};

// SyntaxTreeNode.getHumanReadableImage, which joins the tokens of an expression without spaces.
const getExpressionImage = (expression: Expression): string => {
  if (expression.kind === "Identifier") return expression.name;
  if (expression.kind !== "Apply") return "";
  const args = expression.args.map(getExpressionImage);
  return /^[A-Za-z_]/.test(expression.operator)
    ? `${expression.operator}(${args.join(",")})`
    : args.join(expression.operator);
};

const isPermutations = (
  expression: Expression,
): expression is Expression & { kind: "Apply"; args: [Expression] } =>
  expression.kind === "Apply" &&
  expression.operator === "Permutations" &&
  expression.args.length === 1;

// The sets a SYMMETRY definition permutes, which Tool#getSymmetryPerms warns about where they hold
// fewer than two elements: each by the name the configuration substitutes for it or the text of
// its expression, and, for Permutations(S) of a constant or definition S, S. TLC binds a constant
// the configuration substitutes with <- to the definition, which it skips.
export const getPermutedSets = (
  definition: OperatorDefinition,
  substitutions: Substitution[],
): PermutedSet[] => {
  const configNames = new Map(
    substitutions
      .filter((substitution) => substitution.module === undefined)
      .map((substitution) => [substitution.target, substitution.name]),
  );
  const substitutedNames = new Set(substitutions.map((substitution) => substitution.name));
  return (definition.body.kind === "Apply" ? definition.body.args : []).map((permuted) => {
    const image = getExpressionImage(isPermutations(permuted) ? permuted.args[0] : permuted);
    const operand = isPermutations(permuted) ? permuted.args[0] : undefined;
    return {
      name: configNames.get(image) ?? image,
      operand:
        operand?.kind === "Identifier" && !substitutedNames.has(operand.name) ? operand : undefined,
    };
  });
};

export const getSymmetryGroup = (
  name: string,
  environment: Environment,
  substitutions: Substitution[],
): Images[] | undefined => {
  const definition = environment.definitions.get(name);
  if (definition === undefined && !environment.constants.has(name)) {
    throw new TlaConfigError(
      `The symmetry function ${name} specified in the configuration file\nis not defined in the specification.`,
    );
  }
  if (definition?.kind !== "Operator" || definition.params.length > 0) {
    throw createSymmetryError(`The symmetry function ${name} must specify a set of permutations.`);
  }
  const evaluateConstant = (expression: Expression) =>
    evaluate(expression, { environment, scope: undefined, state: undefined, next: undefined });
  const value = evaluateConstant(definition.body);
  if (!isSetValue(value) || !isEnumerable(value)) {
    throw createSymmetryError("The symmetry operator must specify a set of functions.");
  }
  const elements = toFiniteSet(value).elements;
  if (!elements.every(isFunctionValue)) {
    throw createSymmetryError("The symmetry values must be function records.");
  }
  const permutations = elements.map(toImages);
  const permutedSets = getPermutedSets(definition, substitutions);
  const warnSmallSets = (offenders: PermutedSet[]) => {
    if (offenders.length === 0) return;
    const isPlural = offenders.length > 1;
    environment.runtime.warn(
      MESSAGE_CODE.symmetrySetTooSmall,
      `The set${isPlural ? "s" : ""} ${offenders.map((offender) => offender.name).join(", and ")} ${isPlural ? "have" : "has"} been defined to be a symmetry set but contain${isPlural ? "" : "s"} less than two elements.`,
    );
  };
  // As many permuted sets as permutations means none has two elements.
  if (permutedSets.length >= elements.length) {
    warnSmallSets(permutedSets);
    return undefined;
  }
  const group = new Map<string, Images>();
  permutations.forEach((permutation) => {
    if (permutation.size > 0) group.set(getPermutationKey(permutation), permutation);
  });
  const generators = [...group.values()];
  const frontier = { start: 0 };
  while (frontier.start < group.size) {
    const members = [...group.values()];
    const end = members.length;
    generators.forEach((generator) =>
      members.slice(frontier.start, end).forEach((member) => {
        const composed = composePermutations(generator, member);
        const key = getPermutationKey(composed);
        if (composed.size > 0 && !group.has(key)) group.set(key, composed);
      }),
    );
    frontier.start = end;
  }
  const movedNames = new Set(
    [...group.values()].flatMap((images) => [...images.values()].map((image) => image.name)),
  );
  // Only a permutation of a set TLC holds as an enumerated set is checked.
  warnSmallSets(
    permutedSets.filter((permuted) => {
      if (permuted.operand === undefined) return false;
      const set = evaluateConstant(permuted.operand);
      return (
        typeof set === "object" &&
        set.kind === "Set" &&
        !set.elements.some((element) => isModelValue(element) && movedNames.has(element.name))
      );
    }),
  );
  if (group.size === 0) return undefined;
  return [...group.values()];
};

const permuteElements = (elements: Value[], images: Images) => {
  for (let index = 0; index < elements.length; index++) {
    const element = elements[index];
    const permuted = permuteValue(element, images);
    if (permuted === element) continue;
    const result = elements.slice(0, index);
    result.push(permuted);
    for (let rest = index + 1; rest < elements.length; rest++) {
      result.push(permuteValue(elements[rest], images));
    }
    return result;
  }
  return undefined;
};

// A permutation maps distinct elements to distinct elements and keeps the elements it doesn't move
// in order, so it sorts only the moved ones and merges them back.
const permuteSortedElements = (elements: Value[], images: Images) => {
  const kept: Value[] = [];
  const moved: Value[] = [];
  for (const element of elements) {
    const permuted = permuteValue(element, images);
    if (permuted === element) kept.push(element);
    else moved.push(permuted);
  }
  if (moved.length === 0) return undefined;
  moved.sort(compareValues);
  const merged: Value[] = [];
  let keptIndex = 0;
  let movedIndex = 0;
  while (keptIndex < kept.length && movedIndex < moved.length) {
    merged.push(
      compareValues(kept[keptIndex], moved[movedIndex]) < 0
        ? kept[keptIndex++]
        : moved[movedIndex++],
    );
  }
  while (keptIndex < kept.length) merged.push(kept[keptIndex++]);
  while (movedIndex < moved.length) merged.push(moved[movedIndex++]);
  return merged;
};

// Value#permute: the value with each model value replaced by its image. A value the permutation
// doesn't move is returned itself, so that comparing it with itself stops at identity.
const permuteValue = (value: Value, images: Images): Value => {
  if (typeof value !== "object") return value;
  const kind = value.kind;
  if (kind === "ModelValue") return images.get(value.name) ?? value;
  if (kind === "Set") {
    const elements = permuteSortedElements(value.elements, images);
    return elements ? createSortedSet(elements) : value;
  }
  if (kind === "Function" || (kind === "LazyFunction" && isEnumerable(value.domain))) {
    const functionValue = toFiniteFunction(value);
    const domain = permuteElements(functionValue.domain, images);
    const range = permuteElements(functionValue.range, images) ?? functionValue.range;
    if (domain) {
      const permuted = createFunction(
        domain.map((key, index): [Value, Value] => [key, range[index]]),
      );
      // A permutation often maps the domain to itself, such as a function over the symmetric set.
      // Sharing the original domain array lets comparisons with other images skip the domain.
      const isSameDomain = permuted.domain.every(
        (key, index) => key === functionValue.domain[index],
      );
      return isSameDomain ? createSortedFunction(functionValue.domain, permuted.range) : permuted;
    }
    return range === functionValue.range
      ? functionValue
      : createSortedFunction(functionValue.domain, range);
  }
  if (kind === "Interval" || !isSetValue(value) || !isEnumerable(value)) return value;
  const set = toFiniteSet(value);
  const elements = permuteElements(set.elements, images);
  return elements ? createSet(elements) : set;
};

// TLCStateMut#fingerPrint: the smallest image of the state under the group in TLC's variable
// order. TLC permutes the state under each permutation, variable by variable, and moves on to the
// next permutation as soon as a variable's image is larger than the smallest state's.
export const getRepresentative = (
  state: Value[],
  permutations: Images[],
  order: number[],
): Value[] => {
  let smallest = state;
  for (const images of permutations) {
    const permuted = state.slice();
    let comparison = 0;
    for (const index of order) {
      permuted[index] = permuteValue(state[index], images);
      if (comparison === 0) comparison = compareValues(permuted[index], smallest[index]);
      if (comparison > 0) break;
    }
    if (comparison < 0) smallest = permuted;
  }
  return smallest;
};

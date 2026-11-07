// Compiles TLA+ expressions into closures over interned ids. Each compiled expression knows its
// footprint: the state variables, primed variables, and bound names it reads. An expression worth
// caching is wrapped in a memo table keyed by the ids in its footprint, and one that reads nothing is
// evaluated once.
//
// Operators are expanded where they are applied, with their parameters bound to the argument
// expressions, as TLA+ defines them. A recursive operator or function is compiled once and called by
// value instead.

import {
  type Bound,
  type Definition,
  type Expression,
  type FunctionDefinition,
  isLocallyResolved,
  type OperatorDefinition,
  type OperatorParam,
} from "../ast";
import type {
  Builtin,
  BuiltinArgument,
  Environment,
  EvaluationScope,
  OperatorValue,
} from "../evaluate";
import { getDefinition, getQuantifierElements } from "../evaluate";
import {
  createSortedSet,
  getStreamedElements,
  isReducibleSet,
  toFiniteSet,
  type Value,
} from "../values";
import { fromValue, toValue } from "./convert";
import { MemoTable } from "./memo";
import {
  apply,
  applyField,
  bail,
  bool,
  compare,
  difference,
  domainOf,
  elementAt,
  EMPTY_SET,
  EMPTY_TUPLE,
  equals,
  except,
  exceptAt,
  FALSE,
  findKey,
  functionOf,
  functionOfSorted,
  getKey,
  getRangeValue,
  int,
  intersection,
  intOf,
  isFunctionKind,
  isMember,
  isSubset,
  KIND_BOOL,
  KIND_FUNCTION,
  KIND_INT,
  KIND_MODEL,
  KIND_SET,
  KIND_STRING,
  KIND_TUPLE,
  kindOf,
  setOf,
  setOfSorted,
  sizeOf,
  str,
  textOf,
  TRUE,
  tupleOf,
  union,
} from "./store";

// --- registers the compiled code reads ---

// The current state, or the initial state being built. -1 marks a variable not yet assigned.
export let CUR: Int32Array = new Int32Array(0);
// The next state being built. -1 marks a variable not yet assigned.
export let NXT: Int32Array = new Int32Array(0);
// Bound names, each at a slot fixed when it is compiled.
export let LOC: Int32Array = new Int32Array(256);
let slotCount = 0;

// The same registers as an object, for generated code, along with how many variables of the state
// being built have a value.
export const registers = { cur: CUR, next: NXT, locals: LOC, assigned: 0 };

export const setCurrent = (state: Int32Array) => {
  CUR = state;
  registers.cur = state;
};
export const setNext = (state: Int32Array) => {
  NXT = state;
  registers.next = state;
};

const allocateSlot = () => {
  const slot = slotCount++;
  if (slot >= LOC.length) {
    const next = new Int32Array(LOC.length * 2);
    next.set(LOC);
    LOC = next;
    registers.locals = next;
  }
  return slot;
};

// A recursive definition's body binds its names at slots fixed when it compiles, so a call inside
// the body would overwrite the names of the call that made it. Evaluating the body keeps the slots
// it binds, from start to end, as they were.
const evaluateKeepingSlots = (evaluate: Evaluate, start: number, end: number) => {
  if (end <= start) return evaluate();
  const saved = LOC.slice(start, end);
  try {
    return evaluate();
  } finally {
    LOC.set(saved, start);
  }
};

// An array a compiled node fills on each evaluation. Evaluating an element may evaluate the same
// node again through recursion, so the node takes a fresh array while its own is in use. The array
// is free again once released; a bailout leaves it taken, which only costs fresh arrays after.
const createScratch = (length: number) => {
  const own: number[] = new Array(length);
  let isTaken = false;
  return {
    take: (): number[] => {
      if (isTaken) return new Array(length);
      isTaken = true;
      return own;
    },
    release: (array: number[]) => {
      if (array === own) isTaken = false;
    },
  };
};

// --- footprints ---

export interface Footprint {
  vars: number[];
  primes: number[];
  slots: number[];
}

const EMPTY_FOOTPRINT: Footprint = { vars: [], primes: [], slots: [] };

const isWithinFootprint = (inner: Footprint, outer: Footprint) =>
  inner.vars.every((variable) => outer.vars.includes(variable)) &&
  inner.primes.every((variable) => outer.primes.includes(variable)) &&
  inner.slots.every((slot) => outer.slots.includes(slot));

const mergeSorted = (left: number[], right: number[]) => {
  if (left.length === 0) return right;
  if (right.length === 0 || left === right) return left;
  const merged: number[] = [];
  let leftIndex = 0;
  let rightIndex = 0;
  while (leftIndex < left.length || rightIndex < right.length) {
    const leftValue = leftIndex < left.length ? left[leftIndex] : Infinity;
    const rightValue = rightIndex < right.length ? right[rightIndex] : Infinity;
    if (leftValue === rightValue) {
      merged.push(leftValue);
      leftIndex++;
      rightIndex++;
    } else if (leftValue < rightValue) {
      merged.push(leftValue);
      leftIndex++;
    } else {
      merged.push(rightValue);
      rightIndex++;
    }
  }
  return merged;
};

const mergeFootprints = (...footprints: Footprint[]): Footprint =>
  footprints.reduce(
    (merged, footprint) => ({
      vars: mergeSorted(merged.vars, footprint.vars),
      primes: mergeSorted(merged.primes, footprint.primes),
      slots: mergeSorted(merged.slots, footprint.slots),
    }),
    EMPTY_FOOTPRINT,
  );

const withoutSlots = (footprint: Footprint, slots: number[]): Footprint => ({
  ...footprint,
  slots: footprint.slots.filter((slot) => !slots.includes(slot)),
});

const footprintWidth = (footprint: Footprint) =>
  footprint.vars.length + footprint.primes.length + footprint.slots.length;

// --- compiled expressions ---

export type Evaluate = () => number;

export interface Compiled {
  evaluate: Evaluate;
  footprint: Footprint;
  // Whether evaluating it costs more than looking it up, so that caching it pays.
  isCostly: boolean;
  // For a set: whether TLC's value is a normalized set, whose elements TLC enumerates in its order.
  // The engine enumerates any other set the way the reference interpreter does.
  isNormalized: boolean;
  // For a set: whether TLC's value is a set enumeration, as {a, b} and {e : x \in S} are, and for a
  // set of sets, whether each element's is. TLC's UNION of a set enumeration of set enumerations is
  // a normalized set enumeration, and any other UNION is lazy.
  isEnumerated?: boolean;
  areElementsEnumerated?: boolean;
  // Writes the expression as JavaScript, for generated code. Without it, generated code calls
  // evaluate.
  emit?: (gen: CodeGen) => string;
  // Whether the value is always TRUE or FALSE, whose ids are 1 and 0.
  isBoolean?: boolean;
  // For a set TLC keeps lazy: the reference interpreter's value for it, which says the order TLC
  // enumerates it in.
  reference?: () => Value;
}

// A set's reference value, or undefined for a set TLC keeps lazy that the engine has no reference
// for, such as a UNION that streams duplicates.
const referenceOf = (compiled: Compiled): (() => Value) | undefined =>
  compiled.reference ??
  (compiled.isNormalized
    ? (
        (evaluate) => () =>
          toValue(evaluate())
      )(compiled.evaluate)
    : undefined);

// A reference built from components, when every component has one.
const combineReferences = (
  components: Compiled[],
  build: (references: (() => Value)[]) => () => Value,
): (() => Value) | undefined => {
  const references = components.map(referenceOf);
  return references.every((reference) => reference !== undefined)
    ? build(references as (() => Value)[])
    : undefined;
};

// What generated code needs from the compiler: a name in scope for each value it refers to.
export interface CodeGen {
  ref: (value: unknown) => string;
}

export const codeOf = (compiled: Compiled, gen: CodeGen): string =>
  compiled.emit ? `(${compiled.emit(gen)})` : `${gen.ref(compiled.evaluate)}()`;

export const checkBoolean = (value: number) =>
  value === TRUE || value === FALSE ? value : bail("expected a boolean");

export const booleanCodeOf = (compiled: Compiled, gen: CodeGen): string =>
  compiled.isBoolean ? codeOf(compiled, gen) : `${gen.ref(checkBoolean)}(${codeOf(compiled, gen)})`;

const equalsId = (left: number, right: number) =>
  left === right ? TRUE : equals(left, right) ? TRUE : FALSE;
const differsId = (left: number, right: number) =>
  left === right ? FALSE : equals(left, right) ? FALSE : TRUE;
const readNext = (index: number) => {
  const value = NXT[index];
  return value === -1 ? bail("primed variable not assigned") : value;
};
const readCurrent = (index: number) => {
  const value = CUR[index];
  return value === -1 ? bail("variable not assigned") : value;
};

const leaf = (evaluate: Evaluate, footprint: Footprint, isNormalized = true): Compiled => ({
  evaluate,
  footprint,
  isCostly: false,
  isNormalized,
});

const constant = (id: number): Compiled =>
  ({
    ...leaf(() => id, EMPTY_FOOTPRINT),
    isConstant: true,
    emit: () => String(id),
    isBoolean: id === TRUE || id === FALSE,
  }) as Compiled;

const MAXIMUM_MEMO_WIDTH = 6;

const lookup1 = (table: MemoTable, key: number, inner: Evaluate) => {
  if (!table.isEnabled) return inner();
  const known = table.get1(key);
  if (known !== -1) return known;
  const value = inner();
  table.set1(key, value);
  return value;
};

const lookup2 = (table: MemoTable, first: number, second: number, inner: Evaluate) => {
  if (!table.isEnabled) return inner();
  const known = table.get2(first, second);
  if (known !== -1) return known;
  const value = inner();
  table.set2(first, second, value);
  return value;
};

// The code that reads each id of a footprint, in the order the memo tables key them.
const keyCodes = (footprint: Footprint, gen: CodeGen) => {
  const name = gen.ref(registers);
  return [
    ...footprint.vars.map((variable) => `${name}.cur[${variable}]`),
    ...footprint.primes.map((variable) => `${name}.next[${variable}]`),
    ...footprint.slots.map((slot) => `${name}.locals[${slot}]`),
  ];
};

const memoTables: MemoTable[] = [];

// Caches a costly expression by the ids it reads, and evaluates one that reads nothing only once.
const cached = (compiled: Compiled): Compiled => {
  const footprint = compiled.footprint;
  const inner = compiled.evaluate;
  const width = footprintWidth(footprint);
  if (width === 0 && !(compiled as { isConstant?: boolean }).isConstant) {
    let value = -1;
    return {
      ...compiled,
      isCostly: false,
      isConstant: true,
      emit: undefined,
      evaluate: () => (value !== -1 ? value : (value = inner())),
    } as Compiled;
  }
  if (!compiled.isCostly) return compiled;
  if (width === 0) {
    let value = -1;
    return {
      ...compiled,
      isCostly: false,
      emit: undefined,
      evaluate: () => (value !== -1 ? value : (value = inner())),
    };
  }
  if (width > MAXIMUM_MEMO_WIDTH) return compiled;
  const table = new MemoTable(width);
  memoTables.push(table);
  const vars = footprint.vars;
  const primes = footprint.primes;
  const slots = footprint.slots;
  if (width === 1) {
    const read: () => number =
      vars.length === 1
        ? (
            (variable) => () =>
              CUR[variable]
          )(vars[0])
        : primes.length === 1
          ? (
              (variable) => () =>
                NXT[variable]
            )(primes[0])
          : (
              (slot) => () =>
                LOC[slot]
            )(slots[0]);
    return {
      ...compiled,
      isCostly: false,
      emit: (gen: CodeGen) =>
        `${gen.ref(lookup1)}(${gen.ref(table)}, ${keyCodes(footprint, gen)[0]}, ${gen.ref(inner)})`,
      evaluate: () => {
        if (!table.isEnabled) return inner();
        const key = read();
        const known = table.get1(key);
        if (known !== -1) return known;
        const value = inner();
        table.set1(key, value);
        return value;
      },
    };
  }
  const scratch = new Int32Array(width);
  const fill = () => {
    let index = 0;
    for (let position = 0; position < vars.length; position++)
      scratch[index++] = CUR[vars[position]];
    for (let position = 0; position < primes.length; position++) {
      scratch[index++] = NXT[primes[position]];
    }
    for (let position = 0; position < slots.length; position++)
      scratch[index++] = LOC[slots[position]];
  };
  if (width === 2) {
    return {
      ...compiled,
      isCostly: false,
      emit: (gen: CodeGen) => {
        const [first, second] = keyCodes(footprint, gen);
        return `${gen.ref(lookup2)}(${gen.ref(table)}, ${first}, ${second}, ${gen.ref(inner)})`;
      },
      evaluate: () => {
        if (!table.isEnabled) return inner();
        fill();
        const first = scratch[0];
        const second = scratch[1];
        const known = table.get2(first, second);
        if (known !== -1) return known;
        const value = inner();
        table.set2(first, second, value);
        return value;
      },
    };
  }
  return {
    ...compiled,
    isCostly: false,
    emit: undefined,
    evaluate: () => {
      if (!table.isEnabled) return inner();
      fill();
      const known = table.getN(scratch);
      if (known !== -1) return known;
      const value = inner();
      // The inner evaluation may have overwritten the scratch through a nested lookup of this table.
      fill();
      table.setN(scratch, value);
      return value;
    },
  };
};

export const getMemoStatistics = () =>
  memoTables.map((table) => ({
    width: table.width,
    size: table.size,
    lookups: table.lookups,
    hits: table.hits,
    isEnabled: table.isEnabled,
  }));

// --- scopes ---

interface Context {
  scope: Scope | undefined;
  isPrimed: boolean;
  // Whether the expression is part of the initial predicate, where unprimed variables are assigned.
  isInit: boolean;
}

type Binding =
  | { kind: "slot"; slot: number }
  // An operator's argument, which TLA+ substitutes for the parameter.
  | {
      kind: "argument";
      expression: Expression;
      context: Context;
      compiled: (Compiled | undefined)[];
    }
  | { kind: "operator"; operator: OperatorBinding }
  // A value, or a function a LET defines, which TLC keeps lazy, with the scope it is defined in.
  | {
      kind: "value";
      compiled: Compiled;
      lazy?: { definition: FunctionDefinition; scope: Scope | undefined };
    }
  // A recursive function defined in a LET, whose body sees the LET's scope, itself included.
  | { kind: "recursive"; definition: FunctionDefinition; scope: Scope | undefined };

interface OperatorBinding {
  name: string;
  params: OperatorParam[];
  body: Expression;
  context: Context;
  // A RECURSIVE operator defined in a LET, whose context binds it.
  isRecursive?: boolean;
}

interface Scope {
  name: string;
  binding: Binding;
  parent: Scope | undefined;
}

const lookup = (scope: Scope | undefined, name: string): Binding | undefined => {
  for (let current = scope; current; current = current.parent) {
    if (current.name === name) return current.binding;
  }
  return undefined;
};

const bind = (scope: Scope | undefined, name: string, binding: Binding): Scope => ({
  name,
  binding,
  parent: scope,
});

// --- the compiler ---

export interface Compiler {
  compile: (expression: Expression, context: Context) => Compiled;
  compileOperatorBody: (
    definition: OperatorDefinition,
    args: Expression[],
    context: Context,
  ) => {
    body: Expression;
    context: Context;
  };
  resolveAction: (expression: Expression, context: Context) => ActionTarget | undefined;
  // For f[e] where TLC keeps f lazy, a LET's function or a function constructor: the body of f
  // walked at e, which an action walks, and whether e is in f's domain.
  resolveLazyApplication: (
    expression: Expression,
    context: Context,
  ) =>
    | {
        body: Expression;
        context: Context;
        isInDomain: () => boolean;
        // The function's own body, in its own scope, and whether it applies itself.
        functionBody: Expression;
        functionContext: Context;
        isRecursive: boolean;
      }
    | undefined;
  bindLet: (expression: Expression & { kind: "Let" }, context: Context) => Context;
  compileOrdered: (
    expression: Expression,
    context: Context,
    mode: "quantifier" | "streamed",
  ) => Compiled;
  bindValue: (context: Context, name: string) => { context: Context; slot: number };
  // The context the reference interpreter's scope stands for, or undefined for one that binds an
  // operator.
  contextFromScope: (scope: EvaluationScope | undefined) => Context | undefined;
  // How the compiler tests ENABLED A, which it needs the action compiler for.
  setEnabledCompiler: (compile: (action: Expression, context: Context) => () => boolean) => void;
  environment: Environment;
  variableCount: number;
}

// What an expression that may be an action names: a user-defined operator expanded with its
// arguments, or a binding of an argument that is itself an action.
export type ActionTarget = { body: Expression; context: Context; name: string | undefined };

export const ROOT_CONTEXT: Context = { scope: undefined, isPrimed: false, isInit: false };

// Operators whose results depend on more than their arguments, or that print, so the engine can't
// cache or reorder them.
const IMPURE_BUILTINS = new Set([
  "Print",
  "PrintT",
  "JavaTime",
  "TLCGet",
  "TLCSet",
  "RandomElement",
  "TLCEval",
  "Any",
]);

// The builtins the engine runs in the reference interpreter when it has no implementation of its
// own: those whose result depends only on their arguments.
const PURE_BUILTINS = new Set([
  "SubSeq",
  "SelectSeq",
  "IsFiniteSet",
  "Permutations",
  "SortSeq",
  "ToString",
  "EmptyBag",
  "IsABag",
  "BagCardinality",
  "BagIn",
  "CopiesIn",
  "\\oplus",
  "\\ominus",
  "BagUnion",
  "\\sqsubseteq",
  "BagOfAll",
  "SubBag",
  "BagToSet",
  "SetToBag",
]);

const unsupported = (what: string): never => bail(`unsupported: ${what}`);

export const createCompiler = (environment: Environment): Compiler => {
  const variableCount = environment.variables.length;
  const definitionCache = new Map<Definition, Compiled[]>();
  const recursiveOperators = new Map<object, RecursiveOperator>();
  const expanding = new Set<Definition>();
  let depth = 0;

  const compile = (expression: Expression, context: Context): Compiled => {
    if (++depth > 2000) unsupported("expansion too deep");
    try {
      const compiled = compileNode(expression, context);
      return compiled.isCostly || footprintWidth(compiled.footprint) === 0
        ? cached(compiled)
        : compiled;
    } finally {
      depth--;
    }
  };

  const compileBoolean = (expression: Expression, context: Context) => {
    const compiled = compile(expression, context);
    if (compiled.isBoolean) return compiled;
    const evaluate = compiled.evaluate;
    return {
      ...compiled,
      evaluate: () => {
        const value = evaluate();
        if (value !== TRUE && value !== FALSE) bail("expected a boolean");
        return value;
      },
      emit: (gen: CodeGen) => booleanCodeOf(compiled, gen),
      isBoolean: true,
    };
  };

  const readVariable = (index: number, context: Context): Compiled => {
    if (context.isPrimed) {
      return {
        ...leaf(() => readNext(index), { vars: [], primes: [index], slots: [] }),
        emit: (gen) => `${gen.ref(readNext)}(${index})`,
      };
    }
    const isInit = context.isInit;
    return {
      ...leaf(() => readCurrent(index), { vars: [index], primes: [], slots: [] }),
      emit: (gen) =>
        isInit ? `${gen.ref(readCurrent)}(${index})` : `${gen.ref(registers)}.cur[${index}]`,
    };
  };

  const compileBinding = (binding: Binding, context: Context): Compiled => {
    switch (binding.kind) {
      case "slot": {
        const slot = binding.slot;
        return {
          ...leaf(() => LOC[slot], { vars: [], primes: [], slots: [slot] }),
          emit: (gen) => `${gen.ref(registers)}.locals[${slot}]`,
        };
      }
      case "argument": {
        const isPrimed = context.isPrimed || binding.context.isPrimed;
        const index = isPrimed ? 1 : 0;
        const known = binding.compiled[index];
        if (known) return known;
        const compiled = compile(binding.expression, { ...binding.context, isPrimed });
        binding.compiled[index] = compiled;
        return compiled;
      }
      case "value":
        return binding.compiled;
      case "recursive":
        return materializeRecursive(
          getRecursiveFunction(binding.definition, context, binding.scope),
        );
      default:
        return unsupported("an operator used as a value");
    }
  };

  const compileDefinitionReference = (definition: Definition, context: Context): Compiled => {
    if (definition.kind === "Function") return compileFunctionDefinition(definition, context);
    if (definition.params.length > 0) return unsupported("an operator used as a value");
    const index = context.isPrimed ? 1 : 0;
    const known = definitionCache.get(definition)?.[index];
    if (known) return known;
    if (expanding.has(definition)) return unsupported("a recursive zero-arity definition");
    expanding.add(definition);
    try {
      const compiled = cached(
        markCostly(
          compile(definition.body, {
            scope: undefined,
            isPrimed: context.isPrimed,
            isInit: context.isInit,
          }),
        ),
      );
      const entries = definitionCache.get(definition) ?? [];
      entries[index] = compiled;
      definitionCache.set(definition, entries);
      return compiled;
    } finally {
      expanding.delete(definition);
    }
  };

  const markCostly = (compiled: Compiled): Compiled =>
    compiled.isCostly ? compiled : { ...compiled, isCostly: true };

  const compileIdentifier = (expression: Expression & { kind: "Identifier" }, context: Context) => {
    const name = expression.name;
    if (isLocallyResolved(expression)) {
      const binding = lookup(context.scope, name);
      if (binding) return compileBinding(binding, context);
    }
    const variable = environment.variableIndex.get(name);
    if (variable !== undefined) return readVariable(variable, context);
    const constantValue = environment.constants.get(name);
    if (constantValue !== undefined) return constant(fromValue(constantValue));
    const definition = getDefinition(name, environment);
    if (definition) return compileDefinitionReference(definition, context);
    // The model may substitute a builtin for the name, as Nat <- Int does.
    const target = environment.substitutions.get(name) ?? name;
    const builtin = environment.builtins.get(target);
    if (builtin && builtin.arity === 0) return compileNullaryBuiltin(target, builtin);
    const binding = lookup(context.scope, name);
    if (binding) return compileBinding(binding, context);
    return unsupported(`the name ${name}`);
  };

  const compileNullaryBuiltin = (name: string, builtin: Builtin): Compiled => {
    if (builtin.isStateLevel || IMPURE_BUILTINS.has(name)) return unsupported(name);
    switch (name) {
      case "TRUE":
        return constant(TRUE);
      case "FALSE":
        return constant(FALSE);
      case "BOOLEAN":
        return constant(setOf([FALSE, TRUE]));
      case "Nat":
      case "Int":
      case "STRING":
        return infiniteSet(name);
      default: {
        const value = builtin.evaluate([]);
        return constant(fromValue(value));
      }
    }
  };

  // Nat, Int and STRING, which the engine only tests for membership.
  const infiniteSet = (name: string): Compiled =>
    ({
      ...leaf(() => bail(`enumerated ${name}`), EMPTY_FOOTPRINT, false),
      infinite: name,
      reference: () => environment.builtins.get(name)!.evaluate([]),
    }) as Compiled;

  const compileNode = (expression: Expression, context: Context): Compiled => {
    switch (expression.kind) {
      case "Number":
        return constant(int(expression.value));
      case "String":
        return constant(str(expression.value));
      case "Identifier":
        return compileIdentifier(expression, context);
      case "Apply":
        return compileApply(expression, context);
      case "And":
      case "Or":
        return compileJunction(expression, context);
      case "Prime":
        if (context.isPrimed) return unsupported("a doubly primed expression");
        return compile(expression.expression, { ...context, isPrimed: true });
      case "If": {
        const condition = compileBoolean(expression.condition, context);
        const consequent = compile(expression.consequent, context);
        const alternative = compile(expression.alternative, context);
        const conditionEvaluate = condition.evaluate;
        const consequentEvaluate = consequent.evaluate;
        const alternativeEvaluate = alternative.evaluate;
        return {
          evaluate: () =>
            conditionEvaluate() === TRUE ? consequentEvaluate() : alternativeEvaluate(),
          footprint: mergeFootprints(
            condition.footprint,
            consequent.footprint,
            alternative.footprint,
          ),
          isCostly: consequent.isCostly || alternative.isCostly,
          isNormalized: consequent.isNormalized && alternative.isNormalized,
          reference: combineReferences([consequent, alternative], ([then, otherwise]) => {
            const evaluateCondition = condition.evaluate;
            return () => (evaluateCondition() === TRUE ? then() : otherwise());
          }),
          isEnumerated: consequent.isEnumerated === true && alternative.isEnumerated === true,
          areElementsEnumerated:
            consequent.areElementsEnumerated === true && alternative.areElementsEnumerated === true,
          emit: (gen) =>
            `${codeOf(condition, gen)} ? ${codeOf(consequent, gen)} : ${codeOf(alternative, gen)}`,
          isBoolean: consequent.isBoolean === true && alternative.isBoolean === true,
        };
      }
      case "Case": {
        const arms = expression.arms.map((arm) => ({
          condition: compileBoolean(arm.condition, context),
          body: compile(arm.body, context),
        }));
        const other = expression.other ? compile(expression.other, context) : undefined;
        const conditions = arms.map((arm) => arm.condition.evaluate);
        const bodies = arms.map((arm) => arm.body.evaluate);
        const otherEvaluate = other?.evaluate;
        return {
          evaluate: () => {
            for (let index = 0; index < conditions.length; index++) {
              if (conditions[index]() === TRUE) return bodies[index]();
            }
            return otherEvaluate ? otherEvaluate() : bail("no CASE arm holds");
          },
          footprint: mergeFootprints(
            ...arms.map((arm) => arm.condition.footprint),
            ...arms.map((arm) => arm.body.footprint),
            ...(other ? [other.footprint] : []),
          ),
          isCostly: true,
          isNormalized: arms.every((arm) => arm.body.isNormalized) && (other?.isNormalized ?? true),
          isEnumerated:
            arms.every((arm) => arm.body.isEnumerated === true) && (other?.isEnumerated ?? true),
          areElementsEnumerated:
            arms.every((arm) => arm.body.areElementsEnumerated === true) &&
            (other?.areElementsEnumerated ?? true),
        };
      }
      case "Let":
        return compile(expression.body, bindLetDefinitions(expression, context));
      case "Forall":
      case "Exists":
        return compileQuantifier(expression, context);
      case "Choose":
        return compileChoose(expression, context);
      case "SetEnumeration": {
        const elements = expression.elements.map((element) => compile(element, context));
        const evaluators = elements.map((element) => element.evaluate);
        const footprint = mergeFootprints(...elements.map((element) => element.footprint));
        if (evaluators.length === 0)
          return { ...constant(EMPTY_SET), isEnumerated: true, areElementsEnumerated: true };
        return {
          evaluate: () => setOf(evaluators.map((evaluate) => evaluate())),
          footprint,
          isCostly: true,
          isNormalized: true,
          isEnumerated: true,
          areElementsEnumerated: elements.every((element) => element.isEnumerated === true),
        };
      }
      case "Tuple": {
        const elements = expression.elements.map((element) => compile(element, context));
        const evaluators = elements.map((element) => element.evaluate);
        if (evaluators.length === 0) return constant(EMPTY_TUPLE);
        const scratch = createScratch(evaluators.length);
        return {
          evaluate: () => {
            const elements = scratch.take();
            for (let index = 0; index < evaluators.length; index++)
              elements[index] = evaluators[index]();
            scratch.release(elements);
            return tupleOf(elements, elements.length);
          },
          footprint: mergeFootprints(...elements.map((element) => element.footprint)),
          isCostly: true,
          isNormalized: true,
        };
      }
      case "Record": {
        const fields = expression.fields
          .map((field) => ({ key: str(field.name), value: compile(field.value, context) }))
          .sort((left, right) => compare(left.key, right.key));
        const keys = fields.map((field) => field.key);
        const evaluators = fields.map((field) => field.value.evaluate);
        const scratch = createScratch(keys.length);
        return {
          evaluate: () => {
            const values = scratch.take();
            for (let index = 0; index < evaluators.length; index++)
              values[index] = evaluators[index]();
            scratch.release(values);
            return functionOfSorted(keys, values, keys.length);
          },
          footprint: mergeFootprints(...fields.map((field) => field.value.footprint)),
          isCostly: true,
          isNormalized: true,
        };
      }
      case "FunctionApplication":
        return compileFunctionApplication(expression, context);
      case "FieldAccess": {
        const record = compile(expression.record, context);
        const key = str(expression.field);
        const evaluate = record.evaluate;
        const hint = { position: 0 };
        return {
          ...leaf(() => applyField(evaluate(), key, hint), record.footprint),
          emit: (gen) => `${gen.ref(applyField)}(${codeOf(record, gen)}, ${key}, ${gen.ref(hint)})`,
        };
      }
      case "Except":
        return compileExcept(expression, context);
      case "ExceptAt": {
        const binding = lookup(context.scope, "@");
        if (!binding) return unsupported("@ outside EXCEPT");
        return compileBinding(binding, context);
      }
      case "FunctionConstruction":
        return compileFunctionConstruction(expression.bounds, expression.body, context);
      case "SetFilter":
        return compileSetFilter(expression, context);
      case "SetMap":
        return compileSetMap(expression, context);
      case "FunctionSet":
      case "RecordSet":
      case "Product":
        return compileLazySet(
          expression as Expression & { kind: "FunctionSet" | "RecordSet" | "Product" },
          context,
        );
      case "Unchanged": {
        const now = compile(expression.expression, { ...context, isPrimed: false });
        const next = compile(expression.expression, { ...context, isPrimed: true });
        const nowEvaluate = now.evaluate;
        const nextEvaluate = next.evaluate;
        return leaf(
          () => bool(equals(nextEvaluate(), nowEvaluate())),
          mergeFootprints(now.footprint, next.footprint),
        );
      }
      case "Enabled":
        return compileEnabled(expression.expression, context);
      case "Label":
        return compile(expression.body, context);
      default:
        return unsupported(`expression ${expression.kind}`);
    }
  };

  // ENABLED A runs A from the current state until its first successor. It reads every variable and
  // may read any name bound around it.
  let compileEnabledTest: ((action: Expression, context: Context) => () => boolean) | undefined;
  const allVariables = Array.from({ length: variableCount }, (_, index) => index);
  const getBoundSlots = (scope: Scope | undefined, slots: Set<number>, seen: Set<Scope>) => {
    for (let current = scope; current && !seen.has(current); current = current.parent) {
      seen.add(current);
      const binding = current.binding;
      if (binding.kind === "slot") slots.add(binding.slot);
      else if (binding.kind === "argument") getBoundSlots(binding.context.scope, slots, seen);
      else if (binding.kind === "operator")
        getBoundSlots(binding.operator.context.scope, slots, seen);
      else if (binding.kind === "recursive") getBoundSlots(binding.scope, slots, seen);
    }
    return slots;
  };
  const compileEnabled = (action: Expression, context: Context): Compiled => {
    if (!compileEnabledTest || context.isPrimed || context.isInit)
      return unsupported("expression Enabled");
    const test = compileEnabledTest(action, context);
    const slots = [...getBoundSlots(context.scope, new Set(), new Set())].sort((a, b) => a - b);
    return {
      ...leaf(() => (test() ? TRUE : FALSE), { vars: allVariables, primes: [], slots }),
      isCostly: true,
      isBoolean: true,
    } as Compiled;
  };

  const compileJunction = (expression: Expression & { kind: "And" | "Or" }, context: Context) => {
    const operands = expression.operands.map((operand) => compileBoolean(operand, context));
    const evaluators = operands.map((operand) => operand.evaluate);
    const footprint = mergeFootprints(...operands.map((operand) => operand.footprint));
    const isAnd = expression.kind === "And";
    const stop = isAnd ? FALSE : TRUE;
    const evaluate =
      evaluators.length === 2
        ? ((first, second) => () => (first() === stop ? stop : second()))(
            evaluators[0],
            evaluators[1],
          )
        : () => {
            for (let index = 0; index < evaluators.length; index++) {
              if (evaluators[index]() === stop) return stop;
            }
            return isAnd ? TRUE : FALSE;
          };
    return {
      evaluate,
      footprint,
      isCostly: operands.some((operand) => operand.isCostly),
      isNormalized: true,
      emit: (gen: CodeGen) =>
        operands.map((operand) => codeOf(operand, gen)).join(isAnd ? " && " : " || "),
      isBoolean: true,
    };
  };

  // --- LET ---

  const bindLetDefinitions = (
    expression: Expression & { kind: "Let" },
    context: Context,
  ): Context => {
    if (expression.instances && expression.instances.length > 0) unsupported("INSTANCE in LET");
    let scope = context.scope;
    for (const definition of expression.definitions) {
      const definitionContext = { ...context, scope };
      if (definition.kind === "Function") {
        if (definition.isRecursive || definition.isSelfReferential) {
          const binding: Binding = { kind: "recursive", definition, scope: undefined };
          scope = bind(scope, definition.name, binding);
          binding.scope = scope;
          continue;
        }
        const compiled = cached(
          markCostly(
            compileFunctionConstruction(definition.bounds, definition.body, definitionContext),
          ),
        );
        scope = bind(scope, definition.name, {
          kind: "value",
          compiled,
          lazy: { definition, scope: definitionContext.scope },
        });
      } else if (definition.params.length === 0) {
        if (definition.isRecursive) unsupported("a recursive LET definition");
        scope = bind(scope, definition.name, {
          kind: "argument",
          expression: definition.body,
          context: definitionContext,
          compiled: [],
        });
      } else {
        const operator: OperatorBinding = {
          name: definition.name,
          params: definition.params,
          body: definition.body,
          context: definitionContext,
        };
        scope = bind(scope, definition.name, { kind: "operator", operator });
        if (definition.isRecursive) {
          operator.isRecursive = true;
          operator.context = { ...definitionContext, scope };
        }
      }
    }
    return { ...context, scope };
  };

  // --- operator application ---

  // Binds the parameters of an operator to its arguments.
  const bindArguments = (
    params: OperatorParam[],
    args: Expression[],
    callerContext: Context,
    calleeContext: Context,
  ): Context => {
    if (params.length !== args.length)
      return unsupported("an operator applied to the wrong number of arguments");
    let scope = calleeContext.scope;
    params.forEach((param, index) => {
      const argument = args[index];
      if (param.arity > 0) {
        scope = bind(scope, param.name, {
          kind: "operator",
          operator: resolveOperatorArgument(argument, callerContext),
        });
      } else {
        scope = bind(scope, param.name, {
          kind: "argument",
          expression: argument,
          context: callerContext,
          compiled: [],
        });
      }
    });
    return { ...calleeContext, scope };
  };

  const resolveOperatorArgument = (argument: Expression, context: Context): OperatorBinding => {
    if (argument.kind === "Lambda") {
      return {
        name: "LAMBDA",
        params: argument.params.map((name) => ({ name, arity: 0 })),
        body: argument.body,
        context,
      };
    }
    const name =
      argument.kind === "Identifier" || argument.kind === "OperatorReference"
        ? argument.kind === "Identifier"
          ? argument.name
          : argument.operator
        : undefined;
    if (name === undefined) return unsupported("an operator argument");
    const local = lookup(context.scope, name);
    if (local?.kind === "operator") return local.operator;
    const definition = getDefinition(name, environment);
    if (definition?.kind === "Operator" && !definition.isRecursive) {
      return {
        name,
        params: definition.params,
        body: definition.body,
        context: { ...context, scope: undefined },
      };
    }
    const builtin = environment.builtins.get(environment.substitutions.get(name) ?? name);
    if (builtin) {
      const params = Array.from({ length: builtin.arity }, (_, index) => ({
        name: `$${index}`,
        arity: 0,
      }));
      return {
        name,
        params,
        body: {
          kind: "Apply",
          operator: name,
          args: params.map((param) => ({
            kind: "Identifier",
            name: param.name,
            location: argument.location,
            resolution: { kind: "Local" },
          })),
          location: argument.location,
        } as Expression,
        context: { ...context, scope: undefined },
      };
    }
    return unsupported(`the operator argument ${name}`);
  };

  const compileApply = (expression: Expression & { kind: "Apply" }, context: Context): Compiled => {
    const name = expression.operator;
    if (isLocallyResolved(expression)) {
      const binding = lookup(context.scope, name);
      if (binding?.kind === "operator")
        return compileOperatorCall(binding.operator, expression.args, context);
      if (binding) return unsupported("applying a local value");
    }
    const target = environment.substitutions.get(name) ?? name;
    const definition = environment.definitions.get(target);
    if (definition?.kind === "Operator") {
      if (definition.isRecursive || expanding.has(definition)) {
        return compileRecursiveCall(definition, expression.args, context);
      }
      expanding.add(definition);
      try {
        const callee = bindArguments(definition.params, expression.args, context, {
          scope: undefined,
          isPrimed: context.isPrimed,
          isInit: context.isInit,
        });
        return cached(compile(definition.body, callee));
      } finally {
        expanding.delete(definition);
      }
    }
    if (definition) return unsupported("applying a function definition as an operator");
    const builtin = environment.builtins.get(target);
    if (builtin) return compileBuiltin(target, builtin, expression, context);
    const binding = lookup(context.scope, name);
    if (binding?.kind === "operator")
      return compileOperatorCall(binding.operator, expression.args, context);
    return unsupported(`the operator ${name}`);
  };

  const compileOperatorCall = (operator: OperatorBinding, args: Expression[], context: Context) => {
    if (operator.isRecursive) return compileRecursiveCall(operator, args, context, operator);
    const callee = bindArguments(operator.params, args, context, {
      ...operator.context,
      isPrimed: context.isPrimed || operator.context.isPrimed,
    });
    return cached(compile(operator.body, callee));
  };

  // --- recursion ---

  interface RecursiveOperator {
    slots: number[];
    body: Compiled | undefined;
    table: MemoTable | undefined;
    keySlots: number[];
    keyVars: number[];
    keyPrimes: number[];
    // Whether the operator's value, when a set, is normalized and a set enumeration. A call inside
    // the body takes it to be until the body says otherwise, when the body compiles again.
    isNormalized: boolean;
    isEnumerated: boolean;
    // The slots the body binds.
    slotStart: number;
    slotEnd: number;
    // What a call inside the body reads besides its arguments, as the body compiles: nothing at
    // first, then what the last compile of the body read, until the body reads no more.
    assumed: Footprint;
  }

  // A call of a RECURSIVE operator: a global one, or one a LET defines, whose body sees the LET's
  // scope.
  const compileRecursiveCall = (
    definition: { params: OperatorParam[]; body: Expression },
    args: Expression[],
    context: Context,
    local?: OperatorBinding,
  ): Compiled => {
    if (definition.params.some((param) => param.arity > 0))
      return unsupported("a recursive higher-order operator");
    const key: object = local ?? definition;
    let recursive = recursiveOperators.get(key);
    if (!recursive) {
      const slots = definition.params.map(() => allocateSlot());
      const created: RecursiveOperator = {
        slots,
        body: undefined,
        table: undefined,
        keySlots: [],
        keyVars: [],
        keyPrimes: [],
        isNormalized: true,
        isEnumerated: true,
        slotStart: 0,
        slotEnd: 0,
        assumed: EMPTY_FOOTPRINT,
      };
      recursive = created;
      recursiveOperators.set(key, created);
      let scope = local?.context.scope;
      definition.params.forEach((param, index) => {
        scope = bind(scope, param.name, { kind: "slot", slot: slots[index] });
      });
      if (!local) expanding.add(definition as OperatorDefinition);
      try {
        const bodyContext = {
          scope,
          isPrimed: context.isPrimed || (local?.context.isPrimed ?? false),
          isInit: context.isInit,
        };
        created.slotStart = slotCount;
        created.body = compile(definition.body, bodyContext);
        created.slotEnd = slotCount;
        // Each compile can only take away what the last one claimed, and add to what the body
        // reads, so this settles.
        const getRead = (body: Compiled) => withoutSlots(body.footprint, slots);
        while (
          (created.isNormalized && !created.body.isNormalized) ||
          (created.isEnumerated && created.body.isEnumerated !== true) ||
          !isWithinFootprint(getRead(created.body), created.assumed)
        ) {
          created.isNormalized &&= created.body.isNormalized;
          created.isEnumerated &&= created.body.isEnumerated === true;
          created.assumed = mergeFootprints(created.assumed, getRead(created.body));
          created.body = undefined;
          created.slotStart = slotCount;
          created.body = compile(definition.body, bodyContext);
          created.slotEnd = slotCount;
        }
      } finally {
        if (!local) expanding.delete(definition as OperatorDefinition);
      }
      const footprint = created.body.footprint;
      created.keySlots = mergeSorted(
        slots.slice().sort((left, right) => left - right),
        footprint.slots,
      );
      created.keyVars = footprint.vars;
      created.keyPrimes = footprint.primes;
      const width = created.keySlots.length + created.keyVars.length + created.keyPrimes.length;
      if (width <= MAXIMUM_MEMO_WIDTH) {
        created.table = new MemoTable(width);
        memoTables.push(created.table);
      }
    }
    const operator = recursive;
    const compiledArgs = args.map((argument) => compile(argument, context));
    const argEvaluators = compiledArgs.map((argument) => argument.evaluate);
    const slots = operator.slots;
    const argumentScratch = createScratch(slots.length);
    let scratch: Int32Array | undefined;
    const evaluate = () => {
      const values = argumentScratch.take();
      for (let index = 0; index < argEvaluators.length; index++)
        values[index] = argEvaluators[index]();
      argumentScratch.release(values);
      const saved = slots.map((slot) => LOC[slot]);
      for (let index = 0; index < slots.length; index++) LOC[slots[index]] = values[index];
      try {
        const table = operator.table;
        const body = operator.body!;
        if (!table || !table.isEnabled)
          return evaluateKeepingSlots(body.evaluate, operator.slotStart, operator.slotEnd);
        scratch ??= new Int32Array(table.width);
        const fill = () => {
          let position = 0;
          for (const variable of operator.keyVars) scratch![position++] = CUR[variable];
          for (const variable of operator.keyPrimes) scratch![position++] = NXT[variable];
          for (const slot of operator.keySlots) scratch![position++] = LOC[slot];
        };
        fill();
        const known = table.getN(scratch);
        if (known !== -1) return known;
        const value = evaluateKeepingSlots(body.evaluate, operator.slotStart, operator.slotEnd);
        fill();
        table.setN(scratch, value);
        return value;
      } finally {
        for (let index = 0; index < slots.length; index++) LOC[slots[index]] = saved[index];
      }
    };
    // While the body compiles, a call inside it reads what the operator assumes it does.
    const bodyFootprint = operator.body?.footprint;
    const footprint = mergeFootprints(
      ...compiledArgs.map((argument) => argument.footprint),
      bodyFootprint ? withoutSlots(bodyFootprint, slots) : operator.assumed,
    );
    return {
      evaluate,
      footprint,
      isCostly: false,
      isNormalized: operator.isNormalized,
      isEnumerated: operator.isEnumerated,
    };
  };

  const compileFunctionDefinition = (
    definition: FunctionDefinition,
    context: Context,
  ): Compiled => {
    if (!definition.isRecursive && !definition.isSelfReferential) {
      const index = context.isPrimed ? 1 : 0;
      const known = definitionCache.get(definition)?.[index];
      if (known) return known;
      const compiled = cached(
        markCostly(
          compileFunctionConstruction(definition.bounds, definition.body, {
            scope: undefined,
            isPrimed: context.isPrimed,
            isInit: context.isInit,
          }),
        ),
      );
      const entries = definitionCache.get(definition) ?? [];
      entries[index] = compiled;
      definitionCache.set(definition, entries);
      return compiled;
    }
    return materializeRecursive(getRecursiveFunction(definition, context, undefined));
  };

  // A recursive function as a value: its body applied to each element of its domain.
  const materializeRecursive = (recursive: RecursiveFunction): Compiled => {
    return {
      evaluate: () => {
        const domain = recursive.domain.evaluate();
        if (kindOf(domain) !== KIND_SET) return bail("a function over a non-set");
        const size = sizeOf(domain);
        const keys: number[] = new Array(size);
        const values: number[] = new Array(size);
        for (let index = 0; index < size; index++) {
          keys[index] = elementAt(domain, index);
          values[index] = callRecursiveFunction(recursive, keys[index]);
        }
        return functionOfSorted(keys, values, size);
      },
      footprint: recursive.footprint(),
      isCostly: true,
      isNormalized: true,
    };
  };

  // A function defined in terms of itself, such as f[n \in Nat] == IF n = 0 THEN 1 ELSE n * f[n-1].
  // Applying it evaluates its body with the argument bound, cached by the argument and whatever else
  // the body reads.
  interface RecursiveFunction {
    slot: number;
    domain: Compiled;
    isInDomain?: (element: number) => boolean;
    body: Compiled | undefined;
    table: MemoTable | undefined;
    keyVars: number[];
    keyPrimes: number[];
    keySlots: number[];
    footprint: () => Footprint;
    // The slots the body binds.
    slotStart: number;
    slotEnd: number;
    // What a call inside the body reads besides its argument, as for a RECURSIVE operator.
    assumed: Footprint;
  }

  const recursiveFunctions = new Map<
    FunctionDefinition,
    Map<Scope | undefined, RecursiveFunction[]>
  >();

  const getRecursiveFunction = (
    definition: FunctionDefinition,
    context: Context,
    baseScope: Scope | undefined,
  ) => {
    const index = context.isPrimed ? 1 : 0;
    const byScope =
      recursiveFunctions.get(definition) ?? new Map<Scope | undefined, RecursiveFunction[]>();
    recursiveFunctions.set(definition, byScope);
    const known = byScope.get(baseScope)?.[index];
    if (known) return known;
    const bound = definition.bounds[0];
    if (definition.bounds.length !== 1 || bound.pattern.kind !== "Name") {
      return unsupported("a recursive function of several arguments");
    }
    const outer = { scope: baseScope, isPrimed: context.isPrimed, isInit: context.isInit };
    const slot = allocateSlot();
    const record: RecursiveFunction = {
      slot,
      domain: compile(bound.set, outer),
      body: undefined,
      table: undefined,
      keyVars: [],
      keyPrimes: [],
      keySlots: [],
      slotStart: 0,
      slotEnd: 0,
      assumed: EMPTY_FOOTPRINT,
      footprint: () =>
        mergeFootprints(
          record.domain.footprint,
          record.body ? withoutSlots(record.body.footprint, [slot]) : record.assumed,
        ),
    };
    const entries = byScope.get(baseScope) ?? [];
    entries[index] = record;
    byScope.set(baseScope, entries);
    const bodyContext = {
      ...outer,
      scope: bind(baseScope, bound.pattern.name, { kind: "slot", slot }),
    };
    const compileBody = () => {
      record.slotStart = slotCount;
      const body = compile(definition.body, bodyContext);
      record.slotEnd = slotCount;
      return body;
    };
    // A call inside the body reads what the last compile of the body read, until it reads no more.
    let body = compileBody();
    while (!isWithinFootprint(withoutSlots(body.footprint, [slot]), record.assumed)) {
      record.assumed = mergeFootprints(record.assumed, withoutSlots(body.footprint, [slot]));
      body = compileBody();
    }
    record.body = body;
    const footprint = record.body.footprint;
    record.keySlots = mergeSorted([slot], footprint.slots);
    record.keyVars = footprint.vars;
    record.keyPrimes = footprint.primes;
    const width = record.keySlots.length + record.keyVars.length + record.keyPrimes.length;
    if (width <= MAXIMUM_MEMO_WIDTH) {
      record.table = new MemoTable(width);
      memoTables.push(record.table);
    }
    return record;
  };

  const callRecursiveFunction = (record: RecursiveFunction, argument: number) => {
    record.isInDomain ??= memberTest(record.domain);
    if (!record.isInDomain(argument))
      return bail("applied a recursive function outside its domain");
    const slot = record.slot;
    const saved = LOC[slot];
    LOC[slot] = argument;
    try {
      const table = record.table;
      const body = record.body!;
      if (!table || !table.isEnabled)
        return evaluateKeepingSlots(body.evaluate, record.slotStart, record.slotEnd);
      const scratch = new Int32Array(table.width);
      let position = 0;
      for (const variable of record.keyVars) scratch[position++] = CUR[variable];
      for (const variable of record.keyPrimes) scratch[position++] = NXT[variable];
      for (const keySlot of record.keySlots) scratch[position++] = LOC[keySlot];
      const known = table.getN(scratch);
      if (known !== -1) return known;
      const value = evaluateKeepingSlots(body.evaluate, record.slotStart, record.slotEnd);
      table.setN(scratch, value);
      return value;
    } finally {
      LOC[slot] = saved;
    }
  };

  // The recursive function an application applies, when it names one directly.
  const getAppliedRecursiveFunction = (fn: Expression, context: Context) => {
    if (fn.kind !== "Identifier") return undefined;
    const local = lookup(context.scope, fn.name);
    if (local?.kind === "recursive") {
      return getRecursiveFunction(local.definition, context, local.scope);
    }
    if (local) return undefined;
    if (environment.variableIndex.has(fn.name) || environment.constants.has(fn.name)) {
      return undefined;
    }
    const definition = getDefinition(fn.name, environment);
    if (definition?.kind !== "Function") return undefined;
    if (!definition.isRecursive && !definition.isSelfReferential) return undefined;
    return getRecursiveFunction(definition, context, undefined);
  };

  // --- quantifiers and bindings ---

  // Binds the names of a bound to fresh slots.
  const bindBound = (bound: Bound, context: Context) => {
    const pattern = bound.pattern;
    if (pattern.kind === "Name") {
      const slot = allocateSlot();
      return {
        context: { ...context, scope: bind(context.scope, pattern.name, { kind: "slot", slot }) },
        slots: [slot],
        tuple: undefined,
      };
    }
    let scope = context.scope;
    const slots = pattern.names.map((name) => {
      const slot = allocateSlot();
      scope = bind(scope, name, { kind: "slot", slot });
      return slot;
    });
    return { context: { ...context, scope }, slots, tuple: slots };
  };

  const assignBound = (slots: number[], tuple: number[] | undefined, element: number) => {
    if (!tuple) {
      LOC[slots[0]] = element;
      return;
    }
    if (kindOf(element) !== KIND_TUPLE || sizeOf(element) !== tuple.length)
      bail("a tuple pattern that doesn't match");
    for (let index = 0; index < tuple.length; index++)
      LOC[tuple[index]] = getRangeValue(element, index);
  };

  const compileQuantifier = (
    expression: Expression & { kind: "Forall" | "Exists" },
    context: Context,
  ): Compiled => {
    const isForall = expression.kind === "Forall";
    let inner = context;
    const levels: { set: Compiled; slots: number[]; tuple: number[] | undefined }[] = [];
    const bound: number[] = [];
    for (const item of expression.bounds) {
      const set = compile(item.set, inner);
      const binding = bindBound(item, inner);
      inner = binding.context;
      levels.push({ set, slots: binding.slots, tuple: binding.tuple });
      bound.push(...binding.slots);
    }
    const body = compileBoolean(expression.body, inner);
    const bodyEvaluate = body.evaluate;
    const stop = isForall ? FALSE : TRUE;
    const visit = (level: number): number => {
      if (level === levels.length) return bodyEvaluate();
      const current = levels[level];
      const set = current.set.evaluate();
      if (kindOf(set) !== KIND_SET) return bail("quantified over a non-set");
      const size = sizeOf(set);
      for (let index = 0; index < size; index++) {
        assignBound(current.slots, current.tuple, elementAt(set, index));
        if (visit(level + 1) === stop) return stop;
      }
      return isForall ? TRUE : FALSE;
    };
    const single = levels.length === 1 && !levels[0].tuple ? levels[0] : undefined;
    const evaluate = single
      ? ((setEvaluate, slot) => () => {
          const set = setEvaluate();
          if (kindOf(set) !== KIND_SET) return bail("quantified over a non-set");
          const size = sizeOf(set);
          for (let index = 0; index < size; index++) {
            LOC[slot] = elementAt(set, index);
            if (bodyEvaluate() === stop) return stop;
          }
          return isForall ? TRUE : FALSE;
        })(single.set.evaluate, single.slots[0])
      : () => visit(0);
    return {
      evaluate,
      footprint: mergeFootprints(
        ...levels.map((level) => level.set.footprint),
        withoutSlots(body.footprint, bound),
      ),
      isCostly: true,
      isNormalized: true,
    };
  };

  const compileChoose = (
    expression: Expression & { kind: "Choose" },
    context: Context,
  ): Compiled => {
    if (!expression.set) return unsupported("unbounded CHOOSE");
    const set = compile(expression.set, context);
    const binding = bindBound({ pattern: expression.pattern, set: expression.set }, context);
    const body = compileBoolean(expression.body, binding.context);
    const setEvaluate = set.evaluate;
    const bodyEvaluate = body.evaluate;
    return {
      evaluate: () => {
        const id = setEvaluate();
        if (kindOf(id) !== KIND_SET) return bail("CHOOSE from a non-set");
        const size = sizeOf(id);
        for (let index = 0; index < size; index++) {
          const element = elementAt(id, index);
          assignBound(binding.slots, binding.tuple, element);
          if (bodyEvaluate() === TRUE) return element;
        }
        return bail("CHOOSE found no element");
      },
      footprint: mergeFootprints(set.footprint, withoutSlots(body.footprint, binding.slots)),
      isCostly: true,
      isNormalized: true,
    };
  };

  const compileSetFilter = (
    expression: Expression & { kind: "SetFilter" },
    context: Context,
  ): Compiled => {
    const set = compile(expression.bound.set, context);
    if ((set as LazySet).infinite) return unsupported("filtering an infinite set");
    const binding = bindBound(expression.bound, context);
    const predicate = compileBoolean(expression.predicate, binding.context);
    const setEvaluate = set.evaluate;
    const predicateEvaluate = predicate.evaluate;
    return {
      evaluate: () => {
        const id = setEvaluate();
        if (kindOf(id) !== KIND_SET) return bail("filtered a non-set");
        const size = sizeOf(id);
        const kept: number[] = [];
        for (let index = 0; index < size; index++) {
          const element = elementAt(id, index);
          assignBound(binding.slots, binding.tuple, element);
          if (predicateEvaluate() === TRUE) kept.push(element);
        }
        return kept.length === size ? id : setOfSorted(kept, kept.length);
      },
      footprint: mergeFootprints(set.footprint, withoutSlots(predicate.footprint, binding.slots)),
      isCostly: true,
      isNormalized: set.isNormalized,
      isEnumerated: set.isEnumerated,
      areElementsEnumerated: set.areElementsEnumerated,
      // TLC filters a set it can't enumerate, such as SUBSET S, lazily, in the order of the set.
      reference: set.isNormalized
        ? undefined
        : combineReferences([set], ([base]) => {
            const test = (element: Value) => {
              const saved = binding.slots.map((slot) => LOC[slot]);
              try {
                assignBound(binding.slots, binding.tuple, fromValue(element));
                const value = predicateEvaluate();
                return value === TRUE
                  ? true
                  : value === FALSE
                    ? false
                    : bail("a filter that isn't a boolean");
              } finally {
                binding.slots.forEach((slot, index) => {
                  LOC[slot] = saved[index];
                });
              }
            };
            return (): Value => {
              const value = base();
              if (isReducibleSet(value))
                return createSortedSet(toFiniteSet(value).elements.filter(test));
              return { kind: "FilteredSet", base: value, test };
            };
          }),
    };
  };

  const compileSetMap = (
    expression: Expression & { kind: "SetMap" },
    context: Context,
  ): Compiled => {
    let inner = context;
    const levels: { set: Compiled; slots: number[]; tuple: number[] | undefined }[] = [];
    const bound: number[] = [];
    for (const item of expression.bounds) {
      const set = compile(item.set, inner);
      const binding = bindBound(item, inner);
      inner = binding.context;
      levels.push({ set, slots: binding.slots, tuple: binding.tuple });
      bound.push(...binding.slots);
    }
    const body = compile(expression.expression, inner);
    const bodyEvaluate = body.evaluate;
    return {
      evaluate: () => {
        const images: number[] = [];
        const visit = (level: number) => {
          if (level === levels.length) {
            images.push(bodyEvaluate());
            return;
          }
          const current = levels[level];
          const set = current.set.evaluate();
          if (kindOf(set) !== KIND_SET) bail("mapped a non-set");
          const size = sizeOf(set);
          for (let index = 0; index < size; index++) {
            assignBound(current.slots, current.tuple, elementAt(set, index));
            visit(level + 1);
          }
        };
        visit(0);
        return setOf(images);
      },
      footprint: mergeFootprints(
        ...levels.map((level) => level.set.footprint),
        withoutSlots(body.footprint, bound),
      ),
      isCostly: true,
      isNormalized: true,
      isEnumerated: true,
      areElementsEnumerated: body.isEnumerated === true,
    };
  };

  const compileFunctionConstruction = (
    bounds: Bound[],
    bodyExpression: Expression,
    context: Context,
  ): Compiled => {
    let inner = context;
    const levels: { set: Compiled; slots: number[]; tuple: number[] | undefined }[] = [];
    const bound: number[] = [];
    for (const item of bounds) {
      const set = compile(item.set, inner);
      const binding = bindBound(item, inner);
      inner = binding.context;
      levels.push({ set, slots: binding.slots, tuple: binding.tuple });
      bound.push(...binding.slots);
    }
    const body = compile(bodyExpression, inner);
    const bodyEvaluate = body.evaluate;
    const single = levels.length === 1 && !levels[0].tuple ? levels[0] : undefined;
    const evaluate = single
      ? ((setEvaluate, slot) => () => {
          const set = setEvaluate();
          if (kindOf(set) !== KIND_SET) return bail("a function over a non-set");
          const size = sizeOf(set);
          const keys: number[] = new Array(size);
          const values: number[] = new Array(size);
          for (let index = 0; index < size; index++) {
            const key = elementAt(set, index);
            keys[index] = key;
            LOC[slot] = key;
            values[index] = bodyEvaluate();
          }
          return functionOfSorted(keys, values, size);
        })(single.set.evaluate, single.slots[0])
      : () => {
          // A function of several arguments takes tuples, in TLC's order of the product.
          const sets = levels.map((level) => {
            const set = level.set.evaluate();
            if (kindOf(set) !== KIND_SET) bail("a function over a non-set");
            return set;
          });
          if (levels.some((level) => level.tuple)) bail("a tuple pattern in a function");
          const keys: number[] = [];
          const values: number[] = [];
          const current: number[] = new Array(levels.length);
          const visit = (level: number) => {
            if (level === levels.length) {
              keys.push(tupleOf(current, current.length));
              values.push(bodyEvaluate());
              return;
            }
            const set = sets[level];
            const size = sizeOf(set);
            for (let index = 0; index < size; index++) {
              const element = elementAt(set, index);
              current[level] = element;
              LOC[levels[level].slots[0]] = element;
              visit(level + 1);
            }
          };
          visit(0);
          return functionOf(keys, values);
        };
    return {
      evaluate,
      footprint: mergeFootprints(
        ...levels.map((level) => level.set.footprint),
        withoutSlots(body.footprint, bound),
      ),
      isCostly: true,
      isNormalized: true,
    };
  };

  // --- functions ---

  const compileFunctionApplication = (
    expression: Expression & { kind: "FunctionApplication" },
    context: Context,
  ): Compiled => {
    const recursive = getAppliedRecursiveFunction(expression.function, context);
    if (recursive && expression.args.length === 1) {
      const argument = compile(expression.args[0], context);
      const argumentEvaluate = argument.evaluate;
      return {
        evaluate: () => callRecursiveFunction(recursive, argumentEvaluate()),
        footprint: mergeFootprints(argument.footprint, recursive.footprint()),
        isCostly: false,
        isNormalized: true,
      };
    }
    const fn = compile(expression.function, context);
    const args = expression.args.map((argument) => compile(argument, context));
    const fnEvaluate = fn.evaluate;
    const footprint = mergeFootprints(fn.footprint, ...args.map((argument) => argument.footprint));
    if (args.length === 1) {
      const argumentEvaluate = args[0].evaluate;
      return {
        ...leaf(() => apply(fnEvaluate(), argumentEvaluate()), footprint),
        emit: (gen) => `${gen.ref(apply)}(${codeOf(fn, gen)}, ${codeOf(args[0], gen)})`,
      };
    }
    const evaluators = args.map((argument) => argument.evaluate);
    return leaf(() => {
      const values = evaluators.map((evaluate) => evaluate());
      return apply(fnEvaluate(), tupleOf(values, values.length));
    }, footprint);
  };

  const compileExcept = (
    expression: Expression & { kind: "Except" },
    context: Context,
  ): Compiled => {
    const fn = compile(expression.function, context);
    const updates = expression.updates.map((update) => {
      const path = update.path.map((step) => {
        if (step.kind === "Field") return { key: constant(str(step.name)) };
        const args = step.args.map((argument) => compile(argument, context));
        if (args.length === 1) return { key: args[0] };
        const evaluators = args.map((argument) => argument.evaluate);
        return {
          key: {
            evaluate: () => {
              const values = evaluators.map((evaluate) => evaluate());
              return tupleOf(values, values.length);
            },
            footprint: mergeFootprints(...args.map((argument) => argument.footprint)),
            isCostly: false,
            isNormalized: true,
          } as Compiled,
        };
      });
      const atSlot = allocateSlot();
      const valueContext = {
        ...context,
        scope: bind(context.scope, "@", { kind: "slot", slot: atSlot }),
      };
      const value = compile(update.value, valueContext);
      return { path, atSlot, value, usesAt: value.footprint.slots.includes(atSlot) };
    });
    const fnEvaluate = fn.evaluate;
    // Each update names one key, as [f EXCEPT ![k] = v] and [r EXCEPT !.a = v] do.
    const flat = updates.every((update) => update.path.length === 1)
      ? updates.map((update) => ({
          key: update.path[0].key.evaluate,
          value: update.value.evaluate,
          atSlot: update.usesAt ? update.atSlot : -1,
        }))
      : undefined;
    // Several updates write one new function: each key's position is the same in every
    // intermediate function, and @ reads the value an earlier update gave the key, if any.
    const evaluateMany = (flatUpdates: NonNullable<typeof flat>) => () => {
      const base = fnEvaluate();
      if (!isFunctionKind(kindOf(base))) return bail("EXCEPT on a non-function");
      const count = flatUpdates.length;
      const positions: number[] = new Array(count);
      const values: number[] = new Array(count);
      for (let index = 0; index < count; index++) {
        const update = flatUpdates[index];
        const position = findKey(base, update.key());
        if (position === -1) return bail("EXCEPT outside the domain");
        if (update.atSlot !== -1) {
          let old = getRangeValue(base, position);
          for (let earlier = 0; earlier < index; earlier++)
            if (positions[earlier] === position) old = values[earlier];
          LOC[update.atSlot] = old;
        }
        positions[index] = position;
        values[index] = update.value();
      }
      return exceptAt(base, positions, values, count);
    };
    const evaluateFlat = (flatUpdates: NonNullable<typeof flat>) => () => {
      let result = fnEvaluate();
      for (let index = 0; index < flatUpdates.length; index++) {
        const update = flatUpdates[index];
        const key = update.key();
        if (update.atSlot !== -1) {
          if (!isFunctionKind(kindOf(result))) return bail("EXCEPT on a non-function");
          const position = findKey(result, key);
          if (position === -1) return bail("EXCEPT outside the domain");
          LOC[update.atSlot] = getRangeValue(result, position);
        }
        result = except(result, key, update.value());
      }
      return result;
    };
    const evaluate = flat
      ? flat.length > 1
        ? evaluateMany(flat)
        : evaluateFlat(flat)
      : () => {
          let result = fnEvaluate();
          for (const update of updates) {
            const keys = update.path.map((step) => step.key.evaluate());
            const rewrite = (current: number, depthIndex: number): number => {
              const key = keys[depthIndex];
              if (!isFunctionKind(kindOf(current))) return bail("EXCEPT on a non-function");
              const position = findKey(current, key);
              if (position === -1) return bail("EXCEPT outside the domain");
              const old = getRangeValue(current, position);
              if (depthIndex === keys.length - 1) {
                LOC[update.atSlot] = old;
                return except(current, key, update.value.evaluate());
              }
              return except(current, key, rewrite(old, depthIndex + 1));
            };
            result = rewrite(result, 0);
          }
          return result;
        };
    return {
      evaluate,
      footprint: mergeFootprints(
        fn.footprint,
        ...updates.flatMap((update) => [
          ...update.path.map((step) => step.key.footprint),
          withoutSlots(update.value.footprint, [update.atSlot]),
        ]),
      ),
      isCostly: true,
      isNormalized: true,
    };
  };

  // --- sets the engine tests for membership without building ---

  interface LazySet extends Compiled {
    infinite?: string;
    // Membership, when the engine can test it without building the set.
    member?: (element: number) => boolean;
  }

  const compileLazySet = (
    expression: Expression & { kind: "FunctionSet" | "RecordSet" | "Product" },
    context: Context,
  ): LazySet => {
    if (expression.kind === "FunctionSet") {
      const domain = compile(expression.domain, context) as LazySet;
      const range = compile(expression.range, context) as LazySet;
      const domainEvaluate = domain.evaluate;
      const rangeMember = memberTest(range);
      const footprint = mergeFootprints(domain.footprint, range.footprint);
      return {
        evaluate: () => {
          const domainSet = domainEvaluate();
          const rangeSet = range.evaluate();
          return enumerateFunctionSet(domainSet, rangeSet);
        },
        footprint,
        isCostly: true,
        // TLC enumerates [S -> T] in its own order, which the engine leaves to the reference.
        isNormalized: false,
        reference: combineReferences(
          [domain, range],
          ([domainReference, rangeReference]) =>
            () => ({
              kind: "FunctionSet",
              domain: domainReference(),
              range: rangeReference(),
            }),
        ),
        member: (element) => {
          const kind = kindOf(element);
          if (kind !== KIND_FUNCTION && kind !== KIND_TUPLE) return false;
          const domainSet = domainEvaluate();
          if (!equalsDomain(element, domainSet)) return false;
          const size = sizeOf(element);
          for (let index = 0; index < size; index++) {
            if (!rangeMember(getRangeValue(element, index))) return false;
          }
          return true;
        },
      };
    }
    if (expression.kind === "RecordSet") {
      const fields = expression.fields
        .map((field) => ({ key: str(field.name), set: compile(field.value, context) as LazySet }))
        .sort((left, right) => compare(left.key, right.key));
      const keys = fields.map((field) => field.key);
      const members = fields.map((field) => memberTest(field.set));
      const footprint = mergeFootprints(...fields.map((field) => field.set.footprint));
      return {
        evaluate: () => {
          const sets = fields.map((field) => field.set.evaluate());
          let partial: number[][] = [[]];
          for (const set of sets) {
            if (kindOf(set) !== KIND_SET) bail("a record set of a non-set");
            const next: number[][] = [];
            for (const prefix of partial) {
              for (let index = 0; index < sizeOf(set); index++)
                next.push([...prefix, elementAt(set, index)]);
            }
            partial = next;
          }
          return setOf(partial.map((values) => functionOfSorted(keys, values, keys.length)));
        },
        footprint,
        isCostly: true,
        isNormalized: false,
        reference: combineReferences(
          fields.map((field) => field.set),
          (references) => () => ({
            kind: "RecordSet",
            names: fields.map((field) => textOf(field.key)),
            sets: references.map((reference) => reference()),
          }),
        ),
        member: (element) => {
          if (kindOf(element) !== KIND_FUNCTION || sizeOf(element) !== keys.length) return false;
          for (let index = 0; index < keys.length; index++) {
            if (getKey(element, index) !== keys[index]) return false;
            if (!members[index](getRangeValue(element, index))) return false;
          }
          return true;
        },
      };
    }
    const factors = expression.factors.map((factor) => compile(factor, context) as LazySet);
    const members = factors.map(memberTest);
    return {
      evaluate: () => {
        let partial: number[][] = [[]];
        for (const factor of factors) {
          const set = factor.evaluate();
          if (kindOf(set) !== KIND_SET) bail("a product of a non-set");
          const next: number[][] = [];
          for (const prefix of partial) {
            for (let index = 0; index < sizeOf(set); index++)
              next.push([...prefix, elementAt(set, index)]);
          }
          partial = next;
        }
        return setOf(partial.map((values) => tupleOf(values, values.length)));
      },
      footprint: mergeFootprints(...factors.map((factor) => factor.footprint)),
      isCostly: true,
      isNormalized: false,
      reference: combineReferences(factors, (references) => () => ({
        kind: "ProductSet",
        factors: references.map((reference) => reference()),
      })),
      member: (element) => {
        if (kindOf(element) !== KIND_TUPLE || sizeOf(element) !== factors.length) return false;
        for (let index = 0; index < factors.length; index++) {
          if (!members[index](getRangeValue(element, index))) return false;
        }
        return true;
      },
    };
  };

  const equalsDomain = (fn: number, domain: number) => {
    if (kindOf(domain) !== KIND_SET) return bail("a function set over a non-set domain");
    const size = sizeOf(fn);
    if (size !== sizeOf(domain)) return false;
    for (let index = 0; index < size; index++)
      if (getKey(fn, index) !== elementAt(domain, index)) return false;
    return true;
  };

  const enumerateFunctionSet = (domain: number, range: number) => {
    if (kindOf(domain) !== KIND_SET || kindOf(range) !== KIND_SET)
      return bail("a function set of non-sets");
    const domainSize = sizeOf(domain);
    const rangeSize = sizeOf(range);
    if (Math.pow(rangeSize, domainSize) > 1e6) return bail("a function set too large to build");
    const keys = Array.from({ length: domainSize }, (_, index) => elementAt(domain, index));
    const functions: number[] = [];
    const values: number[] = new Array(domainSize);
    const visit = (index: number) => {
      if (index === domainSize) {
        functions.push(functionOfSorted(keys, values, domainSize));
        return;
      }
      for (let position = 0; position < rangeSize; position++) {
        values[index] = elementAt(range, position);
        visit(index + 1);
      }
    };
    visit(0);
    return setOf(functions);
  };

  // TLC fails to test a value other than a model value for membership in a set of another kind.
  const notIn = (element: number, set: string) =>
    kindOf(element) === KIND_MODEL ? false : bail(`a mistyped membership in ${set}`);

  // A membership test for a compiled set, which builds the set only when it must.
  const memberTest = (set: Compiled): ((element: number) => boolean) => {
    const lazy = set as LazySet;
    if (lazy.member) return lazy.member;
    if (lazy.infinite) {
      switch (lazy.infinite) {
        case "Nat":
          return (element) =>
            kindOf(element) === KIND_INT ? intOf(element) >= 0 : notIn(element, "Nat");
        case "Int":
          return (element) => kindOf(element) === KIND_INT || notIn(element, "Int");
        default:
          return (element) => kindOf(element) === KIND_STRING || notIn(element, "STRING");
      }
    }
    const evaluate = set.evaluate;
    return (element) => {
      const id = evaluate();
      if (kindOf(id) !== KIND_SET) return bail("membership in a non-set");
      return isMember(element, id);
    };
  };

  // --- builtins ---

  const compileBuiltin = (
    name: string,
    builtin: Builtin,
    expression: Expression & { kind: "Apply" },
    context: Context,
  ): Compiled => {
    if (builtin.isStateLevel || IMPURE_BUILTINS.has(name)) {
      if (name === "TLCEval" && expression.args.length === 1)
        return compile(expression.args[0], context);
      return unsupported(name);
    }
    const args = expression.args;
    const native = compileNativeBuiltin(name, args, context);
    if (native) return native;
    if (!PURE_BUILTINS.has(name)) return unsupported(name);
    return compileBridgedBuiltin(name, builtin, args, context);
  };

  const binary = (
    left: Compiled,
    right: Compiled,
    operation: (left: number, right: number) => number,
    isCostly = false,
    isBoolean = false,
  ): Compiled => {
    const leftEvaluate = left.evaluate;
    const rightEvaluate = right.evaluate;
    return {
      evaluate: () => operation(leftEvaluate(), rightEvaluate()),
      footprint: mergeFootprints(left.footprint, right.footprint),
      isCostly,
      isNormalized: true,
      emit: (gen) => `${gen.ref(operation)}(${codeOf(left, gen)}, ${codeOf(right, gen)})`,
      isBoolean,
    };
  };

  const unary = (
    operand: Compiled,
    operation: (value: number) => number,
    isCostly = false,
  ): Compiled => {
    const evaluate = operand.evaluate;
    return {
      evaluate: () => operation(evaluate()),
      footprint: operand.footprint,
      isCostly,
      isNormalized: true,
      emit: (gen) => `${gen.ref(operation)}(${codeOf(operand, gen)})`,
    };
  };

  const expectInt = (id: number) =>
    kindOf(id) === KIND_INT ? intOf(id) : bail("expected an integer");
  const expectSet = (id: number) => (kindOf(id) === KIND_SET ? id : bail("expected a set"));

  const compileNativeBuiltin = (
    name: string,
    args: Expression[],
    context: Context,
  ): Compiled | undefined => {
    const operand = (index: number) => compile(args[index], context);
    switch (name) {
      case "=":
        return binary(operand(0), operand(1), equalsId, false, true);
      case "#":
        return binary(operand(0), operand(1), differsId, false, true);
      case "~": {
        const negated = compileBoolean(args[0], context);
        return {
          ...unary(negated, (value) => (value === TRUE ? FALSE : TRUE)),
          emit: (gen) => `1 - ${codeOf(negated, gen)}`,
          isBoolean: true,
        };
      }
      case "/\\":
      case "\\/":
        return compileJunction(
          { kind: name === "/\\" ? "And" : "Or", operands: args, location: args[0].location },
          context,
        );
      case "=>": {
        const left = compileBoolean(args[0], context);
        const right = compileBoolean(args[1], context);
        const leftEvaluate = left.evaluate;
        const rightEvaluate = right.evaluate;
        return leaf(
          () => (leftEvaluate() === FALSE ? TRUE : rightEvaluate()),
          mergeFootprints(left.footprint, right.footprint),
        );
      }
      case "<=>":
        return binary(
          compileBoolean(args[0], context),
          compileBoolean(args[1], context),
          (left, right) => bool(left === right),
        );
      case "\\in":
      case "\\notin": {
        const element = operand(0);
        const set = operand(1);
        const member = memberTest(set);
        const elementEvaluate = element.evaluate;
        const isIn = name === "\\in";
        return {
          evaluate: () => bool(member(elementEvaluate()) === isIn),
          footprint: mergeFootprints(element.footprint, set.footprint),
          isCostly: (set as LazySet).member !== undefined,
          isNormalized: true,
          emit: (gen) =>
            `${gen.ref(member)}(${codeOf(element, gen)}) ? ${isIn ? 1 : 0} : ${isIn ? 0 : 1}`,
          isBoolean: true,
        };
      }
      case "\\subseteq": {
        const left = operand(0);
        const right = operand(1);
        const member = memberTest(right);
        const leftEvaluate = left.evaluate;
        const isLazy =
          (right as LazySet).member !== undefined || (right as LazySet).infinite !== undefined;
        return {
          evaluate: isLazy
            ? () => {
                const set = expectSet(leftEvaluate());
                const size = sizeOf(set);
                for (let index = 0; index < size; index++)
                  if (!member(elementAt(set, index))) return FALSE;
                return TRUE;
              }
            : (
                (rightEvaluate) => () =>
                  bool(isSubset(expectSet(leftEvaluate()), expectSet(rightEvaluate())))
              )(right.evaluate),
          footprint: mergeFootprints(left.footprint, right.footprint),
          isCostly: true,
          isNormalized: true,
        };
      }
      case "\\cup":
      case "\\cap":
      case "\\": {
        const left = operand(0);
        const right = operand(1);
        // A set the engine tests for membership without building it, such as Nat \ {0} or a union
        // of record sets with a field in Nat, combines the operands' tests.
        const isLazy = (set: Compiled) =>
          (set as LazySet).infinite !== undefined || (set as LazySet).member !== undefined;
        const lazyMember = (() => {
          if (!isLazy(left) && !isLazy(right)) return undefined;
          const leftMember = memberTest(left);
          const rightMember = memberTest(right);
          if (name === "\\cup")
            return (element: number) => leftMember(element) || rightMember(element);
          if (name === "\\cap")
            return (element: number) => leftMember(element) && rightMember(element);
          return (element: number) => leftMember(element) && !rightMember(element);
        })();
        if ((left as LazySet).infinite || (right as LazySet).infinite) {
          if (name === "\\" ? (right as LazySet).infinite : name !== "\\cup") return undefined;
          return {
            ...leaf(
              () => bail("an enumerated infinite set"),
              mergeFootprints(left.footprint, right.footprint),
              false,
            ),
            infinite: "Combined",
            member: lazyMember,
          } as LazySet;
        }
        const operation = name === "\\cup" ? union : name === "\\cap" ? intersection : difference;
        const compiled = binary(
          left,
          right,
          (leftId, rightId) => operation(expectSet(leftId), expectSet(rightId)),
          true,
        );
        // TLC tests each element of a set enumeration for membership in the other set, so the
        // difference or intersection with one keeps its order whatever the other set is.
        const isNormalized =
          name === "\\"
            ? left.isNormalized
            : name === "\\cap"
              ? left.isNormalized || right.isNormalized
              : left.isNormalized && right.isNormalized;
        return {
          ...compiled,
          isNormalized,
          ...(lazyMember && { member: lazyMember }),
          // TLC combines a set it keeps lazy with another lazily, as the reference does.
          reference: isNormalized
            ? undefined
            : (() => {
                const leftReference = referenceOf(left);
                // TLC enumerates the left set of a difference or an intersection and only tests
                // the right one for membership, which any value of it answers alike.
                const rightReference =
                  referenceOf(right) ??
                  (name !== "\\cup" && !(right as LazySet).infinite
                    ? (
                        (evaluate) => () =>
                          toValue(evaluate())
                      )(right.evaluate)
                    : undefined);
                if (!leftReference || !rightReference) return undefined;
                const builtin = environment.builtins.get(name)!;
                return () => builtin.evaluate([leftReference(), rightReference()]);
              })(),
        };
      }
      case "SUBSET": {
        const base = operand(0);
        return {
          ...unary(base, (set) => powerSet(expectSet(set)), true),
          isNormalized: false,
          reference: combineReferences([base], ([baseReference]) => () => ({
            kind: "Subset",
            base: baseReference(),
          })),
          member: ((baseMember) => (element: number) => {
            if (kindOf(element) !== KIND_SET) return false;
            for (let index = 0; index < sizeOf(element); index++)
              if (!baseMember(elementAt(element, index))) return false;
            return true;
          })(memberTest(base)),
        } as LazySet;
      }
      case "UNION": {
        const outer = operand(0);
        const isEnumerated = outer.isEnumerated === true && outer.areElementsEnumerated === true;
        return {
          ...unary(
            outer,
            (set) => {
              let result = EMPTY_SET;
              const sets = expectSet(set);
              for (let index = 0; index < sizeOf(sets); index++)
                result = union(result, expectSet(elementAt(sets, index)));
              return result;
            },
            true,
          ),
          isNormalized: isEnumerated,
          isEnumerated,
        };
      }
      case "DOMAIN":
        return unary(
          operand(0),
          (fn) => (isFunctionKind(kindOf(fn)) ? domainOf(fn) : bail("DOMAIN of a non-function")),
          true,
        );
      case "+":
        return binary(operand(0), operand(1), (left, right) =>
          int(expectInt(left) + expectInt(right)),
        );
      case "-":
        return binary(operand(0), operand(1), (left, right) =>
          int(expectInt(left) - expectInt(right)),
        );
      case "*":
        return binary(operand(0), operand(1), (left, right) =>
          int(expectInt(left) * expectInt(right)),
        );
      case "-.":
        return unary(operand(0), (value) => int(-expectInt(value)));
      case "\\div":
        return binary(operand(0), operand(1), (left, right) => {
          const divisor = expectInt(right);
          if (divisor === 0) return bail("division by zero");
          return int(Math.floor(expectInt(left) / divisor));
        });
      case "%":
        return binary(operand(0), operand(1), (left, right) => {
          const divisor = expectInt(right);
          if (divisor <= 0) return bail("modulus by a non-positive number");
          const remainder = expectInt(left) % divisor;
          return int(remainder < 0 ? remainder + divisor : remainder);
        });
      case "^":
        return binary(operand(0), operand(1), (left, right) => {
          const exponent = expectInt(right);
          if (exponent < 0) return bail("negative exponent");
          return int(Math.pow(expectInt(left), exponent));
        });
      case "<":
        return binary(
          operand(0),
          operand(1),
          (left, right) => bool(expectInt(left) < expectInt(right)),
          false,
          true,
        );
      case ">":
        return binary(
          operand(0),
          operand(1),
          (left, right) => bool(expectInt(left) > expectInt(right)),
          false,
          true,
        );
      case "<=":
        return binary(
          operand(0),
          operand(1),
          (left, right) => bool(expectInt(left) <= expectInt(right)),
          false,
          true,
        );
      case ">=":
        return binary(
          operand(0),
          operand(1),
          (left, right) => bool(expectInt(left) >= expectInt(right)),
          false,
          true,
        );
      case "..":
        return binary(
          operand(0),
          operand(1),
          (left, right) => interval(expectInt(left), expectInt(right)),
          true,
        );
      case "Len":
        return unary(operand(0), (sequence) => int(sizeOf(expectSequence(sequence))));
      case "Head":
        return unary(operand(0), (sequence) => {
          const tuple = expectSequence(sequence);
          return sizeOf(tuple) === 0 ? bail("Head of an empty sequence") : getRangeValue(tuple, 0);
        });
      case "Tail":
        return unary(operand(0), (sequence) => {
          const tuple = expectSequence(sequence);
          const size = sizeOf(tuple);
          if (size === 0) return bail("Tail of an empty sequence");
          const elements: number[] = new Array(size - 1);
          for (let index = 1; index < size; index++)
            elements[index - 1] = getRangeValue(tuple, index);
          return tupleOf(elements, size - 1);
        });
      case "Append":
        return binary(operand(0), operand(1), (sequence, element) => {
          const tuple = expectSequence(sequence);
          const size = sizeOf(tuple);
          const elements: number[] = new Array(size + 1);
          for (let index = 0; index < size; index++) elements[index] = getRangeValue(tuple, index);
          elements[size] = element;
          return tupleOf(elements, size + 1);
        });
      case "\\o":
        return binary(operand(0), operand(1), (left, right) => {
          if (kindOf(left) === KIND_STRING && kindOf(right) === KIND_STRING) {
            return str(textOf(left) + textOf(right));
          }
          if (kindOf(left) === KIND_STRING || kindOf(right) === KIND_STRING) {
            return bail("concatenation of a string and a sequence");
          }
          const first = expectSequence(left);
          const second = expectSequence(right);
          const elements: number[] = [];
          for (let index = 0; index < sizeOf(first); index++)
            elements.push(getRangeValue(first, index));
          for (let index = 0; index < sizeOf(second); index++)
            elements.push(getRangeValue(second, index));
          return tupleOf(elements, elements.length);
        });
      case "Seq": {
        const base = operand(0);
        const member = memberTest(base);
        return {
          ...leaf(() => bail("enumerated Seq(S)"), base.footprint, false),
          infinite: "Seq",
          member: (element: number) => {
            if (kindOf(element) !== KIND_TUPLE) return false;
            for (let index = 0; index < sizeOf(element); index++)
              if (!member(getRangeValue(element, index))) return false;
            return true;
          },
        } as LazySet;
      }
      case "Assert": {
        // Assert(P, message) is TRUE when P holds. When it doesn't, TLC fails with the message,
        // which the interpreter reports.
        const condition = compileBoolean(args[0], context);
        const conditionEvaluate = condition.evaluate;
        return {
          ...leaf(
            () => (conditionEvaluate() === TRUE ? TRUE : bail("an assertion failed")),
            condition.footprint,
          ),
          isBoolean: true,
        };
      }
      case "SelectSeq": {
        if (!isOperatorArgument(args[1], context)) return undefined;
        const sequence = operand(0);
        const test = compileApplier(args[1], context);
        const sequenceEvaluate = sequence.evaluate;
        const element = [0];
        return {
          evaluate: () => {
            const tuple = expectSequence(sequenceEvaluate());
            const kept: number[] = [];
            for (let index = 0; index < sizeOf(tuple); index++) {
              element[0] = getRangeValue(tuple, index);
              const holds = test.apply(element);
              if (holds === TRUE) kept.push(element[0]);
              else if (holds !== FALSE) bail("a SelectSeq test that isn't a boolean");
            }
            return kept.length === sizeOf(tuple) ? tuple : tupleOf(kept, kept.length);
          },
          footprint: mergeFootprints(sequence.footprint, test.footprint),
          isCostly: true,
          isNormalized: true,
        };
      }
      case "Cardinality":
        return unary(operand(0), (set) => int(sizeOf(expectSet(set))));
      case "IsFiniteSet":
        return undefined;
      case ":>":
        return binary(operand(0), operand(1), (key, value) => functionOfSorted([key], [value], 1));
      case "@@":
        return binary(
          operand(0),
          operand(1),
          (left, right) => {
            if (!isFunctionKind(kindOf(left)) || !isFunctionKind(kindOf(right)))
              return bail("@@ of non-functions");
            const keys: number[] = [];
            const values: number[] = [];
            for (let index = 0; index < sizeOf(left); index++) {
              keys.push(getKey(left, index));
              values.push(getRangeValue(left, index));
            }
            for (let index = 0; index < sizeOf(right); index++) {
              const key = getKey(right, index);
              if (findKey(left, key) !== -1) continue;
              keys.push(key);
              values.push(getRangeValue(right, index));
            }
            return functionOf(keys, values);
          },
          true,
        );
      default:
        return undefined;
    }
  };

  const expectSequence = (id: number) =>
    kindOf(id) === KIND_TUPLE ? id : bail("expected a sequence");

  const interval = (low: number, high: number) => {
    if (high < low) return EMPTY_SET;
    if (high - low > 1e7) return bail("an interval too large to build");
    const elements: number[] = new Array(high - low + 1);
    for (let value = low; value <= high; value++) elements[value - low] = int(value);
    return setOfSorted(elements, elements.length);
  };

  const powerSet = (set: number) => {
    const size = sizeOf(set);
    if (size > 20) return bail("a power set too large to build");
    const subsets: number[] = [];
    for (let mask = 0; mask < 1 << size; mask++) {
      const elements: number[] = [];
      for (let index = 0; index < size; index++)
        if (mask & (1 << index)) elements.push(elementAt(set, index));
      subsets.push(setOfSorted(elements, elements.length));
    }
    return setOf(subsets);
  };

  // An operator the engine doesn't implement runs in the reference interpreter, on values converted
  // there and back, and is cached like any other computation.
  // Whether an argument names or writes an operator, such as Test in SelectSeq(s, Test).
  const isOperatorArgument = (argument: Expression, context: Context) => {
    if (argument.kind === "Lambda" || argument.kind === "OperatorReference") return true;
    if (argument.kind !== "Identifier") return false;
    const local = lookup(context.scope, argument.name);
    if (local) return local.kind === "operator";
    const definition = getDefinition(argument.name, environment);
    if (definition) return definition.kind === "Operator" && definition.params.length > 0;
    const builtin = environment.builtins.get(
      environment.substitutions.get(argument.name) ?? argument.name,
    );
    return builtin !== undefined && builtin.arity > 0;
  };

  // An operator argument compiled once, with its parameters bound to slots, to apply to ids.
  const compileApplier = (argument: Expression, context: Context) => {
    const operator = resolveOperatorArgument(argument, context);
    if (operator.params.some((param) => param.arity > 0)) {
      return unsupported("an operator argument that takes an operator");
    }
    const slots = operator.params.map(() => allocateSlot());
    let scope = operator.context.scope;
    operator.params.forEach((param, index) => {
      scope = bind(scope, param.name, { kind: "slot", slot: slots[index] });
    });
    const body = compile(operator.body, {
      ...operator.context,
      scope,
      isPrimed: context.isPrimed || operator.context.isPrimed,
    });
    const evaluate = body.evaluate;
    return {
      arity: slots.length,
      apply: (args: ArrayLike<number>) => {
        const saved = slots.map((slot) => LOC[slot]);
        for (let index = 0; index < slots.length; index++) LOC[slots[index]] = args[index];
        try {
          return evaluate();
        } finally {
          for (let index = 0; index < slots.length; index++) LOC[slots[index]] = saved[index];
        }
      },
      footprint: withoutSlots(body.footprint, slots),
    };
  };

  const compileBridgedBuiltin = (
    name: string,
    builtin: Builtin,
    args: Expression[],
    context: Context,
  ): Compiled => {
    const compiledArgs = args.map((argument) =>
      isOperatorArgument(argument, context)
        ? { applier: compileApplier(argument, context) }
        : { value: compile(argument, context) },
    );
    const footprint = mergeFootprints(
      ...compiledArgs.map((argument) =>
        argument.value ? argument.value.footprint : argument.applier!.footprint,
      ),
    );
    // The reference implementation calls an operator argument with values, which the engine
    // converts to ids, applies, and converts back.
    const toArgument = (argument: (typeof compiledArgs)[number]): BuiltinArgument => {
      if (argument.value) return toValue(argument.value.evaluate());
      const applier = argument.applier!;
      const operator: OperatorValue = {
        kind: "Operator",
        name,
        arity: applier.arity,
        call: (values) => toValue(applier.apply(values.map(fromValue))),
      };
      return operator;
    };
    return {
      evaluate: () => fromValue(builtin.evaluate(compiledArgs.map(toArgument))),
      footprint,
      isCostly: true,
      isNormalized: false,
    };
  };

  // --- actions ---

  // Resolves an expression that applies or names an operator to its body with the arguments bound,
  // for the action compiler, which walks into operators to find assignments.
  // Tool.getNextStates walks the body of a function it keeps lazy where an action applies it, with
  // the argument bound as Tool.getFcnContext binds it, so each disjunct or witness of the body that
  // holds gives a successor.
  let lazyArgumentCount = 0;
  const resolveLazyApplication = (expression: Expression, context: Context) => {
    if (expression.kind !== "FunctionApplication") return undefined;
    const fn = expression.function;
    let bounds: Bound[];
    let body: Expression;
    let base: Context;
    let isRecursive = false;
    if (fn.kind === "FunctionConstruction") {
      bounds = fn.bounds;
      body = fn.body;
      base = context;
    } else if (fn.kind === "Identifier" && isLocallyResolved(fn)) {
      const binding = lookup(context.scope, fn.name);
      if (binding?.kind === "recursive") {
        bounds = binding.definition.bounds;
        body = binding.definition.body;
        base = { ...context, scope: binding.scope };
        isRecursive = true;
      } else if (binding?.kind === "value" && binding.lazy) {
        bounds = binding.lazy.definition.bounds;
        body = binding.lazy.definition.body;
        base = { ...context, scope: binding.lazy.scope };
      } else {
        return undefined;
      }
    } else {
      return undefined;
    }
    const bound = bounds[0];
    if (bounds.length !== 1 || bound.pattern.kind !== "Name" || expression.args.length !== 1)
      return unsupported("walking a lazy function of several arguments");
    const argument = compile(expression.args[0], context);
    const member = memberTest(compile(bound.set, base));
    const argumentEvaluate = argument.evaluate;
    const name = `$argument${lazyArgumentCount++}`;
    const scope = bind(base.scope, name, {
      kind: "argument",
      expression: expression.args[0],
      context,
      compiled: [],
    });
    const location = expression.location;
    return {
      body: {
        kind: "Exists",
        bounds: [
          {
            pattern: bound.pattern,
            set: {
              kind: "SetEnumeration",
              elements: [{ kind: "Identifier", name, location, resolution: { kind: "Local" } }],
              location,
            },
          },
        ],
        body,
        location,
      } as Expression,
      context: { ...base, scope },
      isInDomain: () => member(argumentEvaluate()),
      functionBody: body,
      functionContext: base,
      isRecursive,
    };
  };

  const resolveAction = (expression: Expression, context: Context): ActionTarget | undefined => {
    if (expression.kind === "Identifier") {
      if (isLocallyResolved(expression)) {
        const binding = lookup(context.scope, expression.name);
        if (binding?.kind === "argument") {
          return {
            body: binding.expression,
            context: { ...binding.context, isPrimed: binding.context.isPrimed || context.isPrimed },
            name: undefined,
          };
        }
        if (binding) return undefined;
      }
      if (
        environment.variableIndex.has(expression.name) ||
        environment.constants.has(expression.name)
      )
        return undefined;
      const definition = getDefinition(expression.name, environment);
      if (definition?.kind === "Operator" && definition.params.length === 0) {
        return {
          body: definition.body,
          context: { scope: undefined, isPrimed: context.isPrimed, isInit: context.isInit },
          name: definition.name,
        };
      }
      return undefined;
    }
    if (expression.kind !== "Apply") return undefined;
    const name = expression.operator;
    if (isLocallyResolved(expression)) {
      const binding = lookup(context.scope, name);
      if (binding?.kind === "operator") {
        const operator = binding.operator;
        if (operator.isRecursive) return undefined;
        return {
          body: operator.body,
          context: bindArguments(operator.params, expression.args, context, {
            ...operator.context,
            isPrimed: context.isPrimed || operator.context.isPrimed,
          }),
          name: operator.name,
        };
      }
      if (binding) return undefined;
    }
    const target = environment.substitutions.get(name) ?? name;
    const definition = environment.definitions.get(target);
    if (definition?.kind === "Operator") {
      if (definition.isRecursive) return undefined;
      return {
        body: definition.body,
        context: bindArguments(definition.params, expression.args, context, {
          scope: undefined,
          isPrimed: context.isPrimed,
          isInit: context.isInit,
        }),
        name: definition.name,
      };
    }
    return undefined;
  };

  // The elements of a set in the order TLC enumerates them where an action quantifies over the set
  // (quantifier) or assigns a variable from it (streamed): the set itself when TLC normalizes it,
  // else a tuple of its elements in the reference interpreter's order, cached like any other value.
  // What a set the engine can't enumerate in TLC's order is, for the reason it hands over.
  const describeSet = (expression: Expression, context: Context): string => {
    if (expression.kind === "Identifier") {
      const binding = isLocallyResolved(expression)
        ? lookup(context.scope, expression.name)
        : undefined;
      if (binding?.kind === "argument") return describeSet(binding.expression, binding.context);
      const definition = binding ? undefined : getDefinition(expression.name, environment);
      if (definition?.kind === "Operator" && definition.params.length === 0)
        return `${expression.name}: ${describeSet(definition.body, ROOT_CONTEXT)}`;
      return expression.name;
    }
    if (expression.kind === "Apply") return expression.operator;
    return expression.kind;
  };

  const compileOrdered = (
    expression: Expression,
    context: Context,
    mode: "quantifier" | "streamed",
  ): Compiled => {
    const set = compile(expression, context);
    if (set.isNormalized) return set;
    const reference = set.reference;
    if (!reference) {
      return unsupported(
        `enumerating a set TLC keeps lazy (${describeSet(expression, context)} at line ${expression.location.line})`,
      );
    }
    const version = environment.runtime.version;
    return cached({
      evaluate: () => {
        const value = reference();
        const elements =
          mode === "streamed"
            ? getStreamedElements(value)
            : getQuantifierElements(value, expression, version);
        const ids: number[] = [];
        if (Array.isArray(elements)) {
          for (const element of elements) ids.push(fromValue(element));
        } else {
          for (let element = elements.low; element <= elements.high; element++)
            ids.push(int(element));
        }
        return tupleOf(ids, ids.length);
      },
      footprint: set.footprint,
      isCostly: true,
      isNormalized: true,
      isOrdered: true,
    } as Compiled);
  };

  // A closure or thunk in the reference may close over the scope that binds it, so a binding whose
  // scope is its own node gets the translated context once that exists.
  const translatedScopes = new WeakMap<EvaluationScope, Context | null>();
  const contextFromScope = (scope: EvaluationScope | undefined): Context | undefined => {
    if (!scope) return ROOT_CONTEXT;
    const known = translatedScopes.get(scope);
    if (known !== undefined) return known ?? undefined;
    translatedScopes.set(scope, null);
    const context = translateScope(scope);
    translatedScopes.set(scope, context ?? null);
    return context;
  };
  const translateScope = (scope: EvaluationScope): Context | undefined => {
    const parent = contextFromScope(scope.parent);
    if (!parent) return undefined;
    const binding = scope.binding;
    const closeOver = (inner: EvaluationScope | undefined, patch: (context: Context) => void) => {
      if (inner === scope) return true;
      const context = contextFromScope(inner);
      if (!context) return false;
      patch(context);
      return true;
    };
    let translated: Binding;
    let patchSelf: ((context: Context) => void) | undefined;
    if (binding.kind === "Value") {
      translated = { kind: "value", compiled: constant(fromValue(binding.value)) };
    } else if (binding.kind === "Thunk") {
      const argument = {
        kind: "argument" as const,
        expression: binding.expression,
        context: ROOT_CONTEXT,
        compiled: [],
      };
      const patch = (context: Context) => {
        argument.context = context;
      };
      if (!closeOver(binding.scope, patch)) return undefined;
      if (binding.scope === scope) patchSelf = patch;
      translated = argument;
    } else if (binding.operator.kind === "Closure") {
      const closure = binding.operator;
      const operator: OperatorBinding = {
        name: closure.name,
        params: closure.params,
        body: closure.body,
        context: ROOT_CONTEXT,
      };
      const patch = (context: Context) => {
        operator.context = context;
      };
      if (!closeOver(closure.scope, patch)) return undefined;
      if (closure.scope === scope) patchSelf = patch;
      translated = { kind: "operator", operator };
    } else {
      return undefined;
    }
    const context = { ...parent, scope: bind(parent.scope, scope.name, translated) };
    patchSelf?.(context);
    return context;
  };

  const bindValueSlot = (context: Context, name: string) => {
    const slot = allocateSlot();
    return {
      context: { ...context, scope: bind(context.scope, name, { kind: "slot", slot }) },
      slot,
    };
  };

  return {
    compile,
    compileOperatorBody: (definition, args, context) => ({
      body: definition.body,
      context: bindArguments(definition.params, args, context, {
        scope: undefined,
        isPrimed: context.isPrimed,
        isInit: context.isInit,
      }),
    }),
    resolveAction,
    resolveLazyApplication,
    compileOrdered,
    bindLet: bindLetDefinitions,
    bindValue: bindValueSlot,
    contextFromScope,
    setEnabledCompiler: (compileTest) => {
      compileEnabledTest = compileTest;
    },
    environment,
    variableCount,
  };
};

// Whether a compiled enumeration yields a tuple of elements in order rather than a set.
export const isOrderedEnumeration = (compiled: Compiled) =>
  (compiled as { isOrdered?: boolean }).isOrdered === true;

export const memberTestFor = (compiled: Compiled): ((element: number) => boolean) | undefined =>
  (compiled as { member?: (element: number) => boolean }).member;

export const getInfiniteName = (compiled: Compiled): string | undefined =>
  (compiled as { infinite?: string }).infinite;

export type { Context as CompileContext, Scope as CompileScope };
export const isSetId = (id: number) => kindOf(id) === KIND_SET;
export const isBoolId = (id: number) => kindOf(id) === KIND_BOOL;

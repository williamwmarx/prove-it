// The engine IR: one binary blob that holds what the engine reads of a model, so that the native
// engine, which reads no AST or Environment, can compile and check it. native/DESIGN.md (1.3) sets
// out what it holds, and native/crates/tla-ir decodes it and encodes it again byte for byte.
//
// The blob is little-endian 32-bit words. A header gives the magic, IR_VERSION, the number of
// words and the number of bytes of UTF-8 text after them. The words hold, in order:
// - the texts: how many TLC ranks, how many there are, and where each ends in the text, in UTF-16
//   code units. Text i below the ranked count is the string of rank i in createTlcOrder's order.
//   The texts themselves are one UTF-8 string after the words;
// - the variables, by name, in the engine's order, and TLC's order of them;
// - the builtins the model names: name, arity and flags;
// - the constants it names, each with its value, or -1 for one transfer.ts can't encode;
// - the scopes of instances it reads, which bind a name to a value, an expression or an operator;
// - the values: those of the constants and scopes, in transfer.ts's encoding, whose strings are
//   indices into the texts;
// - the model: Init, Next, TLC's actions, the configuration's names, the properties (each checked as
//   an invariant with the name TLC reports it by), the VIEW, the symmetry group, the settings, the
//   liveness checker's atoms, each action atom with the position of the ENABLED atom of its
//   fairness, or -1, and the formula the checker solves, as its number of words and its terms in
//   prefix order, each atom by its position among the atoms, or past them for one the checker asks
//   nothing of, then the properties, each its name and its formula the same way, then what TLC
//   evaluates when it starts: the substitutes it checks, each its constant's name and its
//   definition; the constant definitions with effects, in the order TLC evaluates them; and the
//   assumptions, each its expression and the name TLC reports it by. Their definitions and nodes
//   are written after the model's other roots, in that order. The settings hold TLC's seed, from
//   which the engine draws what the startup and the initial states draw;
// - the definitions the model reaches, as the offsets of their records among the nodes;
// - the nodes: expressions and definitions in prefix order, each its tag, its line and column, its
//   source range (the module's name, or -1 for none, then the start's and the end's line and
//   column, which TLC's messages print), then its fields and children. A node met again is a
//   reference to its first offset. A junction is flagged when it is a bulleted list, and its fields
//   are where each prefix of an infix chain such as A /\ B /\ C ends, which SANY parses as nested
//   junctions whose ranges TLC prints.

import type {
  Bound,
  BoundPattern,
  Definition,
  Expression,
  OperatorParam,
  SourceRange,
} from "../ast";
import type { ModelConfig } from "../config";
import { hasRepeatedEffect, isImpureDefinition } from "../dependencies";
import { type Environment, type EvaluationScope, getDefinition } from "../evaluate";
import { ACTION_LEVEL } from "../levels";
import { getLevel } from "../liveness";
import type { LiveExpression } from "../tableau";
import type { TlcVersion } from "../tlc/version";
import { createStateEncoder } from "../transfer";
import { findStringRank, getRankedStringCount, getStringOrder, type Value } from "../values";
import type { EngineProperties, EngineSpec } from "./context";
import type { NamedPermutation } from "./symmetry";

// The version of the layout below, which the decoder checks. Any change to it changes this.
export const IR_VERSION = 11;

// "PIIR" read as a little-endian word.
const MAGIC = 0x52494950;

// The node tags, by position. A tag word holds the tag in its low byte and the node's flags above.
const NODE_KINDS = [
  "Number",
  "Decimal",
  "String",
  "Identifier",
  "Apply",
  "OperatorReference",
  "Lambda",
  "And",
  "Or",
  "Prime",
  "Unchanged",
  "Enabled",
  "If",
  "Case",
  "Let",
  "Forall",
  "Exists",
  "UnboundedQuantifier",
  "Choose",
  "SetEnumeration",
  "SetFilter",
  "SetMap",
  "Tuple",
  "FunctionConstruction",
  "FunctionSet",
  "Record",
  "RecordSet",
  "Except",
  "ExceptAt",
  "FunctionApplication",
  "Bracket",
  "FieldAccess",
  "Product",
  "Always",
  "Eventually",
  "BoxAction",
  "AngleAction",
  "WeakFairness",
  "StrongFairness",
  "Label",
  "Subexpression",
] as const;
const TAGS: Record<string, number> = Object.fromEntries(NODE_KINDS.map((kind, tag) => [kind, tag]));
const REFERENCE_TAG = 64;
const DEFINITION_TAG = 65;

// Flags of a node's tag word.
const LOCAL_FLAG = 1 << 8;
const WIDE_NUMBER_FLAG = 1 << 8;
const FORALL_FLAG = 1 << 8;
const RECURSIVE_FLAG = 1 << 8;
const HAS_OTHER_FLAG = 1 << 8;
const BULLETED_FLAG = 1 << 8;

// Flags of a definition record.
const DEFINITION_RECURSIVE = 1 << 8;
const DEFINITION_LOCAL = 1 << 9;
const DEFINITION_SELF_REFERENTIAL = 1 << 10;
const DEFINITION_REPEATED_EFFECT = 1 << 11;
const DEFINITION_SUBSTITUTED = 1 << 12;

// What a name refers to outside any binding of it, in the order the compiler looks.
const NO_RESOLUTION = 0;
const VARIABLE_RESOLUTION = 1;
const CONSTANT_RESOLUTION = 2;
const DEFINITION_RESOLUTION = 3;
const BUILTIN_RESOLUTION = 4;
const RESOLUTION_BITS = 3;
const RESOLUTION_MASK = (1 << RESOLUTION_BITS) - 1;

const BUILTIN_STATE_LEVEL = 1;
const BUILTIN_LEVEL_CONSTANT = 2;
const BUILTIN_LAZY = 4;

const SCOPE_VALUE = 0;
const SCOPE_THUNK = 1;
const SCOPE_CLOSURE = 2;
// A binding to something else, such as a builtin, which the engine can't translate.
const SCOPE_OPAQUE = 3;

const ATOM_STATE = 0;
const ATOM_ACTION = 1;
const ATOM_ENABLED = 2;
// The actions an ENABLED atom splits into: none known, or all of them, else their count.
const ENABLED_UNKNOWN = -2;
const ENABLED_ALL = -1;
const LIVE_FALSE = 0;
const LIVE_TRUE = 1;
const LIVE_STATE = 2;
const LIVE_ENABLED = 3;
const LIVE_ACTION = 4;
const LIVE_TAGS = { Not: 5, Always: 6, Eventually: 7, Next: 8, And: 9, Or: 10 };

// A liveness atom the tableau asks about, and for an ENABLED one the positions of TLC's actions it
// splits into, as check.ts finds them.
export interface IrAtom {
  atom: LiveExpression;
  actions: readonly number[] | "all" | undefined;
}

export interface TraceAction {
  expression: Expression;
  scope: EvaluationScope | undefined;
  label: string;
}

export interface IrInput {
  config: ModelConfig;
  environment: Environment;
  spec: EngineSpec;
  // TLC's actions, with the label a trace gives each step one takes. The search takes its steps
  // through them only when spec.actions is given.
  traceActions: TraceAction[];
  isWarningEnabled: boolean;
  tlcOrder: number[];
  properties: EngineProperties;
  symmetry: NamedPermutation[] | undefined;
  isRecordingGraph: boolean;
  version: TlcVersion | undefined;
  atoms: IrAtom[];
  // The fairness and the negated properties as the liveness checker joins them, and each property.
  liveFormula: LiveExpression | undefined;
  liveProperties: { name: string; formula: LiveExpression }[];
  startup: IrStartup;
}

// What TLC evaluates when it starts, which the engine evaluates before its search.
export interface IrStartup {
  // The substitutes TLC evaluates and rejects if they fail, by the declared constant's name.
  substitutes: { name: string; definition: Definition }[];
  // The constant definitions with effects, in the order TLC evaluates them.
  definitions: Definition[];
  // The assumptions that aren't axioms, each with the name TLC reports it by.
  assumptions: { expression: Expression; name: string }[];
}

export type IrOutcome = { ir: Uint8Array } | { reason: string };

interface Words {
  data: Int32Array;
  length: number;
}

const createWords = (): Words => ({ data: new Int32Array(1024), length: 0 });

const reserve = (words: Words, count: number) => {
  if (words.length + count <= words.data.length) return;
  const data = new Int32Array(Math.max(words.data.length * 2, words.length + count));
  data.set(words.data);
  words.data = data;
};

const push = (words: Words, word: number) => {
  if (words.length === words.data.length) reserve(words, 1);
  words.data[words.length++] = word;
};

const pushAll = (words: Words, from: ArrayLike<number>, count = from.length) => {
  reserve(words, count);
  for (let index = 0; index < count; index++) words.data[words.length++] = from[index];
};

const pushWords = (words: Words, from: Words) => {
  reserve(words, from.length);
  words.data.set(from.data.subarray(0, from.length), words.length);
  words.length += from.length;
};

// The texts in UTF-8, in one call, and where each ends in UTF-16 code units, or undefined if one
// has a lone surrogate, which UTF-8 can't hold.
const encodeTexts = (ranked: readonly string[], rankedCount: number, extra: string[]) => {
  const joined = ranked.slice(0, rankedCount).join("") + extra.join("");
  if (!joined.isWellFormed()) return undefined;
  const ends = new Int32Array(rankedCount + extra.length);
  let end = 0;
  for (let index = 0; index < rankedCount; index++) ends[index] = end += ranked[index].length;
  for (let index = 0; index < extra.length; index++) {
    ends[rankedCount + index] = end += extra[index].length;
  }
  return { bytes: new TextEncoder().encode(joined), ends };
};

const isWide = (value: number) => (value | 0) !== value;

export const lowerToIr = (input: IrInput): IrOutcome => {
  const environment = input.environment;
  const config = input.config;
  const rankedCount = getRankedStringCount();
  const rankedTexts = getStringOrder();
  const extraTexts: string[] = [];
  const extraIndices = new Map<string, number>();
  const getText = (text: string) => {
    const rank = findStringRank(text);
    if (rank !== undefined && rank < rankedCount) return rank;
    const known = extraIndices.get(text);
    if (known !== undefined) return known;
    const index = rankedCount + extraTexts.length;
    extraTexts.push(text);
    extraIndices.set(text, index);
    return index;
  };

  const nodes = createWords();
  const nodeOffsets = new Map<Expression, number>();
  const definitionIndices = new Map<Definition, number>();
  const definitionQueue: Definition[] = [];
  const definitionOffsets: number[] = [];
  const scopeIndices = new Map<EvaluationScope, number>();
  const scopeQueue: EvaluationScope[] = [];
  const scopes = createWords();
  const constantIndices = new Map<string, number>();
  const constants = createWords();
  const builtinIndices = new Map<string, number>();
  const builtins = createWords();
  const valueEncoder = createStateEncoder();
  const valueCount = { encoded: 0 };

  const getValue = (value: Value) => (valueEncoder.encode([value]) ? valueCount.encoded++ : -1);

  const getDefinitionIndex = (definition: Definition) => {
    const known = definitionIndices.get(definition);
    if (known !== undefined) return known;
    const index = definitionQueue.length;
    definitionIndices.set(definition, index);
    definitionQueue.push(definition);
    return index;
  };

  const getScopeIndex = (scope: EvaluationScope | undefined) => {
    if (scope === undefined) return -1;
    const known = scopeIndices.get(scope);
    if (known !== undefined) return known;
    const index = scopeQueue.length;
    scopeIndices.set(scope, index);
    scopeQueue.push(scope);
    return index;
  };

  const getConstantIndex = (name: string, value: Value) => {
    const known = constantIndices.get(name);
    if (known !== undefined) return known;
    const index = constantIndices.size;
    constantIndices.set(name, index);
    push(constants, getText(name));
    push(constants, getValue(value));
    return index;
  };

  const getBuiltinIndex = (name: string) => {
    const known = builtinIndices.get(name);
    if (known !== undefined) return known;
    const builtin = environment.builtins.get(name);
    if (builtin === undefined) return -1;
    const index = builtinIndices.size;
    builtinIndices.set(name, index);
    push(builtins, getText(name));
    push(builtins, builtin.arity);
    push(
      builtins,
      (builtin.isStateLevel ? BUILTIN_STATE_LEVEL : 0) |
        (builtin.isLevelConstant ? BUILTIN_LEVEL_CONSTANT : 0) |
        (builtin.isLazy ? BUILTIN_LAZY : 0),
    );
    return index;
  };

  // What compileIdentifier finds for a name nothing binds: a variable, a constant, a definition,
  // or a builtin, through the model's substitutions. A resolution packs its kind in the low bits.
  const resolveName = (name: string) => {
    const variable = environment.variableIndex.get(name);
    if (variable !== undefined) return VARIABLE_RESOLUTION | (variable << RESOLUTION_BITS);
    const constant = environment.constants.get(name);
    return constant !== undefined
      ? CONSTANT_RESOLUTION | (getConstantIndex(name, constant) << RESOLUTION_BITS)
      : resolveOperator(name);
  };

  // What compileApply finds for an operator nothing binds: a definition, else a builtin.
  const resolveOperator = (name: string) => {
    const target = environment.substitutions.get(name) ?? name;
    const definition = environment.definitions.get(target);
    if (definition) {
      return DEFINITION_RESOLUTION | (getDefinitionIndex(definition) << RESOLUTION_BITS);
    }
    const builtin = getBuiltinIndex(target);
    return builtin === -1 ? NO_RESOLUTION : BUILTIN_RESOLUTION | (builtin << RESOLUTION_BITS);
  };

  // Each name's text and resolution, as a name and as an operator, since names recur.
  const names = new Map<string, number[]>();
  const operators = new Map<string, number[]>();
  const writeName = (name: string, isOperator: boolean) => {
    const cache = isOperator ? operators : names;
    const known = cache.get(name);
    const entry = known ?? [getText(name), isOperator ? resolveOperator(name) : resolveName(name)];
    if (!known) cache.set(name, entry);
    reserve(nodes, 3);
    nodes.data[nodes.length++] = entry[0];
    nodes.data[nodes.length++] = entry[1] & RESOLUTION_MASK;
    nodes.data[nodes.length++] = entry[1] >> RESOLUTION_BITS;
  };

  const writeTexts = (texts: readonly string[]) => {
    push(nodes, texts.length);
    for (let index = 0; index < texts.length; index++) push(nodes, getText(texts[index]));
  };

  const writeNodes = (expressions: readonly Expression[]) => {
    push(nodes, expressions.length);
    for (let index = 0; index < expressions.length; index++) writeNode(expressions[index]);
  };

  const writePattern = (pattern: BoundPattern) => {
    if (pattern.kind === "Name") {
      push(nodes, 0);
      push(nodes, getText(pattern.name));
      return;
    }
    push(nodes, 1);
    writeTexts(pattern.names);
  };

  const writeBounds = (bounds: readonly Bound[]) => {
    push(nodes, bounds.length);
    for (let index = 0; index < bounds.length; index++) {
      const bound = bounds[index];
      writePattern(bound.pattern);
      writeNode(bound.set);
    }
  };

  const writeParams = (params: readonly OperatorParam[]) => {
    push(nodes, params.length);
    for (let index = 0; index < params.length; index++) {
      const param = params[index];
      push(nodes, getText(param.name));
      push(nodes, param.arity);
    }
  };

  const writeRange = (range: SourceRange | undefined) => {
    if (!range) {
      for (const word of [-1, 0, 0, 0, 0]) push(nodes, word);
      return;
    }
    push(nodes, getText(range.module));
    push(nodes, range.start.line);
    push(nodes, range.start.column);
    push(nodes, range.end.line);
    push(nodes, range.end.column);
  };

  const writeDefinition = (definition: Definition) => {
    const isRepeated = isImpureDefinition(definition, environment, "repeated");
    push(
      nodes,
      DEFINITION_TAG |
        (definition.isRecursive ? DEFINITION_RECURSIVE : 0) |
        (definition.isLocal ? DEFINITION_LOCAL : 0) |
        (definition.kind === "Function" && definition.isSelfReferential
          ? DEFINITION_SELF_REFERENTIAL
          : 0) |
        (isRepeated ? DEFINITION_REPEATED_EFFECT : 0) |
        (environment.substitutedDefinitions.has(definition) ? DEFINITION_SUBSTITUTED : 0),
    );
    push(nodes, definition.location.line);
    push(nodes, definition.location.column);
    writeRange(definition.location.range);
    push(nodes, getText(definition.name));
    if (definition.kind === "Operator") {
      push(nodes, 0);
      writeParams(definition.params);
    } else {
      push(nodes, 1);
      writeBounds(definition.bounds);
    }
    writeNode(definition.body);
  };

  const writeNode = (expression: Expression): void => {
    const known = nodeOffsets.get(expression);
    if (known !== undefined) {
      push(nodes, REFERENCE_TAG);
      push(nodes, known);
      return;
    }
    const at = nodes.length;
    nodeOffsets.set(expression, at);
    reserve(nodes, 3);
    const location = expression.location;
    nodes.data[at] = TAGS[expression.kind];
    nodes.data[at + 1] = location.line;
    nodes.data[at + 2] = location.column;
    nodes.length = at + 3;
    writeRange(location.range);
    switch (expression.kind) {
      case "Number": {
        if (isWide(expression.value)) {
          nodes.data[at] |= WIDE_NUMBER_FLAG;
          push(nodes, getText(expression.text ?? String(expression.value)));
        } else push(nodes, expression.value);
        return;
      }
      case "Decimal":
        push(nodes, getText(expression.text));
        return;
      case "String":
        push(nodes, getText(expression.value));
        return;
      case "Identifier":
        if (expression.resolution?.kind === "Local") nodes.data[at] |= LOCAL_FLAG;
        writeName(expression.name, false);
        return;
      case "Apply":
        if (expression.resolution?.kind === "Local") nodes.data[at] |= LOCAL_FLAG;
        writeName(expression.operator, true);
        writeNodes(expression.args);
        return;
      case "OperatorReference":
        writeName(expression.operator, true);
        return;
      case "Lambda":
        writeTexts(expression.params);
        writeNode(expression.body);
        return;
      case "And":
      case "Or":
        if (expression.isBulleted) nodes.data[at] |= BULLETED_FLAG;
        push(nodes, expression.prefixEnds?.length ?? 0);
        for (const end of expression.prefixEnds ?? []) {
          push(nodes, end.line);
          push(nodes, end.column);
        }
        writeNodes(expression.operands);
        return;
      case "Prime":
      case "Unchanged":
      case "Enabled":
      case "Always":
      case "Eventually":
        writeNode(expression.expression);
        return;
      case "If":
        writeNode(expression.condition);
        writeNode(expression.consequent);
        writeNode(expression.alternative);
        return;
      case "Case":
        if (expression.other) nodes.data[at] |= HAS_OTHER_FLAG;
        push(nodes, expression.arms.length);
        for (let index = 0; index < expression.arms.length; index++) {
          const arm = expression.arms[index];
          writeNode(arm.condition);
          writeNode(arm.body);
        }
        if (expression.other) writeNode(expression.other);
        return;
      case "Let":
        // The compiler refuses an INSTANCE in a LET, so only how many there are is kept.
        push(nodes, expression.instances?.length ?? 0);
        push(nodes, expression.definitions.length);
        for (let index = 0; index < expression.definitions.length; index++) {
          writeDefinition(expression.definitions[index]);
        }
        writeNode(expression.body);
        return;
      case "Forall":
      case "Exists":
        writeBounds(expression.bounds);
        writeNode(expression.body);
        return;
      case "UnboundedQuantifier":
        if (expression.quantifier === "Forall") nodes.data[at] |= FORALL_FLAG;
        writeTexts(expression.names);
        writeNode(expression.body);
        return;
      case "Choose":
        writePattern(expression.pattern);
        push(nodes, expression.set ? 1 : 0);
        if (expression.set) writeNode(expression.set);
        writeNode(expression.body);
        return;
      case "SetEnumeration":
      case "Tuple":
        writeNodes(expression.elements);
        return;
      case "SetFilter":
        writeBounds([expression.bound]);
        writeNode(expression.predicate);
        return;
      case "SetMap":
        writeNode(expression.expression);
        writeBounds(expression.bounds);
        return;
      case "FunctionConstruction":
        if (expression.isRecursive) nodes.data[at] |= RECURSIVE_FLAG;
        writeBounds(expression.bounds);
        writeNode(expression.body);
        return;
      case "FunctionSet":
        writeNode(expression.domain);
        writeNode(expression.range);
        return;
      case "Record":
      case "RecordSet":
        push(nodes, expression.fields.length);
        for (let index = 0; index < expression.fields.length; index++) {
          const field = expression.fields[index];
          push(nodes, getText(field.name));
          writeNode(field.value);
        }
        return;
      case "Except":
        writeNode(expression.function);
        push(nodes, expression.updates.length);
        for (let index = 0; index < expression.updates.length; index++) {
          const update = expression.updates[index];
          push(nodes, update.path.length);
          for (const step of update.path) {
            if (step.kind === "Field") {
              push(nodes, 0);
              push(nodes, getText(step.name));
            } else {
              push(nodes, 1);
              writeNodes(step.args);
            }
          }
          writeNode(update.value);
        }
        return;
      case "ExceptAt":
        return;
      case "FunctionApplication":
        writeNode(expression.function);
        writeNodes(expression.args);
        return;
      case "Bracket":
        writeNodes(expression.args);
        return;
      case "FieldAccess":
        writeNode(expression.record);
        push(nodes, getText(expression.field));
        return;
      case "Product":
        writeNodes(expression.factors);
        return;
      case "BoxAction":
      case "AngleAction":
        writeNode(expression.action);
        writeNode(expression.subscript);
        return;
      case "WeakFairness":
      case "StrongFairness":
        writeNode(expression.subscript);
        writeNode(expression.action);
        push(nodes, expression.enabled ? 1 : 0);
        if (expression.enabled) writeNode(expression.enabled);
        return;
      case "Label":
        push(nodes, getText(expression.name));
        writeTexts(expression.params);
        writeNode(expression.body);
        return;
      case "Subexpression":
        push(nodes, expression.selectors.length);
        for (const selector of expression.selectors) {
          switch (selector.kind) {
            case "Name":
              push(nodes, 0);
              push(nodes, getText(selector.name));
              writeNodes(selector.args);
              break;
            case "Operand":
              push(nodes, 1);
              push(
                nodes,
                selector.operand === "<<" ? -1 : selector.operand === ">>" ? -2 : selector.operand,
              );
              break;
            case "Bound":
              push(nodes, 2);
              writeNodes(selector.args);
              break;
            case "At":
              push(nodes, 3);
              break;
            case "Colon":
              push(nodes, 4);
              break;
          }
        }
        return;
    }
  };

  // Writes an expression something outside the nodes refers to, unless it is written already, and
  // returns its offset.
  const writeRoot = (expression: Expression) => {
    const known = nodeOffsets.get(expression);
    if (known !== undefined) return known;
    const offset = nodes.length;
    writeNode(expression);
    return offset;
  };

  const writeScope = (scope: EvaluationScope) => {
    push(scopes, getScopeIndex(scope.parent));
    push(scopes, getText(scope.name));
    const binding = scope.binding;
    if (binding.kind === "Value") {
      push(scopes, SCOPE_VALUE);
      push(scopes, getValue(binding.value));
    } else if (binding.kind === "Thunk") {
      push(scopes, SCOPE_THUNK);
      push(scopes, writeRoot(binding.expression));
      push(scopes, getScopeIndex(binding.scope));
    } else if (binding.operator.kind === "Closure") {
      const closure = binding.operator;
      push(scopes, SCOPE_CLOSURE);
      push(scopes, getText(closure.name));
      push(scopes, closure.params.length);
      for (const param of closure.params) {
        push(scopes, getText(param.name));
        push(scopes, param.arity);
      }
      push(scopes, writeRoot(closure.body));
      push(scopes, getScopeIndex(closure.scope));
    } else push(scopes, SCOPE_OPAQUE);
  };

  // --- the model ---

  const model = createWords();
  // A name the configuration gives, and the definition it names, or -1 for none.
  const writeConfigNames = (names: readonly string[], isPrinted = false) => {
    push(model, names.length);
    for (const name of names) {
      const definition = getDefinition(name, environment);
      push(model, getText(name));
      push(model, definition ? getDefinitionIndex(definition) : -1);
      if (isPrinted) push(model, hasRepeatedEffectOfName(name) ? 1 : 0);
    }
  };
  const hasRepeatedEffectOfName = (name: string) =>
    hasRepeatedEffect({ kind: "Identifier", name, location: { line: 0, column: 0 } }, environment);
  const writeRoots = (expressions: readonly Expression[]) => {
    push(model, expressions.length);
    for (const expression of expressions) push(model, writeRoot(expression));
  };

  const spec = input.spec;
  push(model, writeRoot(spec.init));
  push(model, writeRoot(spec.next));
  push(model, getScopeIndex(spec.scope));
  push(model, input.traceActions.length);
  for (const action of input.traceActions) {
    push(model, writeRoot(action.expression));
    push(model, getScopeIndex(action.scope));
    push(model, getText(action.label));
  }
  push(model, spec.actions ? 1 : 0);
  writeConfigNames(config.invariants, true);
  push(model, input.properties.invariants.length);
  input.properties.invariants.forEach((invariant, index) => {
    push(model, writeRoot(invariant));
    push(model, hasRepeatedEffect(invariant, environment) ? 1 : 0);
    push(model, getText(input.properties.invariantNames[index]));
  });
  writeConfigNames(config.constraints);
  writeConfigNames(config.actionConstraints);
  // Each _POSSIBLE predicate, and whether it is of a step rather than a state.
  push(model, config.possible.length);
  for (const name of config.possible) {
    const definition = getDefinition(name, environment);
    push(model, getText(name));
    push(model, definition ? getDefinitionIndex(definition) : -1);
    const identifier = { kind: "Identifier" as const, name, location: { line: 0, column: 0 } };
    push(model, getLevel(identifier, undefined, environment) >= ACTION_LEVEL ? 1 : 0);
  }
  push(model, input.properties.actionProperties.length);
  for (const property of input.properties.actionProperties) {
    push(model, writeRoot(property.action));
    push(model, writeRoot(property.subscript));
  }
  writeRoots(input.properties.initialPredicates);
  writeConfigNames(config.view === undefined ? [] : [config.view]);
  const symmetry = input.symmetry;
  push(model, symmetry ? symmetry.length : -1);
  for (const permutation of symmetry ?? []) {
    push(model, permutation.length);
    for (const [from, to] of permutation) {
      push(model, getText(from));
      push(model, getText(to));
    }
  }
  push(model, config.checkDeadlock ? 1 : 0);
  push(model, input.isWarningEnabled ? 1 : 0);
  push(model, input.isRecordingGraph ? 1 : 0);
  push(model, input.version === undefined ? -1 : getText(input.version));
  // The seed TLC seeds its generator with before it starts, and reseeds it with for each state it
  // expands.
  const seed = BigInt.asUintN(64, environment.runtime.seed);
  push(model, Number(BigInt.asIntN(32, seed)));
  push(model, Number(BigInt.asIntN(32, seed >> 32n)));
  push(model, input.atoms.length);
  const atomPositions = new Map(input.atoms.map((entry, position) => [entry.atom, position]));
  for (const entry of input.atoms) {
    const atom = entry.atom;
    if (atom.kind === "State") {
      push(model, ATOM_STATE);
      push(model, writeRoot(atom.expression));
      push(model, -1);
    } else if (atom.kind === "Action") {
      push(model, ATOM_ACTION);
      push(model, writeRoot(atom.expression));
      push(model, atom.unchanged ? writeRoot(atom.unchanged) : -1);
    } else if (atom.kind === "Enabled") {
      push(model, ATOM_ENABLED);
      push(model, writeRoot(atom.step));
      push(model, -1);
    } else return { reason: `a liveness atom of kind ${atom.kind}` };
    push(model, getScopeIndex(atom.scope));
    const positions = entry.actions;
    push(
      model,
      positions === undefined
        ? ENABLED_UNKNOWN
        : positions === "all"
          ? ENABLED_ALL
          : positions.length,
    );
    if (Array.isArray(positions)) for (const position of positions) push(model, position);
    if (atom.kind === "Action") {
      push(model, atom.enabled ? (atomPositions.get(atom.enabled) ?? -1) : -1);
    }
  }
  const getAtomPosition = (atom: LiveExpression) => {
    const known = atomPositions.get(atom);
    if (known !== undefined) return known;
    atomPositions.set(atom, atomPositions.size);
    return atomPositions.size - 1;
  };
  const live: number[] = [];
  const writeLive = (term: LiveExpression) => {
    switch (term.kind) {
      case "Boolean":
        live.push(term.value ? LIVE_TRUE : LIVE_FALSE);
        return;
      case "State":
        live.push(LIVE_STATE, getAtomPosition(term));
        return;
      case "Enabled":
        live.push(LIVE_ENABLED, getAtomPosition(term));
        return;
      case "Action":
        live.push(
          LIVE_ACTION,
          getAtomPosition(term),
          term.enabled ? getAtomPosition(term.enabled) : -1,
        );
        return;
      case "And":
      case "Or":
        live.push(LIVE_TAGS[term.kind], term.operands.length);
        term.operands.forEach(writeLive);
        return;
      default:
        live.push(LIVE_TAGS[term.kind]);
        writeLive(term.body);
    }
  };
  const pushLive = (formula: LiveExpression | undefined) => {
    live.length = 0;
    if (formula) writeLive(formula);
    push(model, live.length);
    for (const word of live) push(model, word);
  };
  pushLive(input.liveFormula);
  push(model, input.liveProperties.length);
  for (const property of input.liveProperties) {
    push(model, getText(property.name));
    pushLive(property.formula);
  }
  const startup = input.startup;
  push(model, startup.substitutes.length);
  for (const substitute of startup.substitutes) {
    push(model, getText(substitute.name));
    push(model, getDefinitionIndex(substitute.definition));
  }
  push(model, startup.definitions.length);
  for (const definition of startup.definitions) push(model, getDefinitionIndex(definition));
  push(model, startup.assumptions.length);
  for (const assumption of startup.assumptions) {
    push(model, writeRoot(assumption.expression));
    push(model, getText(assumption.name));
  }

  // Definitions and scopes reach more of each, in the order they are first met.
  for (let definition = 0, scope = 0; ;) {
    if (scope < scopeQueue.length) writeScope(scopeQueue[scope++]);
    else if (definition < definitionQueue.length) {
      definitionOffsets.push(nodes.length);
      writeDefinition(definitionQueue[definition++]);
    } else break;
  }

  // --- the blob ---

  const encodedValues = valueEncoder.finish();
  const valueStrings = encodedValues.strings.map(getText);
  const variables = environment.variables.map(getText);
  const texts = encodeTexts(rankedTexts, rankedCount, extraTexts);
  if (!texts) return { reason: "a text with a lone surrogate" };
  const words = createWords();
  reserve(words, 64 + texts.ends.length + model.length + nodes.length + encodedValues.words.length);
  pushAll(words, [MAGIC, IR_VERSION, 0, texts.bytes.length, rankedCount, texts.ends.length]);
  pushAll(words, texts.ends);
  push(words, variables.length);
  pushAll(words, variables);
  push(words, input.tlcOrder.length);
  pushAll(words, input.tlcOrder);
  push(words, builtinIndices.size);
  pushWords(words, builtins);
  push(words, constantIndices.size);
  pushWords(words, constants);
  push(words, scopeQueue.length);
  pushWords(words, scopes);
  push(words, encodedValues.count);
  push(words, valueStrings.length);
  pushAll(words, valueStrings);
  push(words, encodedValues.words.length);
  pushAll(words, encodedValues.words);
  pushWords(words, model);
  push(words, definitionOffsets.length);
  pushAll(words, definitionOffsets);
  push(words, nodes.length);
  pushWords(words, nodes);
  words.data[2] = words.length;
  // The words in the host's byte order, which is little-endian on every platform the addon is
  // built for, then the texts, padded to a whole word.
  const ir = new Uint8Array(words.length * 4 + ((texts.bytes.length + 3) & ~3));
  new Int32Array(ir.buffer, 0, words.length).set(words.data.subarray(0, words.length));
  ir.set(texts.bytes, words.length * 4);
  return { ir };
};

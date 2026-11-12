// The engine IR: one binary blob that holds what the engine reads of a model, so that the native
// engine, which reads no AST or Environment, can compile and check it. native/DESIGN.md (1.3) sets
// out what it holds, and native/crates/tla-ir decodes it and encodes it again byte for byte.
//
// The blob is little-endian 32-bit words. A header gives the magic, IR_VERSION, the number of
// words and the number of bytes of WTF-8 text after them. The words hold, in order:
// - the texts: how many TLC ranks, how many there are, and where each ends in the text, in UTF-16
//   code units. Text i below the ranked count is the string of rank i in createTlcOrder's order.
//   The texts themselves are one WTF-8 string after the words;
// - the variables, by name, in the engine's order, and TLC's order of them;
// - the builtins the model names: name, arity and flags, then for a configuration's table of an
//   operator's values its number of rows, and each row's arguments as a tuple and its value;
// - the constants it names, each with its value, or -1 for one transfer.ts can't encode;
// - the scopes of instances it reads, which bind a name to a value, an expression or an operator;
// - the values: those of the constants and scopes, in transfer.ts's encoding, whose strings are
//   indices into the texts;
// - the model: Init, Next, TLC's actions, the configuration's names, the properties (each checked as
//   an invariant with the name TLC reports it by), the VIEW, the ALIAS, the settings, the liveness
//   checker's atoms, each action atom with the position of the ENABLED atom of its fairness, or -1,
//   and the formula the checker solves, as its number of words and its terms in prefix order, each
//   atom by its position among the atoms, or past them for one the checker asks nothing of, then
//   the properties, each its name and its formula the same way, then the source range of the
//   definition SPECIFICATION names, or -1 and zeros, then what TLC evaluates when it
//   starts: the substitutes it checks, each its constant's name and its definition; the constant
//   definitions with effects, in the order TLC evaluates them; the SYMMETRY definition, or -1, with
//   the sets it permutes, each the name TLC's warning gives it and the set it checks, or -1; and
//   the assumptions, each its expression and the name TLC reports it by. Their definitions and
//   nodes are written after the model's other roots, in that order. The settings hold TLC's seed,
//   from which the engine draws what the startup and the initial states draw;
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
import type { InstanceAction } from "../environment";
import { type Closure, type Environment, type EvaluationScope, getDefinition } from "../evaluate";
import { ACTION_LEVEL } from "../levels";
import { getLevel } from "../liveness";
import type { getConstantPredicates } from "../search";
import type { PermutedSet } from "../symmetry";
import type { LiveExpression } from "../tableau";
import type { TlcVersion } from "../tlc/version";
import { createStateEncoder } from "../transfer";
import {
  createTuple,
  findStringRank,
  getRankedStringCount,
  getStringOrder,
  type Value,
} from "../values";

// The version of the layout below, which the decoder checks. Any change to it changes this.
export const IR_VERSION = 16;

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
const DEFINITION_NORMALIZED = 1 << 13;
const DEFINITION_LITERAL = 1 << 14;

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
const BUILTIN_TABLE = 8;
const BUILTIN_NATURALS_GEQ = 16;
const BUILTIN_NATURALS_METHOD = 32;

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
  // The name and location TLC's Action holds, which TLCExt's CounterExample records.
  name: string;
  range: SourceRange | undefined;
  // The operator TLC split the action from (Action.getOpDef), if any.
  operator: Closure | undefined;
}

// The specification the IR holds, with no next-state relation where the configuration names none.
export interface IrSpec {
  init: Expression;
  next: Expression | undefined;
  // The bindings of the instance the specification comes from, when it names one.
  scope?: EvaluationScope;
  // TLC's actions of the next-state relation, as it splits it, for a search that labels each step
  // with the action that took it.
  actions?: { expression: Expression; scope: EvaluationScope | undefined }[];
}

// The properties the IR holds, each read in the scope of the instance it comes from, if any.
export interface IrProperties {
  invariants: { expression: Expression; scope: EvaluationScope | undefined; name: string }[];
  actionProperties: {
    action: Expression;
    subscript: Expression;
    scope: EvaluationScope | undefined;
    name: string;
  }[];
  initialPredicates: { expression: Expression; scope: EvaluationScope | undefined; name: string }[];
}

export interface IrInput {
  config: ModelConfig;
  environment: Environment;
  spec: IrSpec;
  // TLC's actions, with the label a trace gives each step one takes. The search takes its steps
  // through them only when spec.actions is given.
  traceActions: TraceAction[];
  isWarningEnabled: boolean;
  tlcOrder: number[];
  properties: IrProperties;
  isRecordingGraph: boolean;
  version: TlcVersion | undefined;
  atoms: IrAtom[];
  // The fairness and the negated properties as the liveness checker joins them, and each property.
  liveFormula: LiveExpression | undefined;
  liveProperties: { name: string; formula: LiveExpression }[];
  startup: IrStartup;
  // Where the specification reaches the next-state relation through an INSTANCE with
  // substitutions, the first such INSTANCE (getNextSubstitution).
  nextSubstitution: SourceRange | undefined;
  instanceActions: Map<string, InstanceAction>;
  // TLCGet("spec") as the interpreter computes it, which the IR holds where an expression reads
  // it, as TLC's actions; the front end's model has neither.
  getSpecification: (() => Value) | undefined;
}

// What TLC evaluates when it starts, which the engine evaluates before its search.
export interface IrStartup {
  // The substitutes TLC evaluates and rejects if they fail, by the declared constant's name.
  substitutes: { name: string; definition: Definition }[];
  // The constant definitions with effects, in the order TLC evaluates them.
  definitions: Definition[];
  // The constant definitions TLC computes and deep-normalizes at startup (processConstantDefns).
  normalized: ReadonlySet<Definition>;
  // The names of the definitions the configuration substitutes for anything but a declared
  // constant of the root module, as written, so in any module.
  substitutesForDefinitions: ReadonlySet<string>;
  // The constant definitions the configuration names, which TLC rejects for their value.
  predicates: ReturnType<typeof getConstantPredicates>;
  // The SYMMETRY definition, which TLC evaluates to its group, and the sets it permutes.
  symmetry: { definition: Definition; permutedSets: PermutedSet[] } | undefined;
  // The assumptions that aren't axioms, each with the name TLC reports it by.
  assumptions: { expression: Expression; name: string }[];
}

const PREDICATE_FORMS = { predicate: 0, definition: 1, specification: 2 };

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

// A string in WTF-8: UTF-8 that also encodes a lone surrogate as a code point of three bytes, as
// tla-ir's wtf8.rs reads it, since a string TLC computes can hold one, as Tail("😀a") does.
const encodeWtf8 = (text: string) => {
  if (text.isWellFormed()) return new TextEncoder().encode(text);
  const bytes: number[] = [];
  for (const character of text) {
    const point = character.codePointAt(0) ?? 0;
    if (point < 0x80) bytes.push(point);
    else if (point < 0x800) bytes.push(0xc0 | (point >> 6), 0x80 | (point & 0x3f));
    else if (point < 0x10000) {
      bytes.push(0xe0 | (point >> 12), 0x80 | ((point >> 6) & 0x3f), 0x80 | (point & 0x3f));
    } else {
      bytes.push(
        0xf0 | (point >> 18),
        0x80 | ((point >> 12) & 0x3f),
        0x80 | ((point >> 6) & 0x3f),
        0x80 | (point & 0x3f),
      );
    }
  }
  return Uint8Array.from(bytes);
};

// The texts in WTF-8, in one call, and where each ends in UTF-16 code units.
const encodeTexts = (ranked: readonly string[], rankedCount: number, extra: string[]) => {
  const joined = ranked.slice(0, rankedCount).join("") + extra.join("");
  const ends = new Int32Array(rankedCount + extra.length);
  let end = 0;
  for (let index = 0; index < rankedCount; index++) ends[index] = end += ranked[index].length;
  for (let index = 0; index < extra.length; index++) {
    ends[rankedCount + index] = end += extra[index].length;
  }
  return { bytes: encodeWtf8(joined), ends };
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
  // Whether a node reads TLCGet("spec"), whose record the IR then holds.
  const specificationRead = { isRead: false };
  const isSpecificationRead = (expression: Expression & { kind: "Apply" }) =>
    expression.operator === "TLCGet" &&
    expression.args[0]?.kind === "String" &&
    expression.args[0].value === "spec" &&
    expression.resolution?.kind !== "Local" &&
    (resolveOperator(expression.operator) & RESOLUTION_MASK) === BUILTIN_RESOLUTION;

  // The definition of the module an operator is, by its body, or -1 for one a LET defines.
  const definitionsByBody = new Map(
    [...environment.definitions.values()]
      .reverse()
      .map((definition) => [definition.body, definition]),
  );
  const getOperatorDefinitionIndex = (operator: Closure | undefined) => {
    const definition = operator && definitionsByBody.get(operator.body);
    return definition ? getDefinitionIndex(definition) : -1;
  };

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
        (builtin.isLazy ? BUILTIN_LAZY : 0) |
        (builtin.table ? BUILTIN_TABLE : 0) |
        (builtin.isNaturalsGeq ? BUILTIN_NATURALS_GEQ : 0) |
        (builtin.isNaturalsMethod ? BUILTIN_NATURALS_METHOD : 0),
    );
    if (builtin.table) {
      push(builtins, builtin.table.length);
      for (const row of builtin.table) {
        push(builtins, getValue(createTuple(row[0])));
        push(builtins, getValue(row[1]));
      }
    }
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

  // Each name's text and resolution, as a name and as an operator, since names recur. A name
  // nothing global resolves is one a scope binds, as a definition an INSTANCE in a LET copies in
  // under a key the resolver leaves alone, so it is written as local.
  const names = new Map<string, number[]>();
  const operators = new Map<string, number[]>();
  const writeName = (name: string, isOperator: boolean, at?: number) => {
    const cache = isOperator ? operators : names;
    const known = cache.get(name);
    const entry = known ?? [getText(name), isOperator ? resolveOperator(name) : resolveName(name)];
    if (!known) cache.set(name, entry);
    if (at !== undefined && entry[1] === NO_RESOLUTION) nodes.data[at] |= LOCAL_FLAG;
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

  const writeRange = (words: Words, range: SourceRange | undefined) => {
    if (!range) {
      for (const word of [-1, 0, 0, 0, 0]) push(words, word);
      return;
    }
    push(words, getText(range.module));
    push(words, range.start.line);
    push(words, range.start.column);
    push(words, range.end.line);
    push(words, range.end.column);
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
        (environment.substitutedDefinitions.has(definition) ? DEFINITION_SUBSTITUTED : 0) |
        (input.startup.normalized.has(definition) ? DEFINITION_NORMALIZED : 0) |
        // TLC holds an operator definition whose body is a numeral or a string as the value it
        // gave the literal (SymbolNodeValueLookupProvider.lookup), unless it is an INSTANCE's copy
        // with substitutions or the configuration substitutes it for another definition.
        (definition.kind === "Operator" &&
        definition.bodyRange !== undefined &&
        (definition.body.kind === "Number" || definition.body.kind === "String") &&
        !environment.substitutedDefinitions.has(definition) &&
        !input.startup.substitutesForDefinitions.has(definition.name)
          ? DEFINITION_LITERAL
          : 0),
    );
    push(nodes, definition.location.line);
    push(nodes, definition.location.column);
    writeRange(nodes, definition.location.range);
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
    writeRange(nodes, location.range);
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
        writeName(expression.name, false, at);
        return;
      case "Apply":
        if (expression.resolution?.kind === "Local") nodes.data[at] |= LOCAL_FLAG;
        if (isSpecificationRead(expression)) specificationRead.isRead = true;
        writeName(expression.operator, true, at);
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
  const spec = input.spec;
  push(model, writeRoot(spec.init));
  push(model, spec.next === undefined ? -1 : writeRoot(spec.next));
  push(model, getScopeIndex(spec.scope));
  push(model, input.traceActions.length);
  for (const action of input.traceActions) {
    push(model, writeRoot(action.expression));
    push(model, getScopeIndex(action.scope));
    push(model, getText(action.label));
    push(model, getText(action.name));
    writeRange(model, action.range);
    push(model, getOperatorDefinitionIndex(action.operator));
  }
  push(model, spec.actions ? 1 : 0);
  writeConfigNames(config.invariants, true);
  push(model, input.properties.invariants.length);
  for (const invariant of input.properties.invariants) {
    push(model, writeRoot(invariant.expression));
    push(model, getScopeIndex(invariant.scope));
    push(model, hasRepeatedEffect(invariant.expression, environment) ? 1 : 0);
    push(model, getText(invariant.name));
  }
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
    push(model, getScopeIndex(property.scope));
    push(model, getText(property.name));
  }
  push(model, input.properties.initialPredicates.length);
  for (const predicate of input.properties.initialPredicates) {
    push(model, writeRoot(predicate.expression));
    push(model, getText(predicate.name));
    push(model, getScopeIndex(predicate.scope));
  }
  writeConfigNames(config.view === undefined ? [] : [config.view]);
  // TLC holds a name the configuration assigns, unscoped, as its value, which it rejects as the
  // ALIAS (Spec.getAliasSpec), unless the configuration also substitutes for it: the IR keeps it as
  // a constant, as the Rust front end does.
  const aliasDefinition =
    config.alias === undefined ? undefined : environment.definitions.get(config.alias);
  const aliasValue =
    config.alias === undefined ? undefined : environment.constants.get(config.alias);
  if (
    config.alias !== undefined &&
    aliasValue !== undefined &&
    config.constants.some(
      (constant) => constant.name === config.alias && constant.module === undefined,
    ) &&
    !environment.substitutions.has(config.alias) &&
    aliasDefinition !== undefined &&
    !(aliasDefinition.kind === "Operator" && aliasDefinition.bodyRange === undefined)
  ) {
    getConstantIndex(config.alias, aliasValue);
  }
  writeConfigNames(config.alias === undefined ? [] : [config.alias]);
  writeConfigNames(config.postconditions);
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
  // The range of the definition SPECIFICATION names, which TLC's warning of a stuttering
  // counterexample prints.
  const specification =
    input.config.specification === undefined
      ? undefined
      : getDefinition(input.config.specification, environment)?.location.range;
  writeRange(model, specification);
  const startup = input.startup;
  push(model, startup.substitutes.length);
  for (const substitute of startup.substitutes) {
    push(model, getText(substitute.name));
    push(model, getDefinitionIndex(substitute.definition));
  }
  push(model, startup.definitions.length);
  for (const definition of startup.definitions) push(model, getDefinitionIndex(definition));
  push(model, startup.predicates.length);
  for (const predicate of startup.predicates) {
    push(model, PREDICATE_FORMS[predicate.form]);
    push(model, getText(predicate.kind));
    push(model, getText(predicate.name));
    push(model, getDefinitionIndex(predicate.definition));
  }
  if (startup.symmetry === undefined) push(model, -1);
  if (startup.symmetry !== undefined) {
    push(model, getDefinitionIndex(startup.symmetry.definition));
    push(model, startup.symmetry.permutedSets.length);
    for (const permuted of startup.symmetry.permutedSets) {
      push(model, getText(permuted.name));
      push(model, permuted.operand === undefined ? -1 : writeRoot(permuted.operand));
    }
  }
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

  // Where the specification reaches the next-state relation through an INSTANCE, and what TLC
  // names the actions of the definitions INSTANCEs copy, of the definitions the IR holds, by index.
  writeRange(model, input.nextSubstitution);
  const getIndexed = <Item>(entries: Iterable<[string, Item]>) =>
    [
      ...new Map(
        [...entries].flatMap(([key, item]): [number, Item][] => {
          const definition = environment.definitions.get(key);
          const index = definition && definitionIndices.get(definition);
          return index === undefined ? [] : [[index, item]];
        }),
      ),
    ].sort(([left], [right]) => left - right);
  const instanceActions = getIndexed(input.instanceActions);
  push(model, instanceActions.length);
  for (const [index, action] of instanceActions) {
    push(model, index);
    push(model, getText(action.name));
    writeRange(model, action.location.range);
  }
  const instanceNames = getIndexed(environment.instanceNames);
  push(model, instanceNames.length);
  for (const [index, name] of instanceNames) {
    push(model, index);
    push(model, getText(name));
  }
  // TLCGet("spec"), where a node reads it, as the interpreter computes it.
  push(
    model,
    specificationRead.isRead && input.getSpecification ? getValue(input.getSpecification()) : -1,
  );

  // --- the blob ---

  const encodedValues = valueEncoder.finish();
  const valueStrings = encodedValues.strings.map(getText);
  const variables = environment.variables.map(getText);
  const texts = encodeTexts(rankedTexts, rankedCount, extraTexts);
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

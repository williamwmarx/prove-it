// Generates JavaScript for the initial predicate and the next-state relation. It walks actions as
// action.ts does, in the same order, but writes the walk out as straight-line code: a conjunction
// becomes nested blocks, an existential a loop, and a guard an `if` whose condition is the guard's
// own code where the compiler can write it. Since each path through the action is written out, the
// generator knows on each path which variables are assigned, and checks at run time only where it
// can't know.
//
// Hosts that refuse code generation from strings get the closures of action.ts instead.

import { type Expression, isLocallyResolved } from "../ast";
import { compileAction, createActionAnalysis, type Step } from "./action";
import {
  booleanCodeOf,
  type CodeGen,
  codeOf,
  type CompileContext,
  type Compiler,
  isOrderedEnumeration,
  registers,
} from "./compile";
import { getCodegenSetting } from "./settings";
import { bail, elementAt, equals, KIND_SET, kindOf, sizeOf } from "./store";

interface GenerateOptions {
  isInit: boolean;
  isAssignedShortcut: boolean;
}

// Whether each variable is unassigned, assigned, or either, on the path being written.
const UNASSIGNED = 0;
const ASSIGNED = 1;
const UNKNOWN = 2;
type Known = number[];
type Continuation = (known: Known) => string;

// Generated code past this size goes back to the closures: the walk writes out every path, so an
// action with many disjunctions followed by more conjuncts grows quickly.
const MAXIMUM_CODE_LENGTH = 1_000_000;

class TooLarge extends Error {}

const expectSetSize = (id: number) =>
  kindOf(id) === KIND_SET ? sizeOf(id) : bail("an action quantified over a non-set");
const orderedSize = (id: number) => sizeOf(id);

const notBoolean = () => bail("a conjunct that isn't a boolean");

export const generateAction = (
  compiler: Compiler,
  expression: Expression,
  context: CompileContext,
  options: GenerateOptions,
): Step | undefined => {
  const isInit = options.isInit;
  const variableCount = compiler.variableCount;
  const analysis = createActionAnalysis(compiler, isInit);
  const values: unknown[] = [];
  const names = new Map<unknown, string>();
  const gen: CodeGen = {
    ref: (value) => {
      const known = names.get(value);
      if (known !== undefined) return known;
      const name = `x${values.length}`;
      values.push(value);
      names.set(value, name);
      return name;
    },
  };
  const R = gen.ref(registers);
  const T = isInit ? `${R}.cur` : `${R}.next`;
  const element = gen.ref(elementAt);
  const setSize = gen.ref(expectSetSize);
  const ordered = gen.ref(orderedSize);
  const equal = gen.ref(equals);
  const nonBoolean = gen.ref(notBoolean);
  let counter = 0;
  const fresh = (prefix: string) => `${prefix}${counter++}`;
  let length = 0;
  const emit = (code: string) => {
    length += code.length;
    if (length > MAXIMUM_CODE_LENGTH) throw new TooLarge();
    return code;
  };

  const guardCode = (guard: Expression, guardContext: CompileContext) =>
    booleanCodeOf(compiler.compile(guard, guardContext), gen);

  // An assignment of `value` to a variable, then the continuation.
  const assign = (variable: number, value: string, known: Known, rest: Continuation) => {
    const valueName = fresh("v");
    const after = known.slice();
    after[variable] = ASSIGNED;
    if (known[variable] === UNASSIGNED) {
      return emit(
        `{ const ${valueName} = ${value}; ${T}[${variable}] = ${valueName}; ${R}.assigned++;\n${rest(after)}\n${T}[${variable}] = -1; ${R}.assigned--; }`,
      );
    }
    if (known[variable] === ASSIGNED) {
      return emit(
        `{ const ${valueName} = ${value}; const o${valueName} = ${T}[${variable}]; if (o${valueName} === ${valueName} || ${equal}(o${valueName}, ${valueName})) {\n${rest(after)}\n} }`,
      );
    }
    const old = fresh("o");
    const flag = fresh("u");
    return emit(
      `{ const ${valueName} = ${value}; const ${old} = ${T}[${variable}]; let ${flag} = 0; if (${old} === -1) { ${T}[${variable}] = ${valueName}; ${R}.assigned++; ${flag} = 1; }
if (${flag} === 1 || ${old} === ${valueName} || ${equal}(${old}, ${valueName})) {\n${rest(after)}\n}
if (${flag} === 1) { ${T}[${variable}] = -1; ${R}.assigned--; } }`,
    );
  };

  const restAsGuards = (
    operands: Expression[],
    operandContext: CompileContext,
    known: Known,
    rest: Continuation,
  ) => {
    const guards = operands.map((operand) => guardCode(operand, operandContext));
    return emit(`if (${guards.join(" && ")}) {\n${rest(known)}\n}`);
  };

  const conjunction = (
    operands: Expression[],
    operandContext: CompileContext,
    index: number,
    known: Known,
    rest: Continuation,
  ): string => {
    if (index === operands.length) return rest(known);
    if (index > 0 && options.isAssignedShortcut) {
      if (known.every((state) => state === ASSIGNED)) {
        return restAsGuards(operands.slice(index), operandContext, known, rest);
      }
      if (known.every((state) => state !== UNASSIGNED)) {
        return emit(
          `if (${R}.assigned === ${variableCount}) {\n${restAsGuards(
            operands.slice(index),
            operandContext,
            known.map(() => ASSIGNED),
            rest,
          )}\n} else {\n${walkConjunct(operands, operandContext, index, known, rest)}\n}`,
        );
      }
    }
    return walkConjunct(operands, operandContext, index, known, rest);
  };

  const walkConjunct = (
    operands: Expression[],
    operandContext: CompileContext,
    index: number,
    known: Known,
    rest: Continuation,
  ): string => {
    const operand = operands[index];
    const next: Continuation = (after) =>
      conjunction(operands, operandContext, index + 1, after, rest);
    if (operand.kind === "Apply" && operand.operator === "=" && !isLocallyResolved(operand)) {
      const variable = analysis.getAssignableIndex(operand.args[0], operandContext);
      if (variable !== undefined) {
        return assign(
          variable,
          codeOf(compiler.compile(operand.args[1], operandContext), gen),
          known,
          next,
        );
      }
    }
    if (!isInit && operand.kind === "Unchanged") {
      const indices = analysis.getUnchangedIndices(operand.expression, operandContext);
      if (indices) return unchanged(indices, 0, known, next);
    }
    if (analysis.isGuard(operand, operandContext)) {
      const condition = fresh("g");
      return emit(
        `{ const ${condition} = ${codeOf(compiler.compile(operand, operandContext), gen)}; if (${condition} === 1) {\n${next(known)}\n} else if (${condition} !== 0) ${nonBoolean}(); }`,
      );
    }
    return step(operand, operandContext, known, next);
  };

  const unchanged = (
    indices: number[],
    position: number,
    known: Known,
    rest: Continuation,
  ): string =>
    position === indices.length
      ? rest(known)
      : assign(indices[position], `${R}.cur[${indices[position]}]`, known, (after) =>
          unchanged(indices, position + 1, after, rest),
        );

  // Hands a subtree the generator doesn't write to the closures of action.ts.
  const opaque = (
    operand: Expression,
    operandContext: CompileContext,
    known: Known,
    rest: Continuation,
  ) => {
    const closure = compileAction(compiler, operand, operandContext, options);
    const after = known.map((state) => (state === ASSIGNED ? ASSIGNED : UNKNOWN));
    return emit(`${gen.ref(closure)}(() => {\n${rest(after)}\n});`);
  };

  const quantified = (
    bounds: (Expression & { kind: "Exists" })["bounds"],
    body: Expression,
    operandContext: CompileContext,
    known: Known,
    rest: Continuation,
    operand: Expression,
  ): string => {
    let inner = operandContext;
    const levels: { set: string; slot: number; isOrdered: boolean }[] = [];
    for (const bound of bounds) {
      if (bound.pattern.kind !== "Name") return opaque(operand, operandContext, known, rest);
      const set = compiler.compileOrdered(bound.set, inner, "quantifier");
      const binding = compiler.bindValue(inner, bound.pattern.name);
      inner = binding.context;
      levels.push({
        set: codeOf(set, gen),
        slot: binding.slot,
        isOrdered: isOrderedEnumeration(set),
      });
    }
    const sets = levels.map(() => fresh("s"));
    const sizes = levels.map(() => fresh("n"));
    const counters = levels.map(() => fresh("j"));
    const header = levels
      .map(
        (level, position) =>
          `const ${sets[position]} = ${level.set}; const ${sizes[position]} = ${level.isOrdered ? ordered : setSize}(${sets[position]});`,
      )
      .join(" ");
    // TLC's ContextEnumerator varies the first bound fastest: the last bound is the outer loop.
    const loops = (position: number): string => {
      if (position < 0) return step(body, inner, known, rest);
      const level = levels[position];
      return `for (let ${counters[position]} = 0; ${counters[position]} < ${sizes[position]}; ${counters[position]}++) { ${R}.locals[${level.slot}] = ${element}(${sets[position]}, ${counters[position]});\n${loops(position - 1)}\n}`;
    };
    return emit(`{ ${header}\n${loops(levels.length - 1)}\n}`);
  };

  const membership = (
    variable: number,
    operand: Expression & { kind: "Apply" },
    operandContext: CompileContext,
    known: Known,
    rest: Continuation,
  ): string => {
    if (known[variable] === ASSIGNED) {
      return emit(`if (${guardCode(operand, operandContext)}) {\n${rest(known)}\n}`);
    }
    const set = compiler.compileOrdered(operand.args[1], operandContext, "streamed");
    const setName = fresh("s");
    const sizeName = fresh("n");
    const counter = fresh("j");
    const after = known.slice();
    after[variable] = ASSIGNED;
    const loop = `{ const ${setName} = ${codeOf(set, gen)}; const ${sizeName} = ${isOrderedEnumeration(set) ? ordered : setSize}(${setName}); ${R}.assigned++;
for (let ${counter} = 0; ${counter} < ${sizeName}; ${counter}++) { ${T}[${variable}] = ${element}(${setName}, ${counter});\n${rest(after)}\n}
${T}[${variable}] = -1; ${R}.assigned--; }`;
    if (known[variable] === UNASSIGNED) return emit(loop);
    return emit(
      `if (${T}[${variable}] !== -1) { if (${guardCode(operand, operandContext)}) {\n${rest(after)}\n} } else ${loop}`,
    );
  };

  const step = (
    operand: Expression,
    operandContext: CompileContext,
    known: Known,
    rest: Continuation,
  ): string => {
    switch (operand.kind) {
      case "And":
        return conjunction(operand.operands, operandContext, 0, known, rest);
      case "Or":
        return operand.operands
          .map((branch) => emit(`{\n${step(branch, operandContext, known, rest)}\n}`))
          .join("\n");
      case "Exists":
        return quantified(operand.bounds, operand.body, operandContext, known, rest, operand);
      case "Forall":
        if (
          !analysis.hasAssignments(operand.body, operandContext) &&
          !analysis.hasBranches(operand.body, operandContext)
        ) {
          return emit(`if (${guardCode(operand, operandContext)}) {\n${rest(known)}\n}`);
        }
        return opaque(operand, operandContext, known, rest);
      case "If": {
        const condition = guardCode(operand.condition, operandContext);
        return emit(
          `if (${condition}) {\n${step(operand.consequent, operandContext, known, rest)}\n} else {\n${step(operand.alternative, operandContext, known, rest)}\n}`,
        );
      }
      case "Case": {
        const arms = operand.arms.map(
          (arm) =>
            `if (${guardCode(arm.condition, operandContext)}) {\n${step(arm.body, operandContext, known, rest)}\n}`,
        );
        const other = operand.other
          ? `{\n${step(operand.other, operandContext, known, rest)}\n}`
          : `${gen.ref(bail)}("no CASE arm holds");`;
        return emit(`${arms.join(" else ")} else ${other}`);
      }
      case "Let":
        return step(operand.body, compiler.bindLet(operand, operandContext), known, rest);
      case "Label":
        return step(operand.body, operandContext, known, rest);
      case "Unchanged": {
        if (isInit) return opaque(operand, operandContext, known, rest);
        const indices = analysis.getUnchangedIndices(operand.expression, operandContext);
        if (indices) return unchanged(indices, 0, known, rest);
        return emit(`if (${guardCode(operand, operandContext)}) {\n${rest(known)}\n}`);
      }
      case "AngleAction": {
        const isUnchanged = codeOf(
          compiler.compile(
            { kind: "Unchanged", expression: operand.subscript, location: operand.location },
            operandContext,
          ),
          gen,
        );
        return step(operand.action, operandContext, known, (after) =>
          emit(`if (${isUnchanged} === 0) {\n${rest(after)}\n}`),
        );
      }
      case "BoxAction":
        return step(
          {
            kind: "Or",
            operands: [
              operand.action,
              { kind: "Unchanged", expression: operand.subscript, location: operand.location },
            ],
            location: operand.location,
          },
          operandContext,
          known,
          rest,
        );
      case "Identifier": {
        const resolved = compiler.resolveAction(operand, operandContext);
        if (!resolved)
          return emit(`if (${guardCode(operand, operandContext)}) {\n${rest(known)}\n}`);
        return step(resolved.body, resolved.context, known, rest);
      }
      case "Apply": {
        const args = operand.args;
        if (
          !isLocallyResolved(operand) &&
          (operand.operator === "=" ||
            operand.operator === "\\in" ||
            operand.operator === "\\subseteq")
        ) {
          const variable = analysis.getAssignableIndex(args[0], operandContext);
          if (variable !== undefined) {
            if (operand.operator === "=")
              return conjunction([operand], operandContext, 0, known, rest);
            if (operand.operator === "\\subseteq")
              return opaque(operand, operandContext, known, rest);
            return membership(variable, operand, operandContext, known, rest);
          }
          if (analysis.isPossiblyAssignable(args[0]))
            return opaque(operand, operandContext, known, rest);
        }
        if (!isLocallyResolved(operand) && operand.operator === "=>") {
          const condition = fresh("c");
          return emit(
            `{ const ${condition} = ${guardCode(args[0], operandContext)}; if (${condition} === 0) {\n${rest(known)}\n} else {\n${step(args[1], operandContext, known, rest)}\n} }`,
          );
        }
        if (
          !isLocallyResolved(operand) &&
          (operand.operator === "/\\" || operand.operator === "\\/")
        ) {
          return step(
            {
              kind: operand.operator === "/\\" ? "And" : "Or",
              operands: args,
              location: operand.location,
            },
            operandContext,
            known,
            rest,
          );
        }
        const resolved = compiler.resolveAction(operand, operandContext);
        if (resolved) return step(resolved.body, resolved.context, known, rest);
        return emit(`if (${guardCode(operand, operandContext)}) {\n${rest(known)}\n}`);
      }
      case "FunctionApplication":
        if (compiler.resolveLazyApplication(operand, operandContext))
          return opaque(operand, operandContext, known, rest);
        return emit(`if (${guardCode(operand, operandContext)}) {\n${rest(known)}\n}`);
      default:
        return emit(`if (${guardCode(operand, operandContext)}) {\n${rest(known)}\n}`);
    }
  };

  let body: string;
  try {
    body = step(
      expression,
      context,
      new Array<number>(variableCount).fill(UNASSIGNED),
      () => "K();",
    );
  } catch (error) {
    if (error instanceof TooLarge) return undefined;
    throw error;
  }
  try {
    if (getCodegenSetting() === "dump") console.error(body);
    const factory = new Function(
      ...names.values(),
      `"use strict";\nreturn function generatedAction(K) {\n${body}\n};`,
    );
    return factory(...values) as Step;
  } catch (error) {
    // A host that disallows code generation from strings, such as one with a strict content
    // security policy, runs the closures.
    if (error instanceof EvalError) return undefined;
    throw error;
  }
};

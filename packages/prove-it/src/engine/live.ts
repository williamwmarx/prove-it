// Answers the liveness checker's questions about the states of a search the engine found: whether
// a state predicate holds of a state, an action predicate of a step, or an action is ENABLED. The
// engine compiles each once and evaluates it on the states' ids, cached like any other expression.
// It returns undefined for anything it can't answer, and the interpreter answers that.

import type { Expression } from "../ast";
import type { EvaluationScope } from "../evaluate";
import type { LiveExpression } from "../tableau";
import type { Value } from "../values";
import { compileAction, type Step } from "./action";
import { generateAction } from "./codegen";
import {
  type CompileContext,
  type Compiled,
  type Compiler,
  registers,
  setCurrent,
  setNext,
} from "./compile";
import { Bailout, FALSE, TRUE } from "./store";

export type LiveOracle = (
  expression: LiveExpression,
  state: Value[],
  next: Value[] | undefined,
) => boolean | undefined;

const UNKNOWN = Symbol("unknown");
const FOUND = Symbol("found");

export const createLiveOracle = (
  compiler: Compiler,
  getIds: (state: Value[]) => Int32Array | undefined,
): LiveOracle => {
  const width = compiler.variableCount;
  const next = new Int32Array(width);
  const contexts = new Map<EvaluationScope | undefined, CompileContext | typeof UNKNOWN>();
  const values = new Map<Expression, Map<EvaluationScope | undefined, Compiled | typeof UNKNOWN>>();
  const steps = new Map<Expression, Map<EvaluationScope | undefined, Step | typeof UNKNOWN>>();

  const getContext = (scope: EvaluationScope | undefined) => {
    let context = contexts.get(scope);
    if (context === undefined) {
      context = compiler.contextFromScope(scope) ?? UNKNOWN;
      contexts.set(scope, context);
    }
    return context;
  };

  // Compiles once per expression and scope, remembering what the engine can't compile.
  const getCompiled = <Result>(
    cache: Map<Expression, Map<EvaluationScope | undefined, Result | typeof UNKNOWN>>,
    expression: Expression,
    scope: EvaluationScope | undefined,
    build: (context: CompileContext) => Result,
  ): Result | typeof UNKNOWN => {
    const byScope =
      cache.get(expression) ?? new Map<EvaluationScope | undefined, Result | typeof UNKNOWN>();
    cache.set(expression, byScope);
    const known = byScope.get(scope);
    if (known !== undefined) return known;
    const context = getContext(scope);
    let result: Result | typeof UNKNOWN = UNKNOWN;
    if (context !== UNKNOWN) {
      try {
        result = build(context);
      } catch (error) {
        if (!(error instanceof Bailout)) throw error;
      }
    }
    byScope.set(scope, result);
    return result;
  };

  const holds = (compiled: Compiled) => {
    const value = compiled.evaluate();
    return value === TRUE ? true : value === FALSE ? false : undefined;
  };

  const isEnabled = (step: Step) => {
    next.fill(-1);
    registers.assigned = 0;
    try {
      step(() => {
        throw FOUND;
      });
      return false;
    } catch (error) {
      if (error === FOUND) return true;
      throw error;
    } finally {
      registers.assigned = 0;
    }
  };

  return (expression, state, successor) => {
    if (
      expression.kind !== "State" &&
      expression.kind !== "Action" &&
      expression.kind !== "Enabled"
    ) {
      return undefined;
    }
    const ids = getIds(state);
    if (!ids) return undefined;
    try {
      setCurrent(ids);
      setNext(next);
      if (expression.kind === "State") {
        const compiled = getCompiled(values, expression.expression, expression.scope, (context) =>
          compiler.compile(expression.expression, context),
        );
        return compiled === UNKNOWN ? undefined : holds(compiled);
      }
      if (expression.kind === "Enabled") {
        const step = getCompiled(steps, expression.step, expression.scope, (context) => {
          const options = { isInit: false, isAssignedShortcut: false };
          return (
            generateAction(compiler, expression.step, context, options) ??
            compileAction(compiler, expression.step, context, options)
          );
        });
        return step === UNKNOWN ? undefined : isEnabled(step);
      }
      const nextIds = successor && getIds(successor);
      if (!nextIds) return undefined;
      setNext(nextIds);
      if (expression.unchanged) {
        const unchanged = getCompiled(values, expression.unchanged, expression.scope, (context) =>
          compiler.compile(expression.unchanged!, context),
        );
        if (unchanged === UNKNOWN) return undefined;
        const isUnchanged = holds(unchanged);
        if (isUnchanged === undefined) return undefined;
        if (isUnchanged) return false;
      }
      const action = getCompiled(values, expression.expression, expression.scope, (context) =>
        compiler.compile(expression.expression, context),
      );
      return action === UNKNOWN ? undefined : holds(action);
    } catch (error) {
      if (error instanceof Bailout) return undefined;
      throw error;
    }
  };
};

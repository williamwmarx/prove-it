// Answers the liveness checker's questions about the states of a search the engine found: whether
// a state predicate holds of a state, an action predicate of a step, or an action is ENABLED. The
// engine compiles each once and evaluates it on the states' ids, cached like any other expression.
// It returns undefined for anything it can't answer, and the interpreter answers that.

import type { Expression } from "../ast";
import type { EvaluationScope } from "../evaluate";
import type { LiveExpression } from "../tableau";
import type { Value } from "../values";
import { compileAction, createEnabledTest } from "./action";
import { generateAction } from "./codegen";
import { type CompileContext, type Compiled, type Compiler, setCurrent, setNext } from "./compile";
import { Bailout, FALSE, TRUE } from "./store";

export type LiveOracle = (
  expression: LiveExpression,
  state: Value[],
  next: Value[] | undefined,
) => boolean | undefined;

const UNKNOWN = Symbol("unknown");

export const createLiveOracle = (
  compiler: Compiler,
  getIds: (state: Value[]) => Int32Array | undefined,
): LiveOracle => {
  const width = compiler.variableCount;
  const next = new Int32Array(width);
  const contexts = new Map<EvaluationScope | undefined, CompileContext | typeof UNKNOWN>();
  const values = new Map<Expression, Map<EvaluationScope | undefined, Compiled | typeof UNKNOWN>>();
  const enabledTests = new Map<
    Expression,
    Map<EvaluationScope | undefined, (() => boolean) | typeof UNKNOWN>
  >();

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

  // The compiled forms of each predicate the checker asks about, found once through the caches
  // above, since it asks about the same predicates on every state.
  const answers = {
    values: new Map<LiveExpression, Compiled | typeof UNKNOWN>(),
    unchanged: new Map<LiveExpression, Compiled | typeof UNKNOWN>(),
    enabledTests: new Map<LiveExpression, (() => boolean) | typeof UNKNOWN>(),
  };
  const getAnswer = <Result>(
    cache: Map<LiveExpression, Result | typeof UNKNOWN>,
    expression: LiveExpression,
    build: () => Result | typeof UNKNOWN,
  ) => {
    const known = cache.get(expression);
    if (known !== undefined) return known;
    const built = build();
    cache.set(expression, built);
    return built;
  };

  // The checker asks about a state many times in a row, so the last lookup of each side of a step
  // is kept.
  const lookups = {
    state: undefined as Value[] | undefined,
    ids: undefined as Int32Array | undefined,
    next: undefined as Value[] | undefined,
    nextIds: undefined as Int32Array | undefined,
  };
  const getStateIds = (state: Value[]) => {
    if (state !== lookups.state) {
      lookups.state = state;
      lookups.ids = getIds(state);
    }
    return lookups.ids;
  };
  const getNextIds = (state: Value[]) => {
    if (state !== lookups.next) {
      lookups.next = state;
      lookups.nextIds = getIds(state);
    }
    return lookups.nextIds;
  };

  const holds = (compiled: Compiled) => {
    const value = compiled.evaluate();
    return value === TRUE ? true : value === FALSE ? false : undefined;
  };

  return (expression, state, successor) => {
    if (
      expression.kind !== "State" &&
      expression.kind !== "Action" &&
      expression.kind !== "Enabled"
    ) {
      return undefined;
    }
    const ids = getStateIds(state);
    if (!ids) return undefined;
    try {
      setCurrent(ids);
      setNext(next);
      if (expression.kind === "State") {
        const compiled = getAnswer(answers.values, expression, () =>
          getCompiled(values, expression.expression, expression.scope, (context) =>
            compiler.compile(expression.expression, context),
          ),
        );
        return compiled === UNKNOWN ? undefined : holds(compiled);
      }
      if (expression.kind === "Enabled") {
        const test = getAnswer(answers.enabledTests, expression, () =>
          getCompiled(enabledTests, expression.step, expression.scope, (context) => {
            const options = { isInit: false, isAssignedShortcut: false };
            const step =
              generateAction(compiler, expression.step, context, options) ??
              compileAction(compiler, expression.step, context, options);
            return createEnabledTest(step, width);
          }),
        );
        return test === UNKNOWN ? undefined : test();
      }
      const nextIds = successor && getNextIds(successor);
      if (!nextIds) return undefined;
      setNext(nextIds);
      const unchangedExpression = expression.unchanged;
      if (unchangedExpression) {
        const unchanged = getAnswer(answers.unchanged, expression, () =>
          getCompiled(values, unchangedExpression, expression.scope, (context) =>
            compiler.compile(unchangedExpression, context),
          ),
        );
        if (unchanged === UNKNOWN) return undefined;
        const isUnchanged = holds(unchanged);
        if (isUnchanged === undefined) return undefined;
        if (isUnchanged) return false;
      }
      const action = getAnswer(answers.values, expression, () =>
        getCompiled(values, expression.expression, expression.scope, (context) =>
          compiler.compile(expression.expression, context),
        ),
      );
      return action === UNKNOWN ? undefined : holds(action);
    } catch (error) {
      if (error instanceof Bailout) return undefined;
      throw error;
    }
  };
};

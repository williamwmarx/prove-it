// Answers the liveness checker's questions about the states of a search the engine found: whether
// a state predicate holds of a state, an action predicate of a step, or an action is ENABLED. The
// engine compiles each once and evaluates it on the states' ids, cached like any other expression.
// It returns undefined for anything it can't answer, and the interpreter answers that.

import type { Expression } from "../ast";
import { EngineInvariantError } from "../errors";
import type { EvaluationScope } from "../evaluate";
import type { LiveEnabled, LiveExpression } from "../tableau";
import type { Value } from "../values";
import { type CompileContext, type Compiled, type Compiler, setCurrent, setNext } from "./compile";
import { getEnvironmentFlag, reportEngine } from "./settings";
import { Bailout, FALSE, TRUE } from "./store";

export type LiveOracle = (
  expression: LiveExpression,
  state: Value[],
  next: Value[] | undefined,
) => boolean | undefined;

// The positions, among TLC's actions of the next-state relation, of the actions the action of
// ENABLED splits into, in their order, "all" when it splits into every one, or undefined when it
// isn't made of them.
export type EnabledActions = (expression: LiveEnabled) => readonly number[] | "all" | undefined;

// The states of the search, `width` ids each, and its steps: those from state i between
// edgeOffsets[i] and edgeOffsets[i + 1], in the order generated, each labelled with the position
// of the action that took it when the search took TLC's actions one by one.
export interface LiveGraph {
  states: Int32Array;
  // How many of the states, from the first, the search took all the steps of.
  expanded: number;
  edgeOffsets: Int32Array;
  edges: Int32Array;
  labels: Int32Array | undefined;
  // Whether a state's steps are those TLC's ENABLED finds when it runs an action from the state.
  isEnabledExact: boolean;
}

// How the steps a state took answer ENABLED <<A>>_v: the subscript's UNCHANGED, and the actions,
// by position, whose steps A takes, or undefined when A takes every step.
interface EdgeQuestion {
  unchanged: Compiled;
  actions: Uint8Array | undefined;
}

const UNKNOWN = Symbol("unknown");

export const createLiveOracle = (
  compiler: Compiler,
  graph: LiveGraph,
  getIndex: (state: Value[]) => number | undefined,
  getEnabledActions: EnabledActions,
): LiveOracle => {
  const width = compiler.variableCount;
  const states = graph.states;
  // PROVE_IT_LIVE_CHECK=1 also runs each action ENABLED asks about that the steps answer, and
  // throws where the two answers differ.
  const isLiveChecked = getEnvironmentFlag("PROVE_IT_LIVE_CHECK");
  const report = { isReported: false };
  const contexts = new Map<EvaluationScope | undefined, CompileContext | typeof UNKNOWN>();
  const values = new Map<Expression, Map<EvaluationScope | undefined, Compiled | typeof UNKNOWN>>();

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
  // above, since it asks about the same predicates on every state. They are built only when a
  // lookup misses, so asking again allocates nothing.
  const answers = new Map<LiveExpression, Compiled | typeof UNKNOWN>();
  const unchangedAnswers = new Map<LiveExpression, Compiled | typeof UNKNOWN>();
  const edgeQuestions = new Map<LiveExpression, EdgeQuestion | typeof UNKNOWN>();
  const compileIn = (expression: Expression, scope: EvaluationScope | undefined) =>
    getCompiled(values, expression, scope, (context) => compiler.compile(expression, context));
  const answer = (expression: Extract<LiveExpression, { scope: unknown }>) => {
    // ENABLED compiles as an expression, cached by what the action reads.
    const built =
      expression.kind === "Enabled"
        ? compileIn(
            { kind: "Enabled", expression: expression.step, location: expression.step.location },
            expression.scope,
          )
        : compileIn(expression.expression, expression.scope);
    answers.set(expression, built);
    return built;
  };
  const answerUnchanged = (
    expression: Extract<LiveExpression, { kind: "Action" }>,
    unchanged: Expression,
  ) => {
    const built = compileIn(unchanged, expression.scope);
    unchangedAnswers.set(expression, built);
    return built;
  };
  // ENABLED <<A>>_v holds of a state the search ran TLC's actions from just when one of the steps
  // A takes changes v, which TLC's ENABLED, running A, finds in the same order.
  const getEdgeQuestion = (expression: LiveEnabled) => {
    const step = expression.step;
    const actions =
      graph.isEnabledExact && step.kind === "AngleAction" && getEnabledActions(expression);
    const unchanged =
      actions && (actions === "all" || graph.labels)
        ? compileIn(
            { kind: "Unchanged", expression: step.subscript, location: step.location },
            expression.scope,
          )
        : UNKNOWN;
    const question =
      !actions || unchanged === UNKNOWN
        ? UNKNOWN
        : {
            unchanged,
            actions:
              actions === "all"
                ? undefined
                : Uint8Array.from({ length: Math.max(...actions) + 1 }, (_, position) =>
                    actions.includes(position) ? 1 : 0,
                  ),
          };
    edgeQuestions.set(expression, question);
    if (!report.isReported && (question !== UNKNOWN || !graph.isEnabledExact)) {
      report.isReported = true;
      reportEngine(
        question === UNKNOWN
          ? "runs each action ENABLED asks about: its search evaluated conjuncts TLC's ENABLED walks"
          : "answers ENABLED from the steps its search took",
      );
    }
    return question;
  };

  // The ids of the states the checker asks about. It asks about a state many times in a row, so
  // the last lookup of each side of a step is kept.
  const ids = new Int32Array(width);
  const nextIds = new Int32Array(width);
  const edgeIds = new Int32Array(width);
  const lookups = {
    state: undefined as Value[] | undefined,
    index: undefined as number | undefined,
    next: undefined as Value[] | undefined,
    nextIndex: undefined as number | undefined,
  };
  const load = (target: Int32Array, index: number) => {
    const offset = index * width;
    for (let variable = 0; variable < width; variable++)
      target[variable] = states[offset + variable];
    return target;
  };
  const getStateIndex = (state: Value[]) => {
    if (state !== lookups.state) {
      lookups.state = state;
      lookups.index = getIndex(state);
      if (lookups.index !== undefined) load(ids, lookups.index);
    }
    return lookups.index;
  };
  const getNextIndex = (state: Value[]) => {
    if (state !== lookups.next) {
      lookups.next = state;
      lookups.nextIndex = getIndex(state);
      if (lookups.nextIndex !== undefined) load(nextIds, lookups.nextIndex);
    }
    return lookups.nextIndex;
  };

  const holds = (compiled: Compiled) => {
    const value = compiled.evaluate();
    return value === TRUE ? true : value === FALSE ? false : undefined;
  };

  // Whether a step from the state with the index that the question's action takes changes the
  // subscript, scanning the steps in the order generated.
  const holdsOnEdges = (question: EdgeQuestion, index: number) => {
    const edges = graph.edges;
    const labels = graph.labels;
    const actions = question.actions;
    const end = graph.edgeOffsets[index + 1];
    for (let edge = graph.edgeOffsets[index]; edge < end; edge++) {
      if (actions && actions[labels![edge]] !== 1) continue;
      setNext(load(edgeIds, edges[edge]));
      const isUnchanged = holds(question.unchanged);
      if (isUnchanged === undefined) return undefined;
      if (!isUnchanged) return true;
    }
    return false;
  };

  const ask = (
    expression: Extract<LiveExpression, { scope: unknown }>,
    successor: Value[] | undefined,
  ) => {
    try {
      setCurrent(ids);
      setNext(nextIds);
      if (expression.kind !== "Action") {
        const compiled = answers.get(expression) ?? answer(expression);
        return compiled === UNKNOWN ? undefined : holds(compiled);
      }
      if (!successor || getNextIndex(successor) === undefined) return undefined;
      setNext(nextIds);
      const unchangedExpression = expression.unchanged;
      if (unchangedExpression) {
        const unchanged =
          unchangedAnswers.get(expression) ?? answerUnchanged(expression, unchangedExpression);
        if (unchanged === UNKNOWN) return undefined;
        const isUnchanged = holds(unchanged);
        if (isUnchanged === undefined) return undefined;
        if (isUnchanged) return false;
      }
      const action = answers.get(expression) ?? answer(expression);
      return action === UNKNOWN ? undefined : holds(action);
    } catch (error) {
      if (error instanceof Bailout) return undefined;
      throw error;
    }
  };

  const askOnEdges = (expression: LiveEnabled, index: number) => {
    const question = edgeQuestions.get(expression) ?? getEdgeQuestion(expression);
    if (question === UNKNOWN) return undefined;
    try {
      setCurrent(ids);
      return holdsOnEdges(question, index);
    } catch (error) {
      if (error instanceof Bailout) return undefined;
      throw error;
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
    const index = getStateIndex(state);
    if (index === undefined) return undefined;
    if (expression.kind !== "Enabled" || index >= graph.expanded) {
      return ask(expression, successor);
    }
    const fromEdges = askOnEdges(expression, index);
    if (fromEdges !== undefined && !isLiveChecked) return fromEdges;
    const ran = ask(expression, undefined);
    if (fromEdges !== undefined && ran !== undefined && ran !== fromEdges) {
      throw new EngineInvariantError(
        "ENABLED from the steps the search took differs from ENABLED run",
      );
    }
    return fromEdges ?? ran;
  };
};

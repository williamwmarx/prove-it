// What a thread needs to explore a spec: the compiled initial predicate and next-state relation,
// and the compiled invariants and constraints. The coordinator and each worker build their own.

import { type Definition, type Expression, isLocallyResolved } from "../ast";
import type { ModelConfig } from "../config";
import { type Environment, type EvaluationScope, getDefinition } from "../evaluate";
import { compileAction, createEnabledTest, type Step } from "./action";
import { generateAction } from "./codegen";
import {
  type CompileContext,
  type Compiled,
  type Compiler,
  createCompiler,
  ROOT_CONTEXT,
} from "./compile";
import { getCodegenSetting, reportEngine } from "./settings";
import { bail, Bailout, FALSE, TRUE } from "./store";

export interface EngineSpec {
  init: Expression;
  next: Expression;
  // The bindings of the instance the specification comes from, when it names one.
  scope?: EvaluationScope;
  // TLC's actions of the next-state relation, as it splits it, for a search that labels each step
  // with the action that took it.
  actions?: { expression: Expression; scope: EvaluationScope | undefined }[];
}

// The temporal properties the engine checks as TLC does in its search: those that assert a state
// predicate always ([]P), an action always ([][A]_v), or a state predicate of the initial states.
export interface EngineProperties {
  invariants: Expression[];
  actionProperties: { action: Expression; subscript: Expression }[];
  initialPredicates: Expression[];
}

interface ScopedExpression {
  expression: Expression;
  scope: unknown;
}

// The properties of the reference search the engine checks, or undefined when one needs the scope
// of an instance, which the engine doesn't model.
export const toEngineProperties = (properties: {
  invariants: ScopedExpression[];
  actionProperties:
    | (ScopedExpression & { action: Expression; subscript: Expression })[]
    | { action: Expression; subscript: Expression; scope: unknown }[];
  initialPredicates: ScopedExpression[];
}): EngineProperties | undefined => {
  const all = [
    ...properties.invariants,
    ...properties.actionProperties,
    ...properties.initialPredicates,
  ];
  if (all.some((property) => property.scope !== undefined)) return undefined;
  return {
    invariants: properties.invariants.map((property) => property.expression),
    actionProperties: properties.actionProperties.map((property) => ({
      action: property.action,
      subscript: property.subscript,
    })),
    initialPredicates: properties.initialPredicates.map((property) => property.expression),
  };
};

export interface EngineContext {
  compiler: Compiler;
  width: number;
  initStep: Step;
  nextStep: Step;
  // A step for each of spec.actions, which together take the steps of nextStep in its order, or
  // undefined when the engine can't build one.
  actionSteps: Step[] | undefined;
  invariants: (() => boolean)[];
  // The invariants an initial state may violate: the others are conjuncts of the initial predicate,
  // so hold of every state it gives.
  initialInvariants: (() => boolean)[];
  constraints: (() => boolean)[];
  // The variables each invariant and constraint reads, for holdsAllChanged, or undefined for one
  // that reads names bound outside it, primed variables, or every variable.
  invariantVars: (Int32Array | undefined)[];
  constraintVars: (Int32Array | undefined)[];
  actionConstraints: (() => boolean)[];
  // Each holds of a step unless the action and the subscript's UNCHANGED are both false.
  actionProperties: (() => boolean)[];
  initialPredicates: (() => boolean)[];
  // The value a VIEW maps the current state to, which the search tells states apart by.
  view: (() => number) | undefined;
}

const identifier = (name: string): Expression => ({
  kind: "Identifier",
  name,
  location: { line: 0, column: 0 },
});

// The variables a state predicate reads, which decide its value: it reads only its footprint.
const getPredicateVars = (compiled: Compiled, width: number) => {
  const footprint = compiled.footprint;
  if (footprint.primes.length > 0 || footprint.slots.length > 0) return undefined;
  if (footprint.vars.length === width) return undefined;
  return Int32Array.from(footprint.vars);
};

// The expressions an expression asserts as conjuncts, through zero-arity definitions, resolved as
// the compiler resolves a name that nothing binds locally. A definition that reaches itself stays a
// conjunct, for the compiler to refuse.
const getConjuncts = (
  expression: Expression,
  environment: Environment,
  conjuncts = new Set<Expression>(),
  expanded = new Set<Definition>(),
  expanding = new Set<Definition>(),
) => {
  if (expression.kind === "And") {
    for (const operand of expression.operands)
      getConjuncts(operand, environment, conjuncts, expanded, expanding);
    return conjuncts;
  }
  const definition = getAssertedDefinition(expression, environment);
  if (!definition || expanding.has(definition)) conjuncts.add(expression);
  else if (!expanded.has(definition)) {
    expanded.add(definition);
    expanding.add(definition);
    getConjuncts(definition.body, environment, conjuncts, expanded, expanding);
    expanding.delete(definition);
  }
  return conjuncts;
};

const getAssertedDefinition = (expression: Expression, environment: Environment) => {
  if (expression.kind !== "Identifier" || isLocallyResolved(expression)) return undefined;
  const name = expression.name;
  if (environment.variableIndex.has(name) || environment.constants.has(name)) return undefined;
  const definition = getDefinition(name, environment);
  return definition?.kind === "Operator" && definition.params.length === 0 ? definition : undefined;
};

const compilePredicate = (compiled: Compiled) => {
  const evaluate = compiled.evaluate;
  return () => {
    const value = evaluate();
    if (value === TRUE) return true;
    if (value === FALSE) return false;
    return bail("a predicate that isn't a boolean");
  };
};

const buildStep = (
  compiler: Compiler,
  expression: Expression,
  context: CompileContext,
  isInit: boolean,
  isAssignedShortcut: boolean,
): { step: Step; isGenerated: boolean } => {
  const options = { isInit, isAssignedShortcut };
  const generated =
    getCodegenSetting() === "0"
      ? undefined
      : generateAction(compiler, expression, context, options);
  if (generated) return { step: generated, isGenerated: true };
  return { step: compileAction(compiler, expression, context, options), isGenerated: false };
};

// A compiler that tests ENABLED A by running A, as TLC does: without its shortcut once every
// variable is assigned.
export const createEngineCompiler = (environment: Environment): Compiler => {
  const compiler = createCompiler(environment);
  compiler.setEnabledCompiler((action, context) =>
    createEnabledTest(
      buildStep(compiler, action, context, false, false).step,
      compiler.variableCount,
    ),
  );
  return compiler;
};

export const createEngineContext = (
  environment: Environment,
  config: ModelConfig,
  spec: EngineSpec,
  isWarningEnabled: boolean,
  properties: EngineProperties,
): EngineContext => {
  const compiler = createEngineCompiler(environment);
  const width = environment.variables.length;
  const compileNamed = (kind: string, name: string) => {
    if (!getDefinition(name, environment)) return bail(`the ${kind} ${name} isn't defined`);
    return compiler.compile(identifier(name), ROOT_CONTEXT);
  };
  const named = (kind: string, name: string) => compilePredicate(compileNamed(kind, name));
  const specContext = compiler.contextFromScope(spec.scope);
  if (!specContext) return bail("a specification scope the engine can't translate");
  const buildAction = (expression: Expression, isInit: boolean, isAssignedShortcut: boolean) => {
    const context = isInit ? { ...specContext, isInit: true } : specContext;
    const step = buildStep(compiler, expression, context, isInit, isAssignedShortcut);
    if (!step.isGenerated) reportEngine(`${isInit ? "init" : "next"} runs as closures`);
    return step.step;
  };
  const getActionSteps = () => {
    try {
      return spec.actions?.map((action) => {
        const actionContext = compiler.contextFromScope(action.scope);
        if (!actionContext) return bail("an action scope the engine can't translate");
        return buildStep(compiler, action.expression, actionContext, false, isWarningEnabled).step;
      });
    } catch (error) {
      if (!(error instanceof Bailout)) throw error;
      return undefined;
    }
  };
  const predicate = (expression: Expression) =>
    compilePredicate(compiler.compile(expression, ROOT_CONTEXT));
  // Each invariant and constraint is checked conjunct by conjunct, so a successor skips each
  // conjunct that reads only variables its step left unchanged.
  const getAllConjuncts = (kind: string, names: string[], expressions: Expression[] = []) => [
    ...new Set(
      [
        ...names.map((name) => {
          if (!getDefinition(name, environment)) return bail(`the ${kind} ${name} isn't defined`);
          return identifier(name);
        }),
        ...expressions,
      ].flatMap((expression) => [...getConjuncts(expression, environment)]),
    ),
  ];
  const invariantConjuncts = getAllConjuncts("invariant", config.invariants, properties.invariants);
  const invariants = invariantConjuncts.map((conjunct) => compiler.compile(conjunct, ROOT_CONTEXT));
  // An initial predicate in an instance's scope resolves its names there, so it implies nothing.
  const initConjuncts =
    spec.scope === undefined ? getConjuncts(spec.init, environment) : new Set<Expression>();
  const actionProperties = properties.actionProperties.map((property) => {
    const action = predicate(property.action);
    const isUnchanged = predicate({
      kind: "Unchanged",
      expression: property.subscript,
      location: property.subscript.location,
    });
    return () => action() || isUnchanged();
  });
  const initialPredicates = properties.initialPredicates.map(predicate);
  const view =
    config.view === undefined
      ? undefined
      : compiler.compile(identifier(config.view), ROOT_CONTEXT).evaluate;
  const constraints = getAllConjuncts("constraint", config.constraints).map((conjunct) =>
    compiler.compile(conjunct, ROOT_CONTEXT),
  );
  return {
    compiler,
    width,
    invariants: invariants.map(compilePredicate),
    initialInvariants: invariants
      .filter((_, index) => !initConjuncts.has(invariantConjuncts[index]))
      .map(compilePredicate),
    invariantVars: invariants.map((compiled) => getPredicateVars(compiled, width)),
    actionProperties,
    initialPredicates,
    view,
    constraints: constraints.map(compilePredicate),
    constraintVars: constraints.map((compiled) => getPredicateVars(compiled, width)),
    actionConstraints: config.actionConstraints.map((name) => named("action constraint", name)),
    initStep: buildAction(spec.init, true, true),
    nextStep: buildAction(spec.next, false, isWarningEnabled),
    actionSteps: getActionSteps(),
  };
};

export const holdsAll = (predicates: (() => boolean)[]) => {
  for (let index = 0; index < predicates.length; index++) if (!predicates[index]()) return false;
  return true;
};

// Whether every predicate holds of the successor in the current register, given that each held of
// its parent: one that reads only variables the step left unchanged has the parent's value.
export const holdsAllChanged = (
  predicates: (() => boolean)[],
  vars: (Int32Array | undefined)[],
  successor: Int32Array,
  parent: Int32Array,
) => {
  for (let index = 0; index < predicates.length; index++) {
    const read = vars[index];
    if (read) {
      let isChanged = false;
      for (let position = 0; position < read.length; position++) {
        const variable = read[position];
        if (successor[variable] !== parent[variable]) {
          isChanged = true;
          break;
        }
      }
      if (!isChanged) continue;
    }
    if (!predicates[index]()) return false;
  }
  return true;
};

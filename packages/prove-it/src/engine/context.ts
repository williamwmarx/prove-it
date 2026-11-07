// What a thread needs to explore a spec: the compiled initial predicate and next-state relation,
// and the compiled invariants and constraints. The coordinator and each worker build their own.

import type { Expression } from "../ast";
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
import { bail, FALSE, TRUE } from "./store";

export interface EngineSpec {
  init: Expression;
  next: Expression;
  // The bindings of the instance the specification comes from, when it names one.
  scope?: EvaluationScope;
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
  invariants: (() => boolean)[];
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
  const predicate = (expression: Expression) =>
    compilePredicate(compiler.compile(expression, ROOT_CONTEXT));
  const invariants = [
    ...config.invariants.map((name) => compileNamed("invariant", name)),
    ...properties.invariants.map((expression) => compiler.compile(expression, ROOT_CONTEXT)),
  ];
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
  const constraints = config.constraints.map((name) => compileNamed("constraint", name));
  return {
    compiler,
    width,
    invariants: invariants.map(compilePredicate),
    invariantVars: invariants.map((compiled) => getPredicateVars(compiled, width)),
    actionProperties,
    initialPredicates,
    view,
    constraints: constraints.map(compilePredicate),
    constraintVars: constraints.map((compiled) => getPredicateVars(compiled, width)),
    actionConstraints: config.actionConstraints.map((name) => named("action constraint", name)),
    initStep: buildAction(spec.init, true, true),
    nextStep: buildAction(spec.next, false, isWarningEnabled),
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

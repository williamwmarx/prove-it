// What a thread needs to explore a spec: the compiled initial predicate and next-state relation,
// and the compiled invariants and constraints. The coordinator and each worker build their own.

import type { Expression } from "../ast";
import type { ModelConfig } from "../config";
import { type Environment, getDefinition } from "../evaluate";
import { compileAction, type Step } from "./action";
import { generateAction } from "./codegen";
import { type Compiled, createCompiler, ROOT_CONTEXT } from "./compile";
import { getCodegenSetting, reportEngine } from "./settings";
import { bail, FALSE, TRUE } from "./store";

export interface EngineSpec {
  init: Expression;
  next: Expression;
}

export interface EngineContext {
  width: number;
  initStep: Step;
  nextStep: Step;
  invariants: (() => boolean)[];
  constraints: (() => boolean)[];
  actionConstraints: (() => boolean)[];
}

const identifier = (name: string): Expression => ({
  kind: "Identifier",
  name,
  location: { line: 0, column: 0 },
});

const compilePredicate = (compiled: Compiled) => {
  const evaluate = compiled.evaluate;
  return () => {
    const value = evaluate();
    if (value === TRUE) return true;
    if (value === FALSE) return false;
    return bail("a predicate that isn't a boolean");
  };
};

export const createEngineContext = (
  environment: Environment,
  config: ModelConfig,
  spec: EngineSpec,
  isWarningEnabled: boolean,
): EngineContext => {
  const compiler = createCompiler(environment);
  const named = (kind: string, name: string) => {
    if (!getDefinition(name, environment)) return bail(`the ${kind} ${name} isn't defined`);
    return compilePredicate(compiler.compile(identifier(name), ROOT_CONTEXT));
  };
  const buildAction = (expression: Expression, isInit: boolean, isAssignedShortcut: boolean) => {
    const context = isInit ? { ...ROOT_CONTEXT, isInit: true } : ROOT_CONTEXT;
    const options = { isInit, isAssignedShortcut };
    const generated =
      getCodegenSetting() === "0"
        ? undefined
        : generateAction(compiler, expression, context, options);
    if (generated) return generated;
    reportEngine(`${isInit ? "init" : "next"} runs as closures`);
    return compileAction(compiler, expression, context, options);
  };
  return {
    width: environment.variables.length,
    invariants: config.invariants.map((name) => named("invariant", name)),
    constraints: config.constraints.map((name) => named("constraint", name)),
    actionConstraints: config.actionConstraints.map((name) => named("action constraint", name)),
    initStep: buildAction(spec.init, true, true),
    nextStep: buildAction(spec.next, false, isWarningEnabled),
  };
};

export const holdsAll = (predicates: (() => boolean)[]) => {
  for (let index = 0; index < predicates.length; index++) if (!predicates[index]()) return false;
  return true;
};

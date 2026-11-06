// The engine's breadth-first search. It explores states in TLC's order, counts them as TLC does,
// and reports a complete search. Anything else it meets (a violation, an error, a feature it
// doesn't implement) ends the run with a Bailout, and the reference interpreter checks the spec
// instead.

import type { Expression } from "../ast";
import type { CheckProgress } from "../check";
import type { ModelConfig } from "../config";
import { type Environment, getDefinition } from "../evaluate";
import { compileAction, resetAssigned, type Step } from "./action";
import { generateAction } from "./codegen";
import { type Compiled, createCompiler, ROOT_CONTEXT, setCurrent, setNext } from "./compile";
import { getStateFingerprints, resetFingerprints } from "./fingerprint";
import { getCodegenSetting, reportEngine } from "./settings";
import { bail, Bailout, FALSE, getValueCount, resetStore, TRUE } from "./store";

export interface EngineSpec {
  init: Expression;
  next: Expression;
}

export interface EngineInput {
  config: ModelConfig;
  environment: Environment;
  spec: EngineSpec;
  isWarningEnabled: boolean;
  tlcOrder: number[];
  onProgress: ((progress: CheckProgress) => void) | undefined;
  // Called once the initial states are computed, so the caller reports them.
  onInitialStates: (generated: number, distinct: number) => void;
  startedAt: number;
}

export interface EngineResult {
  generatedStates: number;
  distinctStates: number;
  depth: number;
  outDegrees: number[];
  initialStates: { generated: number; distinct: number };
  getFingerprints: () => BigInt64Array;
  valueCount: number;
}

const OUT_DEGREE_BUCKETS = 32;
const PROGRESS_INTERVAL = 60_000;

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

export const runEngine = (input: EngineInput): EngineResult => {
  const environment = input.environment;
  const config = input.config;
  resetStore();
  resetFingerprints();
  resetAssigned();
  const compiler = createCompiler(environment);
  const width = environment.variables.length;

  const named = (kind: string, name: string) => {
    const definition = getDefinition(name, environment);
    if (!definition) return bail(`the ${kind} ${name} isn't defined`);
    return compilePredicate(compiler.compile(identifier(name), ROOT_CONTEXT));
  };
  const invariants = config.invariants.map((name) => named("invariant", name));
  const constraints = config.constraints.map((name) => named("constraint", name));
  const actionConstraints = config.actionConstraints.map((name) =>
    named("action constraint", name),
  );

  const buildAction = (
    expression: Expression,
    isInit: boolean,
    isAssignedShortcut: boolean,
  ): Step => {
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
  const initStep = buildAction(input.spec.init, true, true);
  const nextStep = buildAction(input.spec.next, false, input.isWarningEnabled);

  // The states found so far, `width` ids each, in the order the search found them.
  let states = new Int32Array(Math.max(1, width) * 1024);
  let stateCount = 0;
  let parents = new Int32Array(1024);
  let table = new Int32Array(1 << 12).fill(-1);
  let tableMask = table.length - 1;

  const hashState = (source: Int32Array, offset: number) => {
    let hash = 0x811c9dc5;
    for (let index = 0; index < width; index++)
      hash = Math.imul(hash ^ source[offset + index], 0x01000193);
    hash ^= hash >>> 13;
    hash = Math.imul(hash, 0x5bd1e995);
    return hash ^ (hash >>> 15);
  };

  const growTable = () => {
    const next = new Int32Array(table.length * 2).fill(-1);
    const mask = next.length - 1;
    for (let state = 0; state < stateCount; state++) {
      let slot = hashState(states, state * width) & mask;
      while (next[slot] !== -1) slot = (slot + 1) & mask;
      next[slot] = state;
    }
    table = next;
    tableMask = mask;
  };

  // The slot of a state in the table: either the slot that holds it, or the empty one to put it in.
  const findSlot = (source: Int32Array) => {
    const hash = hashState(source, 0);
    for (let slot = hash & tableMask; ; slot = (slot + 1) & tableMask) {
      const stored = table[slot];
      if (stored === -1) return slot;
      const offset = stored * width;
      let isEqual = true;
      for (let index = 0; index < width; index++) {
        if (states[offset + index] !== source[index]) {
          isEqual = false;
          break;
        }
      }
      if (isEqual) return slot;
    }
  };

  const addState = (source: Int32Array, slot: number, parent: number) => {
    if ((stateCount + 1) * width > states.length) {
      const next = new Int32Array(states.length * 2);
      next.set(states);
      states = next;
    }
    if (stateCount >= parents.length) {
      const next = new Int32Array(parents.length * 2);
      next.set(parents);
      parents = next;
    }
    states.set(source, stateCount * width);
    parents[stateCount] = parent;
    table[slot] = stateCount;
    stateCount++;
    if (stateCount * 2 > table.length) growTable();
  };

  const holdsAll = (predicates: (() => boolean)[]) => {
    for (let index = 0; index < predicates.length; index++) if (!predicates[index]()) return false;
    return true;
  };

  let generated = 0;
  let initialGenerated = 0;
  let depth = 0;

  // --- initial states ---
  const current = new Int32Array(width).fill(-1);
  const next = new Int32Array(width).fill(-1);
  setCurrent(current);
  setNext(next);
  initStep(() => {
    for (let index = 0; index < width; index++)
      if (current[index] === -1) bail("an initial state that isn't complete");
    if (initialGenerated > 1 && (initialGenerated & (initialGenerated - 1)) === 0) {
      input.onProgress?.({ kind: "initial-states-progress", count: initialGenerated });
    }
    generated++;
    initialGenerated++;
    const isInModel = holdsAll(constraints);
    const slot = isInModel ? findSlot(current) : -1;
    if (isInModel && table[slot] !== -1) return;
    if (!holdsAll(invariants)) bail("an invariant violated in an initial state");
    if (!isInModel) return;
    addState(current, slot, -1);
    depth = 1;
  });
  const initialStates = { generated: initialGenerated, distinct: stateCount };
  input.onInitialStates(initialGenerated, stateCount);

  // --- next states ---
  const outDegrees = new Array<number>(OUT_DEGREE_BUCKETS).fill(0);
  let levelEnd = stateCount;
  let level = 1;
  let newStates = 0;
  let successors = 0;
  let expanding = 0;
  let progressAt = performance.now() + 3000;

  const visitSuccessor = () => {
    successors++;
    generated++;
    setCurrent(next);
    const isStateInModel = holdsAll(constraints);
    setCurrent(current);
    const isInModel = isStateInModel && holdsAll(actionConstraints);
    const slot = isInModel ? findSlot(next) : -1;
    const isNew = isInModel && table[slot] === -1;
    if (!isInModel || isNew) {
      setCurrent(next);
      const holds = holdsAll(invariants);
      setCurrent(current);
      if (!holds) bail("an invariant violated");
    }
    if (!isNew) return;
    addState(next, slot, expanding);
    newStates++;
    depth = level + 1;
  };

  for (expanding = 0; expanding < stateCount; expanding++) {
    if (expanding === levelEnd) {
      level++;
      levelEnd = stateCount;
    }
    current.set(states.subarray(expanding * width, (expanding + 1) * width));
    next.fill(-1);
    resetAssigned();
    newStates = 0;
    successors = 0;
    setCurrent(current);
    nextStep(() => {
      for (let index = 0; index < width; index++)
        if (next[index] === -1) bail("a successor that isn't complete");
      visitSuccessor();
    });
    if (successors === 0 && config.checkDeadlock) bail("deadlock");
    outDegrees[Math.min(newStates, OUT_DEGREE_BUCKETS - 1)]++;
    if ((expanding & 0xff) === 0 && input.onProgress && performance.now() >= progressAt) {
      progressAt = performance.now() + PROGRESS_INTERVAL;
      input.onProgress({
        kind: "progress",
        statistics: {
          generatedStates: generated,
          distinctStates: stateCount,
          queuedStates: stateCount - expanding - 1,
          depth: Math.max(depth, 1),
        },
      });
    }
  }

  return {
    generatedStates: generated,
    distinctStates: stateCount,
    depth: generated === 0 ? 0 : Math.max(depth, 1),
    outDegrees,
    initialStates,
    getFingerprints: () => getStateFingerprints(states, stateCount, width, input.tlcOrder),
    valueCount: getValueCount(),
  };
};

export const isBailout = (error: unknown): error is Bailout => error instanceof Bailout;

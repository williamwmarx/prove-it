import { TlaEvaluationError } from "./errors";
import { type Environment, hasRepeatedEffects } from "./evaluate";
import {
  createTautologyError,
  evaluateLive,
  evaluateOnLasso,
  type LiveCache,
  type ScopedExpression,
  type TemporalProperty,
  toLiveExpression,
} from "./liveness";
import {
  createJunction,
  createUnary,
  getSolutions,
  getTermKey,
  isFulfilling,
  type LiveEnabled,
  type LiveExpression,
  type Solution,
  type Tableau,
} from "./tableau";
import { isSameValue, type Value } from "./values";

export interface LiveSuccessor {
  index: number;
  state: Value[];
}

export interface Lasso {
  prefix: number[];
  cycle: number[];
  // Whether the solution that the lasso violates constrains the cycle, as a liveness property does.
  // TLC warns that a stuttering counterexample to one may come from a missing fairness constraint.
  isCycleConstrained: boolean;
}

export interface LivenessChecker {
  // How many solutions of the negated properties TLC checks, which it calls branches.
  branches: number;
  // With a tracing environment, the checks record their call stack as TLC's replay of a failed
  // check does.
  addInitialState: (index: number, state: Value[], tracing?: Environment) => void;
  addState: (
    index: number,
    state: Value[],
    successors: LiveSuccessor[],
    tracing?: Environment,
  ) => number[] | undefined;
  findViolation: () => Lasso | undefined;
  getViolatedProperties: (path: Value[][], cycleStart: number) => string[];
  // The ENABLED predicates the checks ask about.
  enabledAtoms: LiveEnabled[];
}

interface SearchGraph {
  getFingerprint: (successor: LiveSuccessor) => number;
  getSuccessors: (index: number, state: Value[]) => LiveSuccessor[];
}

// Numbers in a typed array that doubles as it fills, so a graph of millions of nodes takes a few
// bytes for each.
interface Pool<Data extends Int32Array | Int8Array | Uint8Array> {
  data: Data;
  length: number;
  create: (length: number) => Data;
}

// TLC's behavior graph for one solution: a node per state, or per state and tableau node.
interface BehaviorGraph {
  solution: Solution;
  // One id per distinct action check across the solutions.
  actionIds: Int32Array;
  nodeStates: number[];
  nodeTableaux: number[];
  // Where a node's edges start in edgeTargets, or UNWRITTEN until TLC writes the node with its
  // successors, and how many it has.
  edgeStarts: number[];
  edgeCounts: number[];
  edgeTargets: Pool<Int32Array>;
  // The step whose action checks hold on each edge, a row of the checker's steps, and the
  // results of the state checks on each state, which are the same for every node of the state.
  edgeSteps: Pool<Int32Array>;
  stateResults: Pool<Uint8Array>;
  // Whether the behaviors before this one have every action check of this one.
  isCovered: boolean;
  // Whether each state is consistent with each tableau node, as a KNOWN_ result once checked.
  consistency: Pool<Uint8Array>;
  initial: number[];
  // The nodes of each state in the order they are recorded, a list through nextSiblings.
  firstNodes: Pool<Int32Array>;
  lastNodes: Pool<Int32Array>;
  nextSiblings: number[];
  nodeIds: NodeTable;
  isDone: boolean[];
  errorNode: number | undefined;
}

// The results of the state predicates on the state at an offset of a pool, as a LiveCache.
interface IndexedCache extends LiveCache {
  offset: number;
}

const containsAlways = (expression: LiveExpression): boolean => {
  switch (expression.kind) {
    case "Always":
      return true;
    case "Eventually":
    case "Not":
    case "Next":
      return containsAlways(expression.body);
    case "And":
    case "Or":
      return expression.operands.some(containsAlways);
    default:
      return false;
  }
};

// The state predicates whose results evaluateLive keeps in the cache of the state it evaluates.
// The body of a Next is evaluated on the next state, with a cache of its own.
const collectAtoms = (expression: LiveExpression, atoms: Map<LiveExpression, number>) => {
  switch (expression.kind) {
    case "State":
    case "Enabled":
      if (!atoms.has(expression)) atoms.set(expression, atoms.size);
      return;
    case "Action":
      if (expression.enabled) collectAtoms(expression.enabled, atoms);
      return;
    case "Not":
    case "Always":
    case "Eventually":
      collectAtoms(expression.body, atoms);
      return;
    case "And":
    case "Or":
      for (const operand of expression.operands) collectAtoms(operand, atoms);
      return;
    default:
      return;
  }
};

// TLC's OrderOfSolution#hasEmptyPEMAndBoxFreePromises, negated.
const isCycleConstrained = (solution: Solution) =>
  solution.promises.some((promise) => containsAlways(promise.body)) ||
  solution.models.some(
    (model) =>
      model.eventuallyAlways.length > 0 ||
      model.infinitelyOftenStates.length > 0 ||
      model.infinitelyOftenActions.length > 0,
  );

const isSameState = (left: Value[], right: Value[]) =>
  left.every((value, position) => isSameValue(value, right[position]));

const removeRepeats = (path: number[]) =>
  path.filter((node, position) => position === 0 || path[position - 1] !== node);

const createPool = <Data extends Int32Array | Int8Array | Uint8Array>(
  create: (length: number) => Data,
): Pool<Data> => ({ data: create(1024), length: 0, create });

const reservePool = <Data extends Int32Array | Int8Array | Uint8Array>(
  pool: Pool<Data>,
  end: number,
) => {
  if (end > pool.data.length) {
    const data = pool.create(Math.max(2 * pool.data.length, end));
    data.set(pool.data);
    pool.data = data;
  }
  pool.length = Math.max(pool.length, end);
};

const writeToPool = <Data extends Int32Array | Uint8Array>(
  pool: Pool<Data>,
  offset: number,
  values: ArrayLike<number>,
) => {
  reservePool(pool, offset + values.length);
  pool.data.set(values, offset);
};

const createBytes = (length: number) => new Uint8Array(length);

// A typed array that the checks of each state reuse, of at least the length.
const getScratch = <Data extends Int32Array | Int8Array | Uint8Array>(
  pool: Pool<Data>,
  length: number,
) => {
  reservePool(pool, length);
  return pool.data;
};

const NO_NODE = -1;

// A Map holds at most 2^24 entries, so each tableau node of a state finds its node in an
// open-addressing table of (state plus one, tableau node, node) triples.
interface NodeTable {
  slots: Int32Array;
  size: number;
  shift: number;
}

const getNodeSlot = (table: NodeTable, state: number, tableauNode: number) => {
  const mask = table.slots.length / 3 - 1;
  const hash = Math.imul(Math.imul(state, 0x9e3779b1) ^ tableauNode, 0x85ebca6b) >>> table.shift;
  for (let index = hash; ; index = (index + 1) & mask) {
    const slot = index * 3;
    const stored = table.slots[slot];
    if (stored === 0 || (stored === state + 1 && table.slots[slot + 1] === tableauNode)) {
      return slot;
    }
  }
};

const createNodes = (length: number) => new Int32Array(length).fill(NO_NODE);

const UNWRITTEN = -1;

const isWritten = (behavior: BehaviorGraph, node: number) =>
  (behavior.edgeStarts[node] ?? UNWRITTEN) !== UNWRITTEN;

// The first of a node's edges that leads back to the node, or -1.
const findSelfEdge = (behavior: BehaviorGraph, node: number) => {
  const start = behavior.edgeStarts[node];
  const targets = behavior.edgeTargets.data;
  for (let edge = 0; edge < behavior.edgeCounts[node]; edge++) {
    if (targets[start + edge] === node) return edge;
  }
  return -1;
};

const getNodeSuccessors = (behavior: BehaviorGraph, node: number) => {
  const start = behavior.edgeStarts[node];
  return behavior.edgeTargets.data.subarray(start, start + behavior.edgeCounts[node]);
};

const getStateResult = (behavior: BehaviorGraph, node: number, position: number) =>
  behavior.stateResults.data[
    behavior.nodeStates[node] * behavior.solution.stateChecks.length + position
  ] === 1;

// A node owns one entry in each per-node array of its graph.
const pushNode = (behavior: BehaviorGraph, state: number, tableauNode: number) => {
  behavior.nodeStates.push(state);
  behavior.nodeTableaux.push(tableauNode);
  behavior.edgeStarts.push(UNWRITTEN);
  behavior.edgeCounts.push(0);
  behavior.nextSiblings.push(NO_NODE);
  return behavior.nodeStates.length - 1;
};

const SUCCESSOR_CAPACITY = 16;

const SCC_MARKER = -42;

const UNVISITED = -1;

const MAXIMUM_LINK = 0x7fffffff;

// A check's result as the memos keep it: not checked yet, false or true.
const UNKNOWN_RESULT = 0;
const KNOWN_FALSE = 1;
const KNOWN_TRUE = 2;

// Whether the state decides an action check for every step: not known yet, or no, as the results
// 0 and 1 are yes.
const UNDECIDED = -1;
const STEP_DECIDES = 2;

export const createLivenessChecker = (
  properties: TemporalProperty[],
  temporals: ScopedExpression[],
  environment: Environment,
  search: SearchGraph,
): LivenessChecker | undefined => {
  if (properties.length === 0) return undefined;
  const fairness = temporals.map((item) =>
    toLiveExpression(item.expression, item.scope, environment),
  );
  const negations = properties.map((property) =>
    createUnary("Not", toLiveExpression(property.expression, property.scope, environment)),
  );
  const violation = negations.length === 1 ? negations[0] : createJunction("Or", negations);
  const formula =
    fairness.length === 0 ? violation : createJunction("And", [...fairness, violation]);
  const solutions = getSolutions(formula);
  if (solutions.length === 0) {
    throw createTautologyError();
  }
  const actionIds = new Map<string, number>();
  const behaviors = solutions.map((solution): BehaviorGraph => ({
    solution,
    actionIds: Int32Array.from(solution.actionChecks, (predicate) => {
      const key = getTermKey(predicate);
      const id = actionIds.get(key) ?? actionIds.size;
      actionIds.set(key, id);
      return id;
    }),
    nodeStates: [],
    nodeTableaux: [],
    edgeStarts: [],
    edgeCounts: [],
    edgeTargets: createPool((length) => new Int32Array(length)),
    edgeSteps: createPool((length) => new Int32Array(length)),
    stateResults: createPool(createBytes),
    consistency: createPool(createBytes),
    initial: [],
    firstNodes: createPool(createNodes),
    lastNodes: createPool(createNodes),
    nextSiblings: [],
    nodeIds: { slots: new Int32Array(3 << 10), size: 0, shift: 22 },
    isDone: [],
    errorNode: undefined,
    isCovered: false,
  }));
  behaviors.forEach((behavior, position) => {
    const earlier = new Set(behaviors.slice(0, position).flatMap((other) => [...other.actionIds]));
    behavior.isCovered = behavior.actionIds.every((id) => earlier.has(id));
  });
  const atomIds = new Map<LiveExpression, number>();
  for (const solution of solutions) {
    for (const predicate of [...solution.stateChecks, ...solution.actionChecks]) {
      collectAtoms(predicate, atomIds);
    }
    for (const node of solution.tableau?.nodes ?? []) {
      for (const predicate of node.statePredicates) collectAtoms(predicate, atomIds);
    }
  }
  const capacity = { multiplier: 1 };
  // The results of the action checks on each step the checker has seen, a row of action ids per
  // step: -1 until checked, then 0 or 1.
  const steps = { results: createPool((length) => new Int8Array(length)), count: 0 };
  const addSteps = (count: number) => {
    const first = steps.count;
    steps.count += count;
    reservePool(steps.results, steps.count * actionIds.size);
    steps.results.data.fill(-1, first * actionIds.size, steps.count * actionIds.size);
    return first;
  };
  const scratch = {
    decided: createPool((length) => new Int8Array(length)),
    consistency: createPool(createBytes),
    rows: createPool((length) => new Int32Array(length)),
  };

  // TLC evaluates every check on its own. Without side effects the order can't show, so the
  // checks of one state share their results, across the states the checker adds as long as no
  // evaluation records its call stack.
  const isShared = !hasRepeatedEffects(environment);
  const evaluation = { environment, isMemoized: isShared };
  const shared = {
    states: new Map<Value[], Map<LiveExpression, boolean>>(),
    actions: new Map<Value[], Map<Value[], number>>(),
  };
  // The state each index stands for, and the results of the state predicates on it.
  const memo = {
    states: [] as (Value[] | undefined)[],
    atoms: createPool(createBytes),
  };
  const atomCache: IndexedCache = {
    offset: 0,
    get: (expression) => {
      const id = atomIds.get(expression);
      const result = id === undefined ? UNKNOWN_RESULT : memo.atoms.data[atomCache.offset + id];
      return result === UNKNOWN_RESULT ? undefined : result === KNOWN_TRUE;
    },
    set: (expression, result) => {
      const id = atomIds.get(expression);
      if (id !== undefined) {
        memo.atoms.data[atomCache.offset + id] = result ? KNOWN_TRUE : KNOWN_FALSE;
      }
    },
  };
  const getStateCache = (state: Value[]) => {
    const cache = shared.states.get(state) ?? new Map<LiveExpression, boolean>();
    shared.states.set(state, cache);
    return cache;
  };
  // Whether the checks of the state with the index keep their results across the states the
  // checker adds. A state the search rebuilt the same is another array, which the checks see anew.
  const isMemoized = (index: number, state: Value[]) => {
    if (!evaluation.isMemoized || index < 0) return false;
    const known = memo.states[index];
    if (known !== undefined) return known === state;
    while (memo.states.length < index) memo.states.push(undefined);
    memo.states[index] = state;
    return true;
  };
  const getCache = (index: number, state: Value[]): LiveCache => {
    if (!isMemoized(index, state)) return isShared ? getStateCache(state) : new Map();
    reservePool(memo.atoms, (index + 1) * atomIds.size);
    atomCache.offset = index * atomIds.size;
    return atomCache;
  };
  // TLCGet("level") reads the level of the state whose successors the checks run on.
  const checkState = (behavior: BehaviorGraph, index: number, state: Value[]) => {
    const predicates = behavior.solution.stateChecks;
    const results = new Uint8Array(predicates.length);
    environment.runtime.setLivenessSource(index);
    for (let position = 0; position < predicates.length; position++) {
      const cache = getCache(index, state);
      results[position] = evaluateLive(
        predicates[position],
        state,
        undefined,
        evaluation.environment,
        cache,
      )
        ? 1
        : 0;
    }
    environment.runtime.setLivenessSource(undefined);
    return results;
  };
  // The result of an action check that the state decides whatever the step, since evaluateLive
  // reaches no action or next state before it knows the result, or undefined.
  const evaluateOnState = (
    expression: LiveExpression,
    state: Value[],
    cache: LiveCache,
  ): boolean | undefined => {
    switch (expression.kind) {
      case "Boolean":
        return expression.value;
      case "State":
      case "Enabled":
        return evaluateLive(expression, state, undefined, evaluation.environment, cache);
      case "Action":
        return expression.enabled && cache.get(expression.enabled) === false ? false : undefined;
      case "Not": {
        const body = evaluateOnState(expression.body, state, cache);
        return body === undefined ? undefined : !body;
      }
      case "And":
      case "Or": {
        const isAnd = expression.kind === "And";
        for (const operand of expression.operands) {
          const result = evaluateOnState(operand, state, cache);
          if (result === undefined) return undefined;
          if (result !== isAnd) return result;
        }
        return isAnd;
      }
      default:
        return undefined;
    }
  };
  // The action checks of a behavior on a step, into the step's row. Without repeated effects, the
  // behaviors share the results of the checks they have in common through the row, and decided
  // keeps the results that the state decides, by action id, for the steps of one state.
  const checkStep = (
    behavior: BehaviorGraph,
    source: number,
    state: Value[],
    successor: Value[],
    step: number,
    decided: Int8Array | undefined,
  ) => {
    const predicates = behavior.solution.actionChecks;
    const row = step * actionIds.size;
    environment.runtime.setLivenessSource(source);
    for (let position = 0; position < predicates.length; position++) {
      const id = behavior.actionIds[position];
      if (steps.results.data[row + id] !== -1) continue;
      if (decided && decided[id] === UNDECIDED) {
        const result = evaluateOnState(predicates[position], state, getCache(source, state));
        decided[id] = result === undefined ? STEP_DECIDES : result ? 1 : 0;
      }
      const isHeld =
        decided && decided[id] !== STEP_DECIDES
          ? decided[id] === 1
          : evaluateLive(
              predicates[position],
              state,
              successor,
              evaluation.environment,
              isShared ? getCache(source, state) : new Map(),
            );
      steps.results.data[row + id] = isHeld ? 1 : 0;
    }
    environment.runtime.setLivenessSource(undefined);
  };
  // The row of a step that a node found late checks, which the checks of the state share.
  const checkAction = (
    behavior: BehaviorGraph,
    source: number,
    state: Value[],
    successor: Value[],
  ) => {
    if (!isShared) {
      const step = addSteps(1);
      checkStep(behavior, source, state, successor, step, undefined);
      return step;
    }
    const successors = shared.actions.get(state) ?? new Map<Value[], number>();
    shared.actions.set(state, successors);
    const step = successors.get(successor) ?? addSteps(1);
    successors.set(successor, step);
    checkStep(behavior, source, state, successor, step, undefined);
    return step;
  };
  const isConsistent = (
    behavior: BehaviorGraph,
    tableau: Tableau,
    node: number,
    source: number | undefined,
    index: number,
    state: Value[],
  ) => {
    const slot = index * tableau.nodes.length + node;
    const isKept = isMemoized(index, state);
    if (isKept) {
      reservePool(behavior.consistency, slot + 1);
      const known = behavior.consistency.data[slot];
      if (known !== UNKNOWN_RESULT) return known === KNOWN_TRUE;
    }
    environment.runtime.setLivenessSource(source);
    const isHeld = tableau.nodes[node].statePredicates.every((predicate) =>
      evaluateLive(predicate, state, undefined, evaluation.environment, getCache(index, state)),
    );
    environment.runtime.setLivenessSource(undefined);
    if (isKept) behavior.consistency.data[slot] = isHeld ? KNOWN_TRUE : KNOWN_FALSE;
    return isHeld;
  };
  // TLC 1.7.4 doesn't stop at a tableau node that accepts every behavior, so it finds a violation
  // of a property like a safety property only in its liveness checks.
  const isAccepting = (tableau: Tableau, node: number) => {
    if (environment.runtime.version === "1.7.4") return false;
    const tableauNode = tableau.nodes[node];
    return (
      tableauNode.particle.length === 0 &&
      tableauNode.successors.length === 1 &&
      tableauNode.successors[0] === node
    );
  };
  const hasEmptyModel = (behavior: BehaviorGraph) =>
    behavior.solution.models.some(
      (model) =>
        model.eventuallyAlways.length === 0 &&
        model.infinitelyOftenStates.length === 0 &&
        model.infinitelyOftenActions.length === 0,
    );

  const getNodeId = (behavior: BehaviorGraph, state: number, tableauNode: number) => {
    if (!behavior.solution.tableau) return state;
    const slots = behavior.nodeIds.slots;
    const slot = getNodeSlot(behavior.nodeIds, state, tableauNode);
    return slots[slot] === 0 ? undefined : slots[slot + 2];
  };
  const recordNode = (behavior: BehaviorGraph, state: number, tableauNode: number) => {
    const node = pushNode(behavior, state, tableauNode);
    const table = behavior.nodeIds;
    if (++table.size * 2 > table.slots.length / 3) {
      const old = table.slots;
      table.slots = new Int32Array(old.length * 2);
      table.shift--;
      for (let slot = 0; slot < old.length; slot += 3) {
        if (old[slot] !== 0) {
          table.slots.set(
            old.subarray(slot, slot + 3),
            getNodeSlot(table, old[slot] - 1, old[slot + 1]),
          );
        }
      }
    }
    const slot = getNodeSlot(table, state, tableauNode);
    table.slots[slot] = state + 1;
    table.slots[slot + 1] = tableauNode;
    table.slots[slot + 2] = node;
    const last = behavior.lastNodes.data[state] ?? NO_NODE;
    if (last === NO_NODE) {
      reservePool(behavior.firstNodes, state + 1);
      behavior.firstNodes.data[state] = node;
    } else {
      behavior.nextSiblings[last] = node;
    }
    reservePool(behavior.lastNodes, state + 1);
    behavior.lastNodes.data[state] = node;
    return node;
  };
  // Writes a node's edges and the step of each.
  const writeNode = (
    behavior: BehaviorGraph,
    node: number,
    targets: number[],
    edgeSteps: number[],
    stateResults: Uint8Array,
  ) => {
    const start = behavior.edgeTargets.length;
    writeToPool(behavior.edgeTargets, start, targets);
    writeToPool(behavior.edgeSteps, start, edgeSteps);
    writeToPool(
      behavior.stateResults,
      behavior.nodeStates[node] * stateResults.length,
      stateResults,
    );
    behavior.edgeStarts[node] = start;
    behavior.edgeCounts[node] = targets.length;
  };

  // TLC collects a state's successors and the state itself in a SetOfStates, a hash set it
  // iterates in slot order. Its capacity starts at 16 times a factor that grows with every set
  // that outgrows it.
  const getSuccessorSet = (index: number, state: Value[], successors: LiveSuccessor[]) => {
    const table = {
      slots: new Array<LiveSuccessor | undefined>(SUCCESSOR_CAPACITY * capacity.multiplier).fill(
        undefined,
      ),
      count: 0,
    };
    const insertSuccessor = (slots: (LiveSuccessor | undefined)[], successor: LiveSuccessor) => {
      for (
        let slot = (search.getFingerprint(successor) & 0x7fffffff) % slots.length;
        ;
        slot = (slot + 1) % slots.length
      ) {
        const entry = slots[slot];
        if (entry === undefined) {
          slots[slot] = successor;
          return true;
        }
        if (entry.index === successor.index && isSameState(entry.state, successor.state))
          return false;
      }
    };
    const addSuccessor = (successor: LiveSuccessor) => {
      if (table.count >= table.slots.length >> 1) {
        const old = table.slots;
        table.slots = new Array<LiveSuccessor | undefined>(2 * old.length + 1).fill(undefined);
        for (const entry of old) if (entry) insertSuccessor(table.slots, entry);
      }
      if (insertSuccessor(table.slots, successor)) table.count++;
    };
    successors.forEach(addSuccessor);
    addSuccessor({ index, state });
    if (table.slots.length > SUCCESSOR_CAPACITY * capacity.multiplier) capacity.multiplier++;
    return table.slots.filter((entry): entry is LiveSuccessor => entry !== undefined);
  };

  // TLC's TableauLiveChecker#addNextState for a node it finds after it expanded the node's state.
  const expandLate = (
    behavior: BehaviorGraph,
    tableau: Tableau,
    state: Value[],
    index: number,
    node: number,
  ) => {
    const stateResults = checkState(behavior, index, state);
    const tableauNode = tableau.nodes[behavior.nodeTableaux[node]];
    const edgeSteps: number[] = [];
    const successors: number[] = [];
    const selfStep =
      tableauNode.successors.length > 0 ? checkAction(behavior, index, state, state) : -1;
    for (const next of tableauNode.successors) {
      if (!isConsistent(behavior, tableau, next, index, index, state)) continue;
      if (
        isAccepting(tableau, next) &&
        behavior.errorNode === undefined &&
        hasEmptyModel(behavior)
      ) {
        behavior.errorNode = node;
        return;
      }
      const existing = getNodeId(behavior, index, next);
      if (existing !== undefined && successors.includes(existing)) continue;
      const target = existing ?? recordNode(behavior, index, next);
      successors.push(target);
      edgeSteps.push(selfStep);
      if (existing === undefined) expandLate(behavior, tableau, state, index, target);
    }
    for (const successor of search.getSuccessors(index, state)) {
      const successorStep = checkAction(behavior, index, state, successor.state);
      const isDone = behavior.isDone[successor.index] === true;
      for (const next of tableauNode.successors) {
        if (!isConsistent(behavior, tableau, next, index, successor.index, successor.state)) {
          continue;
        }
        // A successor the search never stored follows a violation or an error, after which nothing
        // checks the graph. TLC records its node, which it never expands.
        if (successor.index === -1) continue;
        const existing = getNodeId(behavior, successor.index, next);
        if (existing !== undefined && successors.includes(existing)) continue;
        const target = existing ?? recordNode(behavior, successor.index, next);
        successors.push(target);
        edgeSteps.push(successorStep);
        if (existing === undefined && isDone) {
          expandLate(behavior, tableau, successor.state, successor.index, target);
        }
      }
    }
    if (successors.length > 0) writeNode(behavior, node, successors, edgeSteps, stateResults);
  };

  const addTableauState = (
    behavior: BehaviorGraph,
    tableau: Tableau,
    set: LiveSuccessor[],
    firstStep: number,
    stateResults: Uint8Array,
    index: number,
  ) => {
    const nodeCount = tableau.nodes.length;
    const consistency = getScratch(scratch.consistency, nodeCount * set.length);
    // Where each successor's known consistency starts, or -1 for one checked anew.
    const rows = getScratch(scratch.rows, set.length);
    for (let position = 0; position < set.length; position++) {
      const successor = set[position];
      const isKept = isMemoized(successor.index, successor.state);
      if (isKept) reservePool(behavior.consistency, (successor.index + 1) * nodeCount);
      rows[position] = isKept ? successor.index * nodeCount : -1;
    }
    for (let node = 0; node < nodeCount; node++) {
      for (let position = 0; position < set.length; position++) {
        const known =
          rows[position] === -1 ? UNKNOWN_RESULT : behavior.consistency.data[rows[position] + node];
        const successor = set[position];
        const isHeld =
          known === UNKNOWN_RESULT
            ? isConsistent(behavior, tableau, node, index, successor.index, successor.state)
            : known === KNOWN_TRUE;
        consistency[node * set.length + position] = isHeld ? 1 : 0;
      }
    }
    behavior.isDone[index] = true;
    // TLC expands the nodes recorded before the loop, not the ones the loop records.
    const last = behavior.lastNodes.data[index] ?? NO_NODE;
    for (
      let node = last === NO_NODE ? NO_NODE : behavior.firstNodes.data[index];
      node !== NO_NODE;
      node = node === last ? NO_NODE : behavior.nextSiblings[node]
    ) {
      const successors: number[] = [];
      const edgeSteps: number[] = [];
      const tableauSuccessors = tableau.nodes[behavior.nodeTableaux[node]].successors;
      for (let position = 0; position < set.length; position++) {
        const successor = set[position];
        const isDone = behavior.isDone[successor.index] === true;
        for (const next of tableauSuccessors) {
          if (consistency[next * set.length + position] === 0) continue;
          const existing = getNodeId(behavior, successor.index, next);
          if (existing !== undefined && successors.includes(existing)) continue;
          const target = existing ?? recordNode(behavior, successor.index, next);
          successors.push(target);
          edgeSteps.push(firstStep + position);
          if (existing === undefined && isDone) {
            expandLate(behavior, tableau, successor.state, successor.index, target);
          }
        }
      }
      writeNode(behavior, node, successors, edgeSteps, stateResults);
    }
    if (behavior.errorNode === undefined) return undefined;
    return removeRepeats(
      getPath(behavior, behavior.errorNode)
        .reverse()
        .map((node) => behavior.nodeStates[node]),
    );
  };

  const addPlainState = (
    behavior: BehaviorGraph,
    set: LiveSuccessor[],
    firstStep: number,
    stateResults: Uint8Array,
    index: number,
  ) => {
    while (behavior.nodeStates.length <= index) pushNode(behavior, behavior.nodeStates.length, -1);
    const successors: number[] = [];
    const edgeSteps: number[] = [];
    set.forEach((successor, position) => {
      if (isWritten(behavior, successor.index) && successors.includes(successor.index)) return;
      successors.push(successor.index);
      edgeSteps.push(firstStep + position);
    });
    writeNode(behavior, index, successors, edgeSteps, stateResults);
  };

  // The shortest path from an initial node to the node, last node first, as TLC's getPath finds it.
  const getPath = (behavior: BehaviorGraph, target: number) => {
    if (behavior.initial.includes(target)) return [target];
    const parents = new Map<number, number>();
    const queue: number[] = [];
    for (const node of behavior.initial) {
      if (!isWritten(behavior, node)) continue;
      queue.push(node);
      parents.set(node, -1);
    }
    for (let position = 0; position < queue.length; position++) {
      const current = queue[position];
      for (const next of getNodeSuccessors(behavior, current)) {
        if (next === current && behavior.solution.tableau) continue;
        if (next === target) {
          const path = [target];
          for (let node = current; node !== -1; node = parents.get(node) ?? -1) path.push(node);
          return path;
        }
        if (!isWritten(behavior, next) || parents.has(next)) continue;
        parents.set(next, current);
        queue.push(next);
      }
    }
    throw new TlaEvaluationError(`Couldn't re-create liveness trace (path) starting at: ${target}`);
  };

  // TLC's LiveWorker#checkSccs, a Tarjan search that pushes every successor of a node at once.
  const findLassoInModel = (
    behavior: BehaviorGraph,
    model: Solution["models"][number],
  ): Lasso | undefined => {
    const solution = behavior.solution;
    const edgeStarts = behavior.edgeStarts;
    const edgeCounts = behavior.edgeCounts;
    const edgeTargets = behavior.edgeTargets.data;
    const edgeSteps = behavior.edgeSteps.data;
    const results = steps.results.data;
    const nodeCount = behavior.nodeStates.length;
    const getAction = (node: number, edge: number, position: number) =>
      results[
        edgeSteps[edgeStarts[node] + edge] * actionIds.size + behavior.actionIds[position]
      ] === 1;
    const allowedIds = model.eventuallyAlways.map((position) => behavior.actionIds[position]);
    const isAllowed = (node: number, edge: number) => {
      const row = edgeSteps[edgeStarts[node] + edge] * actionIds.size;
      for (const id of allowedIds) if (results[row + id] !== 1) return false;
      return true;
    };
    const links = new Int32Array(nodeCount).fill(UNVISITED);
    const queue = behavior.initial.filter((node) => isWritten(behavior, node));
    const components: number[] = [];
    // The members of the component being checked, in the order they leave the stack, and a mark
    // for each node of the component it last belonged to.
    const members: number[] = [];
    const memberMarks = new Int32Array(nodeCount);
    const mark = { component: 0 };
    const isMember = (node: number) => memberMarks[node] === mark.component;
    // Whether each tableau node fulfills each promise.
    const tableauNodes = solution.tableau?.nodes ?? [];
    const fulfilling = new Uint8Array(tableauNodes.length * solution.promises.length);
    tableauNodes.forEach((tableauNode, position) =>
      solution.promises.forEach((promise, promiseIndex) => {
        fulfilling[position * solution.promises.length + promiseIndex] = isFulfilling(
          tableauNode.particle,
          promise,
        )
          ? 1
          : 0;
      }),
    );
    const isFulfilled = (node: number, promiseIndex: number) =>
      solution.tableau !== undefined &&
      fulfilling[behavior.nodeTableaux[node] * solution.promises.length + promiseIndex] === 1;

    const isStuttering = (node: number) => {
      const edge = findSelfEdge(behavior, node);
      return edge !== -1 && isAllowed(node, edge);
    };
    const isStateSatisfied = (position: number) => {
      for (const node of members) if (getStateResult(behavior, node, position)) return true;
      return false;
    };
    // Whether the component's edges that stay in it take every action that the model requires
    // infinitely often, in one pass over the edges.
    const satisfiedActions = new Uint8Array(model.infinitelyOftenActions.length);
    const isActionSatisfied = () => {
      satisfiedActions.fill(0);
      const remaining = { count: satisfiedActions.length };
      for (const node of members) {
        const start = edgeStarts[node];
        for (let edge = 0; edge < edgeCounts[node] && remaining.count > 0; edge++) {
          if (!isMember(edgeTargets[start + edge]) || !isAllowed(node, edge)) continue;
          for (let slot = 0; slot < satisfiedActions.length; slot++) {
            if (
              satisfiedActions[slot] === 0 &&
              getAction(node, edge, model.infinitelyOftenActions[slot])
            ) {
              satisfiedActions[slot] = 1;
              remaining.count--;
            }
          }
        }
      }
      return remaining.count === 0;
    };
    const isPromiseSatisfied = (promiseIndex: number) => {
      for (const node of members) if (isFulfilled(node, promiseIndex)) return true;
      return false;
    };

    const checkComponent = (root: number) => {
      const top = components.pop() ?? root;
      if (top === root && !isStuttering(top)) {
        links[top] = MAXIMUM_LINK;
        return undefined;
      }
      members.length = 0;
      mark.component++;
      for (let member = top; ; member = components.pop() ?? root) {
        members.push(member);
        memberMarks[member] = mark.component;
        links[member] = MAXIMUM_LINK;
        if (member === root) break;
      }
      if (!model.infinitelyOftenStates.every(isStateSatisfied)) return undefined;
      if (!isActionSatisfied()) return undefined;
      if (!solution.promises.every((_, promiseIndex) => isPromiseSatisfied(promiseIndex))) {
        return undefined;
      }
      const membersByState = new Map<number, number[]>();
      for (const member of members) {
        const siblings = membersByState.get(behavior.nodeStates[member]);
        if (siblings) siblings.push(member);
        else membersByState.set(behavior.nodeStates[member], [member]);
      }
      return getLasso(root, membersByState);
    };

    // TLC's LiveWorker#printTrace: a prefix to the root, a greedy walk through the component
    // until it satisfies every check, and a breadth-first path back to the root.
    const getLasso = (root: number, membersByState: Map<number, number[]>) => {
      const prefix = removeRepeats(
        getPath(behavior, root)
          .reverse()
          .map((node) => behavior.nodeStates[node]),
      );
      const cycleStack: number[] = [];
      const seen = new Set<number>([root]);
      const stateDone = model.infinitelyOftenStates.map(() => false);
      const actionDone = model.infinitelyOftenActions.map(() => false);
      const promiseDone = solution.promises.map(() => false);
      const remaining = { count: stateDone.length + actionDone.length + promiseDone.length };
      const current = { node: root };
      const moveTo = (next: number) => {
        cycleStack.push(current.node);
        current.node = next;
      };
      while (remaining.count > 0) {
        const countAtStart = remaining.count;
        while (true) {
          model.infinitelyOftenStates.forEach((position, slot) => {
            if (!stateDone[slot] && getStateResult(behavior, current.node, position)) {
              stateDone[slot] = true;
              remaining.count--;
            }
          });
          solution.promises.forEach((_, position) => {
            if (!promiseDone[position] && isFulfilled(current.node, position)) {
              promiseDone[position] = true;
              remaining.count--;
            }
          });
          if (remaining.count <= 0) break;
          const step = { last: -1, unvisited: -1 };
          const countBeforeActions = remaining.count;
          const taken = getNodeSuccessors(behavior, current.node).some((next, edge) => {
            if (membersByState.has(behavior.nodeStates[next])) {
              if (!isMember(next) || !isAllowed(current.node, edge)) return false;
              step.last = next;
              model.infinitelyOftenActions.forEach((position, slot) => {
                if (!actionDone[slot] && getAction(current.node, edge, position)) {
                  actionDone[slot] = true;
                  remaining.count--;
                }
              });
            }
            if (remaining.count < countBeforeActions) {
              moveTo(next);
              seen.clear();
              return true;
            }
            if (isMember(next) && !seen.has(next)) step.unvisited = next;
            return false;
          });
          if (taken) break;
          if (remaining.count < countAtStart) {
            moveTo(step.last);
            seen.clear();
            break;
          }
          while (step.unvisited === -1) {
            const previous = cycleStack.pop();
            if (previous === undefined) {
              throw new TlaEvaluationError(
                "TLC failed to build the counterexample of a liveness property",
              );
            }
            current.node = previous;
            step.unvisited =
              getNodeSuccessors(behavior, previous).find(
                (next) => isMember(next) && !seen.has(next),
              ) ?? -1;
          }
          moveTo(step.unvisited);
          seen.add(step.unvisited);
        }
      }
      const postfix = getClosingPath(root, current.node, membersByState, isAllowed);
      for (let position = cycleStack.length - 1; position >= 0; position--) {
        const state = behavior.nodeStates[cycleStack[position]];
        if (postfix[postfix.length - 1] !== state) postfix.push(state);
      }
      const cycleState = prefix[prefix.length - 1];
      if (postfix[postfix.length - 1] === cycleState) postfix.pop();
      return {
        prefix: prefix.slice(0, -1),
        cycle: [cycleState, ...postfix.reverse()],
        isCycleConstrained: isCycleConstrained(solution),
      };
    };

    // TLC's LiveWorker#bfsPostFix, the states from the walk's end back to the root, last first.
    const getClosingPath = (
      root: number,
      end: number,
      membersByState: Map<number, number[]>,
      isAllowedEdge: (node: number, edge: number) => boolean,
    ) => {
      if (end === root) return [];
      const start = behavior.nodeStates[end];
      const parents = new Map<number, number>();
      const seen = new Set<number>([start]);
      const queue: [number, number][] = [];
      for (let state = start, parent = -1, position = 0; ; position++) {
        for (const node of membersByState.get(state) ?? []) {
          for (const [edge, next] of getNodeSuccessors(behavior, node).entries()) {
            if (next === node || !isAllowedEdge(node, edge)) continue;
            if (next === root) {
              const path: number[] = [];
              for (let item = state, itemParent = parent; item !== start;) {
                path.push(item);
                item = itemParent;
                itemParent = parents.get(item) ?? -1;
              }
              path.push(start);
              return path;
            }
            const nextState = behavior.nodeStates[next];
            if (!membersByState.has(nextState) || seen.has(nextState)) continue;
            seen.add(nextState);
            queue.push([nextState, state]);
          }
        }
        parents.set(state, parent);
        const item = queue[position];
        if (item === undefined) {
          throw new TlaEvaluationError(
            "TLC failed to build the counterexample of a liveness property",
          );
        }
        state = item[0];
        parent = item[1];
      }
    };

    const stack: number[] = [];
    for (let position = 0; position < queue.length; position++) {
      stack.push(queue[position], UNVISITED, 0);
      const counter = { link: 0 };
      while (stack.length >= 3) {
        const lowLink = stack.pop() ?? 0;
        const location = stack.pop();
        const node = stack.pop() ?? 0;
        if (location === SCC_MARKER) {
          if (links[node] === lowLink) {
            const lasso = checkComponent(node);
            if (lasso) return lasso;
          }
          stack.push(Math.min(stack.pop() ?? lowLink, lowLink));
          continue;
        }
        if (links[node] !== UNVISITED) {
          stack.push(Math.min(lowLink, links[node]));
          continue;
        }
        links[node] = counter.link;
        stack.push(lowLink, node, SCC_MARKER);
        components.push(node);
        const start = edgeStarts[node];
        const nextLowLink = { value: counter.link++ };
        for (let edge = 0; edge < edgeCounts[node]; edge++) {
          const next = edgeTargets[start + edge];
          if (!isWritten(behavior, next)) continue;
          if (!isAllowed(node, edge)) {
            if (links[next] === UNVISITED) queue.push(next);
            continue;
          }
          if (links[next] === UNVISITED) stack.push(next, UNVISITED);
          else nextLowLink.value = Math.min(nextLowLink.value, links[next]);
        }
        stack.push(nextLowLink.value);
      }
      stack.length = 0;
    }
    return undefined;
  };

  // Each check of the state starts from the environment it records its call stack in, if any.
  const startChecks = (tracing: Environment | undefined) => {
    evaluation.environment = tracing ?? environment;
    evaluation.isMemoized = isShared && tracing === undefined;
    if (shared.states.size > 0) shared.states.clear();
    if (shared.actions.size > 0) shared.actions.clear();
  };
  const endChecks = () => {
    evaluation.environment = environment;
  };

  return {
    branches: behaviors.length,
    enabledAtoms: [...atomIds.keys()].filter((atom) => atom.kind === "Enabled"),
    addInitialState: (index, state, tracing) => {
      startChecks(tracing);
      try {
        for (const behavior of behaviors) {
          const tableau = behavior.solution.tableau;
          if (!tableau) {
            behavior.initial.push(index);
            continue;
          }
          for (let node = 0; node < tableau.initialCount; node++) {
            if (!isConsistent(behavior, tableau, node, undefined, index, state)) continue;
            behavior.initial.push(
              getNodeId(behavior, index, node) ?? recordNode(behavior, index, node),
            );
          }
        }
      } finally {
        endChecks();
      }
    },
    addState: (index, state, successors, tracing) => {
      startChecks(tracing);
      try {
        const set = getSuccessorSet(index, state, successors);
        const sharedSteps = isShared ? addSteps(set.length) : -1;
        const decided = isShared
          ? getScratch(scratch.decided, actionIds.size).fill(UNDECIDED, 0, actionIds.size)
          : undefined;
        // A node of the state found late checks the stuttering step again, and finds its results.
        const self = set.findIndex((successor) => successor.state === state);
        if (isShared && self !== -1) {
          shared.actions.set(state, new Map([[state, sharedSteps + self]]));
        }
        for (const behavior of behaviors) {
          const firstStep = isShared ? sharedSteps : addSteps(set.length);
          // The behaviors before a covered one checked its actions on every step already.
          const checkedCount = isShared && behavior.isCovered ? 0 : set.length;
          for (let position = 0; position < checkedCount; position++) {
            checkStep(behavior, index, state, set[position].state, firstStep + position, decided);
          }
          const stateResults = checkState(behavior, index, state);
          const tableau = behavior.solution.tableau;
          if (!tableau) {
            addPlainState(behavior, set, firstStep, stateResults, index);
            continue;
          }
          const accepted = addTableauState(behavior, tableau, set, firstStep, stateResults, index);
          if (accepted) return accepted;
        }
        return undefined;
      } finally {
        endChecks();
      }
    },
    findViolation: () => {
      for (const behavior of behaviors) {
        for (const model of behavior.solution.models) {
          const lasso = findLassoInModel(behavior, model);
          if (lasso) return lasso;
        }
      }
      return undefined;
    },
    // TLC names every property that the counterexample violates, once each.
    getViolatedProperties: (path, cycleStart) => [
      ...new Set(
        properties
          .filter(
            (_, position) =>
              !evaluateOnLasso(negations[position].body, path, cycleStart, 0, environment),
          )
          .map((property) => property.name),
      ),
    ],
  };
};

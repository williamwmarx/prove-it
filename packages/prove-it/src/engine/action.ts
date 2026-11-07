// Compiles the initial predicate and the next-state relation into code that enumerates states in
// the order TLC does. It walks conjunctions, disjunctions, quantifiers and operators as TLC's Tool
// does, assigning a variable at its first conjunct of the form x' = e or x' \in S, and evaluating
// every other conjunct as a guard.

import { type Expression, isLocallyResolved } from "../ast";
import {
  type CompileContext,
  type Compiled,
  type Compiler,
  CUR,
  LOC,
  NXT,
  registers,
  setNext,
} from "./compile";
import {
  bail,
  elementAt,
  equals,
  FALSE,
  KIND_SET,
  KIND_TUPLE,
  kindOf,
  sizeOf,
  TRUE,
} from "./store";

type Continue = () => void;
export type Step = (onComplete: Continue) => void;

interface ActionOptions {
  isInit: boolean;
  // TLC evaluates the conjuncts left once every variable has a value, rather than walking them. It
  // does so for the initial predicate always, and for the next-state relation with warnings on.
  isAssignedShortcut: boolean;
}

export const resetAssigned = () => {
  registers.assigned = 0;
  undoTop.value = 0;
  frameTop.value = 0;
};

const FOUND = Symbol("found");

// Whether a step has a successor from the current state, which ENABLED asks. It runs the step from
// a next state of its own until the first successor, and puts back the next state and assignments
// of any step it runs inside.
export const createEnabledTest = (step: Step, width: number) => {
  const buffers: Int32Array[] = [];
  let depth = 0;
  return (): boolean => {
    const outerNext = NXT;
    const outerAssigned = registers.assigned;
    const outerTop = undoTop.value;
    const outerFrameTop = frameTop.value;
    const next = (buffers[depth] ??= new Int32Array(width));
    next.fill(-1);
    depth++;
    setNext(next);
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
      depth--;
      setNext(outerNext);
      registers.assigned = outerAssigned;
      undoTop.value = outerTop;
      frameTop.value = outerFrameTop;
    }
  };
};

const target = (isInit: boolean) => (isInit ? CUR : NXT);

// The variables assigned so far, in order, so each conjunction unassigns its own on the way out.
const undoStack = new Int32Array(1 << 16);
const undoTop = { value: 0 };

// What each running walk of a universal action keeps while its body runs, above what the walks
// around it keep: the binding it is at, then each level's set, stride and saved slot.
let frames = new Int32Array(1024);
const frameTop = { value: 0 };

// The offset of room for length words, which the walk pops by restoring frameTop.
const pushFrame = (length: number) => {
  const at = frameTop.value;
  frameTop.value += length;
  if (frameTop.value > frames.length) {
    let capacity = frames.length * 2;
    while (frameTop.value > capacity) capacity *= 2;
    const grown = new Int32Array(capacity);
    grown.set(frames);
    frames = grown;
  }
  return at;
};

export const compileAction = (
  compiler: Compiler,
  expression: Expression,
  context: CompileContext,
  options: ActionOptions,
): Step => {
  const variableCount = compiler.variableCount;
  const isInit = options.isInit;
  const {
    getAssignableIndex,
    getUnchangedIndices,
    isGuard,
    isPossiblyAssignable,
    hasBranches,
    hasAssignments,
  } = createActionAnalysis(compiler, isInit);

  const compileGuard = (guard: Expression, guardContext: CompileContext): Compiled => {
    const compiled = compiler.compile(guard, guardContext);
    return compiled;
  };

  const guardStep = (guard: Expression, guardContext: CompileContext): Step => {
    const evaluate = compileGuard(guard, guardContext).evaluate;
    return (onComplete) => {
      const value = evaluate();
      if (value === TRUE) onComplete();
      else if (value !== FALSE) bail("a guard that isn't a boolean");
    };
  };

  // The variable an expression such as x' (or x in the initial predicate) assigns, following
  // operator arguments and zero-arity definitions.
  type Conjunct =
    | { kind: "guard"; evaluate: () => number }
    | { kind: "assign"; index: number; evaluate: () => number }
    | { kind: "unchanged"; indices: number[] }
    | { kind: "branch"; step: Step };

  const toConjunct = (operand: Expression, operandContext: CompileContext): Conjunct => {
    if (operand.kind === "Apply" && operand.operator === "=" && !isLocallyResolved(operand)) {
      const index = getAssignableIndex(operand.args[0], operandContext);
      if (index !== undefined) {
        return {
          kind: "assign",
          index,
          evaluate: compiler.compile(operand.args[1], operandContext).evaluate,
        };
      }
    }
    if (!isInit && operand.kind === "Unchanged") {
      const indices = getUnchangedIndices(operand.expression, operandContext);
      if (indices) return { kind: "unchanged", indices };
    }
    if (isGuard(operand, operandContext)) {
      return { kind: "guard", evaluate: compileGuard(operand, operandContext).evaluate };
    }
    return { kind: "branch", step: compileStep(operand, operandContext) };
  };

  // Whether an expression is a guard, which TLC evaluates rather than walks.
  const compileConjunction = (operands: Expression[], conjunctionContext: CompileContext): Step => {
    const conjuncts = operands.map((operand) => toConjunct(operand, conjunctionContext));
    const guards: (Compiled | undefined)[] = [];
    const getGuard = (index: number) =>
      (guards[index] ??= compiler.compile(operands[index], conjunctionContext));
    const count = conjuncts.length;
    const isShortcut = options.isAssignedShortcut;
    // Each conjunct is a closure that returns whether the conjunction goes on, pushing any variable
    // it assigns on the undo stack, or a branch that the runner continues through.
    const simple: ((() => boolean) | undefined)[] = conjuncts.map((conjunct) => {
      switch (conjunct.kind) {
        case "guard": {
          const evaluate = conjunct.evaluate;
          return () => {
            const value = evaluate();
            if (value === TRUE) return true;
            if (value !== FALSE) bail("a conjunct that isn't a boolean");
            return false;
          };
        }
        case "assign": {
          const evaluate = conjunct.evaluate;
          const variable = conjunct.index;
          return () => {
            const value = evaluate();
            const state = target(isInit);
            const current = state[variable];
            if (current === -1) {
              state[variable] = value;
              registers.assigned++;
              undoStack[undoTop.value++] = variable;
              return true;
            }
            return current === value || equals(current, value);
          };
        }
        case "unchanged": {
          const indices = conjunct.indices;
          return () => {
            for (let position = 0; position < indices.length; position++) {
              const variable = indices[position];
              const current = NXT[variable];
              if (current === -1) {
                NXT[variable] = CUR[variable];
                registers.assigned++;
                undoStack[undoTop.value++] = variable;
              } else if (current !== CUR[variable] && !equals(current, CUR[variable])) {
                return false;
              }
            }
            return true;
          };
        }
        default:
          return undefined;
      }
    });
    const branches = conjuncts.map((conjunct) =>
      conjunct.kind === "branch" ? conjunct.step : undefined,
    );
    // What follows the running conjunction, which each branch goes on to through the conjuncts
    // after it. A conjunction run inside another's continuation puts the other's back on return.
    let pending: Continue = () => {};
    const continuations = conjuncts.map((_, index) => () => runFrom(index + 1, pending));
    const runFrom = (start: number, onComplete: Continue): void => {
      const mark = undoTop.value;
      let index = start;
      for (; index < count; index++) {
        if (index > 0 && isShortcut && registers.assigned === variableCount) {
          let holds = true;
          for (let rest = index; rest < count; rest++) {
            const value = getGuard(rest).evaluate();
            if (value === FALSE) {
              holds = false;
              break;
            }
            if (value !== TRUE) bail("a conjunct that isn't a boolean");
          }
          if (holds) onComplete();
          break;
        }
        const step = simple[index];
        if (step !== undefined) {
          if (!step()) break;
          continue;
        }
        branches[index]!(continuations[index]);
        break;
      }
      if (index === count) onComplete();
      const state = target(isInit);
      for (let position = undoTop.value - 1; position >= mark; position--)
        state[undoStack[position]] = -1;
      registers.assigned -= undoTop.value - mark;
      undoTop.value = mark;
    };
    if (branches.every((branch) => branch === undefined))
      return (onComplete) => runFrom(0, onComplete);
    return (onComplete) => {
      const outer = pending;
      pending = onComplete;
      try {
        runFrom(0, onComplete);
      } finally {
        pending = outer;
      }
    };
  };

  const compileMembership = (
    index: number,
    setExpression: Expression,
    membershipContext: CompileContext,
    guard: Expression,
  ): Step => {
    const set = compiler.compileOrdered(setExpression, membershipContext, "streamed");
    const setEvaluate = set.evaluate;
    const guardEvaluate = compiler.compile(guard, membershipContext).evaluate;
    return (onComplete) => {
      const state = target(isInit);
      if (state[index] !== -1) {
        const value = guardEvaluate();
        if (value === TRUE) onComplete();
        else if (value !== FALSE) bail("a guard that isn't a boolean");
        return;
      }
      const id = setEvaluate();
      if (kindOf(id) !== KIND_SET && kindOf(id) !== KIND_TUPLE) bail("x' \\in S with S not a set");
      const size = sizeOf(id);
      registers.assigned++;
      try {
        for (let position = 0; position < size; position++) {
          state[index] = elementAt(id, position);
          onComplete();
        }
      } finally {
        state[index] = -1;
        registers.assigned--;
      }
    };
  };

  const compileStep = (step: Expression, stepContext: CompileContext): Step => {
    switch (step.kind) {
      case "And":
        return compileConjunction(step.operands, stepContext);
      case "Or": {
        const branches = step.operands.map((operand) => compileStep(operand, stepContext));
        return (onComplete) => {
          for (let index = 0; index < branches.length; index++) branches[index](onComplete);
        };
      }
      case "Exists": {
        let inner = stepContext;
        const levels: { set: Compiled; slot: number }[] = [];
        for (const bound of step.bounds) {
          if (bound.pattern.kind !== "Name") return bail("a tuple pattern in an action's \\E");
          const set = compiler.compileOrdered(bound.set, inner, "quantifier");
          const binding = compiler.bindValue(inner, bound.pattern.name);
          inner = binding.context;
          levels.push({ set, slot: binding.slot });
        }
        const body = compileStep(step.body, inner);
        if (levels.length === 1) {
          const setEvaluate = levels[0].set.evaluate;
          const slot = levels[0].slot;
          return (onComplete) => {
            const id = setEvaluate();
            if (kindOf(id) !== KIND_SET && kindOf(id) !== KIND_TUPLE)
              bail("an action quantified over a non-set");
            const size = sizeOf(id);
            for (let position = 0; position < size; position++) {
              LOC[slot] = elementAt(id, position);
              body(onComplete);
            }
          };
        }
        const setEvaluators = levels.map((level) => level.set.evaluate);
        const slots = Int32Array.from(levels, (level) => level.slot);
        const levelCount = levels.length;
        // TLC's ContextEnumerator varies the first bound fastest: the last bound is the outer loop.
        // The frame holds each level's set, then its position.
        return (onComplete) => {
          const at = pushFrame(2 * levelCount);
          let isEmpty = false;
          for (let level = 0; level < levelCount; level++) {
            const id = setEvaluators[level]();
            if (kindOf(id) !== KIND_SET && kindOf(id) !== KIND_TUPLE)
              bail("an action quantified over a non-set");
            if (sizeOf(id) === 0) isEmpty = true;
            frames[at + level] = id;
            frames[at + levelCount + level] = 0;
          }
          for (let level = isEmpty ? levelCount : 0; level < levelCount;) {
            for (let bound = 0; bound < levelCount; bound++)
              LOC[slots[bound]] = elementAt(frames[at + bound], frames[at + levelCount + bound]);
            body(onComplete);
            for (level = 0; level < levelCount; level++) {
              if (++frames[at + levelCount + level] < sizeOf(frames[at + level])) break;
              frames[at + levelCount + level] = 0;
            }
          }
          frameTop.value = at;
        };
      }
      case "Forall": {
        if (!hasAssignments(step.body, stepContext) && !hasBranches(step.body, stepContext)) {
          return guardStep(step, stepContext);
        }
        return compileWalkedForall(step, stepContext);
      }
      case "If": {
        const condition = compiler.compile(step.condition, stepContext).evaluate;
        const consequent = compileStep(step.consequent, stepContext);
        const alternative = compileStep(step.alternative, stepContext);
        return (onComplete) => {
          const value = condition();
          if (value === TRUE) consequent(onComplete);
          else if (value === FALSE) alternative(onComplete);
          else bail("an IF condition that isn't a boolean");
        };
      }
      case "Case": {
        const arms = step.arms.map((arm) => ({
          condition: compiler.compile(arm.condition, stepContext).evaluate,
          body: compileStep(arm.body, stepContext),
        }));
        const other = step.other ? compileStep(step.other, stepContext) : undefined;
        return (onComplete) => {
          for (const arm of arms) {
            const value = arm.condition();
            if (value === TRUE) {
              arm.body(onComplete);
              return;
            }
            if (value !== FALSE) bail("a CASE condition that isn't a boolean");
          }
          if (!other) bail("no CASE arm holds");
          other!(onComplete);
        };
      }
      case "Let":
        return compileStep(step.body, compiler.bindLet(step, stepContext));
      case "Unchanged": {
        if (isInit) return bail("UNCHANGED in the initial predicate");
        const indices = getUnchangedIndices(step.expression, stepContext);
        if (indices) return compileConjunction([step], stepContext);
        return guardStep(step, stepContext);
      }
      case "AngleAction": {
        const body = compileStep(step.action, stepContext);
        const unchanged = compiler.compile(
          { kind: "Unchanged", expression: step.subscript, location: step.location },
          stepContext,
        ).evaluate;
        return (onComplete) =>
          body(() => {
            if (unchanged() === FALSE) onComplete();
          });
      }
      case "BoxAction":
        return compileStep(
          {
            kind: "Or",
            operands: [
              step.action,
              { kind: "Unchanged", expression: step.subscript, location: step.location },
            ],
            location: step.location,
          },
          stepContext,
        );
      case "Label":
        return compileStep(step.body, stepContext);
      case "FunctionApplication": {
        const lazy = compiler.resolveLazyApplication(step, stepContext);
        // Walking a body with no disjunction, existential or assignment comes to evaluating it.
        if (
          !lazy ||
          (!hasBranches(lazy.functionBody, lazy.functionContext) &&
            !hasAssignments(lazy.functionBody, lazy.functionContext))
        )
          return guardStep(step, stepContext);
        if (lazy.isRecursive) return bail("walking a recursive function in an action");
        const isInDomain = lazy.isInDomain;
        const walk = compileStep(lazy.body, lazy.context);
        return (onComplete) => {
          if (!isInDomain()) bail("applied a function outside its domain");
          walk(onComplete);
        };
      }
      case "Identifier": {
        const resolved = compiler.resolveAction(step, stepContext);
        if (!resolved) return guardStep(step, stepContext);
        return compileStep(resolved.body, resolved.context);
      }
      case "Apply": {
        const args = step.args;
        if (
          !isLocallyResolved(step) &&
          (step.operator === "=" || step.operator === "\\in" || step.operator === "\\subseteq")
        ) {
          const index = getAssignableIndex(args[0], stepContext);
          if (index !== undefined) {
            if (step.operator === "=") return compileConjunction([step], stepContext);
            if (step.operator === "\\subseteq") return bail("x' \\subseteq S");
            return compileMembership(index, args[1], stepContext, step);
          }
          if (isPossiblyAssignable(args[0]))
            return bail(
              `an assignment the engine can't resolve statically at line ${step.location.line}`,
            );
        }
        if (!isLocallyResolved(step) && step.operator === "=>") {
          const condition = compiler.compile(args[0], stepContext).evaluate;
          const right = compileStep(args[1], stepContext);
          return (onComplete) => {
            const value = condition();
            if (value === FALSE) onComplete();
            else if (value === TRUE) right(onComplete);
            else bail("the left side of => isn't a boolean");
          };
        }
        if (!isLocallyResolved(step) && (step.operator === "/\\" || step.operator === "\\/")) {
          return compileStep(
            {
              kind: step.operator === "/\\" ? "And" : "Or",
              operands: args,
              location: step.location,
            },
            stepContext,
          );
        }
        const resolved = compiler.resolveAction(step, stepContext);
        if (resolved) return compileStep(resolved.body, resolved.context);
        return guardStep(step, stepContext);
      }
      default:
        return guardStep(step, stepContext);
    }
  };

  // TLC walks a universal action that may assign or branch as the conjunction of its body over the
  // bindings: the first binding, then the others in reverse.
  const compileWalkedForall = (
    step: Expression & { kind: "Forall" | "Exists" },
    stepContext: CompileContext,
  ): Step => {
    let inner = stepContext;
    const levels: { set: Compiled; slot: number }[] = [];
    for (const bound of step.bounds) {
      if (bound.pattern.kind !== "Name") return bail("a tuple pattern in an action's \\A");
      const set = compiler.compileOrdered(bound.set, inner, "quantifier");
      const binding = compiler.bindValue(inner, bound.pattern.name);
      inner = binding.context;
      levels.push({ set, slot: binding.slot });
    }
    const body = compileStep(step.body, inner);
    const slots = Int32Array.from(levels, (level) => level.slot);
    const setEvaluators = levels.map((level) => level.set.evaluate);
    // The body as a guard, compiled the first time an initial state needs it and then kept: each
    // compile binds new slots.
    let forallGuard: (() => number) | undefined;
    const levelCount = levels.length;
    // The running walk: the offset of its frame, its number of bindings, and what follows it. A
    // walk of this action inside another's continuation puts the other's back once it returns.
    let frame = 0;
    let count = 0;
    let complete: Continue = () => {};
    // The bindings are numbered with the first name varying fastest, so binding b binds level l
    // to the element at (b / stride of l) % size of its set.
    const bind = (index: number) => {
      const binding = index === 0 ? 0 : count - index;
      for (let level = 0; level < levelCount; level++) {
        const set = frames[frame + 1 + level];
        const stride = frames[frame + 1 + levelCount + level];
        LOC[slots[level]] = elementAt(set, Math.floor(binding / stride) % sizeOf(set));
      }
    };
    const restore = () => {
      for (let level = 0; level < levelCount; level++)
        LOC[slots[level]] = frames[frame + 1 + 2 * levelCount + level];
    };
    // The walk visits the first binding, then the others in reverse.
    const visit = (index: number) => {
      if (index === count) {
        restore();
        complete();
        return;
      }
      if (index > 0 && isInit && registers.assigned === variableCount) {
        const guard = getForallGuard();
        for (let rest = index; rest < count; rest++) {
          bind(rest);
          const value = guard();
          if (value === FALSE) return;
          if (value !== TRUE) bail("a conjunct that isn't a boolean");
        }
        restore();
        complete();
        return;
      }
      frames[frame] = index;
      bind(index);
      body(advance);
    };
    // The rest of the conjunction rebinds the names for the next binding, so this binding's walk
    // gets them back once the rest returns. A body that branches goes on more than once.
    const advance = () => {
      const index = frames[frame];
      visit(index + 1);
      frames[frame] = index;
      bind(index);
    };
    return (onComplete) => {
      const at = pushFrame(1 + 3 * levelCount);
      let bindings = 1;
      for (let level = 0; level < levelCount; level++) {
        const id = setEvaluators[level]();
        if (kindOf(id) !== KIND_SET && kindOf(id) !== KIND_TUPLE)
          bail("an action quantified over a non-set");
        frames[at + 1 + level] = id;
        frames[at + 1 + levelCount + level] = bindings;
        frames[at + 1 + 2 * levelCount + level] = LOC[slots[level]];
        bindings *= sizeOf(id);
      }
      const outerFrame = frame;
      const outerCount = count;
      const outerComplete = complete;
      frame = at;
      count = bindings;
      complete = onComplete;
      try {
        visit(0);
      } finally {
        frame = outerFrame;
        count = outerCount;
        complete = outerComplete;
        frameTop.value = at;
      }
    };
    function getForallGuard() {
      forallGuard ??= compiler.compile(step.body, inner).evaluate;
      return forallGuard;
    }
  };

  return compileStep(expression, context);
};

// What the action compilers need to know about an expression: which variable it assigns, which it
// leaves unchanged, and whether TLC evaluates or walks it.
export const createActionAnalysis = (compiler: Compiler, isInit: boolean) => {
  const environment = compiler.environment;
  const getAssignable = (
    expression: Expression,
    assignableContext: CompileContext,
    isPrimed: boolean,
    depth = 0,
  ): number | undefined => {
    if (depth > 50) return undefined;
    if (expression.kind === "Prime" && isPrimed) {
      return getAssignable(expression.expression, assignableContext, false, depth + 1);
    }
    if (expression.kind !== "Identifier") return undefined;
    if (isLocallyResolved(expression)) {
      const resolved = compiler.resolveAction(expression, assignableContext);
      if (!resolved) return undefined;
      return getAssignable(resolved.body, resolved.context, isPrimed, depth + 1);
    }
    const index = environment.variableIndex.get(expression.name);
    if (index !== undefined) return isPrimed ? undefined : index;
    const resolved = compiler.resolveAction(expression, assignableContext);
    if (!resolved) return undefined;
    return getAssignable(resolved.body, resolved.context, isPrimed, depth + 1);
  };

  const getAssignableIndex = (expression: Expression, assignableContext: CompileContext) =>
    getAssignable(expression, assignableContext, !isInit);

  const getUnchangedIndices = (
    expression: Expression,
    unchangedContext: CompileContext,
    depth = 0,
  ): number[] | undefined => {
    if (depth > 50) return undefined;
    if (expression.kind === "Tuple") {
      const indices = expression.elements.map((element) =>
        getUnchangedIndices(element, unchangedContext, depth + 1),
      );
      return indices.every((item) => item !== undefined) ? indices.flat() : undefined;
    }
    if (expression.kind !== "Identifier") return undefined;
    if (!isLocallyResolved(expression)) {
      const index = environment.variableIndex.get(expression.name);
      if (index !== undefined) return [index];
    }
    const resolved = compiler.resolveAction(expression, unchangedContext);
    if (!resolved) return undefined;
    return getUnchangedIndices(resolved.body, resolved.context, depth + 1);
  };

  const isGuard = (operand: Expression, operandContext: CompileContext): boolean => {
    switch (operand.kind) {
      case "Label":
      case "And":
      case "Or":
      case "Exists":
      case "Forall":
      case "If":
      case "Case":
      case "Let":
      case "Unchanged":
      case "BoxAction":
      case "AngleAction":
      case "FunctionApplication":
        return false;
      case "Identifier":
        return compiler.resolveAction(operand, operandContext) === undefined;
      case "Apply": {
        if (operand.operator === "=>") return false;
        if (
          operand.operator === "=" ||
          operand.operator === "\\in" ||
          operand.operator === "\\subseteq"
        ) {
          if (getAssignableIndex(operand.args[0], operandContext) !== undefined) return false;
          if (isPossiblyAssignable(operand.args[0])) return false;
        }
        return compiler.resolveAction(operand, operandContext) === undefined;
      }
      default:
        return true;
    }
  };

  // The engine follows names to what they're bound to as it compiles, so only a target under a LET
  // may assign a variable it can't find. TLC finds such a target as it runs.
  const isPossiblyAssignable = (expression: Expression) => expression.kind === "Let";

  // Whether an expression has a disjunction or an existential, for each of which TLC generates a
  // successor when it walks the expression.
  const hasBranches = (body: Expression, bodyContext: CompileContext, depth = 0): boolean => {
    if (depth > 30) return true;
    if (body.kind === "Or" || body.kind === "Exists") return true;
    if (body.kind === "Apply" || body.kind === "Identifier") {
      const resolved = compiler.resolveAction(body, bodyContext);
      if (resolved && hasBranches(resolved.body, resolved.context, depth + 1)) return true;
    }
    if (body.kind === "FunctionApplication") {
      const lazy = compiler.resolveLazyApplication(body, bodyContext);
      if (lazy && hasBranches(lazy.functionBody, lazy.functionContext, depth + 1)) return true;
    }
    const children: Expression[] = [];
    collectChildren(body, children);
    return children.some((child) => hasBranches(child, bodyContext, depth + 1));
  };

  // Whether walking an expression may assign a variable, in which case TLC walks rather than
  // evaluates it.
  const hasAssignments = (body: Expression, bodyContext: CompileContext, depth = 0): boolean => {
    if (depth > 30) return true;
    if (body.kind === "Prime") return true;
    if (body.kind === "Unchanged") return true;
    if (body.kind === "Apply" || body.kind === "Identifier") {
      const resolved = compiler.resolveAction(body, bodyContext);
      if (resolved && hasAssignments(resolved.body, resolved.context, depth + 1)) return true;
    }
    if (body.kind === "FunctionApplication") {
      const lazy = compiler.resolveLazyApplication(body, bodyContext);
      if (lazy && hasAssignments(lazy.functionBody, lazy.functionContext, depth + 1)) return true;
    }
    const children: Expression[] = [];
    collectChildren(body, children);
    return children.some((child) => hasAssignments(child, bodyContext, depth + 1));
  };

  return {
    getAssignableIndex,
    getUnchangedIndices,
    isGuard,
    isPossiblyAssignable,
    hasBranches,
    hasAssignments,
  };
};

const collectChildren = (expression: Expression, children: Expression[]) => {
  for (const value of Object.values(expression)) {
    if (Array.isArray(value)) {
      for (const item of value) {
        if (item && typeof item === "object" && "kind" in item && "location" in item)
          children.push(item as Expression);
        else if (item && typeof item === "object") collectChildren(item as Expression, children);
      }
    } else if (value && typeof value === "object" && "kind" in value && "location" in value) {
      children.push(value as Expression);
    }
  }
};

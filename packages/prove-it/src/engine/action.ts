// Compiles the initial predicate and the next-state relation into code that enumerates states in
// the order TLC does. It walks conjunctions, disjunctions, quantifiers and operators as TLC's Tool
// does, assigning a variable at its first conjunct of the form x' = e or x' \in S, and evaluating
// every other conjunct as a guard.

import { type Expression, isLocallyResolved } from "../ast";
import { type CompileContext, type Compiled, type Compiler, CUR, LOC, NXT } from "./compile";
import { bail, elementAt, equals, FALSE, KIND_SET, kindOf, sizeOf, TRUE } from "./store";

type Continue = () => void;
export type Step = (onComplete: Continue) => void;

interface ActionOptions {
  isInit: boolean;
  // TLC evaluates the conjuncts left once every variable has a value, rather than walking them. It
  // does so for the initial predicate always, and for the next-state relation with warnings on.
  isAssignedShortcut: boolean;
}

// How many variables of the state being built have a value.
const assigned = { count: 0 };

export const resetAssigned = () => {
  assigned.count = 0;
  undoTop.value = 0;
};

const target = (isInit: boolean) => (isInit ? CUR : NXT);

// The variables assigned so far, in order, so each conjunction unassigns its own on the way out.
const undoStack = new Int32Array(1 << 16);
const undoTop = { value: 0 };

export const compileAction = (
  compiler: Compiler,
  expression: Expression,
  context: CompileContext,
  options: ActionOptions,
): Step => {
  const variableCount = compiler.variableCount;
  const environment = compiler.environment;
  const isInit = options.isInit;

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

  const isPossiblyAssignable = (expression: Expression) =>
    expression.kind === "Let" ||
    (expression.kind === "Identifier" && (isInit || isLocallyResolved(expression))) ||
    (!isInit && expression.kind === "Prime");

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
              assigned.count++;
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
                assigned.count++;
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
    const runFrom = (start: number, onComplete: Continue): void => {
      const mark = undoTop.value;
      let index = start;
      for (; index < count; index++) {
        if (index > 0 && isShortcut && assigned.count === variableCount) {
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
        const next = index + 1;
        branches[index]!(() => runFrom(next, onComplete));
        break;
      }
      if (index === count) onComplete();
      const state = target(isInit);
      for (let position = undoTop.value - 1; position >= mark; position--)
        state[undoStack[position]] = -1;
      assigned.count -= undoTop.value - mark;
      undoTop.value = mark;
    };
    return (onComplete) => runFrom(0, onComplete);
  };

  const compileMembership = (
    index: number,
    setExpression: Expression,
    membershipContext: CompileContext,
    guard: Expression,
  ): Step => {
    const set = compiler.compile(setExpression, membershipContext);
    if (!set.isNormalized) return bail("an assignment from a set TLC enumerates in its own order");
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
      if (kindOf(id) !== KIND_SET) bail("x' \\in S with S not a set");
      const size = sizeOf(id);
      assigned.count++;
      try {
        for (let position = 0; position < size; position++) {
          state[index] = elementAt(id, position);
          onComplete();
        }
      } finally {
        state[index] = -1;
        assigned.count--;
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
          const set = compiler.compile(bound.set, inner);
          if (!set.isNormalized)
            return bail("an action quantified over a set TLC enumerates in its own order");
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
            if (kindOf(id) !== KIND_SET) bail("an action quantified over a non-set");
            const size = sizeOf(id);
            for (let position = 0; position < size; position++) {
              LOC[slot] = elementAt(id, position);
              body(onComplete);
            }
          };
        }
        // TLC's ContextEnumerator varies the first bound fastest: the last bound is the outer loop.
        return (onComplete) => {
          const sets = levels.map((level) => {
            const id = level.set.evaluate();
            if (kindOf(id) !== KIND_SET) bail("an action quantified over a non-set");
            return id;
          });
          if (sets.some((id) => sizeOf(id) === 0)) return;
          const visit = (level: number) => {
            if (level < 0) {
              body(onComplete);
              return;
            }
            const id = sets[level];
            const slot = levels[level].slot;
            for (let position = 0; position < sizeOf(id); position++) {
              LOC[slot] = elementAt(id, position);
              visit(level - 1);
            }
          };
          visit(levels.length - 1);
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
            return bail("an assignment the engine can't resolve statically");
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
      const set = compiler.compile(bound.set, inner);
      if (!set.isNormalized)
        return bail("an action quantified over a set TLC enumerates in its own order");
      const binding = compiler.bindValue(inner, bound.pattern.name);
      inner = binding.context;
      levels.push({ set, slot: binding.slot });
    }
    const body = compileStep(step.body, inner);
    const slots = levels.map((level) => level.slot);
    return (onComplete) => {
      const sets = levels.map((level) => {
        const id = level.set.evaluate();
        if (kindOf(id) !== KIND_SET) bail("an action quantified over a non-set");
        return id;
      });
      const bindings: number[][] = [];
      const current: number[] = new Array(levels.length);
      const collect = (level: number) => {
        if (level < 0) {
          bindings.push(current.slice());
          return;
        }
        for (let position = 0; position < sizeOf(sets[level]); position++) {
          current[level] = elementAt(sets[level], position);
          collect(level - 1);
        }
      };
      collect(levels.length - 1);
      const ordered = [...bindings.slice(0, 1), ...bindings.slice(1).reverse()];
      const saved = slots.map((slot) => LOC[slot]);
      const visit = (index: number) => {
        if (index === ordered.length) {
          for (let level = 0; level < slots.length; level++) LOC[slots[level]] = saved[level];
          onComplete();
          return;
        }
        if (index > 0 && isInit && assigned.count === variableCount) {
          const guard = getForallGuard();
          for (let rest = index; rest < ordered.length; rest++) {
            for (let level = 0; level < slots.length; level++)
              LOC[slots[level]] = ordered[rest][level];
            const value = guard();
            if (value === FALSE) return;
            if (value !== TRUE) bail("a conjunct that isn't a boolean");
          }
          for (let level = 0; level < slots.length; level++) LOC[slots[level]] = saved[level];
          onComplete();
          return;
        }
        const binding = ordered[index];
        for (let level = 0; level < slots.length; level++) LOC[slots[level]] = binding[level];
        body(() => visit(index + 1));
      };
      visit(0);
    };
    function getForallGuard() {
      return compiler.compile(step.body, inner).evaluate;
    }
  };

  // Whether an expression has a disjunction or an existential, for each of which TLC generates a
  // successor when it walks the expression.
  const hasBranches = (body: Expression, bodyContext: CompileContext, depth = 0): boolean => {
    if (depth > 30) return true;
    if (body.kind === "Or" || body.kind === "Exists") return true;
    if (body.kind === "Apply" || body.kind === "Identifier") {
      const resolved = compiler.resolveAction(body, bodyContext);
      if (resolved && hasBranches(resolved.body, resolved.context, depth + 1)) return true;
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
    const children: Expression[] = [];
    collectChildren(body, children);
    return children.some((child) => hasAssignments(child, bodyContext, depth + 1));
  };

  return compileStep(expression, context);
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

// Records the calls theory_lra makes into the lp solver, for the Rust port of lp
// (native/design/prover.md, P3b-lp): a replayer drives the Rust lp with the same calls, answers its
// callbacks from the trace, and compares every result and field read. It is inert unless
// PROVE_IT_LP_TRACE names a directory, and with it set it only records: the theory sees the same
// values, and lp the same callbacks, so the search, its steps included, is the same. Only a search
// that exhausts the stack may stop sooner, as the proxies add frames.
//
// Each SMT decision writes <dir>/<digest>.lptrace, where the digest is that of
// .prover-inputs/smt/<digest>.smt: the first 16 hex digits of the input text's SHA-256. The file
// holds JSON lines in the order the events happen:
//   {"c":obj,"m":"new","a":[args]}           lp made the object obj ("lar#0", "lia#0", "bp#0",
//                                             "nla#0"), numbered in order of creation per kind
//   {"c":obj,"m":method,"a":[args],"r":result}  the theory called obj.method; a method reached
//                                             through fields is a path, as "divisions.addIdivision"
//   {"c":..,"m":..,"a":..,"o":[args],..}     the same, with the arguments after the call, when
//                                             one is an Explanation, which lp fills in
//   {"c":..,"m":..,"a":..,"e":"Name: message"}  the call threw
//   {"c":"lp","m":"randomUpdate","a":[..]}   a call of lp's free function random_updater::update
//   {"cb":name,"a":[args],"r":value}         lp called back into the theory; "e" when it threw
//   {"f":obj,"p":path,"r":value}             the theory read a field, as
//                                             "columnsWithChangedBounds.size"
//   {"w":obj,"p":path,"v":value}             the theory wrote a field
// A call's line comes before the callbacks it makes. Lines without "r" returned undefined.
//
// Values: a Rational is "n" or "n/d"; an Impq ["x","y"]; a LarTerm
// {"col":n,"coeffs":[[col,"r"],..]} in its iteration order; an Explanation {"expl":[constraints in iteration order]}, with
// "pairs":[[constraint,"r"],..] when it has pairs; a Dependency {"dep":[leaves]} linearized; an
// algebraic number {"anum":value}; a bigint its decimal string; an infinite number its string;
// undefined null in an array; arrays, maps ({"map":[..]}), other iterables ({"iter":[..]}) and
// records structurally. An lp object is {"ref":obj}. A function the theory passes becomes a
// callback named "<obj>.<method>.<argument index>", as "lar#0.new.0" (LarSolver's isCanceled,
// which counts a step of the resource limit), and an object of methods it passes, as
// BoundPropagator's host or NlaCore's resource limit, has callbacks "<that name>.<method>", as
// "bp#0.new.1.addEq" or "nla#0.new.1.inc"; either is {"cb":name}. A function the theory stores
// in a field is the callback "<obj>.<path>", as "nla#0.isRelevant". A function in a value lp
// returns is {"fn":true}.
//
// Only what the theory does is recorded: a call, read or write that lp makes, through the same
// objects (NlaCore's lra and IntSolver's solver are the traced LarSolver) or through a callback's
// theory code, is not, as the replayer neither makes it nor runs the theory (a callback's theory
// code only reads lp). A callback is recorded whatever the depth of lp calls it comes from, but
// not one made while the theory answers another. An object a field read reaches is traced along
// its path, so solver.constraints.constraints.length is the read of
// "constraints.constraints.length"; iterating an array or iterable the theory reached so is one
// read of the whole of it, whose elements with methods (an ImpliedBound) are traced at
// "<path>.<index>". An object with methods that a call returns is traced as "obj#n".
//
// What theory-lra*.ts reaches, and so what is recorded:
//   LarSolver: activate, activateCheckOnEqual, addEquality, addTerm, addVar,
//     collectMoreRowsForLpPropagation, constraintIsRedundant, externalToLocalColumn,
//     findFeasibleSolution, getBound, getExactValue, getExternal, getInfeasibilityExplanation,
//     getModelValue, getTerm, getValue, hasInfInt, hasTerm, initModel, isFeasible, isFixed,
//     mkVarBound, pop, push, registerExistingTerms; reads of status, columnsWithChangedBounds.size,
//     constraints.constraints.length; writes of constraints.isAuxiliaryMode.
//   IntSolver: check; reads of term and explanation.
//   BoundPropagator: init, propagateBoundsForTouchedRows; the iteration of ibounds, and of each
//     ImpliedBound the reads of column, bound, isLower and isStrict and calls of explain; the
//     host's callbacks columnIsInteresting, boundIsInteresting, isEqual and addEq.
//   NlaCore: addMonic, check, checkBoundedDivisions, hasRelevantMonomial, incrementalPropagate,
//     pop, propagate, push, divisions.addIdivision, divisions.addBoundedDivision,
//     divisions.addDivisibility, nra.value, nra.am.add, nra.am.mul, nra.am.compare; reads of
//     isCheckFeasible, isUsingNraModel, lemmas.length and the iteration of lemmas, literals,
//     fixedEqualities and equalities; the write of isRelevant, whose calls are callbacks, and
//     the resource limit's inc, which nla and nlsat call.
//   randomUpdate, and LarSolver's isCanceled callback.

import { getEnvironmentSetting } from "../../../engine/settings";
import type { Dependency } from "./lp/dependency";
import { Explanation } from "./lp/explanation";
import { LarTerm } from "./lp/lar-term";
import { Impq } from "./lp/numeric-pair";
import { Anum } from "./nlsat/algebraic";
import { Rational } from "./rational";

interface TraceLine {
  c?: string;
  m?: string;
  cb?: string;
  f?: string;
  w?: string;
  p?: string;
  a?: unknown[];
  o?: unknown[];
  r?: unknown;
  v?: unknown;
  e?: string;
}

interface Trace {
  path: string;
  lines: TraceLine[];
  counts: Map<string, number>;
  // The names of the traced objects, path proxies and callbacks, for their values.
  names: WeakMap<object, string>;
  callbacks: WeakMap<object, string>;
  // The path proxy of each object a field read reached, so that it keeps its identity.
  pathProxies: WeakMap<object, object>;
}

// The lines kept before they are written, past which a finished call writes them.
const FLUSH_SIZE = 4096;

let trace: Trace | undefined;
// The depth of lp calls the theory made: only those at depth 0 are the theory's.
let depth = 0;
let isInCallback = false;

const getId = (current: Trace, kind: string) => {
  const count = current.counts.get(kind) ?? 0;
  current.counts.set(kind, count + 1);
  return `${kind}#${count}`;
};

const joinPath = (path: string, key: string) => (path === "" ? key : `${path}.${key}`);

const describeError = (error: unknown) =>
  error instanceof Error ? `${error.name}: ${error.message}` : String(error);

const isDependency = (value: object): value is NonNullable<Dependency> =>
  "isLeaf" in value && "isMarked" in value;

// The leaves of a dependency in the order of linearize, without marking its nodes.
const getLeaves = (root: Dependency) => {
  const todo = root === null ? [] : [root];
  const visited = new Set(todo);
  const leaves: number[] = [];
  for (let head = 0; head < todo.length; head++) {
    const node = todo[head];
    if (node.isLeaf) {
      leaves.push(node.value);
      continue;
    }
    for (const child of [node.first, node.second]) {
      if (child === null || visited.has(child)) continue;
      visited.add(child);
      todo.push(child);
    }
  }
  return leaves;
};

const isIterable = (value: object): value is Iterable<unknown> => Symbol.iterator in value;

const isValue = (value: unknown) =>
  value === null ||
  typeof value !== "object" ||
  value instanceof Rational ||
  value instanceof Impq ||
  value instanceof LarTerm ||
  value instanceof Explanation ||
  value instanceof Anum ||
  isDependency(value);

// An object that is not data: an instance of a class other than the values', or a record with a
// method.
const hasMethods = (value: unknown): value is object =>
  typeof value === "object" &&
  value !== null &&
  !isValue(value) &&
  !Array.isArray(value) &&
  (Object.getPrototypeOf(value) !== Object.prototype ||
    Object.values(value).some((field) => typeof field === "function"));

const serialize = (current: Trace, value: unknown, seen = new Set<object>()): unknown => {
  if (typeof value === "number") return Number.isFinite(value) ? value : String(value);
  if (typeof value === "bigint") return String(value);
  if (typeof value === "function") {
    const callback = current.callbacks.get(value);
    return callback === undefined ? { fn: true } : { cb: callback };
  }
  if (typeof value !== "object" || value === null) return value;
  const name = current.names.get(value);
  if (name !== undefined) return { ref: name };
  const callback = current.callbacks.get(value);
  if (callback !== undefined) return { cb: callback };
  if (value instanceof Rational) return value.toString();
  if (value instanceof Impq) return [value.x.toString(), value.y.toString()];
  if (value instanceof LarTerm)
    return {
      col: value.column,
      coeffs: [...value.coeffs].map((entry) => [entry[0], entry[1].toString()]),
    };
  if (value instanceof Explanation) {
    const pairs: unknown = Reflect.get(value, "pairs");
    const expl = [...value];
    return Array.isArray(pairs) && pairs.length > 0
      ? { expl, pairs: serialize(current, pairs, seen) }
      : { expl };
  }
  if (value instanceof Anum) return { anum: serialize(current, value.value, seen) };
  if (isDependency(value)) return { dep: getLeaves(value) };
  if (seen.has(value)) return { cycle: true };
  seen.add(value);
  const getItems = (items: Iterable<unknown>) =>
    [...items].map((item) => serialize(current, item, seen));
  const result = Array.isArray(value)
    ? getItems(value)
    : value instanceof Map
      ? { map: getItems(value) }
      : isIterable(value) && Object.getPrototypeOf(value) !== Object.prototype
        ? { iter: getItems(value) }
        : Object.fromEntries(
            Object.entries(value).map((entry) => [entry[0], serialize(current, entry[1], seen)]),
          );
  seen.delete(value);
  return result;
};

// A callback lp makes, unless it comes while the theory answers another.
const wrapCallback = (current: Trace, name: string, run: (...args: unknown[]) => unknown) => {
  const callback = (...args: unknown[]) => {
    if (trace !== current || isInCallback) return run(...args);
    depth++;
    const line: TraceLine = { cb: name, a: args.map((arg) => serialize(current, arg)) };
    depth--;
    current.lines.push(line);
    isInCallback = true;
    try {
      const result = run(...args);
      depth++;
      line.r = serialize(current, result);
      depth--;
      return result;
    } catch (error) {
      line.e = describeError(error);
      throw error;
    } finally {
      isInCallback = false;
    }
  };
  current.callbacks.set(callback, name);
  return callback;
};

// An object of methods the theory passes to lp, whose calls are callbacks.
const wrapCallbacks = (current: Trace, name: string, target: object) => {
  const wrappers = new Map<string | symbol, unknown>();
  const proxy = new Proxy(target, {
    get: (_, key) => {
      const value: unknown = Reflect.get(target, key);
      if (typeof value !== "function" || typeof key === "symbol") return value;
      const wrapper =
        wrappers.get(key) ??
        wrapCallback(current, `${name}.${key}`, (...args) => Reflect.apply(value, target, args));
      wrappers.set(key, wrapper);
      return wrapper;
    },
  });
  current.callbacks.set(proxy, name);
  return proxy;
};

const isTraced = (current: Trace, value: unknown) =>
  typeof value === "object" &&
  value !== null &&
  (current.names.has(value) || current.callbacks.has(value));

const prepareArgument = (current: Trace, argument: unknown, name: string) =>
  typeof argument === "function"
    ? wrapCallback(current, name, (...args) => Reflect.apply(argument, undefined, args))
    : !isTraced(current, argument) && hasMethods(argument)
      ? wrapCallbacks(current, name, argument)
      : argument;

const flush = (current: Trace) => {
  if (current.lines.length === 0) return;
  const fs = process.getBuiltinModule("node:fs");
  fs.appendFileSync(
    current.path,
    `${current.lines.map((line) => JSON.stringify(line)).join("\n")}\n`,
  );
  current.lines = [];
};

// A call of the theory: its line, with the arguments as lp gets them, then the call one lp call
// deeper.
const recordCall = <Result>(
  current: Trace,
  owner: string,
  method: string,
  args: unknown[],
  run: () => Result,
  isResultRecorded: boolean,
) => {
  depth++;
  const line: TraceLine = { c: owner, m: method, a: args.map((arg) => serialize(current, arg)) };
  current.lines.push(line);
  try {
    const result = run();
    if (args.some((arg) => arg instanceof Explanation))
      line.o = args.map((arg) => serialize(current, arg));
    if (isResultRecorded) line.r = serialize(current, result);
    return result;
  } catch (error) {
    line.e = describeError(error);
    throw error;
  } finally {
    depth--;
    if (depth === 0 && !isInCallback && current.lines.length >= FLUSH_SIZE) flush(current);
  }
};

const recordRead = (current: Trace, owner: string, path: string, value: unknown) => {
  depth++;
  current.lines.push({ f: owner, p: path, r: serialize(current, value) });
  depth--;
};

// What a call returns: an object with methods is traced under a new id.
const share = (current: Trace, value: unknown) =>
  !isTraced(current, value) && hasMethods(value)
    ? traceObject(current, value, getId(current, "obj"), "")
    : value;

// A traced object, or an object a field read of one reached along path.
const traceObject = <Target extends object>(
  current: Trace,
  target: Target,
  owner: string,
  path: string,
): Target => {
  const isTheory = () => trace === current && depth === 0 && !isInCallback;
  const proxy = new Proxy(target, {
    get: (_, key) => {
      if (!isTheory()) return Reflect.get(target, key);
      depth++;
      const value: unknown = Reflect.get(target, key);
      depth--;
      if (typeof key === "symbol") {
        if (key !== Symbol.iterator || typeof value !== "function") return value;
        return () => {
          depth++;
          const items: unknown[] = [...Reflect.apply(value, target, [])];
          depth--;
          recordRead(current, owner, path, items);
          return items
            .map((item, index) =>
              !isTraced(current, item) && hasMethods(item)
                ? getPathProxy(current, item, owner, joinPath(path, String(index)))
                : item,
            )
            .values();
        };
      }
      const keyPath = joinPath(path, key);
      if (typeof value === "function")
        return (...args: unknown[]) => {
          if (!isTheory()) return Reflect.apply(value, target, args);
          const prepared = args.map((arg, index) =>
            prepareArgument(current, arg, `${owner}.${keyPath}.${index}`),
          );
          const result = recordCall(
            current,
            owner,
            keyPath,
            prepared,
            () => Reflect.apply(value, target, prepared),
            true,
          );
          return share(current, result);
        };
      if (typeof value !== "object" || value === null || isValue(value)) {
        recordRead(current, owner, keyPath, value);
        return value;
      }
      if (isTraced(current, value)) return value;
      return getPathProxy(current, value, owner, keyPath);
    },
    set: (_, key, value) => {
      if (!isTheory() || typeof key === "symbol") return Reflect.set(target, key, value);
      const keyPath = joinPath(path, key);
      const stored =
        typeof value === "function"
          ? wrapCallback(current, `${owner}.${keyPath}`, (...args) =>
              Reflect.apply(value, undefined, args),
            )
          : value;
      depth++;
      current.lines.push({ w: owner, p: keyPath, v: serialize(current, stored) });
      depth--;
      return Reflect.set(target, key, stored);
    },
  });
  current.names.set(proxy, path === "" ? owner : `${owner}.${path}`);
  return proxy;
};

const getPathProxy = (current: Trace, target: object, owner: string, path: string) => {
  const existing = current.pathProxies.get(target);
  if (existing !== undefined) return existing;
  const proxy = traceObject(current, target, owner, path);
  current.pathProxies.set(target, proxy);
  return proxy;
};

// An lp object the theory makes, traced while a decision is.
export const traceLp = <Args extends unknown[], Instance extends object>(
  kind: string,
  make: new (...args: Args) => Instance,
  ...args: Args
): Instance => {
  const current = trace;
  if (current === undefined) return new make(...args);
  const id = getId(current, kind);
  const prepared = args.map((arg, index) => prepareArgument(current, arg, `${id}.new.${index}`));
  const instance: Instance = recordCall(
    current,
    id,
    "new",
    prepared,
    () => Reflect.construct(make, prepared),
    false,
  );
  return traceObject(current, instance, id, "");
};

// An lp function the theory calls, traced while a decision is.
export const traceLpFunction = <Args extends unknown[], Result>(
  name: string,
  run: (...args: Args) => Result,
) => {
  const current = trace;
  if (current === undefined) return run;
  return (...args: Args) => recordCall(current, "lp", name, args, () => run(...args), true);
};

// Decides with a trace of the lp calls when PROVE_IT_LP_TRACE names a directory.
export const recordLpTrace = <Result>(text: string, decide: () => Result) => {
  const directory = getEnvironmentSetting("PROVE_IT_LP_TRACE");
  if (directory === undefined || directory === "") return decide();
  const fs = process.getBuiltinModule("node:fs");
  const digest = process
    .getBuiltinModule("node:crypto")
    .createHash("sha256")
    .update(text)
    .digest("hex")
    .slice(0, 16);
  fs.mkdirSync(directory, { recursive: true });
  const current: Trace = {
    path: process.getBuiltinModule("node:path").join(directory, `${digest}.lptrace`),
    lines: [],
    counts: new Map(),
    names: new WeakMap(),
    callbacks: new WeakMap(),
    pathProxies: new WeakMap(),
  };
  fs.writeFileSync(current.path, "");
  trace = current;
  depth = 0;
  isInCallback = false;
  try {
    return decide();
  } finally {
    flush(current);
    trace = undefined;
  }
};

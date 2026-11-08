// SANY analyzes TLC's standard modules the same way on every run, and the modules that TLC's trace
// exploration loads, _TLCTrace and the modules it needs, take it most of a small spec's run. The
// build analyzes them once and stores their level-checked nodes in dist as a table of objects,
// whose slots name other objects, constants, or the builtins of the specification, which each run
// creates anew.

import { existsSync, readFileSync } from "node:fs";

import { MissingBuildFileError, TlaError } from "../errors";
import { parseSanyModule } from "../parser";
import {
  generateSanySpecification,
  getDependencies,
  type ModuleDependencies,
  type PrecomputedModules,
} from "./generator";
import { checkModuleLevels } from "./levels";
import { getSanyStandardModules } from "./modules";
import type { ModuleNode, OpDefNode } from "./nodes";

type Constant = string | number | boolean | null;

// An object is its kind, then the index of its shape, of its external, or else the number of its
// elements or entries, then its slots. A slot is where an object starts in the snapshot's objects,
// or else -1 - the index of a constant. Constant 0 stands for undefined, which JSON has no word for.
type EncodedObject = number[];

interface EncodedDependencies {
  extendees: string[];
  instancees: string[];
  importers: [string, string][];
}

export interface SanySnapshot {
  modules: { name: string; node: number; dependencies: EncodedDependencies }[];
  maxId: number;
  constants: Constant[];
  shapes: string[][];
  // The objects one after another, which JSON reads faster than an array for each.
  objects: number[];
  // Where the objects that the modules reach without a lazy key end.
  eagerEnd: number;
}

const SNAPSHOT_URL = new URL("./sany-snapshot.json", import.meta.url);

const PLAIN_OBJECT = 0;
const ARRAY = 1;
const MAP = 2;
const SET = 3;
const EXTERNAL = 4;

// The keys of the parts of a node that SANY seldom reads of a standard module, and that hold most
// of the snapshot's objects: the bodies of definitions, the hash tables of contexts, and the level
// conditions of operators. The decode builds each such part once it is read.
const LAZY_KEYS = new Set(["body", "table", "opLevelCond"]);

// The objects of a specification's builtins, which the standard modules' nodes refer to: the
// builtins and their phony parameters, in the order SANY creates them.
const getExternals = (builtins: OpDefNode[]): object[] => [
  ...builtins,
  ...builtins.flatMap((builtin) => builtin.params ?? []),
];

const getReachable = (roots: unknown[]) => {
  const reachable = new Set<unknown>();
  const pending = [...roots];
  while (pending.length > 0) {
    const value = pending.pop();
    if (typeof value !== "object" || value === null || reachable.has(value)) continue;
    reachable.add(value);
    if (value instanceof Map) value.forEach((entry, key) => pending.push(key, entry));
    else if (value instanceof Set) value.forEach((entry) => pending.push(entry));
    else pending.push(...Object.values(value));
  }
  return reachable;
};

export const createSanySnapshot = (): SanySnapshot => {
  const standardModules = getSanyStandardModules("master");
  // The report level-checks each module once SANY has analyzed it, which the snapshot repeats.
  const specification = generateSanySpecification(
    "---- MODULE Snapshot ----\n====\n",
    (name) => standardModules.get(name),
    {
      rootFileName: "Snapshot",
      rootExtendees: ["_TLCTrace"],
      onModule: (module, messages) => checkModuleLevels(module, { messages, isTlc174: false }),
    },
  );
  if (specification.messages.length > 0) {
    throw new TlaError("SANY reports messages for its standard modules");
  }
  const modules = specification.modules.slice(0, -1);
  const externals = getExternals(specification.builtins);
  const externalIndexes = new Map(externals.map((external, index) => [external, index]));
  const builtinObjects = getReachable(specification.builtins);
  // The objects in the order the decode makes them: first those that the modules reach without
  // a lazy key, then the rest.
  const objects: object[] = [...modules];
  const objectIndexes = new Map<unknown, number>(objects.map((object, index) => [object, index]));
  const addObject = (value: unknown) => {
    if (typeof value !== "object" || value === null || objectIndexes.has(value)) return;
    objectIndexes.set(value, objects.length);
    objects.push(value);
  };
  const lazyParts: unknown[] = [];
  const eager = { end: 0 };
  for (let index = 0; index < objects.length; index++) {
    const value = objects[index];
    if (externalIndexes.has(value)) continue;
    if (value instanceof Map) value.forEach((entry, key) => [key, entry].forEach(addObject));
    else if (value instanceof Set || Array.isArray(value)) value.forEach(addObject);
    else {
      Object.entries(value).forEach((entry) =>
        eager.end === 0 && LAZY_KEYS.has(entry[0]) ? lazyParts.push(entry[1]) : addObject(entry[1]),
      );
    }
    if (index === objects.length - 1 && eager.end === 0) {
      eager.end = objects.length;
      lazyParts.forEach(addObject);
    }
  }
  const constants: Constant[] = [null];
  const constantIndexes = new Map<unknown, number>([[undefined, 0]]);
  const shapes: string[][] = [];
  const shapeIndexes = new Map<string, number>();
  const encodeSlot = (value: unknown): number => {
    const objectIndex = objectIndexes.get(value);
    if (objectIndex !== undefined) return objectIndex;
    const isConstant =
      value === null ||
      typeof value === "string" ||
      typeof value === "boolean" ||
      (typeof value === "number" && Number.isFinite(value) && !Object.is(value, -0));
    if (!isConstant && value !== undefined) {
      throw new TlaError(`SANY's standard modules hold a value JSON can't keep: ${String(value)}`);
    }
    const index = constantIndexes.get(value) ?? constants.length;
    if (index === constants.length) {
      constantIndexes.set(value, index);
      constants.push(value ?? null);
    }
    return -1 - index;
  };
  const encodeObject = (value: object): EncodedObject => {
    const externalIndex = externalIndexes.get(value);
    if (externalIndex !== undefined) return [EXTERNAL, externalIndex];
    if (builtinObjects.has(value) || Object.getPrototypeOf(value) === null) {
      throw new TlaError("SANY's standard modules share an object with the builtins");
    }
    if (Array.isArray(value)) return [ARRAY, value.length, ...value.map(encodeSlot)];
    if (value instanceof Map) {
      return [
        MAP,
        value.size,
        ...[...value].flatMap((entry) => [encodeSlot(entry[0]), encodeSlot(entry[1])]),
      ];
    }
    if (value instanceof Set) return [SET, value.size, ...[...value].map(encodeSlot)];
    if (Object.getPrototypeOf(value) !== Object.prototype) {
      throw new TlaError("SANY's standard modules hold an object JSON can't keep");
    }
    const keys = Object.keys(value);
    const shape = shapeIndexes.get(keys.join()) ?? shapes.length;
    if (shape === shapes.length) {
      shapeIndexes.set(keys.join(), shape);
      shapes.push(keys);
    }
    return [PLAIN_OBJECT, shape, ...Object.values(value).map(encodeSlot)];
  };
  const encoded = objects.map(encodeObject);
  // Where each object starts in the objects one after another.
  const starts = encoded.map(() => 0);
  encoded.forEach((object, index) => {
    if (index + 1 < starts.length) starts[index + 1] = starts[index] + object.length;
  });
  return {
    modules: modules.map((module, index) => {
      const text = standardModules.get(module.name) ?? "";
      const dependencies = getDependencies(parseSanyModule(text));
      return {
        name: module.name,
        node: starts[index],
        dependencies: {
          extendees: dependencies.extendees,
          instancees: dependencies.instancees,
          importers: [...dependencies.importers],
        },
      };
    }),
    maxId: objects.reduce(
      (maxId, object) =>
        "id" in object && typeof object.id === "number" && !externalIndexes.has(object)
          ? Math.max(maxId, object.id)
          : maxId,
      0,
    ),
    constants,
    shapes,
    eagerEnd: encoded.slice(0, eager.end).reduce((end, object) => end + object.length, 0),
    objects: encoded.flatMap((object) => [
      object[0],
      object[1],
      ...object.slice(2).map((slot) => (slot >= 0 ? starts[slot] : slot)),
    ]),
  };
};

// Makes the objects the modules reach without a lazy key in two passes, so an object can refer to
// any other, and the others once a lazy key is read.
const decodeModules = (snapshot: SanySnapshot, builtins: OpDefNode[]) => {
  const externals = getExternals(builtins);
  const constants = snapshot.constants.map((constant, index) =>
    index === 0 ? undefined : constant,
  );
  const shapes = snapshot.shapes;
  // An object starts as a copy of its shape's template, which holds every key, so filling it in
  // adds no key.
  const templates = shapes.map((keys) => Object.fromEntries(keys.map((key) => [key, undefined])));
  const lazyKeys = shapes.map((keys) => keys.map((key) => LAZY_KEYS.has(key)));
  const slots = snapshot.objects;
  // Each object by where it starts, once it is made.
  const objects: (object | undefined)[] = new Array(slots.length).fill(undefined);
  const getEnd = (start: number) => {
    const kind = slots[start];
    const count = slots[start + 1];
    return (
      start +
      2 +
      (kind === PLAIN_OBJECT
        ? shapes[count].length
        : kind === EXTERNAL
          ? 0
          : kind === MAP
            ? 2 * count
            : count)
    );
  };
  const make = (start: number) => {
    const kind = slots[start];
    objects[start] =
      kind === EXTERNAL
        ? externals[slots[start + 1]]
        : kind === PLAIN_OBJECT
          ? { ...templates[slots[start + 1]] }
          : kind === ARRAY
            ? []
            : kind === MAP
              ? new Map()
              : new Set();
  };
  const getSlot = (slot: number) => (slot >= 0 ? objects[slot] : constants[-1 - slot]);
  const setData = (target: object, key: string, value: unknown) =>
    Object.defineProperty(target, key, {
      value,
      writable: true,
      enumerable: true,
      configurable: true,
    });
  const fill = (start: number) => {
    const target = objects[start];
    const first = start + 2;
    const count = slots[start + 1];
    if (slots[start] === EXTERNAL || target === undefined) return;
    if (target instanceof Map) {
      for (let slot = first; slot < first + 2 * count; slot += 2) {
        target.set(getSlot(slots[slot]), getSlot(slots[slot + 1]));
      }
    } else if (target instanceof Set) {
      for (let slot = first; slot < first + count; slot++) target.add(getSlot(slots[slot]));
    } else if (Array.isArray(target)) {
      for (let slot = first; slot < first + count; slot++) target.push(getSlot(slots[slot]));
    } else {
      const keys = shapes[count];
      for (let slot = 0; slot < keys.length; slot++) {
        const value = slots[first + slot];
        const key = keys[slot];
        if (value < 0 || objects[value] !== undefined) Reflect.set(target, key, getSlot(value));
        else {
          Object.defineProperty(target, key, {
            enumerable: true,
            configurable: true,
            get: () => {
              const object = build(value);
              setData(target, key, object);
              return object;
            },
            set: (object) => {
              setData(target, key, object);
            },
          });
        }
      }
    }
  };
  // Makes a lazy part: the objects not yet made that it reaches without a lazy key.
  const build = (root: number) => {
    const made: number[] = [];
    const pending = [root];
    for (let start = pending.pop(); start !== undefined; start = pending.pop()) {
      if (objects[start] !== undefined) continue;
      make(start);
      made.push(start);
      if (slots[start] === EXTERNAL) continue;
      const isLazy = slots[start] === PLAIN_OBJECT ? lazyKeys[slots[start + 1]] : undefined;
      const end = getEnd(start);
      for (let slot = start + 2; slot < end; slot++) {
        const value = slots[slot];
        if (value >= 0 && objects[value] === undefined && !isLazy?.[slot - start - 2]) {
          pending.push(value);
        }
      }
    }
    made.forEach(fill);
    return objects[root];
  };
  for (let start = 0; start < snapshot.eagerEnd; start = getEnd(start)) make(start);
  for (let start = 0; start < snapshot.eagerEnd; start = getEnd(start)) fill(start);
  return new Map(
    snapshot.modules.map((module): [string, ModuleNode] => [
      module.name,
      // HACK: the slot holds the module's node, which the snapshot encoded from one.
      objects[module.node] as ModuleNode,
    ]),
  );
};

export const getPrecomputedModules = (snapshot: SanySnapshot): PrecomputedModules => {
  const standardModules = getSanyStandardModules("master");
  return {
    sources: new Map(
      snapshot.modules.map((module) => [module.name, standardModules.get(module.name) ?? ""]),
    ),
    dependencies: new Map(
      snapshot.modules.map((module): [string, ModuleDependencies] => [
        module.name,
        {
          extendees: module.dependencies.extendees,
          instancees: module.dependencies.instancees,
          importers: new Map(module.dependencies.importers),
        },
      ]),
    ),
    maxId: snapshot.maxId,
    getModules: (builtins) => decodeModules(snapshot, builtins),
  };
};

// The executables build-binary.ts compiles define PROVE_IT_BINARY, and embed the snapshot.
declare const PROVE_IT_BINARY: boolean | undefined;

// The snapshot the build wrote beside the bundle, which a run from the sources goes without. An
// executable that can't find it would analyze the standard modules on every run.
export const readSanySnapshot = () => {
  if (existsSync(SNAPSHOT_URL)) {
    return getPrecomputedModules(JSON.parse(readFileSync(SNAPSHOT_URL, "utf8")));
  }
  if (typeof PROVE_IT_BINARY === "boolean" && PROVE_IT_BINARY) {
    throw new MissingBuildFileError(SNAPSHOT_URL);
  }
  return undefined;
};

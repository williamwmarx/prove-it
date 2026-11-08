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

// A slot of an object: the index of an object at or above 0, or else -1 - the index of a constant.
// Constant 0 stands for undefined, which JSON has no word for.
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
  objects: EncodedObject[];
}

const SNAPSHOT_URL = new URL("./sany-snapshot.json", import.meta.url);

const PLAIN_OBJECT = 0;
const ARRAY = 1;
const MAP = 2;
const SET = 3;
const EXTERNAL = 4;

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
  const objects: object[] = [];
  const objectIndexes = new Map<object, number>();
  const constants: Constant[] = [null];
  const constantIndexes = new Map<unknown, number>([[undefined, 0]]);
  const shapes: string[][] = [];
  const shapeIndexes = new Map<string, number>();
  const encodeSlot = (value: unknown): number => {
    if (typeof value === "object" && value !== null) {
      const index = objectIndexes.get(value) ?? objects.length;
      if (index === objects.length) {
        objectIndexes.set(value, index);
        objects.push(value);
      }
      return index;
    }
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
    if (Array.isArray(value)) return [ARRAY, ...value.map(encodeSlot)];
    if (value instanceof Map) {
      return [MAP, ...[...value].flatMap((entry) => [encodeSlot(entry[0]), encodeSlot(entry[1])])];
    }
    if (value instanceof Set) return [SET, ...[...value].map(encodeSlot)];
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
  const moduleSlots = modules.map(encodeSlot);
  const encoded: EncodedObject[] = [];
  // Encoding an object can add objects to encode.
  for (let index = 0; index < objects.length; index++) encoded.push(encodeObject(objects[index]));
  return {
    modules: modules.map((module, index) => {
      const text = standardModules.get(module.name) ?? "";
      const dependencies = getDependencies(parseSanyModule(text));
      return {
        name: module.name,
        node: moduleSlots[index],
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
    objects: encoded,
  };
};

// Builds the nodes in two passes, so an object can refer to any other.
const decodeModules = (snapshot: SanySnapshot, builtins: OpDefNode[]) => {
  const externals = getExternals(builtins);
  const constants = snapshot.constants.map((constant, index) =>
    index === 0 ? undefined : constant,
  );
  const objects = snapshot.objects.map((entry): object => {
    switch (entry[0]) {
      case EXTERNAL:
        return externals[entry[1]];
      case ARRAY:
        return [];
      case MAP:
        return new Map();
      case SET:
        return new Set();
      default:
        return {};
    }
  });
  const getSlot = (slot: number) => (slot >= 0 ? objects[slot] : constants[-1 - slot]);
  snapshot.objects.forEach((entry, index) => {
    const target = objects[index];
    if (target instanceof Map) {
      for (let slot = 1; slot < entry.length; slot += 2) {
        target.set(getSlot(entry[slot]), getSlot(entry[slot + 1]));
      }
    } else if (target instanceof Set) {
      for (let slot = 1; slot < entry.length; slot++) target.add(getSlot(entry[slot]));
    } else if (Array.isArray(target)) {
      for (let slot = 1; slot < entry.length; slot++) target.push(getSlot(entry[slot]));
    } else if (entry[0] === PLAIN_OBJECT) {
      const keys = snapshot.shapes[entry[1]];
      for (let slot = 0; slot < keys.length; slot++) {
        Reflect.set(target, keys[slot], getSlot(entry[slot + 2]));
      }
    }
  });
  return new Map(
    snapshot.modules.map((module): [string, ModuleNode] => [
      module.name,
      // HACK: the slot holds the module's node, which the snapshot encoded from one.
      getSlot(module.node) as ModuleNode,
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

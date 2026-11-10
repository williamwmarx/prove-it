// The native engine as WebAssembly, which native/crates/prove-it-wasm builds, for where there is
// no process.dlopen to load the addon. It offers the addon's functions over the module's ABI: each
// call's arguments go into the module's memory as one array in the format encoding.rs describes,
// and its result comes back in it. Where the addon writes into an array it is given, the module
// returns the new elements, which this copies in.
//
// A trap leaves the instance's stack pointer and borrows where they were, so it is replaced with
// a new one. The engine runs on the host's call stack, which is shallower than the addon's search
// thread's, so a check that exhausts it stops without handing anything over, and the interpreter
// searches from the start, as for any such stop. So that what the search reported and printed
// before then isn't reported again, its events are held until the check returns, and dropped where
// it ran out of stack. The call blocks the thread throughout, so nothing sees them sooner either way.

import { isStackOverflow } from "../errors";
import type { NativeAddon } from "./native";

const UNDEFINED = 0;
const NULL = 1;
const FALSE = 2;
const TRUE = 3;
const NUMBER = 4;
const TEXT = 5;
const INT32S = 6;
const FLOAT64S = 7;
const BIGINT64S = 8;
const UINT8S = 9;
const ARRAY = 10;
const OBJECT = 11;

const TYPE_ERROR = 1;

type Argument =
  | undefined
  | null
  | boolean
  | number
  | string
  | Int32Array
  | Float64Array
  | BigInt64Array
  | Uint8Array
  | Argument[];

interface Exports {
  memory: WebAssembly.Memory;
  prove_it_alloc: (length: number) => number;
  prove_it_free: (pointer: number, length: number) => void;
  prove_it_abi_version: () => number;
  prove_it_check: Call;
  prove_it_decide: Call;
  prove_it_sany_text: Call;
  prove_it_store_perform: Call;
  prove_it_store_decode: Call;
  prove_it_store_encode: Call;
  prove_it_store_fingerprints: Call;
  prove_it_store_reset_fingerprints: Call;
}

type Call = (pointer: number, length: number) => number;

type CallName = {
  [Name in keyof Exports]: Exports[Name] extends Call ? Name : never;
}[keyof Exports];

// The events of the check that is running, each a call of its callbacks, in the order it made them.
interface Running {
  report: Parameters<NativeAddon["check"]>[3];
  print: Parameters<NativeAddon["check"]>[4];
  events: (() => void)[];
}

const getSize = (value: Argument): number =>
  value === undefined || value === null || typeof value === "boolean"
    ? 1
    : typeof value === "number"
      ? 9
      : typeof value === "string"
        ? 5 + 2 * value.length
        : Array.isArray(value)
          ? value.reduce<number>((size, element) => size + getSize(element), 5)
          : 5 + value.byteLength;

const getTypedTag = (value: Int32Array | Float64Array | BigInt64Array | Uint8Array) =>
  value instanceof Int32Array
    ? INT32S
    : value instanceof Float64Array
      ? FLOAT64S
      : value instanceof BigInt64Array
        ? BIGINT64S
        : UINT8S;

// Writes a value at an offset of the memory, and returns the offset after it. WebAssembly is
// little-endian, as every platform JavaScript runs on is, so typed arrays are copied as they are.
const write = (memory: Uint8Array, view: DataView, offset: number, value: Argument): number => {
  if (value === undefined || value === null || typeof value === "boolean") {
    view.setUint8(
      offset,
      value === undefined ? UNDEFINED : value === null ? NULL : value ? TRUE : FALSE,
    );
    return offset + 1;
  }
  if (typeof value === "number") {
    view.setUint8(offset, NUMBER);
    view.setFloat64(offset + 1, value, true);
    return offset + 9;
  }
  if (typeof value === "string") {
    view.setUint8(offset, TEXT);
    view.setUint32(offset + 1, value.length, true);
    for (let index = 0; index < value.length; index++) {
      view.setUint16(offset + 5 + 2 * index, value.charCodeAt(index), true);
    }
    return offset + 5 + 2 * value.length;
  }
  if (Array.isArray(value)) {
    view.setUint8(offset, ARRAY);
    view.setUint32(offset + 1, value.length, true);
    return value.reduce<number>((next, element) => write(memory, view, next, element), offset + 5);
  }
  view.setUint8(offset, getTypedTag(value));
  view.setUint32(offset + 1, value.length, true);
  memory.set(new Uint8Array(value.buffer, value.byteOffset, value.byteLength), offset + 5);
  return offset + 5 + value.byteLength;
};

const getText = (units: Uint16Array) => {
  const parts = [];
  for (let start = 0; start < units.length; start += 8192) {
    parts.push(String.fromCharCode(...units.subarray(start, start + 8192)));
  }
  return parts.join("");
};

// Reads the value at an offset of the memory, with the offset after it. Typed arrays are copied
// out, since the module frees what they were read from.
const read = (memory: Uint8Array, view: DataView, offset: number): [unknown, number] => {
  const tag = view.getUint8(offset);
  if (tag === UNDEFINED) return [undefined, offset + 1];
  if (tag === NULL) return [null, offset + 1];
  if (tag === FALSE || tag === TRUE) return [tag === TRUE, offset + 1];
  if (tag === NUMBER) return [view.getFloat64(offset + 1, true), offset + 9];
  const count = view.getUint32(offset + 1, true);
  const start = offset + 5;
  const copy = (width: number) => memory.slice(start, start + count * width).buffer;
  if (tag === TEXT) return [getText(new Uint16Array(copy(2))), start + 2 * count];
  if (tag === INT32S) return [new Int32Array(copy(4)), start + 4 * count];
  if (tag === FLOAT64S) return [new Float64Array(copy(8)), start + 8 * count];
  if (tag === BIGINT64S) return [new BigInt64Array(copy(8)), start + 8 * count];
  if (tag === UINT8S) return [new Uint8Array(copy(1)), start + count];
  if (tag !== ARRAY && tag !== OBJECT) throw new TypeError(`${tag} tags no value`);
  const elements: unknown[] = [];
  const object: Record<string, unknown> = {};
  const next = Array.from({ length: count }).reduce<number>((at) => {
    if (tag === ARRAY) {
      const [element, after] = read(memory, view, at);
      elements.push(element);
      return after;
    }
    const length = view.getUint32(at, true);
    const name = getText(new Uint16Array(memory.slice(at + 4, at + 4 + 2 * length).buffer));
    const [property, after] = read(memory, view, at + 4 + 2 * length);
    object[name] = property;
    return after;
  }, start);
  return [tag === ARRAY ? elements : object, next];
};

const getMemory = (exports: Exports) =>
  [new Uint8Array(exports.memory.buffer), new DataView(exports.memory.buffer)] as const;

// Calls an export with its arguments, and returns its result or throws its TypeError.
const callExport = (exports: Exports, call: Call, args: Argument[]) => {
  const size = getSize(args);
  const pointer = exports.prove_it_alloc(size);
  const [memory, view] = getMemory(exports);
  write(memory, view, pointer, args);
  const result = call(pointer, size);
  const [after, afterView] = getMemory(exports);
  const length = afterView.getUint32(result, true);
  const [value] = read(after, afterView, result + 5);
  const isTypeError = afterView.getUint8(result + 4) === TYPE_ERROR;
  exports.prove_it_free(result, 4 + length);
  if (isTypeError) throw new TypeError(String(value));
  return value;
};

// What a check returned, after its events, or a stop that hands nothing over and drops them where
// it ran out of stack. Once a callback throws, the rest aren't called, as with the addon, and the
// check throws that.
const getChecked = (check: Running, call: () => unknown): ReturnType<NativeAddon["check"]> => {
  const outcome = (() => {
    try {
      return call() as ReturnType<NativeAddon["check"]>;
    } catch (error) {
      if (!isStackOverflow(error)) throw error;
      return undefined;
    }
  })();
  if (outcome === undefined) {
    return {
      status: "stopped",
      reason: "WebAssembly ran out of stack",
      counts: Float64Array.of(0),
    };
  }
  check.events.forEach((event) => event());
  return outcome;
};

// The addon's functions over a compiled module of the engine.
export const instantiateEngine = (module: WebAssembly.Module): NativeAddon => {
  const running: { check?: Running } = {};
  const imports = {
    env: {
      prove_it_now: () => performance.now(),
      // The state log, which goes nowhere without a file system.
      prove_it_write: (
        pathPointer: number,
        pathLength: number,
        pointer: number,
        length: number,
        isAppended: number,
      ) => {
        const fs = globalThis.process?.getBuiltinModule?.("node:fs");
        if (fs === undefined) return;
        const memory = new Uint8Array(current.exports.memory.buffer);
        const path = new TextDecoder().decode(
          memory.subarray(pathPointer, pathPointer + pathLength),
        );
        const bytes = memory.slice(pointer, pointer + length);
        // The addon writes no log where it can't create or write the file, and the check goes on.
        try {
          if (isAppended === 1) fs.appendFileSync(path, bytes);
          else fs.writeFileSync(path, bytes);
        } catch {
          return;
        }
      },
      prove_it_report: (kind: number, a: number, b: number, c: number, d: number, e: number) => {
        const check = running.check;
        check?.events.push(() => check.report(kind, a, b, c, d, e));
      },
      // The values are read now, while the memory holds them.
      prove_it_print: (pointer: number) => {
        const check = running.check;
        if (check === undefined) return;
        const [memory, view] = getMemory(current.exports);
        const [width, words, strings] = read(memory, view, pointer)[0] as [
          number,
          Int32Array,
          string[],
        ];
        check.events.push(() => check.print(width, words, strings));
      },
    },
  };
  const instantiate = () => new WebAssembly.Instance(module, imports).exports as unknown as Exports;
  const current = { exports: instantiate() };
  const callCurrent = (name: CallName, args: Argument[]) => {
    try {
      return callExport(current.exports, current.exports[name], args);
    } catch (error) {
      if (error instanceof WebAssembly.RuntimeError || isStackOverflow(error)) {
        current.exports = instantiate();
      }
      throw error;
    }
  };
  return {
    abiVersion: () => current.exports.prove_it_abi_version(),
    check: (ir, settings, stateLog, report, print) => {
      const check: Running = { report, print, events: [] };
      running.check = check;
      try {
        return getChecked(check, () => callCurrent("prove_it_check", [ir, settings, stateLog]));
      } finally {
        running.check = undefined;
      }
    },
    // A decision runs on this thread, so nothing can set a cancel cell while it runs.
    decide: (prover, text, timeLimitMs, stepLimit) =>
      callCurrent("prove_it_decide", [prover, text, timeLimitMs, stepLimit]) as ReturnType<
        NativeAddon["decide"]
      >,
    sanyText: (root, source, fileName, known) =>
      callCurrent("prove_it_sany_text", [root, source, fileName, known]) as ReturnType<
        NativeAddon["sanyText"]
      >,
    storePerform: (name, args) =>
      callCurrent("prove_it_store_perform", [name, args as Argument[]]) as
        number | boolean | null | string,
    storeDecode: (words, strings, width, count, ids) => {
      const decoded = callCurrent("prove_it_store_decode", [words, strings, width, count, ids]);
      if (typeof decoded === "string") return decoded;
      ids.set(decoded as Int32Array);
      return null;
    },
    storeEncode: (states, width) =>
      callCurrent("prove_it_store_encode", [states, width]) as ReturnType<
        NativeAddon["storeEncode"]
      >,
    storeFingerprints: (states, width, order, parents, isReference, fingerprints) => {
      fingerprints.set(
        callCurrent("prove_it_store_fingerprints", [
          states,
          width,
          order,
          parents,
          isReference,
          fingerprints,
        ]) as BigInt64Array,
      );
    },
    storeResetFingerprints: () => {
      callCurrent("prove_it_store_reset_fingerprints", []);
    },
  };
};

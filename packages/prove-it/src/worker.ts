// Worker threads as Web Workers, or as Node's worker_threads where there are none.

import { MissingBuildFileError } from "./errors";

const WORKER_THREADS_MODULE = "node:worker_threads";
const BUN_JSC_MODULE = "bun:jsc";

export interface Port {
  postMessage: (message: unknown, transfer?: unknown[]) => void;
  addEventListener: (type: "message", listener: (event: { data: unknown }) => void) => void;
  removeEventListener?: (type: "message", listener: (event: { data: unknown }) => void) => void;
  start?: () => void;
}

export interface WorkerHandle {
  postMessage: (message: unknown, transfer?: unknown[]) => void;
  terminate: () => void;
}

interface WebWorker {
  postMessage: (message: unknown, transfer?: unknown[]) => void;
  addEventListener: (type: string, listener: (event: { data: unknown }) => void) => void;
  terminate: () => void;
}

declare const Worker: new (url: URL, options: { type: "module" }) => WebWorker;

export const isWorkerSupported = () =>
  typeof Worker === "function" ||
  (typeof process !== "undefined" && process.versions?.node !== undefined);

// A worker whose entry isn't in the file its URL names would only report an error once it fails to
// load, which a search that runs on meanwhile never sees, so a build that left the entry out, or put
// it elsewhere, fails here rather than checking with fewer threads than it was asked for. Bun runs
// the entry's TypeScript from the sources, where the build puts its JavaScript.
export const assertWorkerFile = (url: URL) => {
  const fs =
    url.protocol === "file:" && typeof process !== "undefined"
      ? process.getBuiltinModule?.("node:fs")
      : undefined;
  const isFound =
    fs === undefined ||
    fs.existsSync(url) ||
    ("Bun" in globalThis && fs.existsSync(new URL(url.href.replace(/\.js$/, ".ts"))));
  if (!isFound) throw new MissingBuildFileError(url);
};

// The caller writes url as new URL("./name.js", import.meta.url) for bundlers to find.
export const spawnWorker = async (
  url: URL,
  onMessage: (message: unknown) => void,
  onError: (error: unknown) => void,
): Promise<WorkerHandle> => {
  assertWorkerFile(url);
  if (typeof Worker === "function") {
    const worker = new Worker(url, { type: "module" });
    worker.addEventListener("message", (event) => onMessage(event.data));
    worker.addEventListener("error", onError);
    return worker;
  }
  const threads: typeof import("node:worker_threads") = await import(
    /* @vite-ignore */ /* webpackIgnore: true */ WORKER_THREADS_MODULE
  );
  const worker = new threads.Worker(url);
  worker.on("message", onMessage);
  worker.on("error", onError);
  return {
    postMessage: (message, transfer) =>
      worker.postMessage(message, transfer as Parameters<typeof worker.postMessage>[1]),
    terminate: () => void worker.terminate(),
  };
};

export const getParentPort = async () => {
  if (typeof (globalThis as { postMessage?: unknown }).postMessage === "function") {
    return globalThis as unknown as Port;
  }
  const threads: typeof import("node:worker_threads") = await import(
    /* @vite-ignore */ /* webpackIgnore: true */ WORKER_THREADS_MODULE
  );
  return threads.parentPort as unknown as Port;
};

// A break runs an eden collection on Bun, then lets the event loop turn, where JavaScriptCore's
// timers give back the memory the collection freed.
export const createBreak = () => {
  const jsc: Promise<{ edenGC: () => void }> | undefined =
    "Bun" in globalThis
      ? import(/* @vite-ignore */ /* webpackIgnore: true */ BUN_JSC_MODULE)
      : undefined;
  return async () => {
    (await jsc)?.edenGC();
    await new Promise((resolve) =>
      typeof setImmediate === "function" ? setImmediate(resolve) : setTimeout(resolve, 0),
    );
  };
};

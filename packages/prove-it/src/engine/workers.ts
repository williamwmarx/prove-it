// Starts the engine's worker threads without waiting, since the search that wants them runs on
// synchronously: as Web Workers where the host has them, such as Bun, or as Node's worker_threads.

import type { ModelConfig } from "../config";
import type { EngineStartMessage } from "../engine-worker";
import type { TlcVersion } from "../tlc/version";
import { assertWorkerFile } from "../worker";

interface StartInfo {
  source: string;
  config: ModelConfig;
  modules: [string, string | undefined][];
  isWarningEnabled: boolean;
  version: TlcVersion | undefined;
}

export interface EngineWorkers {
  post: (message: unknown) => void;
  // How many workers have built the spec's environment.
  getStartedCount: () => number;
  terminate: () => void;
}

interface ThreadHandle {
  postMessage: (message: unknown) => void;
  terminate: () => unknown;
}

const WORKER_URL = new URL("./engine-worker.js", import.meta.url);

const createThread = (): ThreadHandle | undefined => {
  const WebWorker = (globalThis as { Worker?: new (url: URL, options: object) => ThreadHandle })
    .Worker;
  if (typeof WebWorker === "function") return new WebWorker(WORKER_URL, { type: "module" });
  const getBuiltinModule = (
    globalThis as {
      process?: { getBuiltinModule?: (name: string) => unknown };
    }
  ).process?.getBuiltinModule;
  const threads = getBuiltinModule?.("node:worker_threads") as
    { Worker: new (url: URL) => ThreadHandle & { unref: () => void } } | undefined;
  if (!threads) return undefined;
  const worker = new threads.Worker(WORKER_URL);
  worker.unref();
  return worker;
};

export const spawnEngineWorkers = (count: number, info: StartInfo): EngineWorkers | undefined => {
  const started = new SharedArrayBuffer(4);
  const threads: ThreadHandle[] = [];
  assertWorkerFile(WORKER_URL);
  for (let index = 0; index < count; index++) {
    // A host without workers searches alone.
    const thread = (() => {
      try {
        return createThread();
      } catch {
        return undefined;
      }
    })();
    if (!thread) break;
    threads.push(thread);
  }
  if (threads.length === 0) return undefined;
  const start: EngineStartMessage = { type: "start", ...info, started };
  threads.forEach((thread) => thread.postMessage(start));
  const startedCount = new Int32Array(started);
  return {
    post: (message) => threads.forEach((thread) => thread.postMessage(message)),
    getStartedCount: () => Atomics.load(startedCount, 0),
    terminate: () => threads.forEach((thread) => void thread.terminate()),
  };
};

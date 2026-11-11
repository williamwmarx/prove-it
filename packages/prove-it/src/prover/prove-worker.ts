// A worker of the decide pool: it decides each request with the backend its prover selects.

import { loadWasmEngine } from "../engine/native";
import { TlaProverError } from "../errors";
import { getParentPort } from "../worker";
import { type DecideRequest, type DecideResponse, WORKER_READY } from "./decide-pool";
import { decide } from "./deciders";

const getResponse = (request: DecideRequest): DecideResponse => {
  try {
    return decide(request.prover, request.text, {
      timeLimitMs: request.timeLimitMs,
      cancel: request.cancel,
    });
  } catch (error) {
    if (error instanceof TlaProverError) return { error: error.message };
    throw error;
  }
};

// The worker answers once the engine as WebAssembly has compiled where there is no process.dlopen,
// as in a browser, and says so, so that the pool sends it nothing before. An error a backend throws
// then escapes the handler, as the pool's error listener expects.
void Promise.all([getParentPort(), loadWasmEngine()]).then(([parent]) => {
  parent.addEventListener("message", (event) =>
    parent.postMessage(getResponse(event.data as DecideRequest)),
  );
  parent.start?.();
  parent.postMessage(WORKER_READY);
});

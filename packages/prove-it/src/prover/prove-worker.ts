// A worker of the decide pool: it decides each request with the backend its prover selects.

import { loadWasmEngine } from "../engine/native";
import { TlaProverError } from "../errors";
import { getParentPort } from "../worker";
import type { DecideRequest, DecideResponse } from "./decide-pool";
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

// Where there is no process.dlopen, as in a browser, the engine as WebAssembly compiles before the
// worker decides. Each request waits for the same promise, so the answers keep their order.
const loaded = loadWasmEngine();

void getParentPort().then((parent) => {
  parent.addEventListener("message", (event) =>
    loaded.then(() => parent.postMessage(getResponse(event.data as DecideRequest))),
  );
  parent.start?.();
});

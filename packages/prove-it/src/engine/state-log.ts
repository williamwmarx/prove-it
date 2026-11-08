// PROVE_IT_STATE_LOG=path makes the engine's search write the states it found to the file, in
// TLC's order, once it ends, whether it completed or stopped. The first line is a header:
//   {"version": 1, "variables": [...], "count": n, "stopped": reason or null, "expanding": k}
// and each state is a line of its own:
//   [index, parent, action, fingerprint, words, strings]
// with the parent -1 for an initial state, the action the position in spec.actions of the action
// that first reached the state, or -1 when the search doesn't label its steps, TLC's fingerprint of
// the state's key as 16 hex digits, and the state in transfer.ts's encoding, for printing.
// Two searches agree when their headers and the first four fields of every state do.

import { createStateEncoder } from "../transfer";
import { toValue } from "./convert";
import { writeDebugFile } from "./settings";

export interface StateLog {
  variables: string[];
  states: Int32Array;
  parents: Int32Array;
  count: number;
  fingerprints: BigInt64Array;
  edges: Int32Array | undefined;
  labels: Int32Array | undefined;
  stopped: string | undefined;
  expanding: number;
}

export const writeStateLog = (getLog: () => StateLog) =>
  writeDebugFile("PROVE_IT_STATE_LOG", function* () {
    const log = getLog();
    const width = log.variables.length;
    const actions = new Int32Array(log.count).fill(-1);
    const isReached = new Uint8Array(log.count);
    if (log.edges && log.labels) {
      for (const [edge, target] of log.edges.entries()) {
        if (target >= log.count || isReached[target] || log.parents[target] === -1) continue;
        isReached[target] = 1;
        actions[target] = log.labels[edge];
      }
    }
    yield JSON.stringify({
      version: 1,
      variables: log.variables,
      count: log.count,
      stopped: log.stopped ?? null,
      expanding: log.expanding,
    });
    for (let index = 0; index < log.count; index++) {
      const encoder = createStateEncoder();
      encoder.encode(
        Array.from({ length: width }, (_, variable) =>
          toValue(log.states[index * width + variable]),
        ),
      );
      const encoded = encoder.finish();
      yield JSON.stringify([
        index,
        log.parents[index],
        actions[index],
        BigInt.asUintN(64, log.fingerprints[index]).toString(16).padStart(16, "0"),
        [...encoded.words],
        encoded.strings,
      ]);
    }
  });

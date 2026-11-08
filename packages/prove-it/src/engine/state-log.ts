// PROVE_IT_STATE_LOG=path makes the engine's search write the states it found to the file, in
// TLC's order, once it ends, whether it completed or stopped. The first line is a header:
//   {"version": 1, "variables": [...], "count": n, "stopped": reason or null, "expanding": k,
//    "order": [...], "strings": [...], "keyWidth": w}
// and each state is a line of its own:
//   [index, parent, action, fingerprint, words, strings, keyWords, keyStrings]
// with the parent -1 for an initial state, the action the position in spec.actions of the action
// that first reached the state, or -1 when the search doesn't label its steps, TLC's fingerprint of
// the state's key as 16 hex digits, and the state in transfer.ts's encoding, for printing.
// Two searches agree when their headers' variables and the first four fields of every state do.
// The rest lets another implementation fingerprint each state again: the order in which the
// fingerprint reads the key's values, TLC's order of strings then, which ranks model values, and,
// when the key isn't the state but a VIEW's value or a representative under symmetry, its width
// and each state's key, encoded as the state is.

import { createStateEncoder } from "../transfer";
import { getStringOrder } from "../values";
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
  // The order in which a fingerprint reads a key's values.
  order: number[];
  // Each state's key, keyWidth ids each, when it isn't the state.
  keys: Int32Array | undefined;
  keyWidth: number;
}

const encode = (ids: Int32Array, offset: number, width: number) => {
  const encoder = createStateEncoder();
  encoder.encode(Array.from({ length: width }, (_, index) => toValue(ids[offset + index])));
  const encoded = encoder.finish();
  return [[...encoded.words], encoded.strings];
};

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
      order: log.order,
      strings: getStringOrder(),
      ...(log.keys && { keyWidth: log.keyWidth }),
    });
    for (let index = 0; index < log.count; index++) {
      yield JSON.stringify([
        index,
        log.parents[index],
        actions[index],
        BigInt.asUintN(64, log.fingerprints[index]).toString(16).padStart(16, "0"),
        ...encode(log.states, index * width, width),
        ...(log.keys ? encode(log.keys, index * log.keyWidth, log.keyWidth) : []),
      ]);
    }
  });

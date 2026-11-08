// Compares two state logs PROVE_IT_STATE_LOG wrote (src/engine/state-log.ts) and reports the
// first state where they differ, with both states and their parents decoded and printed.
// Usage: bun scripts/state-log-diff.ts <left log> <right log>

import { readFileSync } from "node:fs";

import { createStateDecoder } from "../src/transfer";
import { formatValue } from "../src/values";

interface StateLogHeader {
  version: number;
  variables: string[];
  count: number;
  stopped: string | null;
  expanding: number;
}

type StateRecord = [number, number, number, string, number[], string[]];

const readLog = (text: string) => {
  const lines = text.split("\n").filter((line) => line !== "");
  const header: StateLogHeader = JSON.parse(lines[0]);
  return { header, states: lines.slice(1).map((line): StateRecord => JSON.parse(line)) };
};

const formatState = (variables: string[], record: StateRecord | undefined) => {
  if (!record) return "nothing";
  const state = createStateDecoder(variables.length)({
    words: Int32Array.from(record[4]),
    strings: record[5],
    count: 1,
  })[0];
  return variables
    .map((name, index) => `${name} = ${formatValue(state[index], false, true)}`)
    .join(" /\\ ");
};

const describe = (side: string, log: ReturnType<typeof readLog>, index: number): string => {
  const record = log.states[index];
  if (!record) return `${side} has no state ${index}`;
  const parent = record[1];
  const action = record[2] === -1 ? "" : ` by action ${record[2]}`;
  const origin =
    parent === -1
      ? "as an initial state"
      : `from ${parent} (${formatState(log.header.variables, log.states[parent])})${action}`;
  return `${side} reached ${formatState(log.header.variables, record)} with fingerprint ${record[3]} ${origin}`;
};

// Where two logs differ, or undefined if they agree: on the header and on the index, parent,
// action and fingerprint of every state.
export const getStateLogDifference = (leftText: string, rightText: string) => {
  const left = readLog(leftText);
  const right = readLog(rightText);
  if (JSON.stringify(left.header.variables) !== JSON.stringify(right.header.variables)) {
    return `the variables differ: ${left.header.variables.join(", ")} and ${right.header.variables.join(", ")}`;
  }
  const length = Math.max(left.states.length, right.states.length);
  for (let index = 0; index < length; index++) {
    const leftRecord = left.states[index];
    const rightRecord = right.states[index];
    if (JSON.stringify(leftRecord?.slice(0, 4)) === JSON.stringify(rightRecord?.slice(0, 4))) {
      continue;
    }
    return `state ${index}:\n  ${describe("left", left, index)}\n  ${describe("right", right, index)}`;
  }
  const leftEnd = `${left.header.stopped ?? "completed"} expanding ${left.header.expanding}`;
  const rightEnd = `${right.header.stopped ?? "completed"} expanding ${right.header.expanding}`;
  return leftEnd === rightEnd
    ? undefined
    : `the searches found the same states but ended differently: left ${leftEnd}, right ${rightEnd}`;
};

if (process.argv[1] === import.meta.filename) {
  const difference = getStateLogDifference(
    readFileSync(process.argv[2], "utf8"),
    readFileSync(process.argv[3], "utf8"),
  );
  console.log(difference ?? "The logs agree on every state.");
  if (difference) process.exitCode = 1;
}

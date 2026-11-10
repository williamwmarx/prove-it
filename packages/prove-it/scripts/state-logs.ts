// Compares two state logs PROVE_IT_STATE_LOG wrote (native/crates/tla-engine/src/search.rs), for
// state-log-diff.ts and engine-coverage.ts --state-logs. A log can be longer than a string can be,
// so it is read and compared as lines, and only the states printed are parsed.

import { closeSync, openSync, readSync } from "node:fs";
import { StringDecoder } from "node:string_decoder";

import { createStateDecoder } from "../src/transfer";
import { formatValue } from "../src/values";

interface StateLogHeader {
  version: number;
  variables: string[];
  count: number;
  stopped: string | null;
  expanding: number;
}

interface StateLog {
  header: StateLogHeader;
  // A line per state, from the second line of the file on.
  states: string[];
}

type StateRecord = [number, number, number, string, number[], string[]];

// The lines of a file, read a chunk at a time. The decoder keeps a character split between chunks.
export const readLogLines = (path: string) => {
  const file = openSync(path, "r");
  const buffer = Buffer.alloc(1 << 24);
  const lines: string[] = [];
  const rest = { text: "" };
  const decoder = new StringDecoder("utf8");
  for (let length = readSync(file, buffer); length > 0; length = readSync(file, buffer)) {
    const chunk = rest.text + decoder.write(buffer.subarray(0, length));
    const parts = chunk.split("\n");
    rest.text = parts.pop() ?? "";
    for (const part of parts) lines.push(part);
  }
  closeSync(file);
  if (rest.text !== "") lines.push(rest.text);
  return lines;
};

const readLog = (lines: string[]): StateLog => {
  const nonEmpty = lines.filter((line) => line !== "");
  return { header: JSON.parse(nonEmpty[0]), states: nonEmpty.slice(1) };
};

// The index, parent, action and fingerprint, which come before the state's encoding: the
// fingerprint is the record's first string.
const getKey = (line: string | undefined) =>
  line?.slice(0, line.indexOf('"', line.indexOf('"') + 1) + 1);

const formatState = (variables: string[], line: string | undefined) => {
  if (!line) return "nothing";
  const record: StateRecord = JSON.parse(line);
  const state = createStateDecoder(variables.length)({
    words: Int32Array.from(record[4]),
    strings: record[5],
    count: 1,
  })[0];
  return variables
    .map((name, index) => `${name} = ${formatValue(state[index], false, true)}`)
    .join(" /\\ ");
};

const describe = (side: string, log: StateLog, index: number) => {
  const line = log.states[index];
  if (!line) return `${side} has no state ${index}`;
  const record: StateRecord = JSON.parse(line);
  const parent = record[1];
  const action = record[2] === -1 ? "" : ` by action ${record[2]}`;
  const origin =
    parent === -1
      ? "as an initial state"
      : `from ${parent} (${formatState(log.header.variables, log.states[parent])})${action}`;
  return `${side} reached ${formatState(log.header.variables, line)} with fingerprint ${record[3]} ${origin}`;
};

// Where two logs, as lines, differ, or undefined if they agree: on the header and on the index,
// parent, action and fingerprint of every state.
export const getStateLogDifference = (leftLines: string[], rightLines: string[]) => {
  const left = readLog(leftLines);
  const right = readLog(rightLines);
  if (JSON.stringify(left.header.variables) !== JSON.stringify(right.header.variables)) {
    return `the variables differ: ${left.header.variables.join(", ")} and ${right.header.variables.join(", ")}`;
  }
  const length = Math.max(left.states.length, right.states.length);
  for (let index = 0; index < length; index++) {
    if (getKey(left.states[index]) === getKey(right.states[index])) continue;
    return `state ${index}:\n  ${describe("left", left, index)}\n  ${describe("right", right, index)}`;
  }
  const leftEnd = `${left.header.stopped ?? "completed"} expanding ${left.header.expanding}`;
  const rightEnd = `${right.header.stopped ?? "completed"} expanding ${right.header.expanding}`;
  return leftEnd === rightEnd
    ? undefined
    : `the searches found the same states but ended differently: left ${leftEnd}, right ${rightEnd}`;
};

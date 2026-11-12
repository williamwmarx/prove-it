import {
  cpSync,
  mkdirSync,
  readdirSync,
  renameSync,
  rmSync,
  statSync,
  writeFileSync,
} from "node:fs";
import { join } from "node:path";

import {
  checkAllSources,
  getNativeAddon,
  loadWasmEngine,
  type NativeFileOperation,
} from "../engine/native";
import { EngineUnavailableError } from "../errors";
import { getMachine, NOT_NATIVE_EXIT_CODE, readFileKey } from "./shared";

// The environment variables tlapm's command line reads: where tlapm is, for its standard library,
// and where it keeps its cache.
const TLAPM_VARIABLES = ["PATH", "TLAPM_CACHE_DIR"];

// Each entry's mtimeMs and name, each ended by a NUL, which no name holds.
const listEntries = (path: string) =>
  statSync(path, { throwIfNoEntry: false })?.isDirectory()
    ? readdirSync(path)
        .map((name) => `${statSync(join(path, name)).mtimeMs}\0${name}\0`)
        .join("")
    : undefined;

// The files the native check reads for tlapm's command line, by key (prove-it-host's check.rs).
const readKey = (key: string) =>
  key.startsWith("entries:") ? listEntries(key.slice("entries:".length)) : readFileKey(key);

const applyFileOperation = (operation: NativeFileOperation) => {
  switch (operation[0]) {
    case "mkdir":
      return void mkdirSync(operation[1], { recursive: true });
    case "write":
      return writeFileSync(operation[1], operation[2]);
    case "remove":
      return rmSync(operation[1], { recursive: true, force: true });
    case "rename":
      return renameSync(operation[1], operation[2]);
    case "copy":
      return cpSync(operation[1], operation[2], { preserveTimestamps: true });
  }
};

// Why the run declines where an operation fails, as prove-it-check's FileOperation::get_failure
// gives it.
const getFailure = (operation: NativeFileOperation) => {
  switch (operation[0]) {
    case "mkdir":
      return `a directory tlapm can't make: ${operation[1]}`;
    case "write":
      return `a file tlapm can't write: ${operation[1]}`;
    case "remove":
      return `a file tlapm can't remove: ${operation[1]}`;
    case "rename":
      return `a file tlapm can't write: ${operation[2]}`;
    case "copy":
      return `a file tlapm can't copy into its history: ${operation[1]}`;
  }
};

// Applies the operations in order, up to the first that fails, and returns why it failed.
const applyFileOperations = (operations: NativeFileOperation[]) => {
  for (const operation of operations) {
    try {
      applyFileOperation(operation);
    } catch {
      return getFailure(operation);
    }
  }
  return undefined;
};

// tlapm's command line, which the native engine runs as the binary does: it prints what the binary
// prints, writes the files it writes, and exits as it does.
export const runTlapm = async (args: string[]) => {
  await loadWasmEngine();
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new EngineUnavailableError(addon);
  const variables = TLAPM_VARIABLES.flatMap((name): [string, string][] => {
    const value = process.env[name];
    return value === undefined ? [] : [[name, value]];
  });
  const result = checkAllSources(addon, ["tlapm", ...args], getMachine(variables), readKey);
  if (result.kind === "declined") {
    console.error(`prove-it: not native yet: ${result.reason}`);
    return NOT_NATIVE_EXIT_CODE;
  }
  const failure = applyFileOperations(result.files);
  if (failure !== undefined) {
    console.error(`prove-it: not native yet: ${failure}`);
    return NOT_NATIVE_EXIT_CODE;
  }
  process.stdout.write(result.out);
  process.stderr.write(result.err);
  return result.exitCode;
};

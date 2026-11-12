import {
  cpSync,
  mkdirSync,
  readdirSync,
  readFileSync,
  realpathSync,
  renameSync,
  rmSync,
  statSync,
  writeFileSync,
} from "node:fs";
import { arch, availableParallelism, release, totalmem, type } from "node:os";
import { join } from "node:path";

import {
  checkAllSources,
  getNativeAddon,
  loadWasmEngine,
  type NativeFileOperation,
} from "../engine/native";
import { getEngineVariables } from "../engine/settings";
import { EngineUnavailableError } from "../errors";
import { getZoneRule } from "./tlc";

// The environment variables tlapm's command line reads: where tlapm is, for its standard library,
// and where it keeps its cache.
const TLAPM_VARIABLES = ["PATH", "TLAPM_CACHE_DIR"];

const getKind = (path: string) => {
  const stats = statSync(path, { throwIfNoEntry: false });
  if (stats === undefined) return undefined;
  return stats.isFile() ? "file" : stats.isDirectory() ? "directory" : "other";
};

const getRealPath = (path: string) => {
  try {
    return realpathSync(path);
  } catch {
    return undefined;
  }
};

// Each entry's mtimeMs and name, each ended by a NUL, which no name holds.
const listEntries = (path: string) =>
  getKind(path) === "directory"
    ? readdirSync(path)
        .map((name) => `${statSync(join(path, name)).mtimeMs}\0${name}\0`)
        .join("")
    : undefined;

// A file that isn't UTF-8 has no text, as the binary's read_to_string gives none: read with U+FFFD
// in place of its bytes, two different files would read alike.
const decoder = new TextDecoder("utf-8", { fatal: true, ignoreBOM: true });
const readText = (path: string) => {
  try {
    return decoder.decode(readFileSync(path));
  } catch {
    return undefined;
  }
};

// The files the native check reads for tlapm's command line, by key (prove-it-host's check.rs).
const readKey = (key: string) => {
  const separator = key.indexOf(":");
  const [kind, path] = [key.slice(0, separator), key.slice(separator + 1)];
  if (kind === "text") return getKind(path) === "file" ? readText(path) : undefined;
  if (kind === "bytes")
    return getKind(path) === "file" ? new Uint8Array(readFileSync(path)) : undefined;
  if (kind === "kind") return getKind(path);
  if (kind === "realpath") return getRealPath(path);
  if (kind === "entries") return listEntries(path);
  return undefined;
};

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
  const result = checkAllSources(
    addon,
    ["tlapm", ...args],
    [
      type(),
      release(),
      arch(),
      availableParallelism(),
      Math.floor(totalmem() / 1024 / 1024),
      process.pid,
      Date.now(),
      getZoneRule(),
      [...getEngineVariables(), ...variables],
      false,
    ],
    readKey,
  );
  if (result.kind === "declined") {
    console.error(`prove-it: not native yet: ${result.reason}`);
    return 1;
  }
  result.files.forEach(applyFileOperation);
  process.stdout.write(result.out);
  process.stderr.write(result.err);
  return result.exitCode;
};

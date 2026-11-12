import {
  accessSync,
  constants,
  existsSync,
  globSync,
  readFileSync,
  realpathSync,
  statSync,
} from "node:fs";
import { arch, availableParallelism, release, tmpdir, totalmem, type } from "node:os";

import type { NativeMachine } from "../engine/native";
import { getEngineVariables } from "../engine/settings";
import { getErrorExitCode, TlaError } from "../errors";

// What the CLI exits with where the native binary declines, as the binary does.
export const NOT_NATIVE_EXIT_CODE = 1;

const GLOB_CHARACTERS = /[*?[{]/;

interface InputPath {
  path: string;
  isGlobbed: boolean;
}

export const getInputPaths = (paths: string[]): InputPath[] =>
  paths.flatMap((arg): InputPath[] =>
    GLOB_CHARACTERS.test(arg)
      ? globSync(arg)
          .sort()
          .map((path) => ({ path, isGlobbed: true }))
      : [{ path: arg, isGlobbed: false }],
  );

const isWritable = (path: string) => {
  try {
    accessSync(path, constants.W_OK);
    return true;
  } catch {
    return false;
  }
};

// What the native check reads of the machine's files, by the keys prove-it-host's `check` names:
// what is at a path, a file's bytes, the path with its links followed, the working directory, the
// temporary directory, the platform, whose rules the engine as WebAssembly names paths by, and
// whether the CLI can write into a directory. A path the system can't follow, as a loop of links, has none, and a file
// it can't read, as a socket, has no bytes, as the binary reads them.
export const readFileKey = (key: string) => {
  const [kind, ...rest] = key.split(":");
  const path = rest.join(":");
  if (kind === "platform") return process.platform;
  if (kind === "cwd") return process.cwd();
  if (kind === "tmpdir") return tmpdir();
  if (!existsSync(path)) return undefined;
  const isDirectory = statSync(path).isDirectory();
  if (kind === "writable") return isDirectory && isWritable(path) ? "directory" : undefined;
  if (kind === "stat") return isDirectory ? "directory" : "file";
  if (kind === "realpath") return realpathSync.native(path);
  if (kind !== "bytes" || isDirectory) return undefined;
  try {
    return new Uint8Array(readFileSync(path));
  } catch {
    return undefined;
  }
};

export const reportErrors = async (run: () => number | Promise<number>) => {
  try {
    return await run();
  } catch (error) {
    if (!(error instanceof TlaError)) throw error;
    console.error(`${error.name}: ${error.message}`);
    return getErrorExitCode(error);
  }
};

// The zone TLC prints its dates in, as a POSIX TZ rule of the offset the process has now.
const getZoneRule = () => {
  const offset = -new Date().getTimezoneOffset();
  const hours = Math.floor(Math.abs(offset) / 60);
  const minutes = String(Math.abs(offset) % 60).padStart(2, "0");
  return `<${offset < 0 ? "-" : "+"}${String(hours).padStart(2, "0")}${minutes}>${offset > 0 ? "-" : ""}${hours}:${minutes}`;
};

// The machine the CLI's native check describes, as prove-it-host's `check` takes it.
export const getMachine = (): NativeMachine => [
  type(),
  release(),
  arch(),
  availableParallelism(),
  Math.floor(totalmem() / 1024 / 1024),
  process.pid,
  Date.now(),
  getZoneRule(),
  getEngineVariables(),
  false,
];

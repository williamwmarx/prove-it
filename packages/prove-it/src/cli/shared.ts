import { existsSync, globSync, readFileSync, realpathSync, statSync } from "node:fs";
import { arch, availableParallelism, release, tmpdir, totalmem, type } from "node:os";
import { delimiter } from "node:path";

import type { NativeMachine } from "../engine/native";
import { getEngineVariables } from "../engine/settings";
import { getErrorExitCode, TlaConfigError, TlaError, TlaEvaluationError } from "../errors";
import {
  createMessagePrinter,
  formatInnerMessage,
  getCodedMessage,
  MESSAGE_CODE,
  MESSAGE_LEVEL,
  type MessagePrinter,
} from "../tlc/messages";
import type { TlcVersion } from "../tlc/version";

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

// What the native check reads of the machine's files, by the keys prove-it-host's `check` names:
// what is at a path, a file's bytes, the path with its links followed, the working directory and
// the temporary directory. A path the system can't follow, as a loop of links, has none, and a file
// it can't read, as a socket, has no bytes, as the binary reads them.
export const readFileKey = (key: string) => {
  const [kind, ...rest] = key.split(":");
  const path = rest.join(":");
  if (kind === "cwd") return process.cwd();
  if (kind === "tmpdir") return tmpdir();
  if (!existsSync(path)) return undefined;
  const isDirectory = statSync(path).isDirectory();
  if (kind === "stat") return isDirectory ? "directory" : "file";
  if (kind === "realpath") return realpathSync.native(path);
  if (kind !== "bytes" || isDirectory) return undefined;
  try {
    return new Uint8Array(readFileSync(path));
  } catch {
    return undefined;
  }
};

// TLC prints an error it raises with that error's message code. tla-ts names the others, such as a
// module SANY rejects.
export const printError = (error: TlaError, printer: MessagePrinter) => {
  if (error instanceof TlaConfigError || error instanceof TlaEvaluationError) {
    const coded = getCodedMessage(error.message);
    const code = coded && !coded.isEvalException ? coded.code : MESSAGE_CODE.general;
    return printer.print(
      code,
      MESSAGE_LEVEL.error,
      formatInnerMessage(code, error.message, printer.isTool),
    );
  }
  console.error(`${error.name}: ${error.message}`);
};

export const reportErrors = async (
  run: () => number | Promise<number>,
  printer = createMessagePrinter(false),
) => {
  try {
    return await run();
  } catch (error) {
    if (!(error instanceof TlaError)) throw error;
    printError(error, printer);
    return getErrorExitCode(error);
  }
};

export interface JavaProperties {
  libraries: string[];
  // The system properties the launch sets with -Dname=value, which TLCGet("-Dname") reads.
  properties: Map<string, string>;
  classPath?: string;
  temporaryDirectory?: string;
  tlcVersion?: TlcVersion;
}

export const getToolsJar = (java: JavaProperties) =>
  java.classPath?.split(delimiter).find((entry) => entry.endsWith(".jar"));

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

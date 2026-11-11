import { existsSync, globSync, readFileSync, statSync } from "node:fs";
import { delimiter, isAbsolute, resolve } from "node:path";
import { pathToFileURL } from "node:url";

import {
  getErrorExitCode,
  TlaConfigError,
  TlaError,
  TlaEvaluationError,
  TlaUnsupportedError,
} from "../errors";
import { SANY_174_STANDARD_MODULES } from "../sany/modules";
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

// TLC's resolver finds a module's file, or a Java class's that overrides it, in the first of the
// directories that has it, by the path it makes there, which the system resolves: the working
// directory written "", and .. after the link before it, as Java's Path.resolve does.
export const findFile = (directories: string[], fileName: string) =>
  directories
    .map((directory) => (directory === "" ? fileName : `${directory}/${fileName}`))
    .find(existsSync);

// Whether a path the resolver found is one TLC can read: anything there but a directory, such as
// /dev/null.
export const isFile = (path: string) => existsSync(path) && !statSync(path).isDirectory();

// SANY can't read a module's file it finds that isn't a file, such as a directory, which tla-ts
// doesn't report as SANY does.
export const createModuleLoader = (directories: string[]) => (name: string) => {
  const path = findFile(directories, `${name}.tla`);
  if (path === undefined) return undefined;
  if (!isFile(path)) {
    throw new TlaUnsupportedError(
      `a module's file TLC finds but can't read, such as a directory: ${path}`,
    );
  }
  return readFileSync(path, "utf8");
};

// SimpleFilenameToStream: SANY names the file of a module it can't find, and where it looked.
export const printMissingFile = (userDirectory: string, fileName: string, directories: string[]) =>
  console.error(
    `File does not exist: ${userDirectory}/${fileName} while looking in these directories: ${userDirectory}, ${directories.join(", ")}, classpath:/tla2sany/StandardModules, classpath:/`,
  );

export const getStandardModulesUrl = (jar: string) =>
  `jar:file:${pathToFileURL(resolve(jar)).pathname}!/tla2sany/StandardModules/`;

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

// TLC 1.7.4's FileUtil.createNamedInputStream names the last file SimpleFilenameToStream looked
// for, and the directories it looked in, the jar's standard modules last.
export const printMissingFile174 = (path: string, libraries: string[], jar: string | undefined) =>
  console.error(
    `File does not exist: ${isAbsolute(path) ? path : `${process.cwd()}/${path}`} while looking in these directories: ${[...libraries, ...(jar === undefined ? [] : [getStandardModulesUrl(jar)])].join(", ")}`,
  );

// SimpleFilenameToStream ends a library directory with a separator.
export const toLibraryPath = (directory: string) =>
  directory.endsWith("/") ? directory : `${directory}/`;

// TLC 1.7.4's SANY reports each module it can't find as it looks for it.
export const reportMissingModules174 =
  (loadModule: (name: string) => string | undefined, onMissing: (fileName: string) => void) =>
  (name: string) => {
    const text = loadModule(name);
    if (text === undefined && !SANY_174_STANDARD_MODULES.has(name)) onMissing(`${name}.tla`);
    return text;
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

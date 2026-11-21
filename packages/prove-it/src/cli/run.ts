import { appendFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";

import { checkAllSources, getNativeAddon, loadWasmEngine } from "../engine/native";
import { EngineUnavailableError } from "../errors";
import { EXIT_STATUS } from "../exit-codes";
import { getMachine, readFileKey, reportErrors } from "./shared";

// What the CLI exits with where the native check declines, as the binary does.
const NOT_NATIVE_EXIT_CODE = 1;

// Writes or appends a file the check wrote, and whether it could.
const isWritten = (path: string, bytes: Uint8Array, isAppended: boolean) => {
  try {
    if (isAppended) appendFileSync(path, bytes);
    else writeFileSync(path, bytes);
    return true;
  } catch {
    return false;
  }
};

// The keys the check asks for first, which the command line names: the spec, last on TLC's
// command line, and its configuration, and the directories the check runs in. Each round of the
// check starts over, so answering them first saves the rounds that would ask only for them.
const getSeededKeys = (args: string[]) => {
  const config = args.indexOf("-config");
  const files = [args.at(-1), config === -1 ? undefined : args[config + 1]].filter(
    (file): file is string => file !== undefined && !file.startsWith("-"),
  );
  return [
    ...files.flatMap((file) => [`bytes:${file}`, `realpath:${file}`, `stat:${file}`]),
    "cwd",
    "tmpdir",
    "platform",
    `realpath:${tmpdir()}`,
  ];
};

// The command line the native binary runs, run in-process: TLC's or XMLExporter's, the Java launch
// included, its files read and written as the binary reads and writes them. The files it wrote
// are written before it prints, so that where one can't be, it declines without printing.
const runNatively = async (args: string[]) => {
  await loadWasmEngine();
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new EngineUnavailableError(addon);
  const result = checkAllSources(addon, args, getMachine(), readFileKey, getSeededKeys(args));
  const unwritten =
    result.kind === "checked"
      ? result.writes.find((write) => !isWritten(write.path, write.bytes, write.isAppended))
      : undefined;
  if (result.kind === "declined" || unwritten !== undefined) {
    console.error(
      `prove-it: not native yet: ${result.kind === "declined" ? result.reason : `a file it can't write: ${unwritten?.path}`}`,
    );
    return NOT_NATIVE_EXIT_CODE;
  }
  process.stdout.write(result.out);
  process.stderr.write(result.err);
  return result.exitCode;
};

const run = async (args: string[]) => {
  if (args[0] !== "tlapm") return runNatively(args);
  const tlapm = await import("./tlapm");
  return reportErrors(() => tlapm.runTlapm(args.slice(1)));
};

// Without a native engine, the CLI exits as TLC does on an internal error.
export const runCli = async () => {
  process.exitCode = await run(process.argv.slice(2)).catch((error: unknown) => {
    if (!(error instanceof EngineUnavailableError)) throw error;
    console.error(error.message);
    return EXIT_STATUS.error;
  });
};

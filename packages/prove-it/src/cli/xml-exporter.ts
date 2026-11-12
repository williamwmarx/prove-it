import { checkAllSources, getNativeAddon, loadWasmEngine } from "../engine/native";
import { EngineUnavailableError } from "../errors";
import { getMachine, readFileKey } from "./shared";

// What the CLI exits with where the native binary declines, as the binary does.
const NOT_NATIVE_EXIT_CODE = 1;

// SANY's XMLExporter, as the native binary runs it (prove-it-check's xml_exporter.rs), for the
// command line as given, the Java launch's included, its files read as the binary reads them.
export const exportXml = async (commandLine: string[]) => {
  await loadWasmEngine();
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new EngineUnavailableError(addon, false);
  const result = checkAllSources(addon, commandLine, getMachine(), readFileKey);
  if (result.kind === "declined") {
    console.error(`prove-it: not native yet: ${result.reason}`);
    return NOT_NATIVE_EXIT_CODE;
  }
  process.stdout.write(result.out);
  process.stderr.write(result.err);
  return result.exitCode;
};

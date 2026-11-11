import { basename } from "node:path";

import { getNativeAddon, type NativeSanyText } from "../engine/native";
import { EngineUnavailableError } from "../errors";
import { readSanyText, type SanyReading } from "../sany/source";
import type { TlcVersion } from "../tlc/version";

// The exit code of a run the CLI declines.
export const NOT_NATIVE_EXIT_CODE = 1;

// Where SANY reads a module from: a file of its own, the file of the root module, which holds the
// root module's inner modules too, or the files of its standard modules.
export type SanyModuleOrigin = "file" | "root file" | "standard";

export interface NativeSanyReport {
  text: string;
  isFailed: boolean;
  readings: ReadonlyMap<string, SanyReading>;
}

interface NativeSanyOptions {
  fileName: string;
  loadModule: (name: string) => string | undefined;
  describeFile: (moduleName: string, origin: SanyModuleOrigin) => string;
  rootExtendees: string[];
}

// The readings of the texts of a spec SANY accepted, made as the order asks for them, as the
// TypeScript report's are.
class SanyReadings extends Map<string, SanyReading> {
  constructor(private readonly version: TlcVersion) {
    super();
  }

  override get(text: string) {
    const known = super.get(text);
    if (known) return known;
    const reading = readSanyText(new Map(), text, this.version);
    this.set(text, reading);
    return reading;
  }
}

// What the report reads, by the keys sany.rs names it by.
const readKey = (key: string, options: NativeSanyOptions) => {
  const [kind, ...rest] = key.split(":");
  if (kind === "module") return options.loadModule(rest.join(":"));
  const [origin, ...name] = rest;
  return options.describeFile(name.join(":"), origin as SanyModuleOrigin);
};

// What SANY prints for the spec as tla-front writes it, through the native engine, which reads
// nothing itself: it names what it needs, and is asked again with it. `source` is null where no
// file holds the root module, and `rootExtendees` are the modules TLC adds to the root module's
// EXTENDS for its post conditions.
export const getNativeSanyReport = (
  specPath: string,
  source: string | null,
  version: TlcVersion,
  options: NativeSanyOptions,
): NativeSanyReport | { declined: string } => {
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new EngineUnavailableError(addon, false);
  const known = new Map<string, string | undefined>();
  const write = (): Exclude<NativeSanyText, { kind: "needed" }> => {
    const result = addon.sanyText(
      basename(specPath, ".tla"),
      source,
      options.fileName,
      version,
      options.rootExtendees,
      [...known],
    );
    if (result.kind !== "needed") return result;
    result.keys.forEach((key) => known.set(key, readKey(key, options)));
    return write();
  };
  const result = write();
  if (result.kind === "declined") return { declined: result.reason };
  // TLC words a Java exception of SANY's generator as a failed parse of its own.
  if (result.exception !== null) return { declined: "SANY's report of a generator exception" };
  return {
    text: result.text,
    isFailed: result.isFailed,
    readings: new SanyReadings(version),
  };
};

import { basename } from "node:path";

import { getNativeAddon, type NativeSanyText } from "../engine/native";
import { reportEngine } from "../engine/settings";
import type { SanyModuleOrigin } from "../sany/report";
import { readSanyText, type SanyReading } from "../sany/source";
import type { TlcVersion } from "../tlc/version";

export interface NativeSanyReport {
  text: string;
  isFailed: boolean;
  readings: ReadonlyMap<string, SanyReading>;
}

interface NativeSanyOptions {
  fileName: string;
  loadModule: (name: string) => string | undefined;
  describeFile: (moduleName: string, origin: SanyModuleOrigin) => string;
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
// nothing itself: it names what it needs, and is asked again with it. Undefined where no engine
// loads or tla-front doesn't write the report, so that the TypeScript report does.
export const getNativeSanyReport = (
  specPath: string,
  source: string,
  version: TlcVersion,
  options: NativeSanyOptions,
): NativeSanyReport | undefined => {
  const addon = getNativeAddon();
  if (typeof addon === "string") {
    reportEngine(`SANY's report: no native engine: ${addon}`);
    return undefined;
  }
  const known = new Map<string, string | undefined>();
  const write = (): Exclude<NativeSanyText, { kind: "needed" }> => {
    const result = addon.sanyText(basename(specPath, ".tla"), source, options.fileName, [...known]);
    if (result.kind !== "needed") return result;
    result.keys.forEach((key) => known.set(key, readKey(key, options)));
    return write();
  };
  const result = write();
  if (result.kind === "declined") {
    reportEngine(`SANY's report: ${result.reason}`);
    return undefined;
  }
  // TLC words a Java exception of SANY's generator as a failed parse of its own, which the
  // TypeScript report doesn't either.
  if (result.exception !== null) {
    reportEngine("SANY's report: an exception of SANY's generator");
    return undefined;
  }
  return {
    text: result.text,
    isFailed: result.isFailed,
    readings: new SanyReadings(version),
  };
};

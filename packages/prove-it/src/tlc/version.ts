import { existsSync, readFileSync } from "node:fs";

import { readZipEntry } from "./zip";

// The TLC whose output tla-ts reproduces: the 1.7.4 release, or the master builds that tla-ts
// follows for any other tla2tools.jar.
export type TlcVersion = "1.7.4" | "master";

const MANIFEST = "META-INF/MANIFEST.MF";

// The version of a tla2tools.jar, from the Git tag that its manifest records.
export const getTlcVersion = async (jar: string | undefined): Promise<TlcVersion> => {
  if (jar === undefined || !existsSync(jar)) return "master";
  const manifest = await readZipEntry(readFileSync(jar), MANIFEST);
  const tag = manifest && /^X-Git-Tag: *(\S*)/m.exec(new TextDecoder().decode(manifest))?.[1];
  return tag === "v1.7.4" ? "1.7.4" : "master";
};

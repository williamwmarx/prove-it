// How long it takes to parse a spec and to serialize its syntax tree, as a stand-in for the cost of
// handing the engine's input across the FFI.
import { readFileSync } from "node:fs";

import { parseModule } from "../../../src/parser";

for (const path of process.argv.slice(2)) {
  const source = readFileSync(path, "utf8");
  let startedAt = performance.now();
  const module = parseModule(source);
  const parseMs = performance.now() - startedAt;
  startedAt = performance.now();
  const seen = new WeakSet();
  const json = JSON.stringify(module, (key, value) => {
    if (typeof value === "object" && value !== null) {
      if (seen.has(value)) return undefined;
      seen.add(value);
    }
    return value;
  });
  const serializeMs = performance.now() - startedAt;
  startedAt = performance.now();
  const bytes = new TextEncoder().encode(json);
  const encodeMs = performance.now() - startedAt;
  console.log(
    `${path.split("/").pop()}: ${source.length} chars, parse ${parseMs.toFixed(1)} ms, JSON ${(bytes.length / 1024).toFixed(0)} KiB in ${serializeMs.toFixed(1)} ms + UTF-8 ${encodeMs.toFixed(1)} ms`,
  );
}

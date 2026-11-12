import { describe, expect, it } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { check, type CheckOptions } from "../../src";
import { checkOnEngine } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/json");

const getOptions = (name: string, written: Map<string, string>): CheckOptions => ({
  source: readFileSync(join(DIRECTORY, `${name}.tla`), "utf8"),
  config: readFileSync(join(DIRECTORY, `${name}.cfg`), "utf8"),
  readFile: (path) => {
    const fixturePath = join(DIRECTORY, path);
    return (
      written.get(path) ?? (existsSync(fixturePath) ? readFileSync(fixturePath, "utf8") : undefined)
    );
  },
  writeFile: (path, content) => written.set(path, content),
});

describe("Json matches TLC", () => {
  it("checks TLC's JsonTests model", async () => {
    const written = new Map<string, string>();
    const result = await checkOnEngine(
      getOptions("JsonTests", written),
      "the engine declined: ndJsonSerialize, whose file the host reads and writes",
    );
    expect(result.status).toBe("success");
    expect(written.get("target/json/test.json")).toBe('{"a":3,"b":{"c":[4,5,6]}}');
  });

  it("converts and reads values like TLC's Java Json module", async () => {
    const written = new Map<string, string>();
    const result = await check(getOptions("JsonValues", written));
    expect(result.status).toBe("success");
    expect(written.size).toBe(0);
  });
});

import { describe, it } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

import type { CheckOptions } from "../../src";
import { expectDeclined } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/json");

const getOptions = (name: string): CheckOptions => ({
  source: readFileSync(join(DIRECTORY, `${name}.tla`), "utf8"),
  config: readFileSync(join(DIRECTORY, `${name}.cfg`), "utf8"),
  readFile: (path) => {
    const fixturePath = join(DIRECTORY, path);
    return existsSync(fixturePath) ? readFileSync(fixturePath, "utf8") : undefined;
  },
  writeFile: () => {},
});

describe("Json matches TLC", () => {
  it("declines TLC's JsonTests model", async () => {
    await expectDeclined(
      getOptions("JsonTests"),
      "the engine declined: ndJsonSerialize, whose file the host reads and writes",
    );
  });

  it("declines reading values like TLC's Java Json module", async () => {
    await expectDeclined(
      getOptions("JsonValues"),
      "the engine declined: JsonDeserialize, whose file the host reads and writes",
    );
  });
});

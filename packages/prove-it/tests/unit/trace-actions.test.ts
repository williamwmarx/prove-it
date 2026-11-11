import { expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { check, parseConfig } from "../../src";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-get-non-determinism");

it("rebuilds a liveness trace from the initial predicate when Next sets registers", async () => {
  const config = parseConfig(readFileSync(join(DIRECTORY, "TLCGetNonDeterminism.cfg"), "utf8"));
  config.checkDeadlock = false;
  const result = await check({
    source: readFileSync(join(DIRECTORY, "TLCGetNonDeterminism.tla"), "utf8"),
    config,
  });
  expect(result.status).toBe("liveness-violation");
  expect(
    result.violations[0]?.states.map((step) => [
      step.label.split(" line ")[0],
      step.variables.y.text,
    ]),
  ).toEqual([
    ["Initial predicate", "0"],
    ["Next", "1"],
    ["Next", "2"],
    ["Next", "3"],
  ]);
  expect(result.violations[0]?.loopStart).toBe(3);
});

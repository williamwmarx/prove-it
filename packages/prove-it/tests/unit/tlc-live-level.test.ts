import { expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { checkOnEngine } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-live-level");

const checkProperty = (name: string) =>
  checkOnEngine({
    source: readFileSync(join(DIRECTORY, "LiveLevel.tla"), "utf8"),
    config: readFileSync(join(DIRECTORY, `${name}.cfg`), "utf8"),
  });

it.each(["ReachesThree", "StepsUp", "LevelsAtMostTwo", "LevelsFromOne"])(
  'evaluates TLCGet("level") in %s like TLC',
  async (name) => {
    const result = await checkProperty(name);
    expect(result.status).toBe("success");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([5, 3, 2]);
  },
);

it('finds the behavior where TLCGet("level") never reaches 4', async () => {
  const result = await checkProperty("ReachesFour");
  expect(result.status).toBe("liveness-violation");
  expect(result.violations[0]?.states.map((step) => step.variables.x.text)).toEqual([
    "0",
    "1",
    "2",
  ]);
  expect(result.violations[0]?.loopStart).toBe(0);
});

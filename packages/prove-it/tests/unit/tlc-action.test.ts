import { expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { checkOnEngine } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-action");

it('returns TLC\'s unnamed action from TLCGet("action") in every context', async () => {
  const result = await checkOnEngine(
    {
      source: readFileSync(join(DIRECTORY, "Action.tla"), "utf8"),
      config: readFileSync(join(DIRECTORY, "Action.cfg"), "utf8"),
    },
    "an assumption that fails to evaluate: evaluating the assumption again: TLCGet",
  );
  expect(result.status).toBe("success");
  expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([3, 3, 3]);
});

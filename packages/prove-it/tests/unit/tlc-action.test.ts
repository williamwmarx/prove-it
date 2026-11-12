import { it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { expectDeclined } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-action");

it('declines TLC\'s unnamed action from TLCGet("action") in every context', async () => {
  await expectDeclined(
    {
      source: readFileSync(join(DIRECTORY, "Action.tla"), "utf8"),
      config: readFileSync(join(DIRECTORY, "Action.cfg"), "utf8"),
    },
    "an assumption that fails to evaluate: evaluating the assumption again: TLCGet",
  );
});

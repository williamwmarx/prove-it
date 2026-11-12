import { it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { expectDeclined } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-constraint-order");

it("declines a spec that prints in its constraints and invariants", async () => {
  await expectDeclined(
    {
      source: readFileSync(join(DIRECTORY, "Order.tla"), "utf8"),
      config: readFileSync(join(DIRECTORY, "Order.cfg"), "utf8"),
    },
    "the engine declined: unsupported: PrintT",
  );
});

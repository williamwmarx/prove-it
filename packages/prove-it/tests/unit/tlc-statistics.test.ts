import { it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { expectDeclined } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-statistics");

it("declines counting states for TLCGet while it generates them", async () => {
  await expectDeclined(
    {
      source: readFileSync(join(DIRECTORY, "Statistics.tla"), "utf8"),
      config: readFileSync(join(DIRECTORY, "Statistics.cfg"), "utf8"),
    },
    "the engine declined: unsupported: PrintT",
  );
});

it("declines the states generated up to the first violation", async () => {
  await expectDeclined(
    {
      source:
        "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' \\in {1, 2, 3} /\\ PrintT(<<x', TLCGet(\"generated\")>>)\nInv == x # 2\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT Inv",
    },
    "the engine stopped: unsupported: TLCGet of a key the search doesn't keep",
  );
});

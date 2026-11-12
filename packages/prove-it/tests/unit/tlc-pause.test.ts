import { it } from "bun:test";

import { expectDeclined } from "../native-check";

it('declines TLCSet("pause", TRUE)', async () => {
  await expectDeclined(
    {
      source:
        '---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x\' = x + 1 /\\ TLCSet("pause", x = 1)\n====',
      config: "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
    },
    "the engine stopped: unsupported: TLCSet of a key that stops or configures TLC",
  );
});

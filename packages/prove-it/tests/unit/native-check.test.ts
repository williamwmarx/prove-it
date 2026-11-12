import { describe, expect, it } from "bun:test";

import { checkOnEngine, expectDeclined } from "../native-check";

const getSource = (body: string) =>
  `---- MODULE M ----\nEXTENDS Naturals, TLCExt\nVARIABLE x\n${body}\n====`;

describe("check", () => {
  it("gives each of two calls at once its own answer", async () => {
    const report = console.error;
    const [, nativeCheck] = await Promise.all([
      expectDeclined(
        {
          source: getSource(
            'Init == x = 0\nNext == x < 5 /\\ x\' = x + 1 /\\ (x = 2 => TLCGetAndSet("exit", LAMBDA old, new : new, TRUE, FALSE) = FALSE)',
          ),
          config: "INIT Init\nNEXT Next",
        },
        "the engine stopped: unsupported: TLCGetAndSet of a key that stops or configures TLC",
      ),
      checkOnEngine({
        source: getSource("Init == x = 0\nNext == x < 3 /\\ x' = x + 1"),
        config: "INIT Init\nNEXT Next",
      }),
    ]);
    expect(nativeCheck.distinctStates).toBe(4);
    expect(console.error).toBe(report);
  });
});

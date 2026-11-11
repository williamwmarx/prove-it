import { describe, expect, it } from "bun:test";

import { checkNatively } from "../native-check";

const getSource = (body: string) =>
  `---- MODULE M ----\nEXTENDS Naturals, TLCExt\nVARIABLE x\n${body}\n====`;

describe("checkNatively", () => {
  it("gives each of two calls at once its own engine's answer", async () => {
    const report = console.error;
    const setting = process.env.PROVE_IT_ENGINE;
    const [declinedCheck, nativeCheck] = await Promise.all([
      checkNatively({
        source: getSource(
          'Init == x = 0\nNext == x < 5 /\\ x\' = x + 1 /\\ (x = 2 => TLCGetAndSet("exit", LAMBDA old, new : new, TRUE, FALSE) = FALSE)',
        ),
        config: "INIT Init\nNEXT Next",
      }),
      checkNatively({
        source: getSource("Init == x = 0\nNext == x < 3 /\\ x' = x + 1"),
        config: "INIT Init\nNEXT Next",
      }),
    ]);
    expect(declinedCheck?.declined).toBe(
      "the engine stopped: unsupported: TLCGetAndSet of a key that stops or configures TLC",
    );
    expect(nativeCheck?.declined).toBeUndefined();
    expect(nativeCheck?.result.distinctStates).toBe(4);
    expect(console.error).toBe(report);
    expect(process.env.PROVE_IT_ENGINE).toBe(setting);
  });
});

import { describe, expect, it } from "bun:test";

import { check, type CheckOptions } from "../../src";
import { expectDeclined } from "../native-check";

// What check passes to onPrint.
const getPrinted = async (options: CheckOptions) => {
  const printed: string[] = [];
  await check({ ...options, onPrint: (text) => printed.push(text) });
  return printed;
};

const ASSERTING = [
  "---- MODULE A ----",
  "EXTENDS Naturals, TLC",
  "VARIABLE x",
  'Init == x = 0 /\\ PrintT(<<"init", x>>)',
  'Next == \\/ PrintT(<<"pre", x>>) /\\ x\' = x + 1 /\\ Assert(x < 2, "boom") /\\ PrintT(<<"post", x>>)',
  '        \\/ x\' = x + 10 /\\ x < 1 /\\ PrintT(<<"D", x>>)',
  "====",
].join("\n");

// TLC's output at d8fb231 (-fp 0 -workers 1 -noGenerateSpecTE), the lines the spec printed.
describe("check reports what the spec prints with a trace in TLC's order", () => {
  it("prints a failure's trace as TLC does", async () => {
    expect(await getPrinted({ source: ASSERTING, config: "INIT Init\nNEXT Next" })).toEqual([
      ...['<<"init", 0>>', '<<"pre", 0>>', '<<"post", 0>>', '<<"D", 0>>'],
      ...['<<"pre", 1>>', '<<"post", 1>>', '<<"pre", 10>>'],
      ...['<<"init", 0>>', '<<"pre", 0>>', '<<"post", 0>>', '<<"D", 0>>'],
      ...['<<"init", 0>>', '<<"pre", 0>>', '<<"post", 0>>', '<<"D", 0>>', '<<"pre", 10>>'],
    ]);
  });

  it("declines -continue with a spec that prints", async () => {
    const source = [
      "---- MODULE C ----",
      "EXTENDS Naturals, TLC",
      "VARIABLE x",
      'Init == x \\in {0, 1} /\\ PrintT(<<"init", x>>)',
      "Next == \\/ x < 3 /\\ x' = x + 1 /\\ PrintT(<<\"A\", x, x'>>)",
      '        \\/ x = 3 /\\ x\' = 3 /\\ PrintT(<<"B", x>>)',
      "Inv == x < 3",
      "====",
    ].join("\n");
    await expectDeclined(
      { source, config: "INIT Init\nNEXT Next\nINVARIANT Inv", isContinued: true },
      "-continue with a spec that prints or sets TLC's registers",
    );
  });

  const DEADLOCKING = [
    "EXTENDS Naturals, TLC",
    "VARIABLE x",
    'Init == x = 0 /\\ PrintT(<<"init", x>>)',
    'Next == x < 1 /\\ x\' = x + 1 /\\ PrintT(<<"next", x>>)',
    "Spec == Init /\\ [][Next]_x",
    "Live == [](x = 0 => [](x # 1))",
  ].join("\n");

  it("declines a deadlock -continue ends at in a spec that prints", async () => {
    await expectDeclined(
      {
        source: `---- MODULE D ----\n${DEADLOCKING}\n====`,
        config: "INIT Init\nNEXT Next",
        isContinued: true,
      },
      "-continue with a spec that prints or sets TLC's registers",
    );
  });

  it("declines the temporal property a deadlocked state violates in a spec that prints", async () => {
    await expectDeclined(
      {
        source: `---- MODULE L ----\n${DEADLOCKING}\n====`,
        config: "SPECIFICATION Spec\nPROPERTY Live",
      },
      "the engine stopped: deadlock: a stop the liveness checker doesn't follow in a model that prints",
    );
  });

  const HEAD = "---- MODULE M ----\nEXTENDS Naturals, TLC, TLCExt, Sequences\nVARIABLE x\n";
  it.each([
    [
      "a printing ALIAS",
      `${HEAD}Init == x = 0\nNext == x < 3 /\\ x' = x + 1 /\\ PrintT(<<"A", x>>)\nInv == x < 3\nAlias == [x |-> x, p |-> PrintT(<<"alias", x>>)]\n====`,
      "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias",
      "an ALIAS that prints",
    ],
    [
      "a printing temporal property",
      `${HEAD}Init == x = 0\nNext == \\/ x < 3 /\\ x' = x + 1 /\\ PrintT(<<"A", x>>)\n        \\/ x = 3 /\\ x' = 0 /\\ PrintT(<<"B", x>>)\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\nLive == <>(PrintT(<<"lp", x>>) /\\ x = 7)\n====`,
      "SPECIFICATION Spec\nPROPERTY Live",
      "the engine stopped: printing where the native checker doesn't check the temporal properties: prints it doesn't place in TLC's order",
    ],
    [
      "TLCExt's Trace",
      `${HEAD}Init == x = 0\nNext == x < 3 /\\ x' = x + 1 /\\ PrintT(<<"A", x, Len(Trace)>>)\nInv == x < 3\n====`,
      "INIT Init\nNEXT Next\nINVARIANT Inv",
      "the engine stopped: TLCExt's Trace, the behavior the engine doesn't keep",
    ],
  ])("declines the trace's prints of %s", async (_, source, config, reason) => {
    await expectDeclined({ source, config }, reason);
  });
});

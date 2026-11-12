import { describe, expect, it } from "bun:test";

import { check, type CheckOptions } from "../../src";

// What check passes to onPrint, with the TypeScript check answering where `isInterpreted` asks
// for it: onProgress takes the TypeScript path.
const getPrinted = async (options: CheckOptions, isInterpreted: boolean) => {
  const printed: string[] = [];
  await check({
    ...options,
    onPrint: (text) => printed.push(text),
    ...(isInterpreted && { onProgress: () => {} }),
  });
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
    expect(await getPrinted({ source: ASSERTING, config: "INIT Init\nNEXT Next" }, false)).toEqual([
      ...['<<"init", 0>>', '<<"pre", 0>>', '<<"post", 0>>', '<<"D", 0>>'],
      ...['<<"pre", 1>>', '<<"post", 1>>', '<<"pre", 10>>'],
      ...['<<"init", 0>>', '<<"pre", 0>>', '<<"post", 0>>', '<<"D", 0>>'],
      ...['<<"init", 0>>', '<<"pre", 0>>', '<<"post", 0>>', '<<"D", 0>>', '<<"pre", 10>>'],
    ]);
  });

  // Where the native check doesn't run, the TypeScript check reports what it printed as it
  // searched, as before.
  it("prints what the TypeScript check printed as it searched where the native check didn't run", async () => {
    expect(await getPrinted({ source: ASSERTING, config: "INIT Init\nNEXT Next" }, true)).toEqual([
      ...['<<"init", 0>>', '<<"pre", 0>>', '<<"post", 0>>', '<<"D", 0>>'],
      ...['<<"pre", 1>>', '<<"post", 1>>', '<<"pre", 10>>'],
    ]);
  });

  it("prints each trace -continue reports as TLC does", async () => {
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
    expect(
      await getPrinted(
        { source, config: "INIT Init\nNEXT Next\nINVARIANT Inv", isContinued: true },
        false,
      ),
    ).toEqual([
      ...['<<"init", 0>>', '<<"init", 1>>', '<<"A", 0, 1>>', '<<"A", 1, 2>>', '<<"A", 2, 3>>'],
      ...['<<"init", 0>>', '<<"init", 1>>', '<<"A", 1, 2>>', '<<"A", 2, 3>>', '<<"B", 3>>'],
    ]);
  });

  // The TypeScript check places these prints otherwise than TLC, or prints other values in them, so
  // where the native check declines them it reports what the TypeScript check printed as it
  // searched, as where the native check doesn't run (fallback.md, "Interpreter limits").
  const HEAD = "---- MODULE M ----\nEXTENDS Naturals, TLC, TLCExt, Sequences\nVARIABLE x\n";
  it.each([
    [
      "a printing ALIAS",
      `${HEAD}Init == x = 0\nNext == x < 3 /\\ x' = x + 1 /\\ PrintT(<<"A", x>>)\nInv == x < 3\nAlias == [x |-> x, p |-> PrintT(<<"alias", x>>)]\n====`,
      "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Alias",
    ],
    [
      "a printing temporal property",
      `${HEAD}Init == x = 0\nNext == \\/ x < 3 /\\ x' = x + 1 /\\ PrintT(<<"A", x>>)\n        \\/ x = 3 /\\ x' = 0 /\\ PrintT(<<"B", x>>)\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\nLive == <>(PrintT(<<"lp", x>>) /\\ x = 7)\n====`,
      "SPECIFICATION Spec\nPROPERTY Live",
    ],
    [
      "TLCExt's Trace",
      `${HEAD}Init == x = 0\nNext == x < 3 /\\ x' = x + 1 /\\ PrintT(<<"A", x, Len(Trace)>>)\nInv == x < 3\n====`,
      "INIT Init\nNEXT Next\nINVARIANT Inv",
    ],
  ])("leaves out the trace's prints of %s", async (_, source, config) => {
    expect(await getPrinted({ source, config }, false)).toEqual(
      await getPrinted({ source, config }, true),
    );
  });
});

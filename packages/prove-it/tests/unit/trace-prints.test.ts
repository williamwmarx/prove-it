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

// TLC's output at d8fb231 (-fp 0 -workers 1 -noGenerateSpecTE), the lines the spec printed.
describe("check reports what the spec prints with a trace in TLC's order", () => {
  it.each([false, true])(
    "prints a failure's trace as TLC does, interpreted: %p",
    async (isInterpreted) => {
      const source = [
        "---- MODULE A ----",
        "EXTENDS Naturals, TLC",
        "VARIABLE x",
        'Init == x = 0 /\\ PrintT(<<"init", x>>)',
        'Next == \\/ PrintT(<<"pre", x>>) /\\ x\' = x + 1 /\\ Assert(x < 2, "boom") /\\ PrintT(<<"post", x>>)',
        '        \\/ x\' = x + 10 /\\ x < 1 /\\ PrintT(<<"D", x>>)',
        "====",
      ].join("\n");
      expect(await getPrinted({ source, config: "INIT Init\nNEXT Next" }, isInterpreted)).toEqual([
        ...['<<"init", 0>>', '<<"pre", 0>>', '<<"post", 0>>', '<<"D", 0>>'],
        ...['<<"pre", 1>>', '<<"post", 1>>', '<<"pre", 10>>'],
        ...['<<"init", 0>>', '<<"pre", 0>>', '<<"post", 0>>', '<<"D", 0>>'],
        ...['<<"init", 0>>', '<<"pre", 0>>', '<<"post", 0>>', '<<"D", 0>>', '<<"pre", 10>>'],
      ]);
    },
  );

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
});

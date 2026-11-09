// The engine IR that src/engine/ir.ts lowers a model to, for the native engine. It is lowered only
// when the native engine or PROVE_IT_IR_DUMP asks for it, and lowering changes nothing the
// TypeScript engine does. native/crates/tla-ir decodes it, and its tests hold the corpus's golden
// files to it.

import { afterEach, describe, expect, it, spyOn } from "bun:test";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { check } from "../../src";
import { parseConfig } from "../../src/config";
import { IR_VERSION } from "../../src/engine/ir";
import { createTlcOrder } from "../../src/tlc/order";
import { getStringRank } from "../../src/values";

const COMMIT = join(import.meta.dirname, "../fixtures/commit");
const SOURCE = readFileSync(join(COMMIT, "Commit.tla"), "utf8");
const CONFIG = readFileSync(join(COMMIT, "Commit.cfg"), "utf8");

const settings = ["PROVE_IT_ENGINE", "PROVE_IT_IR_DUMP", "PROVE_IT_ENGINE_BACKEND"].map(
  (name) => [name, process.env[name]] as const,
);
const directory = mkdtempSync(join(tmpdir(), "prove-it-ir-"));

afterEach(() => {
  for (const [name, value] of settings) {
    if (value === undefined) delete process.env[name];
    else process.env[name] = value;
  }
});

process.on("exit", () => rmSync(directory, { recursive: true, force: true }));

// Checks Commit on the TypeScript engine with the engine's lines collected, writing its IR to `dump`
// if given.
const checkCommit = async (dump?: string) => {
  process.env.PROVE_IT_ENGINE = "debug";
  process.env.PROVE_IT_ENGINE_BACKEND = "ts";
  if (dump === undefined) delete process.env.PROVE_IT_IR_DUMP;
  else process.env.PROVE_IT_IR_DUMP = dump;
  const lines: string[] = [];
  const spy = spyOn(console, "error").mockImplementation((message: unknown) => {
    if (typeof message === "string" && message.startsWith("[engine] ")) lines.push(message);
  });
  try {
    const result = await check({ source: SOURCE, config: CONFIG, onPrint: () => {} });
    return { result, lines };
  } finally {
    spy.mockRestore();
  }
};

// The IR's header, its texts and how many TLC ranks, and its variables by name.
const readIr = (ir: Uint8Array) => {
  const words = new Int32Array(ir.buffer, ir.byteOffset, ir.byteLength >> 2);
  const text = new TextDecoder().decode(ir.subarray(words[2] * 4, words[2] * 4 + words[3]));
  const count = words[5];
  const texts = Array.from({ length: count }, (_, index) =>
    text.slice(index === 0 ? 0 : words[5 + index], words[6 + index]),
  );
  const variablesAt = 6 + count;
  return {
    header: Array.from(words.subarray(0, 4)),
    rankedCount: words[4],
    texts,
    variables: Array.from(
      words.subarray(variablesAt + 1, variablesAt + 1 + words[variablesAt]),
      (index) => texts[index],
    ),
  };
};

describe("the engine IR", () => {
  it("is lowered only when PROVE_IT_IR_DUMP or the native engine asks for it", async () => {
    const run = await checkCommit();
    expect(run.lines.filter((line) => line.startsWith("[engine] native: "))).toEqual([]);
    const dump = join(directory, "asked.ir");
    const dumped = await checkCommit(dump);
    const size = readFileSync(dump).length;
    expect(dumped.lines[0]).toMatch(
      new RegExp(`^\\[engine\\] native: ir: ${size} bytes in \\d+\\.\\d\\d ms$`),
    );
  });

  it("is the same every time, and changes nothing the engine does", async () => {
    const first = join(directory, "first.ir");
    const second = join(directory, "second.ir");
    const dumped = await checkCommit(first);
    const again = await checkCommit(second);
    expect(readFileSync(second)).toEqual(readFileSync(first));
    const plain = await checkCommit();
    expect(dumped.result).toEqual(plain.result);
    expect(again.result).toEqual(plain.result);
    const withoutTimes = (lines: string[]) => lines.map((line) => line.replace(/ \d+ ms/, ""));
    expect(withoutTimes(dumped.lines.slice(1))).toEqual(withoutTimes(plain.lines));
    process.env.PROVE_IT_ENGINE = "0";
    expect(await check({ source: SOURCE, config: CONFIG, onPrint: () => {} })).toEqual(
      plain.result,
    );
  });

  it("starts with its magic and version, and its size", async () => {
    const dump = join(directory, "header.ir");
    await checkCommit(dump);
    const ir = readFileSync(dump);
    const header = readIr(ir).header;
    expect(header.slice(0, 2)).toEqual([0x52494950, IR_VERSION]);
    expect(header[2] * 4 + Math.ceil(header[3] / 4) * 4).toBe(ir.length);
  });

  it("holds TLC's string order, as createTlcOrder and getStringRank give it", async () => {
    const dump = join(directory, "strings.ir");
    await checkCommit(dump);
    const table = readIr(readFileSync(dump));
    const order = [
      ...new Set(createTlcOrder(SOURCE, () => undefined).getStringOrder(parseConfig(CONFIG))),
    ];
    expect(table.texts.slice(0, table.rankedCount)).toEqual(order);
    const ranks = table.texts.slice(0, table.rankedCount).map((text) => getStringRank(text));
    expect(ranks).toEqual(ranks.map((_, index) => index));
  });

  it("names the variables in the engine's order", async () => {
    const dump = join(directory, "variables.ir");
    await checkCommit(dump);
    expect(readIr(readFileSync(dump)).variables).toEqual([
      "participantState",
      "coordinatorState",
      "prepared",
      "messages",
    ]);
  });
});

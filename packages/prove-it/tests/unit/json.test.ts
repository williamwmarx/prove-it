import { describe, expect, it } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

import type { CheckOptions } from "../../src";
import { checkOnEngine, expectDeclined } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/json");

const getOptions = (name: string): CheckOptions => ({
  source: readFileSync(join(DIRECTORY, `${name}.tla`), "utf8"),
  config: readFileSync(join(DIRECTORY, `${name}.cfg`), "utf8"),
  readFile: (path) => {
    const fixturePath = join(DIRECTORY, path);
    return existsSync(fixturePath) ? readFileSync(fixturePath, "utf8") : undefined;
  },
  writeFile: () => {},
});

describe("Json matches TLC", () => {
  it("declines TLC's JsonTests model", async () => {
    await expectDeclined(
      getOptions("JsonTests"),
      "an assumption that fails to evaluate: evaluating the assumption again: a failure within TLCExt's AssertEq",
    );
  });

  // TLC: 4 states generated, 2 distinct.
  it("reads the files the spec reads through readFile", async () => {
    const read: string[] = [];
    const result = await checkOnEngine({
      source: `---- MODULE R ----
EXTENDS Integers, Json
VARIABLE x
ASSUME ndJsonDeserialize("Lines.ndjson") = <<1, <<2, "x">>, [a |-> TRUE]>>
Init == x \\in {JsonDeserialize("Integers.json")[2], 7}
Next == x' = x
====`,
      config: "INIT Init\nNEXT Next",
      readFile: (path) => {
        read.push(path);
        const fixturePath = join(DIRECTORY, path);
        return existsSync(fixturePath) ? readFileSync(fixturePath, "utf8") : undefined;
      },
    });
    expect([result.status, result.generatedStates, result.distinctStates, read]).toEqual([
      "success",
      4,
      2,
      ["Lines.ndjson", "Integers.json"],
    ]);
  });

  // TLC writes these, then reports the deadlock at x = 3.
  it("writes the files the spec writes through writeFile", async () => {
    const written: [string, string][] = [];
    const result = await checkOnEngine({
      source: `---- MODULE W ----
EXTENDS Integers, Json
VARIABLE x
Init == x = 0
Next == x < 3 /\\ x' = x + 1
Inv == /\\ JsonSerialize("out.json", <<x, "s", TRUE, {1, 2}>>)
       /\\ ndJsonSerialize("out.ndjson", <<x, "v\\n", <<-1>> >>)
====`,
      config: "INIT Init\nNEXT Next\nINVARIANT Inv",
      writeFile: (path, text) => written.push([path, text]),
    });
    expect([result.status, written]).toEqual([
      "deadlock",
      [
        ["out.json", '[3,"s",true,[1,2]]'],
        ["out.ndjson", '3\n"v\\n"\n[-1]\n'],
      ],
    ]);
  });

  // TLC writes the file as it checks the assumption, then reports that there is no next-state
  // action.
  it("writes the files the spec writes before the error it stops on", async () => {
    const written: [string, string][] = [];
    const checking = checkOnEngine({
      source: `---- MODULE W ----
EXTENDS Json
VARIABLE x
ASSUME JsonSerialize("out.json", <<42>>)
Init == x = 0
====`,
      config: "INIT Init",
      writeFile: (path, text) => written.push([path, text]),
    });
    await expect(checking).rejects.toThrow(
      "No next state actions defined to generate successor states from.",
    );
    expect(written).toEqual([["out.json", "[42]"]]);
  });

  it("declines reading values like TLC's Java Json module", async () => {
    await expectDeclined(
      getOptions("JsonValues"),
      "the engine declined: checking an assumption again: an assumption the engine found to hold that doesn't again",
    );
  });
});

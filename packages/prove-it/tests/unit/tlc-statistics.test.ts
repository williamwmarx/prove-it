import { expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { expectDeclined, runOnEngine } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-statistics");

// The jar's prints at one worker (`prints.txt`), in the order TLC evaluates each part as it
// generates the states, which the engine follows.
it("answers counting states for TLCGet while it generates them as TLC does", () => {
  const run = runOnEngine({
    source: readFileSync(join(DIRECTORY, "Statistics.tla"), "utf8").replace(
      "MODULE Statistics",
      "MODULE M",
    ),
    config: readFileSync(join(DIRECTORY, "Statistics.cfg"), "utf8"),
  });
  expect(run.exitCode).toBe(0);
  expect(run.output.split("\n").filter((line) => line.startsWith("<<"))).toEqual(
    readFileSync(join(DIRECTORY, "prints.txt"), "utf8").trimEnd().split("\n"),
  );
});

it("declines the states generated up to the first violation", async () => {
  await expectDeclined(
    {
      source:
        "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' \\in {1, 2, 3} /\\ PrintT(<<x', TLCGet(\"generated\")>>)\nInv == x # 2\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT Inv",
    },
    "rebuilding a trace: TLCGet",
  );
});

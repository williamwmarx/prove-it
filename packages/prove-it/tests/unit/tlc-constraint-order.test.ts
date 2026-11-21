import { expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { runOnEngine } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-constraint-order");

// The jar's prints at one worker (`prints.txt`), in the order TLC evaluates each part as it
// generates the states, which the engine follows.
it("answers a spec that prints in its constraints and invariants as TLC does", () => {
  const run = runOnEngine({
    source: readFileSync(join(DIRECTORY, "Order.tla"), "utf8").replace("MODULE Order", "MODULE M"),
    config: readFileSync(join(DIRECTORY, "Order.cfg"), "utf8"),
  });
  expect(run.exitCode).toBe(0);
  expect(run.output.split("\n").filter((line) => line.startsWith("<<"))).toEqual(
    readFileSync(join(DIRECTORY, "prints.txt"), "utf8").trimEnd().split("\n"),
  );
});

import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { checkOnEngine, expectDeclined } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-ext");

const getFixture = (name: string, configName = name) => ({
  source: readFileSync(join(DIRECTORY, `${name}.tla`), "utf8"),
  config: readFileSync(join(DIRECTORY, `${configName}.cfg`), "utf8"),
});

describe("TLCExt matches TLC", () => {
  it("declines the trace of TLC's TLCExtTrace model, rebuilt through Trace in a constraint", async () => {
    await expectDeclined(getFixture("TLCExtTrace"), "rebuilding a trace: the builtin Trace");
  });

  it("checks TLC's TLCExtTrace model with an alias", async () => {
    const result = await checkOnEngine(getFixture("TLCExtTrace", "TLCExtTraceAlias"));
    expect(result.status).toBe("invariant-violation");
    expect(result.violations[0]?.states).toHaveLength(7);
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([7, 7, 7]);
  });

  // TLC's output at d8fb231.
  it("checks Trace in the state that the next-state relation extends", async () => {
    const result = await checkOnEngine(getFixture("TraceNext"));
    expect([result.status, result.generatedStates, result.distinctStates, result.depth]).toEqual([
      "success",
      5,
      5,
      5,
    ]);
  });
});

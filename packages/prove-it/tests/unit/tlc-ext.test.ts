import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { checkOnEngine, expectDeclined } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-ext");

const getFixture = (name: string, configName = name) => ({
  source: readFileSync(join(DIRECTORY, `${name}.tla`), "utf8"),
  config: readFileSync(join(DIRECTORY, `${configName}.cfg`), "utf8"),
});

const TRACE = "the engine stopped: TLCExt's Trace, the behavior the engine doesn't keep";

describe("TLCExt matches TLC", () => {
  it("declines TLC's TLCExtTrace model with Trace in an invariant and a constraint", async () => {
    await expectDeclined(getFixture("TLCExtTrace"), TRACE);
  });

  it("checks TLC's TLCExtTrace model with an alias", async () => {
    const result = await checkOnEngine(getFixture("TLCExtTrace", "TLCExtTraceAlias"));
    expect(result.status).toBe("invariant-violation");
    expect(result.violations[0]?.states).toHaveLength(7);
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([7, 7, 7]);
  });

  it("declines Trace in the state that the next-state relation extends", async () => {
    await expectDeclined(getFixture("TraceNext"), TRACE);
  });
});

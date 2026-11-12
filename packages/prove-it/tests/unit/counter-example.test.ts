import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { checkOnEngine, expectDeclined } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-ext");

const getOptions = (configName: string) => ({
  source: readFileSync(join(DIRECTORY, "CounterExample.tla"), "utf8"),
  config: readFileSync(join(DIRECTORY, `${configName}.cfg`), "utf8"),
});

const checkCounterExample = async (configName: string) => {
  const printed: string[] = [];
  const result = await checkOnEngine({
    ...getOptions(configName),
    onPrint: (text) => printed.push(text),
  });
  // TLC prints what the postcondition prints after the trace, which onPrint reports.
  return [result.status, ...printed];
};

describe("POSTCONDITION after a violation matches TLC", () => {
  it("binds CounterExample to the behavior that violates an invariant or deadlocks", async () => {
    expect(
      await Promise.all(
        ["CounterExampleInvariant", "CounterExampleDeadlock"].map((name) =>
          checkCounterExample(name),
        ),
      ),
    ).toEqual([
      [
        "invariant-violation",
        "<<[x |-> 0], [x |-> 1], [x |-> 2]>>",
        '{<<1, "Up", 2>>, <<2, "Up", 3>>}',
      ],
      ["deadlock", "<<[x |-> 0], [x |-> 1], [x |-> 2]>>", '{<<1, "Up", 2>>, <<2, "Up", 3>>}'],
    ]);
  });

  it("declines a lasso whose step back into the cycle prints", async () => {
    await expectDeclined(
      getOptions("CounterExampleCycle"),
      "a temporal property's counterexample: a step back into the cycle of a spec that prints",
    );
  });

  it("closes the lasso of a liveness violation that stutters", async () => {
    expect(await checkCounterExample("CounterExampleStutter")).toEqual([
      "liveness-violation",
      "<<[x |-> 0], [x |-> 1], [x |-> 2]>>",
      '{<<1, "Up", 2>>, <<2, "Up", 3>>, <<3, "Up", 3>>}',
    ]);
  });

  it("keeps the status of the violation when the postcondition is false", async () => {
    expect((await checkCounterExample("CounterExampleFails"))[0]).toBe("invariant-violation");
  });
});

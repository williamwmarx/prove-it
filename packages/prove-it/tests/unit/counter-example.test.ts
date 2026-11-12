import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { checkOnEngine } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-ext");

// A lasso declines natively where its step back into the cycle prints, and the TypeScript check
// answers it; one that stutters doesn't step back.
const LASSO_DECLINED =
  "a temporal property's counterexample: a step back into the cycle of a spec that prints";

const checkCounterExample = async (configName: string, declinedFor?: string) => {
  const printed: string[] = [];
  const result = await checkOnEngine(
    {
      source: readFileSync(join(DIRECTORY, "CounterExample.tla"), "utf8"),
      config: readFileSync(join(DIRECTORY, `${configName}.cfg`), "utf8"),
      onPrint: (text) => printed.push(text),
    },
    declinedFor,
  );
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

  it("closes the lasso of a liveness violation with the step back to the loop", async () => {
    expect(
      await Promise.all([
        checkCounterExample("CounterExampleCycle", LASSO_DECLINED),
        checkCounterExample("CounterExampleStutter"),
      ]),
    ).toEqual([
      [
        "liveness-violation",
        "<<[x |-> 0], [x |-> 1], [x |-> 2]>>",
        '{<<1, "Up", 2>>, <<2, "Up", 3>>, <<3, "Back", 2>>}',
      ],
      [
        "liveness-violation",
        "<<[x |-> 0], [x |-> 1], [x |-> 2]>>",
        '{<<1, "Up", 2>>, <<2, "Up", 3>>, <<3, "Up", 3>>}',
      ],
    ]);
  });

  it("keeps the status of the violation when the postcondition is false", async () => {
    expect((await checkCounterExample("CounterExampleFails"))[0]).toBe("invariant-violation");
  });
});

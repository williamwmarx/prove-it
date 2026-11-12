import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import type { CheckOptions } from "../../src";
import { checkParsed } from "../../src/parallel";
import { checkOnEngine } from "../native-check";

const FIXTURES = join(import.meta.dirname, "../fixtures");
// TLC's -workers leaves the engine on one thread, so each check asks for as many engine threads
// as it asks for workers.
const checkWithThreads = async (options: CheckOptions, declinedFor?: string) => {
  const previous = process.env.PROVE_IT_WORKERS;
  process.env.PROVE_IT_WORKERS = String(options.workers ?? 1);
  try {
    return await checkOnEngine(options, declinedFor);
  } finally {
    if (previous === undefined) delete process.env.PROVE_IT_WORKERS;
    else process.env.PROVE_IT_WORKERS = previous;
  }
};

const checkFixtureInParallel = (
  directory: string,
  name: string,
  workers: number,
  declinedFor?: string,
) =>
  checkWithThreads(
    {
      source: readFileSync(join(FIXTURES, directory, `${name}.tla`), "utf8"),
      config: readFileSync(join(FIXTURES, directory, `${name}.cfg`), "utf8"),
      workers,
    },
    declinedFor,
  );

const getCounts = (result: { generatedStates: number; distinctStates: number; depth: number }) => [
  result.generatedStates,
  result.distinctStates,
  result.depth,
];

describe("check with workers matches TLC", () => {
  it.each([2, 3, 4])("explores the commit protocol with %i workers", async (workers) => {
    const result = await checkFixtureInParallel("commit", "Commit", workers);
    expect(result.status).toBe("success");
    expect(getCounts(result)).toEqual([890, 251, 11]);
  });

  it("reports an invariant that fails to evaluate on an initial state like one worker", async () => {
    const result = await checkWithThreads({
      source:
        "---- MODULE M ----\nEXTENDS Integers\nVARIABLE x\nInit == x \\in 0..1\nNext == UNCHANGED x\nInv == 1 \\div x = 0\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT Inv",
      workers: 2,
    });
    expect(result.status).toBe("error");
    expect(result.violations.map((violation) => violation.headline)).toEqual([
      "The second argument of \\div is 0.",
    ]);
  });

  it("summarizes the outdegrees and the fingerprints of every worker like one worker", async () => {
    const directory = join(import.meta.dirname, "../../benchmarks/queue");
    const options = {
      source: readFileSync(join(directory, "Queue.tla"), "utf8"),
      config: readFileSync(join(directory, "Queue.cfg"), "utf8"),
    };
    const sequential = await checkParsed(options);
    const parallel = await checkParsed({ ...options, workers: 3 });
    expect(parallel.fingerprintDistance).toBe(sequential.fingerprintDistance);
    expect(parallel.fingerprintDistance).toBeDefined();
    const getTotals = (outDegrees: number[] | undefined = []) => [
      outDegrees.reduce((sum, count) => sum + count, 0),
      outDegrees.reduce((sum, count, degree) => sum + count * degree, 0),
    ];
    expect(getTotals(parallel.outDegrees)).toEqual(getTotals(sequential.outDegrees));
  });

  it("reports an invariant that a successor outside the action constraint violates", async () => {
    const result = await checkWithThreads({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x \\in 0..1\nNext == x < 5 /\\ x' = x + 1\nInv == x # 3\nSkip == x' # 3\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT Inv\nACTION_CONSTRAINT Skip\nCHECK_DEADLOCK FALSE",
      workers: 2,
    });
    expect(result.status).toBe("invariant-violation");
    expect(result.violations[0]?.headline).toBe("Invariant Inv is violated.");
    expect(result.violations[0]?.states).toHaveLength(3);
  });

  it("reports an action property violated in a level the workers expand", async () => {
    const result = await checkWithThreads({
      source: [
        "---- MODULE M ----",
        "EXTENDS Naturals",
        "VARIABLES x, y",
        "Init == x \\in 1..4000 /\\ y = 0",
        // Slow enough for the workers to join before the last levels.
        "Next == y < 9 /\\ (\\A i \\in 1..300 : i + x + y > 0) /\\ y' = y + 1 /\\ x' = x",
        "Spec == Init /\\ [][Next]_<<x, y>>",
        "Prop == [][~(y' = 8 /\\ x = 17)]_<<x, y>>",
        "====",
      ].join("\n"),
      config: "SPECIFICATION Spec\nPROPERTY Prop\nCHECK_DEADLOCK FALSE",
      workers: 4,
    });
    expect(result.status).not.toBe("success");
    expect(result.violations[0]?.headline).toBe("Action property Prop is violated.");
    expect([result.generatedStates, result.distinctStates]).toEqual([32017, 32017]);
  });

  it("prints what assumptions print once when it checks on the calling thread", async () => {
    const printed: string[] = [];
    const result = await checkWithThreads({
      source:
        '---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nASSUME PrintT("start")\nInit == x = 0\nNext == x\' = (x + 1) % 3\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\nLive == <>(x = 2)\n====',
      config: "SPECIFICATION Spec\nPROPERTY Live",
      workers: 2,
      onPrint: (text) => printed.push(text),
    });
    expect(result.status).toBe("success");
    expect(printed).toEqual(['"start"']);
  });

  it("prints values as the version of TLC it matches does", async () => {
    const printed: string[] = [];
    await checkWithThreads(
      {
        source:
          "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nASSUME PrintT([k \\in 1..0 |-> k])\nInit == x = 0\nNext == x' = (x + 1) % 3\n====",
        config: "INIT Init\nNEXT Next",
        workers: 2,
        version: "1.7.4",
        onPrint: (text) => printed.push(text),
      },
      "TLC 1.7.4",
    );
    expect(printed).toEqual(["<< >>"]);
  });

  it("grows the fingerprint table that workers share while they expand a level", async () => {
    const result = await checkWithThreads({
      source:
        "---- MODULE Grid ----\nEXTENDS Naturals\nVARIABLES x, y\nInit == x = 0 /\\ y = 0\nNext == \\/ x < 99 /\\ x' = x + 1 /\\ y' = y\n        \\/ y < 99 /\\ y' = y + 1 /\\ x' = x\n====",
      config: "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
      workers: 4,
    });
    expect(result.status).toBe("success");
    expect(getCounts(result)).toEqual([19801, 10000, 199]);
  });

  it("explores a level long enough for workers to take breaks like one worker", async () => {
    const options = {
      source:
        "---- MODULE Slow ----\nEXTENDS Naturals\nVARIABLE x\nInit == x \\in 1..4000\nNext == x <= 4000 /\\ (\\A i \\in 1..2000 : i > 0) /\\ x' = x + 4000\n====",
      config: "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
    };
    const sequential = await checkWithThreads(options);
    const parallel = await checkWithThreads({ ...options, workers: 3 });
    expect(parallel.status).toBe("success");
    expect(getCounts(parallel)).toEqual(getCounts(sequential));
  });

  it("explores a queue that only grows to its bound", async () => {
    const result = await checkFixtureInParallel("queue", "Queue", 3);
    expect(result.status).toBe("success");
    expect(getCounts(result)).toEqual([181, 105, 9]);
  });

  it("reduces states under a symmetry set", async () => {
    const result = await checkFixtureInParallel("symmetry", "Symmetry", 2);
    expect(result.status).toBe("success");
    expect(getCounts(result)).toEqual([42, 10, 7]);
  });

  it("reports the shortest invariant violation trace like one worker", async () => {
    const result = await checkFixtureInParallel("water-jugs", "WaterJugs", 4);
    expect(result.status).toBe("invariant-violation");
    expect(result.violations[0]?.headline).toBe("Invariant GoalNotReached is violated.");
    expect(result.violations[0]?.states).toHaveLength(7);
    expect(getCounts(result)).toEqual([73, 14, 7]);
  });

  it("reports deadlock with its trace like one worker", async () => {
    const result = await checkFixtureInParallel("counter", "Counter", 2);
    expect(result.status).toBe("deadlock");
    expect(result.violations[0]?.states.map((step) => step.label.split(" line ")[0])).toEqual([
      "Initial predicate",
      "Increment",
      "Increment",
      "Increment",
    ]);
    expect(getCounts(result)).toEqual([4, 4, 4]);
  });

  it.each([2, 3])("orders sets of strings like TLC with %i workers", async (workers) => {
    const result = await checkFixtureInParallel("strings", "StringSets", workers);
    expect(result.status).toBe("success");
    expect(getCounts(result)).toEqual([76, 31, 5]);
  });

  it("checks specs that create strings while checking like one worker", async () => {
    const result = await checkFixtureInParallel(
      "strings",
      "RuntimeStrings",
      2,
      "the engine stopped: an order of strings the search made",
    );
    expect(result.status).toBe("success");
    expect(getCounts(result)).toEqual([115, 97, 6]);
  });
});

import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { check } from "../../src";
import { getUnexpectedException } from "../../src/errors";
import type { TlcVersion } from "../../src/tlc/version";
import { checkOnEngine } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/liveness");

const SOURCE = readFileSync(join(DIRECTORY, "Liveness.tla"), "utf8");

const TLC_VERDICTS: [string, string][] = [
  ["Unfair-ReachesLimit", "liveness-violation"],
  ["Unfair-StaysAtLimit", "liveness-violation"],
  ["Unfair-Served", "liveness-violation"],
  ["Unfair-TokenMoves", "liveness-violation"],
  ["Unfair-NeverCritical", "liveness-violation"],
  ["Fair-ReachesLimit", "success"],
  ["Fair-StaysAtLimit", "success"],
  ["Fair-Served", "success"],
  ["Fair-TokenMoves", "success"],
  ["Fair-NeverCritical", "liveness-violation"],
  ["Strong-ReachesLimit", "success"],
  ["Strong-StaysAtLimit", "success"],
  ["Strong-Served", "success"],
  ["Strong-TokenMoves", "success"],
  ["Strong-NeverCritical", "liveness-violation"],
];

describe("liveness matches TLC", () => {
  it.each(TLC_VERDICTS)("%s is %s", async (name, status) => {
    const result = await checkOnEngine({
      source: SOURCE,
      config: readFileSync(join(DIRECTORY, `${name}.cfg`), "utf8"),
    });
    expect(result.status).toBe<string>(status);
    expect([result.generatedStates, result.distinctStates]).toEqual([92, 36]);
  });

  // The search takes longer than the three seconds before TLC's first periodic check, and every
  // state the check sees can stutter forever.
  it("finds a lasso in the part of the graph that TLC's periodic check sees", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE Tree ----\nEXTENDS Naturals\nVARIABLE x\nNext == x < 4000000 /\\ x' \\in {2 * x + 1, 2 * x + 2}\nSpec == x = 0 /\\ [][Next]_x\nProperty == TRUE ~> FALSE\n====",
      config: "SPECIFICATION Spec\nPROPERTY Property",
    });
    expect(result.status).toBe("liveness-violation");
  }, 60_000);

  // TLC at the commit it is recorded at names the property it finds the lasso violates, after a
  // step to any of a thousand states.
  it("names the temporal property a lasso through one of many states violates", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE Many ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == IF x = 0 THEN x' \\in 1..1000 ELSE UNCHANGED x\nLive == <>(x = 1)\n====",
      config: "INIT Init\nNEXT Next\nPROPERTY Live",
    });
    expect([result.status, result.violations[0]?.headline]).toEqual([
      "liveness-violation",
      "Temporal property Live was violated.\n",
    ]);
  });

  // TLC's LNAction of <<A>>_v compares v in the two states before it evaluates A, so A, whose
  // division fails where x is unchanged, is never evaluated on a step that only toggles y.
  it("checks the subscript of <<A>>_v before A", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE Angle ----\nEXTENDS Naturals\nVARIABLES x, y\nInc == x' = (x + 1) % 3 /\\ UNCHANGED y\nTog == y' = 1 - y /\\ UNCHANGED x\nSpec == x = 0 /\\ y = 0 /\\ [][Inc \\/ Tog]_<<x, y>>\nA == (x' - x) \\div (x' - x) # 0\nP == []<><<A>>_x\n====",
      config: "SPECIFICATION Spec\nPROPERTY P",
    });
    expect([result.status, result.distinctStates]).toEqual(["liveness-violation", 6]);
  });

  it("reports a lasso whose cycle returns to an earlier state", async () => {
    const result = await checkOnEngine({
      source: SOURCE,
      config: readFileSync(join(DIRECTORY, "Unfair-ReachesLimit.cfg"), "utf8"),
    });
    const violation = result.violations[0];
    expect(violation?.loopStart).toBeDefined();
    expect(violation?.loopStart).toBeLessThan(violation?.states.length ?? 0);
  });

  it("reports the deadlock before the temporal property that fails in the same state", async () => {
    const checkConfig = async (name: string) => {
      const directory = join(import.meta.dirname, "../fixtures/github710");
      const result = await checkOnEngine({
        source: readFileSync(join(directory, "Github710d.tla"), "utf8"),
        config: readFileSync(join(directory, `${name}.cfg`), "utf8"),
      });
      return [
        result.status,
        result.violations[0]?.headline,
        result.violations[0]?.states.map((step) => step.variables.x.value),
      ];
    };
    expect(await checkConfig("Github710d")).toEqual([
      "deadlock",
      "Deadlock reached.",
      [0, 1, 2, 3],
    ]);
    expect(await checkConfig("Github710dNoDeadlock")).toEqual([
      "property-violation",
      "Temporal property NeverThree was violated.\n",
      [0, 1, 2, 3],
    ]);
  });

  it("finds a violation of a safety-like property early unless TLC is 1.7.4", async () => {
    const directory = join(import.meta.dirname, "../fixtures/github710");
    const getAdditionalViolation = async (version: TlcVersion) => {
      // The engine follows TLC at the commit it is recorded at.
      const result = await checkOnEngine(
        {
          source: readFileSync(join(directory, "Github710d.tla"), "utf8"),
          config: readFileSync(join(directory, "Github710d.cfg"), "utf8"),
          version,
        },
        version === "1.7.4" ? "TLC 1.7.4" : undefined,
      );
      return result.violations[1]?.headline;
    };
    expect(await getAdditionalViolation("master")).toBe(
      "Temporal property NeverThree was violated.\n",
    );
    expect(await getAdditionalViolation("1.7.4")).toBeUndefined();
  });

  it.each(["master", "1.7.4"] satisfies TlcVersion[])(
    "evaluates a constant conjunct of a temporal property in TLC %s",
    async (version) => {
      const result = check({
        source:
          "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = 1 - x\nSpec == Init /\\ [][Next]_x\nP == <>[](x = 1 /\\ (1 \\div 0) > 0)\n====",
        config: "SPECIFICATION Spec\nPROPERTY P",
        version,
      });
      await expect(result).rejects.toThrow(
        `${getUnexpectedException("tlc2.tool.EvalException")}The second argument of \\div is 0.`,
      );
    },
  );
});

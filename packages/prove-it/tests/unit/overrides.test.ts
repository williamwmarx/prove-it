import { describe, expect, it } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { checkOnEngine, expectDeclined } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/overrides");

const loadClass = (name: string) => {
  const path = join(DIRECTORY, `${name}.class`);
  return existsSync(path) ? readFileSync(path) : undefined;
};

// The spec of a tests/fixtures/override-shapes directory with its classes.
const getShape = (shape: string) => {
  const directory = join(import.meta.dirname, "../fixtures/override-shapes", shape);
  return {
    source: readFileSync(join(directory, "P.tla"), "utf8"),
    config: readFileSync(join(directory, "P.cfg"), "utf8"),
    loadClass: (name: string) => {
      const path = join(directory, `${name}.class`);
      return existsSync(path) ? readFileSync(path) : undefined;
    },
  };
};

describe("Java module overrides match TLC", () => {
  it("declines the overrides TLC lists in the JVM's order", async () => {
    await expectDeclined(
      { source: readFileSync(join(DIRECTORY, "Overrides.tla"), "utf8"), config: "", loadClass },
      "the Java overrides TLC lists in the JVM's order",
    );
  });

  it("declines an override with parameters, whose arguments TLC evaluates first", async () => {
    // TLC evaluates 1 \div 0 before it calls Twice, and reports the division, not -2.
    await expectDeclined(
      {
        source:
          "---- MODULE Overrides ----\nEXTENDS Integers\nVARIABLE x\nTwice(n) == 2 * n\nInit == x = Twice(1 \\div 0)\nNext == x' = x\nInv == x = -2\n====",
        config: "INIT Init\nNEXT Next\nINVARIANT Inv",
        loadClass,
      },
      "a Java override with parameters, whose arguments TLC evaluates",
    );
  });

  it("declines an override class it does not read whole", async () => {
    // tests/fixtures/override-shapes: in each, TLC runs what the front end can't, or matches
    // otherwise (each P.java says what TLC does).
    for (const [shape, reason] of [
      ["clinit", "a Java override class with a static initializer"],
      ["field", "a Java override class with fields"],
      ["super", "a Java override class with a superclass"],
      ["overload", "a Java override class with methods of one name"],
      ["registry", "a Java override of a name TLC maps to an operator's"],
    ]) {
      await expectDeclined(getShape(shape), reason);
    }
  });

  it("skips a method annotated as an operator a TLCOverrides index loads", async () => {
    // TLC at d8fb231 loads no override, so K stays 1 and Inv holds.
    expect((await checkOnEngine(getShape("annotation"))).status).toBe("success");
  });

  it("runs a method that catches an exception up to its first return", async () => {
    // TLC at d8fb231 loads K, whose try block returns 0, and reports x = 0 violating Inv.
    const result = await checkOnEngine(getShape("trycatch"));
    expect([
      result.status,
      result.violations[0]?.states.map((step) => step.variables.x?.text),
    ]).toEqual(["invariant-violation", ["0"]]);
  });

  it("declines an override whose method computes its value", async () => {
    await expectDeclined(
      {
        source: "---- MODULE Overrides ----\nComputed == 0\nASSUME Computed = 7\n====",
        config: "",
        loadClass,
      },
      "a Java override that computes its value",
    );
  });
});

import { describe, expect, it } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { check, type CheckProgress, TlaUnsupportedError } from "../../src";

const DIRECTORY = join(import.meta.dirname, "../fixtures/overrides");

const loadClass = (name: string) => {
  const path = join(DIRECTORY, `${name}.class`);
  return existsSync(path) ? readFileSync(path) : undefined;
};

describe("Java module overrides match TLC", () => {
  it("replaces each operator with the method of the same name and arity", async () => {
    const result = await check({
      source: readFileSync(join(DIRECTORY, "Overrides.tla"), "utf8"),
      config: "",
      loadClass,
    });
    expect(result.status).toBe("success");
  });

  it("reports whether each method matches an operator as it loads the class", async () => {
    const overrides: Extract<CheckProgress, { kind: "java-override" }>[] = [];
    await check({
      source: readFileSync(join(DIRECTORY, "Overrides.tla"), "utf8"),
      config: "",
      loadClass,
      onProgress: (progress) => {
        if (progress.kind === "java-override") overrides.push(progress);
      },
    });
    // TLC lists the methods in an order that depends on the JVM.
    expect(overrides.toSorted((left, right) => (left.operator < right.operator ? -1 : 1))).toEqual<
      unknown[]
    >(
      [
        ["Computed", "()", false],
        ["Flag", "()", true],
        ["Large", "()", true],
        ["Mismatch", "(tlc2.value.impl.Value)", false],
        ["Name", "()", true],
        ["Small", "()", true],
        ["Twice", "(tlc2.value.impl.Value)", false],
      ].map(([operator, parameters, isMatched]) => ({
        kind: "java-override",
        module: "Overrides",
        operator,
        signature: `public static tlc2.value.impl.Value Overrides.${operator}${parameters}`,
        isMatched,
      })),
    );
  });

  it("rejects an override with parameters, whose arguments TLC evaluates first", async () => {
    // TLC evaluates 1 \div 0 before it calls Twice, and reports the division, not -2.
    await expect(
      check({
        source:
          "---- MODULE Overrides ----\nEXTENDS Integers\nVARIABLE x\nTwice(n) == 2 * n\nInit == x = Twice(1 \\div 0)\nNext == x' = x\nInv == x = -2\n====",
        config: "INIT Init\nNEXT Next\nINVARIANT Inv",
        loadClass,
      }),
    ).rejects.toThrow(TlaUnsupportedError);
  });

  it("rejects an override class it does not read whole", async () => {
    // tests/fixtures/override-shapes: in each, TLC runs what the front end can't, or matches
    // otherwise (each P.java says what TLC does).
    for (const [shape, reason] of [
      ["clinit", "A Java override class with a static initializer"],
      ["field", "A Java override class with fields"],
      ["super", "A Java override class with a superclass"],
      ["overload", "A Java override class with methods of one name"],
      ["annotation", "A Java override class with annotations"],
      ["trycatch", "The Java override P.K computes its value"],
      ["registry", "A Java override of a name TLC maps to an operator's"],
    ]) {
      const directory = join(import.meta.dirname, "../fixtures/override-shapes", shape);
      await expect(
        check({
          source: readFileSync(join(directory, "P.tla"), "utf8"),
          config: readFileSync(join(directory, "P.cfg"), "utf8"),
          loadClass: (name) => {
            const path = join(directory, `${name}.class`);
            return existsSync(path) ? readFileSync(path) : undefined;
          },
        }),
      ).rejects.toThrow(`${reason}, which tla-ts cannot run`);
    }
  });

  it("rejects an override whose method computes its value", async () => {
    await expect(
      check({
        source: "---- MODULE Overrides ----\nComputed == 0\nASSUME Computed = 7\n====",
        config: "",
        loadClass,
      }),
    ).rejects.toThrow(TlaUnsupportedError);
  });
});

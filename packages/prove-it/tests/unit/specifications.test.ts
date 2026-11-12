import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { check, TlaConfigError, TlaEvaluationError } from "../../src";
import { checkOnEngine, expectDeclined } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/specifications");

const getOptions = (config: string, moduleName = "Specifications", values = "{a, b}") => ({
  source: readFileSync(join(DIRECTORY, `${moduleName}.tla`), "utf8"),
  config: moduleName === "Specifications" ? `CONSTANT P = ${values}\n${config}` : config,
  loadModule: (name: string) => readFileSync(join(DIRECTORY, `${name}.tla`), "utf8"),
});

const checkSpecification = (config: string, moduleName?: string, values?: string) =>
  check(getOptions(config, moduleName, values));

const getSummary = async (config: string, moduleName?: string) => {
  const result = await checkOnEngine(getOptions(config, moduleName));
  return [result.status, result.generatedStates, result.distinctStates, result.depth];
};

describe("SPECIFICATION matches TLC", () => {
  it.each(["Argument", "Twice", "Instance", "Local"])(
    "takes the initial predicate and next-state relation of %s from operator arguments",
    async (name) => {
      expect(await getSummary(`SPECIFICATION ${name}\nINVARIANT Inv`)).toEqual([
        "success",
        6,
        2,
        1,
      ]);
    },
  );

  it("keeps fairness under a bounded universal quantifier as one temporal formula", async () => {
    expect(await getSummary("SPECIFICATION ForallFair\nPROPERTY Visits")).toEqual([
      "success",
      6,
      2,
      1,
    ]);
    expect((await getSummary("SPECIFICATION Argument\nPROPERTY Visits"))[0]).toBe(
      "liveness-violation",
    );
  });

  it.each(["InsideForall", "InsideExists", "ForallInit"])(
    "takes no initial predicate from inside the quantifier of %s",
    async (name) => {
      await expect(
        checkSpecification(`SPECIFICATION ${name}`, "Specifications", "{1}"),
      ).rejects.toThrow(
        new TlaConfigError("The configuration file did not specify the initial state predicate."),
      );
    },
  );

  it("takes no next-state relation from inside a quantifier", async () => {
    await expect(
      checkSpecification("SPECIFICATION ForallNext", "Specifications", "{1}"),
    ).rejects.toThrow(
      new TlaEvaluationError("No next state actions defined to generate successor states from."),
    );
  });

  it.each(["TemporalExists", "TemporalForall"])(
    "declines the temporal quantifier of %s",
    async (name) => {
      await expectDeclined(
        getOptions(`SPECIFICATION ${name}`),
        "temporal quantification in the specification",
      );
    },
  );

  it.each(["Spec", "SpecNext", "SpecAction"])(
    "passes the formulas of %s through operator parameters",
    async (name) => {
      expect(await getSummary(`SPECIFICATION ${name}`, "Github1244")).toEqual(["success", 3, 2, 2]);
    },
  );
});

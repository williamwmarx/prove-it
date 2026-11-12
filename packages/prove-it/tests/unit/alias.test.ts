import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { parseConfig, TlaConfigError, type TraceStep } from "../../src";
import { checkOnEngine } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/alias");

const checkAlias = (configName: string) =>
  checkOnEngine({
    source: readFileSync(join(DIRECTORY, "Alias.tla"), "utf8"),
    config: readFileSync(join(DIRECTORY, `${configName}.cfg`), "utf8"),
  });

const checkModule = (body: string, config: string) =>
  checkOnEngine({
    source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\n${body}\n====`,
    config: `INIT Init\nNEXT Next\n${config}`,
  });

const formatTrace = (trace: TraceStep[] | undefined) =>
  (trace ?? []).map((step) =>
    Object.entries(step.variables).map(([name, variable]) => `${name} = ${variable.text}`),
  );

const getValues = (step: TraceStep | undefined) =>
  Object.fromEntries(
    Object.entries(step?.variables ?? {}).map(([name, variable]) => [name, variable.value]),
  );

describe("ALIAS matches TLC", () => {
  it("prints the alias of each state in a safety trace", async () => {
    const result = await checkAlias("Alias");
    expect(result.status).toBe("invariant-violation");
    expect(formatTrace(result.violations[0]?.states)).toEqual(
      [1, 2, 3, 4].map((stateNumber) => {
        const records = [1, 2, 3, 4]
          .slice(0, stateNumber)
          .map((step) => `[x |-> ${step}, y |-> ${step % 2 === 0 ? "TRUE" : "FALSE"}]`);
        return [
          `yy = ${stateNumber % 2 === 0 ? "TRUE" : "FALSE"}`,
          `x = ${stateNumber}`,
          `a = ${stateNumber === 4 ? 0 : 1}`,
          `b = ${stateNumber === 4 ? "TRUE" : "FALSE"}`,
          `anim = "e1: ${stateNumber} e2: ${stateNumber % 2 === 0 ? "TRUE" : "FALSE"}"`,
          "te = TRUE",
          `lvl = <<${stateNumber}, ${stateNumber}>>`,
          // TLC's pretty printer breaks a sequence too long for its line.
          stateNumber === 4
            ? `trc = << ${records.join(",\n   ")} >>`
            : `trc = <<${records.join(", ")}>>`,
        ];
      }),
    );
  });

  it("evaluates the last state of a lasso against the state it loops back to", async () => {
    const result = await checkAlias("AliasLasso");
    expect([result.status, result.violations[0]?.loopStart]).toEqual(["liveness-violation", 0]);
    expect(formatTrace(result.violations[0]?.states).map((step) => step.slice(2, 4))).toEqual([
      ["a = 1", "b = FALSE"],
      ["a = 1", "b = FALSE"],
      ["a = 1", "b = FALSE"],
      ["a = -3", "b = FALSE"],
    ]);
  });

  it("evaluates a stuttering state against itself", async () => {
    const result = await checkAlias("AliasStuttering");
    expect([result.status, result.violations[0]?.loopStart]).toEqual(["liveness-violation", 0]);
    expect(formatTrace(result.violations[0]?.states).map((step) => step.slice(2, 4))).toEqual([
      ["a = 0", "b = TRUE"],
    ]);
  });

  it("adds _ALIASEvalError to the state when the alias fails", async () => {
    const next = "Next == x < 1 /\\ x' = x + 1\nArgument(n) == [n |-> n]\nConstant == [c |-> 1]";
    expect(
      await Promise.all(
        ["Undefined", "Argument", "Constant"].map(
          async (name) =>
            (await checkModule(next, `ALIAS ${name}`)).violations[0]?.states[0].variables
              ._ALIASEvalError.value,
        ),
      ),
    ).toEqual([
      "The alias Undefined specified in the configuration file\nis not defined in the specification.",
      "TLC requires alias not to take any argument, but one was given: Argument",
      "The alias Constant cannot be a constant.",
    ]);
    const result = await checkModule(
      "Next == x < 1 /\\ x' = x + 1\nAlias == [y |-> 1 \\div x]",
      "ALIAS Alias",
    );
    expect(Object.keys(getValues(result.violations[0]?.states[0]))).toEqual([
      "x",
      "_ALIASEvalError",
    ]);
    expect(getValues(result.violations[0]?.states[1])).toEqual({ y: 1 });
  });

  it("marks the message of _ALIASEvalError as TLC does in -tool output", async () => {
    const result = await checkOnEngine({
      source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 1 /\\ x' = x + 1\nArgument(n) == [n |-> n]\n====`,
      config: "INIT Init\nNEXT Next\nALIAS Argument",
      isTool: true,
    });
    expect(result.violations[0]?.states[0].variables._ALIASEvalError.value).toBe(
      "@!@!@STARTMSG 2228:0 @!@!@\nTLC requires alias not to take any argument, but one was given: Argument\n@!@!@ENDMSG 2228 @!@!@",
    );
  });

  it("keeps the state when the alias is not a record", async () => {
    const result = await checkModule(
      "Next == x < 1 /\\ x' = x + 1\nAlias == x + 100",
      "ALIAS Alias",
    );
    expect(result.violations[0]?.states.map(getValues)).toEqual([{ x: 0 }, { x: 1 }]);
  });

  it("prints a deadlocked initial state without the alias", async () => {
    const result = await checkModule("Next == x > 0 /\\ x' = x\nAlias == [y |-> x]", "ALIAS Alias");
    expect([result.status, getValues(result.violations[0]?.states[0])]).toEqual([
      "deadlock",
      { x: 0 },
    ]);
  });

  it("rejects a second ALIAS", async () => {
    expect(() => parseConfig("ALIAS A\nALIAS B")).toThrow(TlaConfigError);
  });
});

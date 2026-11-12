import { afterEach, describe, expect, it } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { encodeForBackend } from "../../scripts/native-prover";
import { type ProofObligation, prove, type ProveOptions, TlaUnsupportedError } from "../../src";

// HourClock and Simple come from tlaplus/Examples. Each .smt file is the input tlapm sent to its
// SMT solver for that obligation.
const DIRECTORY = join(import.meta.dirname, "../fixtures/prove");

const loadModule = (name: string) => {
  const path = join(DIRECTORY, `${name}.tla`);
  return existsSync(path) ? readFileSync(path, "utf8") : undefined;
};

const proveFixture = (name: string, options: Partial<ProveOptions> = {}) =>
  prove({ source: loadModule(name) ?? "", loadModule, ...options });

// tlapm's comments name its version and the obligation, so only the commands are compared.
const getCommands = (script: string) =>
  script
    .split("\n")
    .filter((line) => !line.startsWith(";"))
    .join(" ")
    .split(/\s+/)
    .join(" ")
    .trim();

// TLAPS, where the fixtures have none, is the one the obligations know.
const encodeFixture = (name: string, id: number) =>
  encodeForBackend(
    `${name}.tla`,
    loadModule(name) ?? "",
    (moduleName) => {
      const source = loadModule(moduleName);
      return source === undefined ? undefined : { file: `${moduleName}.tla`, source };
    },
    id,
    "smt",
  );

const PATH = process.env.PATH;

afterEach(() => {
  process.env.PATH = PATH;
});

describe("prove follows tlapm's default method", () => {
  it("proves what tlapm proves, with the prover tlapm used", async () => {
    const result = await proveFixture("HourClock_proof");
    expect(
      result.obligations.map((obligation) => [
        obligation.id,
        obligation.status === "proved" ? obligation.prover : obligation.status,
      ]),
    ).toEqual([
      [1, "ls4"],
      [2, "trivial"],
      [3, "trivial"],
      [4, "trivial"],
      [5, "smt"],
      [6, "smt"],
    ]);
  });

  it("reports each obligation as it finishes", async () => {
    const reported: ProofObligation[] = [];
    const result = await proveFixture("HourClock_proof", {
      onObligation: (obligation) => reported.push(obligation),
    });
    expect(reported).toEqual(result.obligations);
    expect(result.obligations).toHaveLength(6);
  });

  it("stops when its signal aborts", async () => {
    const controller = new AbortController();
    const proving = proveFixture("HourClock_proof", {
      signal: controller.signal,
      onObligation: () => controller.abort(),
    });
    await expect(proving).rejects.toThrow(controller.signal.reason);
  });

  // tlapm/test/fast/basic/smt_rlimit_bad_test.tla
  it("fails only the obligation whose method is malformed", async () => {
    const result = await proveFixture("smt_rlimit_bad_test");
    expect(result.obligations.map((obligation) => [obligation.id, obligation.status])).toEqual([
      [1, "failed"],
      [2, "trivial"],
    ]);
  });

  // Two different lone surrogates, which the engine would read as the same U+FFFD, so that the
  // axiom that the two strings differ would contradict itself and prove both.
  it.each(["=", "#"])(
    "proves neither string %s the other where each is a lone surrogate",
    async (operator) => {
      const result = await prove({
        source: `---- MODULE M ----\nEXTENDS TLAPS\nTHEOREM "\uD800" ${operator} "\uDC00" BY SMT\n====\n`,
      });
      expect(result.obligations).toMatchObject([
        { status: "failed", reason: "smt failed: smt declined: the text holds a lone surrogate" },
        { status: "trivial" },
      ]);
    },
  );

  it("needs tlapm on the PATH for the tlapm backend", async () => {
    process.env.PATH = "";
    await expect(proveFixture("HourClock_proof", { backend: "tlapm" })).rejects.toThrow(
      TlaUnsupportedError,
    );
  });
});

describe("SMT-LIB encoding matches tlapm", () => {
  it("encodes an action with an IF and a primed variable", () => {
    expect(getCommands(encodeFixture("HourClock_proof", 6))).toBe(
      getCommands(readFileSync(join(DIRECTORY, "HourClock_proof-6.smt"), "utf8")),
    );
  });

  it("flattens functions and shares the ones with the same body", () => {
    expect(getCommands(encodeFixture("Simple_proof", 7))).toBe(
      getCommands(readFileSync(join(DIRECTORY, "Simple_proof-7.smt"), "utf8")),
    );
  });
});

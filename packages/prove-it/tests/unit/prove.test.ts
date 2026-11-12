import { afterEach, describe, expect, it } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { type ProofObligation, prove, type ProveOptions, TlaUnsupportedError } from "../../src";
import { getObligations } from "../../src/obligations";
import { encodeForBackend } from "../../src/prover/prove";
import { TLAPS_MODULE } from "../../src/prover/tlaps-module";

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

const encodeFixture = (name: string, id: number) => {
  const obligation = getObligations(
    [{ file: `${name}.tla`, source: loadModule(name) ?? "" }],
    (moduleName) => {
      const source = loadModule(moduleName) ?? (moduleName === "TLAPS" ? TLAPS_MODULE : undefined);
      return source === undefined ? undefined : { file: `${moduleName}.tla`, source };
    },
  )
    .flatMap((result) => result.obligations)
    .find((innerObligation) => innerObligation.id === id);
  if (!obligation) throw new Error(`no obligation ${id}`);
  return encodeForBackend(obligation, "smt", { caseErrors: 0 });
};

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

  // The module that defines the strings is one the Rust driver gives way to the TypeScript one for.
  it.each(["rust", "ts"])(
    "proves neither string = nor # the other where a module it extends defines them, with the %s driver",
    async (driver) => {
      const setting = process.env.PROVE_IT_PROVER_DRIVER;
      process.env.PROVE_IT_PROVER_DRIVER = driver;
      const library = '---- MODULE Lib ----\nC1 == "\uD800"\nC2 == "\uDC00"\n====\n';
      const results = await Promise.all(
        ["=", "#"].map((operator) =>
          prove({
            source: `---- MODULE M ----\nEXTENDS Lib, TLAPS\nTHEOREM C1 ${operator} C2 BY SMT DEF C1, C2\n====\n`,
            loadModule: (name) => (name === "Lib" ? library : undefined),
          }),
        ),
      ).finally(() => {
        if (setting === undefined) delete process.env.PROVE_IT_PROVER_DRIVER;
        else process.env.PROVE_IT_PROVER_DRIVER = setting;
      });
      for (const result of results)
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

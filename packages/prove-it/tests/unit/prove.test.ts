import { afterEach, describe, expect, it } from "bun:test";
import { chmodSync, existsSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { delimiter, join } from "node:path";

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
  // axiom that the two strings differ would contradict itself and prove both. The engine's strings
  // can't hold one, so prove declines the text that holds it before it decides anything.
  it.each(["=", "#"])(
    "proves neither string %s the other where each is a lone surrogate",
    async (operator) => {
      const proving = prove({
        source: `---- MODULE M ----\nEXTENDS TLAPS\nTHEOREM "\uD800" ${operator} "\uDC00" BY SMT\n====\n`,
      });
      await expect(proving).rejects.toThrow(
        new TlaUnsupportedError("not native yet: the source isn't well-formed UTF-16"),
      );
    },
  );

  it.each(["=", "#"])(
    "proves neither string %s the other where a module it extends defines them",
    async (operator) => {
      const library = '---- MODULE Lib ----\nC1 == "\uD800"\nC2 == "\uDC00"\n====\n';
      const proving = prove({
        source: `---- MODULE M ----\nEXTENDS Lib, TLAPS\nTHEOREM C1 ${operator} C2 BY SMT DEF C1, C2\n====\n`,
        loadModule: (name) => (name === "Lib" ? library : undefined),
      });
      await expect(proving).rejects.toThrow(
        new TlaUnsupportedError("not native yet: the module Lib isn't well-formed UTF-16"),
      );
    },
  );

  it("needs tlapm on the PATH for the tlapm backend", async () => {
    process.env.PATH = "";
    await expect(proveFixture("HourClock_proof", { backend: "tlapm" })).rejects.toThrow(
      TlaUnsupportedError,
    );
  });

  // A tlapm that proves the first obligation and fails the second, by its toolbox messages; the
  // obligations, their texts and the counts are the engine's.
  it("reads each obligation's status from tlapm with the tlapm backend", async () => {
    const bin = mkdtempSync(join(tmpdir(), "prove-it-tlapm-"));
    const message = (fields: string[]) =>
      `@!!BEGIN\n${fields.map((field) => `@!!${field}\n`).join("")}@!!END\n`;
    writeFileSync(
      join(bin, "tlapm"),
      `#!/bin/sh\ncat >&2 <<'END'\n${message(["type:obligation", "id:1", "status:proved", "prover:smt"])}${message(["type:obligation", "id:2", "status:failed", "reason:no"])}END\n`,
    );
    chmodSync(join(bin, "tlapm"), 0o755);
    process.env.PATH = `${bin}${delimiter}${PATH}`;
    const source =
      "---- MODULE M ----\nEXTENDS Naturals, TLAPS\nTHEOREM 1 + 1 = 2 BY SMT\nTHEOREM 2 = 2\nTHEOREM 3 = 3 OMITTED\n====\n";
    const reported: ProofObligation[] = [];
    const result = await prove({
      source,
      backend: "tlapm",
      onObligation: (obligation) => reported.push(obligation),
    });
    const native = await prove({ source });
    expect(result).toEqual({
      ...native,
      obligations: [
        { ...native.obligations[0], status: "proved", prover: "smt" },
        { ...native.obligations[1], status: "failed", reason: "no" },
        ...native.obligations.slice(2).map(({ id, location, text }) => ({
          id,
          location,
          text,
          status: "unsupported" as const,
          reason: "tlapm reported no result",
        })),
      ],
    });
    expect(reported).toEqual(result.obligations.slice(0, 2));
    expect(result.missingProofCount + result.omittedProofCount).toBe(2);
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

import { describe, expect, it } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { getObligationError, proveInRounds } from "../../scripts/native-prover";
import { getInputKey, getRecordedAnswer, readInputRecords } from "../../scripts/prover-records";
import { getDigest } from "../../scripts/tlapm-digest";
import { prove, type ProveOptions } from "../../src";
import {
  getNativeAddon,
  type NativeAddon,
  type NativeDecideRequest,
  type NativeProve,
} from "../../src/engine/native";
import { instantiateEngine } from "../../src/engine/wasm";

// The Rust driver proves as the TypeScript one did: the same obligations, statuses and reasons,
// the same reports in the same order, and the same errors, but where the TypeScript deviated from
// tlapm (design/prover.md). driver.json holds what the TypeScript driver gave on each case, by its
// name here.
const DIRECTORY = join(import.meta.dirname, "../fixtures/prove");

const EXPECTED: Record<string, unknown> = JSON.parse(
  readFileSync(join(DIRECTORY, "driver.json"), "utf8"),
);

const loadFixture = (name: string) => {
  const path = join(DIRECTORY, `${name}.tla`);
  return existsSync(path) ? readFileSync(path, "utf8") : undefined;
};

const getModule = (body: string, extended = "Naturals, TLAPS") =>
  `---- MODULE M ----\nEXTENDS ${extended}\n${body}\n====\n`;

type Answer = (request: NativeDecideRequest) => string;

// What the Rust driver reports when answer decides, and the error it throws after the reports
// before it.
const proveNatively = (
  name: string,
  source: string,
  answer: Answer,
  loadModule: (moduleName: string) => string | undefined = () => undefined,
) => {
  const result = proveInRounds(`${name}.tla`, source, loadModule, answer);
  if (result.kind === "proved")
    return {
      result: {
        obligations: result.reports,
        missingProofCount: result.missingProofCount,
        omittedProofCount: result.omittedProofCount,
      },
      streamed: result.reports,
    };
  const error = getObligationError(result);
  return {
    error: { class: error.constructor.name, name: error.name, message: error.message },
    streamed: result.reports ?? [],
  };
};

// What prove reports with the Rust driver and the native backends, as it reports each obligation
// and in the end, or the error it throws. It aborts once abortAfter obligations are reported.
const proveWithRust = async (options: ProveOptions, abortAfter?: number) => {
  const controller = new AbortController();
  const streamed: unknown[] = [];
  try {
    const result = await prove({
      ...options,
      signal: options.signal ?? (abortAfter === undefined ? undefined : controller.signal),
      onObligation: (obligation) => {
        streamed.push(obligation);
        if (streamed.length === abortAfter) controller.abort(new Error("stop"));
      },
    });
    return { result, streamed };
  } catch (error) {
    const thrown = error instanceof Error ? error : new Error(String(error));
    return {
      error: { class: thrown.constructor.name, name: thrown.name, message: thrown.message },
      streamed,
    };
  }
};

// Each prover's answer, or "throw" for a TlaProverError and "timeout" for an unknown at its limit.
const byProver =
  (answers: Record<string, string>): Answer =>
  (request) => {
    const answer = answers[request.prover] ?? "unsat";
    if (answer === "throw") return `error:${request.prover} stopped`;
    if (answer === "timeout") return `unknown ${request.timeLimitMs}`;
    return `${answer} 1`;
  };

describe("the Rust driver", () => {
  // Each decision is replayed from the record, which the backends' own tests keep true, as deciding
  // Simple's obligation 7 runs three backends to their limits (design/prover.md, "Deviations from
  // Z3").
  it.each(["HourClock", "Simple"])("proves %s as the TypeScript driver does", (name) => {
    const records = readInputRecords();
    const unrecorded: string[] = [];
    const replay: Answer = (request) => {
      const key = getInputKey(request.prover, getDigest(request.text));
      const record = records[key];
      if (record === undefined) unrecorded.push(key);
      return record === undefined ? "unknown 0" : getRecordedAnswer(record);
    };
    const run = proveNatively(name, loadFixture(name) ?? "", replay, loadFixture);
    expect<unknown>(unrecorded).toEqual([]);
    expect<unknown>(run).toEqual(EXPECTED[`proves ${name}`]);
  });

  // A run's cache is keyed by its source and modules, which a NUL mustn't run together.
  // The engine's strings can't hold a lone surrogate, and reading it as U+FFFD would prove
  // "\uD800" = "\uDC00", so the Rust driver declines before it decides anything.
  it("declines a source that isn't well-formed UTF-16", () => {
    const decided: string[] = [];
    const answer: Answer = (request) => {
      decided.push(request.text);
      return "unsat 1";
    };
    expect<unknown>(
      proveNatively("M", getModule('THEOREM "\uD800" = "\uDC00" BY SMT'), answer),
    ).toEqual({
      error: {
        class: "TlaUnsupportedError",
        name: "TlaUnsupportedError",
        message: "not native yet: the source isn't well-formed UTF-16",
      },
      streamed: [],
    });
    expect(decided).toEqual([]);
  });

  it("proves again when a loaded module changes, whatever the source holds", () => {
    const source = getModule("THEOREM X = 1 BY SMT DEF X", "Lib, TLAPS");
    const answer: Answer = (request) => (request.text.includes("2") ? "sat 1" : "unsat 1");
    const getLibrary = (value: number) => `---- MODULE Lib ----\nX == ${value}\n====\n`;
    expect<unknown>(
      proveNatively("M", source, answer, (name) => (name === "Lib" ? getLibrary(1) : undefined)),
    ).toEqual(EXPECTED["proves again: the first module"]);
    expect<unknown>(
      proveNatively(
        "M",
        `${source}\0module:Lib\0${getLibrary(1)}\0module:TLAPS\0`,
        answer,
        (name) => (name === "Lib" ? getLibrary(2) : undefined),
      ),
    ).toEqual(EXPECTED["proves again: the changed module"]);
  });

  // tlapm's assertion fails on the second theorem, after the first is reported.
  it("reports the obligations before a tlapm bug, and throws the bug", () => {
    expect<unknown>(
      proveNatively(
        "M",
        getModule("VARIABLE v\nTHEOREM 1 = 1 BY SMT\nTHEOREM ENABLED TRUE BY ExpandCdot, Zenon"),
        byProver({}),
      ),
    ).toEqual(EXPECTED["a tlapm bug"]);
  });

  it("throws tlapm's bug for a cycle of EXTENDS", () => {
    expect<unknown>(
      proveNatively("M", getModule("THEOREM 1 = 1", "Lib"), byProver({}), (name) =>
        name === "Lib" ? "---- MODULE Lib ----\nEXTENDS M\n====\n" : undefined,
      ),
    ).toEqual(EXPECTED["a cycle of EXTENDS"]);
  });

  // Each obligation decides its own texts, even one an earlier obligation sent the same backend.
  it("decides a text again for another obligation", () => {
    let calls = 0;
    expect<unknown>(
      proveNatively(
        "M",
        getModule(
          "THEOREM ASSUME NEW x \\in Nat PROVE x + 0 = x BY SMT, Zenon\nTHEOREM ASSUME NEW x \\in Nat PROVE x + 0 = x BY SMT",
        ),
        () => (calls++ % 3 === 0 ? "unknown 1" : "unsat 1"),
      ),
    ).toEqual(EXPECTED["a text again for another obligation"]);
  });

  it.each(["unsat", "sat", "unknown", "throw", "timeout"])(
    "proves as the TypeScript driver does when every backend answers %s",
    (answer) => {
      expect<unknown>(
        proveNatively(
          "M",
          getModule(
            "THEOREM 1 = 1 BY SMT\nTHEOREM 2 = 2 BY Zenon, SMT\nTHEOREM 3 = 3 BY Isa\nTHEOREM 1 = 1 BY SMT",
          ),
          byProver({ smt: answer, zenon: answer, isabelle: answer }),
        ),
      ).toEqual(EXPECTED[`every backend answers ${answer}`]);
    },
  );

  // The third method's prior has another tactic, so the TypeScript decides the text again.
  it("decides a text again for another method of the obligation", () => {
    let calls = 0;
    expect<unknown>(
      proveNatively(
        "M",
        getModule(
          'PA == TRUE (*{ by (prover:"isabelle"; tactic:"auto") }*)\nPI == TRUE (*{ by (prover:"isabelle"; tactic:"force") }*)\nTHEOREM 1 = 1 BY PA, PI, PA',
        ),
        () => (calls++ % 3 === 2 ? "unsat 1" : "unknown 1"),
      ),
    ).toEqual(EXPECTED["a text again for another method"]);
  });

  it("skips a method whose backend can't take the text", () => {
    expect<unknown>(
      proveNatively("M", getModule("THEOREM 1 = 1 BY SMT, Zenon"), (request) =>
        request.prover === "smt" ? "unsupported:thing" : "unsat 1",
      ),
    ).toEqual(EXPECTED["a method whose backend can't take the text"]);
  });

  // An INSTANCE that instantiates its own module again would recurse until the stack overflows.
  // The TypeScript overflows its stack here, where tlapm and the Rust report a bug in tlapm.
  it("throws tlapm's bug for an INSTANCE of a module inside itself", () => {
    const run = proveNatively(
      "M",
      "---- MODULE M ----\n---- MODULE Inner ----\nTHEOREM LET I == INSTANCE Inner IN TRUE\n====\nTHEOREM TRUE\n====\n",
      byProver({}),
    );
    expect<unknown>(run.error).toEqual({
      class: "TlapmBugError",
      name: "TlaProofError",
      message: "Oops, this seems to be a bug in TLAPM.",
    });
  });

  // TLA+ names that objects inherit, which neither driver takes for a builtin or a prover.
  it.each([
    ["an identifier", "CONSTANT toString\nTHEOREM toString = toString BY SMT"],
    ["a definition", "constructor == TRUE\nTHEOREM constructor BY Zenon DEF constructor"],
    ["a prover", 'Mine == TRUE (*{ by (prover:"toString") }*)\nTHEOREM 1 = 1 BY Mine'],
  ])("reads %s named like an object's property as tlapm does", (name, body) => {
    expect<unknown>(proveNatively("M", getModule(body, "TLAPS"), byProver({}))).toEqual(
      EXPECTED[`${name} named like an object's property`],
    );
  });

  // A pragma's string is what tlapm's lexer keeps, each escape as it is written (design/prover.md,
  // "TypeScript deviations"): a tactic reaches Isabelle so, and a prover is named so.
  it.each([
    ["an escape tlapm lacks", 'THEOREM 1 = 1\nOBVIOUS (*{ by (isabelle "\\q") }*)', "by \\q"],
    [
      "an escape of a lone surrogate",
      'F == TRUE (*{ by (prover:"isabelle"; tactic:"\\ud800") }*)\nTHEOREM 1 = 1 BY F',
      "by \\ud800",
    ],
  ])("reads a pragma's string with %s as tlapm does", (_name, body, tactic) => {
    const texts: string[] = [];
    const run = proveNatively("M", getModule(body), (request) => {
      texts.push(request.text);
      return "unsat 1";
    });
    expect(run.result?.obligations[0]).toMatchObject({ status: "proved", prover: "isabelle" });
    expect(texts.flatMap((text) => text.split("\n")).map((line) => line.trim())).toContain(tactic);
  });

  it("names a prover by a pragma's string as tlapm reads it", () => {
    const run = proveNatively(
      "M",
      getModule('F == TRUE (*{ by (prover:"\\uD800") }*)\nTHEOREM 1 = 1 BY F'),
      byProver({}),
    );
    expect(run.result?.obligations[0]).toMatchObject({
      status: "failed",
      reason: "Unknown prover: \\uD800",
    });
  });
});

// What prove does around the Rust driver: it reads the modules, decides with the native backends,
// reports each obligation as it settles and stops when its signal aborts.
describe("prove with the Rust driver", () => {
  it.each([1, 2])("stops after %i reports when the signal aborts", async (abortAfter) => {
    const source = getModule(
      [1, 2, 3, 4].map((value) => `THEOREM ${value} = ${value} BY CVC4`).join("\n"),
    );
    expect<unknown>(await proveWithRust({ source }, abortAfter)).toEqual(
      EXPECTED[`stops after ${abortAfter} reports`],
    );
  });

  it.each([
    ["no obligations", "A == 1"],
    ["a syntax error", "A == == 1"],
    ["obligations", "THEOREM 1 = 1 BY SMT"],
  ])("handles a signal aborted before it starts on %s", async (name, body) => {
    expect<unknown>(
      await proveWithRust({ source: getModule(body), signal: AbortSignal.abort(new Error("pre")) }),
    ).toEqual(EXPECTED[`a signal aborted before it starts on ${name}`]);
  });

  it("throws an abort before an obligation's error", async () => {
    expect<unknown>(
      await proveWithRust(
        {
          source: getModule(
            "VARIABLE v\nTHEOREM 1 = 1 BY SMT\nTHEOREM ENABLED TRUE BY ExpandCdot, Zenon",
          ),
        },
        2,
      ),
    ).toEqual(EXPECTED["an abort before an obligation's error"]);
    expect<unknown>(
      await proveWithRust({
        source: getModule("VARIABLE v\nTHEOREM ENABLED TRUE BY ExpandCdot, Zenon"),
        signal: AbortSignal.abort(new Error("pre")),
      }),
    ).toEqual(EXPECTED["an abort before it starts and an obligation's error"]);
  });

  it("loads a module two others extend once", async () => {
    const loads: string[] = [];
    await proveWithRust({
      source: getModule("THEOREM 1 = 1 BY SMT", "A, B, TLAPS"),
      loadModule: (name) => {
        loads.push(name);
        if (name === "A" || name === "B") return `---- MODULE ${name} ----\nEXTENDS C\n====\n`;
        return name === "C" ? "---- MODULE C ----\nZ == 1\n====\n" : undefined;
      },
    });
    expect<unknown>(loads).toEqual(EXPECTED["loads of a module two others extend"]);
  });

  // An abort on a timer lands between reports.
  it("stops when the signal aborts on a timer", async () => {
    const controller = new AbortController();
    setTimeout(() => controller.abort(new Error("timer")));
    expect<unknown>(
      await proveWithRust({
        source: getModule("THEOREM 1 = 1 BY Trivial\nTHEOREM 2 = 2 BY Trivial"),
        signal: controller.signal,
      }),
    ).toEqual(EXPECTED["the signal aborts on a timer"]);
  });

  // The TypeScript reads a module named like a standard one, or a missing one, again for each
  // module citing it, and stops at a module that doesn't parse.
  it.each([
    ["a standard module", "Naturals, Lib, TLAPS", { Lib: "EXTENDS Naturals\nX == 1" }],
    ["a missing module", "A2, B2, TLAPS", { A2: "EXTENDS X", B2: "EXTENDS X" }],
    ["a module that doesn't parse", "A, B, TLAPS", { A: "X == == 1", B: "Y == 1" }],
  ])("reads %s as the TypeScript driver does", async (name, extended, modules) => {
    const reads: string[] = [];
    const run = await proveWithRust({
      source: getModule("THEOREM 1 + 1 = 2 BY SMT", extended),
      loadModule: (moduleName) => {
        reads.push(moduleName);
        const body = (modules as Record<string, string>)[moduleName];
        return body === undefined ? undefined : `---- MODULE ${moduleName} ----\n${body}\n====\n`;
      },
    });
    expect<unknown>({ run, reads }).toEqual(EXPECTED[`reads ${name}`]);
  });

  // A loaded module is read as the source is, and each module is loaded once.
  it("declines a loaded module that isn't well-formed UTF-16", async () => {
    const loads: string[] = [];
    const run = (surrogate: string) =>
      proveWithRust({
        source: getModule("THEOREM X = Y BY SMT DEF X, Y", "Lib, TLAPS"),
        loadModule: (name) => {
          loads.push(name);
          if (name === "Lib") return '---- MODULE Lib ----\nEXTENDS Lib2\nX == "\uFFFD"\n====\n';
          if (name === "Lib2") return `---- MODULE Lib2 ----\nY == "${surrogate}"\n====`;
          return undefined;
        },
      });
    const wellFormed = await run("\uFFFD");
    expect(wellFormed.error).toBeUndefined();
    expect(wellFormed.result?.obligations[0]?.text).toContain('Y == "\uFFFD"');
    const wellFormedLoads = loads.splice(0);
    for (const surrogate of ["\uD800", "\uDFFF"]) {
      expect<unknown>(await run(surrogate)).toEqual({
        error: {
          class: "TlaUnsupportedError",
          name: "TlaUnsupportedError",
          message: "not native yet: the module Lib2 isn't well-formed UTF-16",
        },
        streamed: [],
      });
      expect(loads.splice(0)).toEqual(wellFormedLoads);
    }
  });

  it("proves with workers as the TypeScript driver does", async () => {
    const run = await proveWithRust({
      source: loadFixture("HourClock") ?? "",
      loadModule: loadFixture,
      workers: 2,
    });
    expect<unknown>(run.result).toEqual(EXPECTED["proves HourClock with workers"]);
  });
});

// Both bindings hand the engine a string's UTF-16 units, and the engine's prove declines a source or
// module with a lone surrogate before it decides anything.
describe("the engine's prove", () => {
  const WASM =
    process.env.PROVE_IT_ENGINE_WASM ??
    join(import.meta.dirname, "../../dist/prove-it-engine.wasm");
  const getAddon = () => {
    const addon = getNativeAddon();
    if (typeof addon === "string") throw new Error(addon);
    return addon;
  };

  // Proves in rounds, reading Lib from library and answering every decision unsat, and returns the
  // last round with the texts decided.
  const proveAll = (engine: NativeAddon, source: string, library: string) => {
    const known: [string, string | undefined][] = [];
    const texts: string[] = [];
    for (;;) {
      const result: NativeProve = engine.prove("M.tla", source, known);
      if (result.kind !== "needed") return { result, texts };
      for (const key of result.keys)
        known.push([key, key.startsWith("module:Lib#") ? library : undefined]);
      for (const request of result.requests) {
        texts.push(request.text);
        known.push([`decide:${request.key}`, "unsat 1"]);
      }
    }
  };

  const SOURCE = getModule(
    'THEOREM "\uFFFD" = Y BY SMT DEF Y\nTHEOREM X BY Zenon DEF X',
    "Lib, TLAPS",
  );
  const LIBRARY =
    '---- MODULE Lib ----\nX == "\uFFFD\uFFFD" = "\uFFFD\uFFFD"\nY == "\uFFFD"\n====\n';

  const expectDeclined = (engine: NativeAddon) => {
    const wellFormed = proveAll(engine, SOURCE, LIBRARY);
    expect(wellFormed.result.kind).toBe("proved");
    expect(wellFormed.texts.length).toBe(2);
    const getDeclined = (what: string) => ({
      result: {
        kind: "error" as const,
        name: "TlaUnsupportedError",
        message: `not native yet: ${what} isn't well-formed UTF-16`,
      },
      texts: [],
    });
    for (const surrogate of ["\uD800", "\uDC00", "\uDBFF", "\uDFFF"]) {
      expect(proveAll(engine, SOURCE.replaceAll("\uFFFD", surrogate), LIBRARY)).toEqual(
        getDeclined("the source"),
      );
      expect(proveAll(engine, SOURCE, LIBRARY.replaceAll("\uFFFD", surrogate))).toEqual(
        getDeclined("the module Lib"),
      );
    }
  };

  it("declines a lone surrogate through the addon", () => {
    expectDeclined(getAddon());
  });

  // The build has the engine once `platform-packages.ts build --target wasm32-unknown-unknown`
  // writes it.
  it.if(existsSync(WASM))("declines a lone surrogate through WebAssembly", () => {
    expectDeclined(instantiateEngine(new WebAssembly.Module(readFileSync(WASM))));
  });
});

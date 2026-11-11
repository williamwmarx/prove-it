import { describe, expect, it } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { prove } from "../../src";
import { SmtUnsupportedError, TlaProverError, TlaUnsupportedError } from "../../src/errors";
import { type ProveOptions, proveWith } from "../../src/prover/prove";
import type { Decision } from "../../src/prover/verdict";

// The Rust driver proves as the TypeScript one does: the same obligations, statuses and reasons,
// the same reports in the same order, and the same errors.
const DIRECTORY = join(import.meta.dirname, "../fixtures/prove");

const loadFixture = (name: string) => {
  const path = join(DIRECTORY, `${name}.tla`);
  return existsSync(path) ? readFileSync(path, "utf8") : undefined;
};

type Decide = (prover: string, text: string, options: { timeLimitMs: number }) => Promise<Decision>;

interface Run {
  options: ProveOptions;
  decide?: Decide;
  // Aborts the run once this many obligations are reported.
  abortAfter?: number;
}

const proveWithDriver = async (driver: string, run: Run) => {
  const setting = process.env.PROVE_IT_PROVER_DRIVER;
  process.env.PROVE_IT_PROVER_DRIVER = driver;
  const controller = new AbortController();
  const streamed: unknown[] = [];
  try {
    const result = await proveWith(
      {
        ...run.options,
        signal:
          run.options.signal ?? (run.abortAfter === undefined ? undefined : controller.signal),
        onObligation: (obligation) => {
          streamed.push(obligation);
          if (streamed.length === run.abortAfter) controller.abort(new Error("stop"));
        },
      },
      run.decide,
    );
    return { result, streamed };
  } catch (error) {
    const thrown = error instanceof Error ? error : new Error(String(error));
    return {
      error: { class: thrown.constructor.name, name: thrown.name, message: thrown.message },
      streamed,
    };
  } finally {
    if (setting === undefined) delete process.env.PROVE_IT_PROVER_DRIVER;
    else process.env.PROVE_IT_PROVER_DRIVER = setting;
  }
};

const expectSame = async (run: Run) => {
  const typescript = await proveWithDriver("ts", run);
  expect(await proveWithDriver("rust", run)).toEqual(typescript);
};

const getModule = (body: string, extended = "Naturals, TLAPS") =>
  `---- MODULE M ----\nEXTENDS ${extended}\n${body}\n====\n`;

// Each prover's answer, or "throw" for a TlaProverError and "timeout" for an unknown at its limit.
const byProver =
  (answers: Record<string, string>): Decide =>
  async (prover, _text, options) => {
    const answer = answers[prover] ?? "unsat";
    if (answer === "throw") throw new TlaProverError(`${prover} stopped`);
    if (answer === "timeout")
      return { verdict: "unknown", timeUsedMs: options.timeLimitMs, statistics: {} };
    return { verdict: answer as Decision["verdict"], timeUsedMs: 1, statistics: {} };
  };

describe("the Rust driver", () => {
  it.each(["HourClock", "Simple"])("proves %s as the TypeScript driver does", async (name) => {
    const typescript = await proveWithDriver("ts", {
      options: { source: loadFixture(name) ?? "", loadModule: loadFixture },
    });
    const rust = await proveWithDriver("rust", {
      options: { source: loadFixture(name) ?? "", loadModule: loadFixture },
    });
    expect(rust).toEqual(typescript);
    expect(rust.streamed).toEqual(typescript.result?.obligations ?? []);
  });

  // A lone surrogate, which a Rust string can't hold, would read as U+FFFD, and "\uD800" =
  // "\uDC00" would be proved.
  it("proves a module that isn't well-formed UTF-16 as the TypeScript driver does", async () => {
    await expectSame({
      options: { source: getModule('THEOREM "\uD800" = "\uDC00" BY SMT') },
      decide: async (_prover, text) => ({
        verdict: text.includes("�") ? "unsat" : "unknown",
        timeUsedMs: 1,
        statistics: {},
      }),
    });
  });

  // A run's cache is keyed by its source and modules, which a NUL mustn't run together.
  it("proves again when a loaded module changes, whatever the source holds", async () => {
    const source = getModule("THEOREM X = 1 BY SMT DEF X", "Lib, TLAPS");
    const decide: Decide = async (_prover, text) => ({
      verdict: text.includes("2") ? "sat" : "unsat",
      timeUsedMs: 1,
      statistics: {},
    });
    const getLibrary = (value: number) => `---- MODULE Lib ----\nX == ${value}\n====\n`;
    await expectSame({
      options: { source, loadModule: (name) => (name === "Lib" ? getLibrary(1) : undefined) },
      decide,
    });
    await expectSame({
      options: {
        source: `${source}\0module:Lib\0${getLibrary(1)}\0module:TLAPS\0`,
        loadModule: (name) => (name === "Lib" ? getLibrary(2) : undefined),
      },
      decide,
    });
  });

  // tlapm's assertion fails on the second theorem, after the first is reported.
  it("reports the obligations before a tlapm bug, and throws the bug", async () => {
    await expectSame({
      options: {
        source: getModule(
          "VARIABLE v\nTHEOREM 1 = 1 BY SMT\nTHEOREM ENABLED TRUE BY ExpandCdot, Zenon",
        ),
      },
      decide: byProver({}),
    });
  });

  it("throws tlapm's bug for a cycle of EXTENDS", async () => {
    await expectSame({
      options: {
        source: getModule("THEOREM 1 = 1", "Lib"),
        loadModule: (name) =>
          name === "Lib" ? "---- MODULE Lib ----\nEXTENDS M\n====\n" : undefined,
      },
      decide: byProver({}),
    });
  });

  it.each([1, 2])("stops after %i reports when the signal aborts", async (abortAfter) => {
    await expectSame({
      options: {
        source: getModule(
          [1, 2, 3, 4].map((value) => `THEOREM ${value} = ${value} BY CVC4`).join("\n"),
        ),
      },
      abortAfter,
    });
  });

  it.each([
    ["no obligations", "A == 1"],
    ["a syntax error", "A == == 1"],
    ["obligations", "THEOREM 1 = 1 BY SMT"],
  ])("handles a signal aborted before it starts on %s", async (_name, body) => {
    await expectSame({
      options: { source: getModule(body), signal: AbortSignal.abort(new Error("pre")) },
      decide: byProver({}),
    });
  });

  // Each obligation decides its own texts, even one an earlier obligation sent the same backend.
  it("decides a text again for another obligation", async () => {
    let calls = 0;
    await expectSame({
      options: {
        source: getModule(
          "THEOREM ASSUME NEW x \\in Nat PROVE x + 0 = x BY SMT, Zenon\nTHEOREM ASSUME NEW x \\in Nat PROVE x + 0 = x BY SMT",
        ),
      },
      decide: async () => ({
        verdict: calls++ % 3 === 0 ? "unknown" : "unsat",
        timeUsedMs: 1,
        statistics: {},
      }),
    });
  });

  it.each(["unsat", "sat", "unknown", "throw", "timeout"])(
    "proves as the TypeScript driver does when every backend answers %s",
    async (answer) => {
      await expectSame({
        options: {
          source: getModule(
            "THEOREM 1 = 1 BY SMT\nTHEOREM 2 = 2 BY Zenon, SMT\nTHEOREM 3 = 3 BY Isa\nTHEOREM 1 = 1 BY SMT",
          ),
        },
        decide: byProver({ smt: answer, zenon: answer, isabelle: answer }),
      });
    },
  );

  // The Rust driver reads only the verdicts it knows, and fails rather than ask again.
  it("fails on an answer it can't read", async () => {
    const run = await proveWithDriver("rust", {
      options: { source: getModule("THEOREM 1 = 1 BY SMT") },
      decide: async () => ({
        verdict: "error" as Decision["verdict"],
        timeUsedMs: 1,
        statistics: {},
      }),
    });
    expect(run.error?.class).toBe("EngineInvariantError");
  });

  // An earlier obligation's decision comes first, as the TypeScript decides in turn: here it
  // throws, and then it proves, so the later obligation's error is the one thrown.
  it.each(["boom1", "unsat"])(
    "throws a decision's error in the order of the obligations when the earlier one answers %s",
    async (earlier) => {
      await expectSame({
        options: { source: getModule("THEOREM 1 = 1 BY Zenon, SMT\nTHEOREM 2 = 2 BY SMT") },
        decide: async (prover, text) => {
          if (prover === "zenon") return { verdict: "unknown", timeUsedMs: 1, statistics: {} };
          if (text.includes("Int 2")) throw new SmtUnsupportedError("boom2");
          if (earlier !== "unsat") throw new SmtUnsupportedError(earlier);
          return { verdict: "unsat", timeUsedMs: 1, statistics: {} };
        },
      });
    },
  );

  it("throws an abort before an obligation's error", async () => {
    await expectSame({
      options: {
        source: getModule(
          "VARIABLE v\nTHEOREM 1 = 1 BY SMT\nTHEOREM ENABLED TRUE BY ExpandCdot, Zenon",
        ),
      },
      decide: byProver({}),
      abortAfter: 2,
    });
    await expectSame({
      options: {
        source: getModule("VARIABLE v\nTHEOREM ENABLED TRUE BY ExpandCdot, Zenon"),
        signal: AbortSignal.abort(new Error("pre")),
      },
      decide: byProver({}),
    });
  });

  // The third method's prior has another tactic, so the TypeScript decides the text again.
  it("decides a text again for another method of the obligation", async () => {
    let calls = 0;
    await expectSame({
      options: {
        source: getModule(
          'PA == TRUE (*{ by (prover:"isabelle"; tactic:"auto") }*)\nPI == TRUE (*{ by (prover:"isabelle"; tactic:"force") }*)\nTHEOREM 1 = 1 BY PA, PI, PA',
        ),
      },
      decide: async () => ({
        verdict: calls++ % 3 === 2 ? "unsat" : "unknown",
        timeUsedMs: 1,
        statistics: {},
      }),
    });
  });

  // The Rust driver gives way on the module that isn't well-formed, after loading the others.
  it("loads each module once when it gives way to the TypeScript driver", async () => {
    const loads: string[] = [];
    let count = 0;
    const run = (driver: string) =>
      proveWithDriver(driver, {
        options: {
          source: getModule("THEOREM X = 1 BY SMT DEF X", "Lib, TLAPS"),
          loadModule: (name) => {
            loads.push(name);
            if (name === "Lib")
              return `---- MODULE Lib ----\nEXTENDS Lib2\nX == ${++count}\n====\n`;
            if (name === "Lib2") return '---- MODULE Lib2 ----\nY == "\uD800"\n====';
            return undefined;
          },
        },
        decide: async (_prover, text) => ({
          verdict: text.includes("2") ? "sat" : "unsat",
          timeUsedMs: 1,
          statistics: {},
        }),
      });
    const typescript = await run("ts");
    const typescriptLoads = loads.splice(0);
    count = 0;
    expect(await run("rust")).toEqual(typescript);
    expect(loads).toEqual(typescriptLoads);
  });

  it("skips a method whose backend can't take the text", async () => {
    await expectSame({
      options: { source: getModule("THEOREM 1 = 1 BY SMT, Zenon") },
      decide: async (prover) => {
        if (prover === "smt") throw new TlaUnsupportedError("thing");
        return { verdict: "unsat", timeUsedMs: 1, statistics: {} };
      },
    });
  });

  it("throws an abort before a decision's error", async () => {
    await expectSame({
      options: { source: getModule("THEOREM 1 + 1 = 2 BY SMT\nTHEOREM 2 + 2 = 4 BY Zenon") },
      decide: async (prover) => {
        if (prover === "zenon") throw new Error("fatal zenon");
        return { verdict: "unsat", timeUsedMs: 1, statistics: {} };
      },
      abortAfter: 2,
    });
  });

  it("reads a decide that throws at once as one that rejects", async () => {
    await expectSame({
      options: { source: getModule("THEOREM 1 + 1 = 2 BY SMT, Zenon") },
      decide: (prover) => {
        if (prover === "smt") throw new TlaProverError("at once");
        return Promise.resolve({ verdict: "unsat", timeUsedMs: 1, statistics: {} });
      },
    });
  });

  it("loads a module two others extend once", async () => {
    const getLoads = async (driver: string) => {
      const loads: string[] = [];
      await proveWithDriver(driver, {
        options: {
          source: getModule("THEOREM 1 = 1 BY SMT", "A, B, TLAPS"),
          loadModule: (name) => {
            loads.push(name);
            if (name === "A" || name === "B") return `---- MODULE ${name} ----\nEXTENDS C\n====\n`;
            return name === "C" ? "---- MODULE C ----\nZ == 1\n====\n" : undefined;
          },
        },
        decide: byProver({}),
      });
      return loads;
    };
    expect(await getLoads("rust")).toEqual(await getLoads("ts"));
  });

  // An abort on a timer lands between reports.
  it("stops when the signal aborts on a timer", async () => {
    const run = async (driver: string) => {
      const controller = new AbortController();
      setTimeout(() => controller.abort(new Error("timer")));
      return proveWithDriver(driver, {
        options: {
          source: getModule("THEOREM 1 = 1 BY Trivial\nTHEOREM 2 = 2 BY Trivial"),
          signal: controller.signal,
        },
        decide: byProver({}),
      });
    };
    expect(await run("rust")).toEqual(await run("ts"));
  });

  // The TypeScript reads a module named like a standard one, or a missing one, again for each
  // module citing it, and stops at a module that doesn't parse.
  it.each([
    ["a standard module", "Naturals, Lib, TLAPS", { Lib: "EXTENDS Naturals\nX == 1" }],
    ["a missing module", "A2, B2, TLAPS", { A2: "EXTENDS X", B2: "EXTENDS X" }],
    ["a module that doesn't parse", "A, B, TLAPS", { A: "X == == 1", B: "Y == 1" }],
  ])("reads %s as the TypeScript driver does", async (_name, extended, modules) => {
    const getReads = async (driver: string) => {
      const reads: string[] = [];
      const run = await proveWithDriver(driver, {
        options: {
          source: getModule("THEOREM 1 + 1 = 2 BY SMT", extended),
          loadModule: (name) => {
            reads.push(name);
            const body = (modules as Record<string, string>)[name];
            return body === undefined ? undefined : `---- MODULE ${name} ----\n${body}\n====\n`;
          },
        },
        decide: byProver({}),
      });
      return { run, reads };
    };
    expect(await getReads("rust")).toEqual(await getReads("ts"));
  });

  it("proves with workers as the TypeScript driver does", async () => {
    const source = loadFixture("HourClock") ?? "";
    const setting = process.env.PROVE_IT_PROVER_DRIVER;
    try {
      process.env.PROVE_IT_PROVER_DRIVER = "ts";
      const typescript = await prove({ source, loadModule: loadFixture, workers: 2 });
      process.env.PROVE_IT_PROVER_DRIVER = "rust";
      expect(await prove({ source, loadModule: loadFixture, workers: 2 })).toEqual(typescript);
    } finally {
      if (setting === undefined) delete process.env.PROVE_IT_PROVER_DRIVER;
      else process.env.PROVE_IT_PROVER_DRIVER = setting;
    }
  });
});

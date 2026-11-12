import { afterAll, describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import {
  cpSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  realpathSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

import { getSteadyLines } from "../../scripts/normalize-output";
import { readMarshaled } from "../../src/prover/tlapm/ocaml-marshal";

const FIXTURES = join(import.meta.dirname, "../fixtures");

const CLI = join(import.meta.dirname, "../../src/cli.ts");

const runCliWith = (directory: string, args: string[], env?: Record<string, string>) =>
  spawnSync("bun", [CLI, ...args], {
    cwd: join(FIXTURES, directory),
    encoding: "utf8",
    env: env && { ...process.env, ...env },
  });

const copies: string[] = [];

afterAll(() => copies.forEach((copy) => rmSync(copy, { recursive: true, force: true })));

// tlapm keeps its cache in the directory it runs in, so each run works in a copy of the fixtures.
const copyFixtures = (directory: string) => {
  const copy = mkdtempSync(join(tmpdir(), "tla-ts-tlapm-"));
  copies.push(copy);
  cpSync(join(FIXTURES, directory), copy, { recursive: true });
  return copy;
};

const runTlapmIn = (directory: string, args: string[]) =>
  spawnSync("bun", [CLI, "tlapm", ...args], { cwd: directory, encoding: "utf8" });

const runTlapm = (directory: string, args: string[]) => runTlapmIn(copyFixtures(directory), args);

const runCli = (directory: string, name: string, args: string[] = []) =>
  runCliWith(directory, [`${name}.tla`, ...args]);

const getCheckedSpecs = (output: string) =>
  output.split("\n").filter((line) => /^Checking \S+\.tla with /.test(line));

const getStateLines = (output: string) =>
  output.split("\n").filter((line) => line.includes(" = ") && !line.startsWith("State"));

describe("the CLI prints traces like TLC", () => {
  it("prints a state with one variable without a conjunction", () => {
    const result = runCli("counter", "Counter");
    expect(result.status).toBe(11);
    expect(getStateLines(result.stdout)).toEqual([
      "count = 0",
      "count = 1",
      "count = 2",
      "count = 3",
    ]);
  });

  it("prints a state with several variables as a conjunction", () => {
    const result = runCli("water-jugs", "WaterJugs");
    expect(result.status).toBe(12);
    expect(getStateLines(result.stdout).slice(0, 2)).toEqual(["/\\ large = 0", "/\\ small = 0"]);
  });
});

const TLC_REPORTS = [
  [
    "AssumptionFalse",
    10,
    [
      "Starting... (_)",
      "Error: Assumption line 4, col 20 to line 4, col 24 of module AssumptionFalse is false.",
      "Finished in _ at (_)",
    ],
  ],
  [
    "Success",
    0,
    [
      "Starting... (_)",
      "Computing initial states...",
      "Finished computing initial states: 2 distinct states generated at _.",
      "Model checking completed. No error has been found.",
      "  Estimates of the probability that TLC did not check all reachable states",
      "  because two distinct states had the same fingerprint:",
      "  calculated (optimistic):  val = 1.3E-18",
      "10 states generated, 6 distinct states found, 0 states left on queue.",
      "The depth of the complete state graph search is 3.",
      "The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 1 and the 95th percentile is 1).",
      "Finished in _ at (_)",
    ],
  ],
  [
    "InitialInvariant",
    12,
    [
      "Starting... (_)",
      "Computing initial states...",
      "Error: Invariant Inv is violated by the initial state:",
      "x = 0",
      "",
      "Finished in _ at (_)",
    ],
  ],
  [
    "Lasso",
    13,
    [
      "Starting... (_)",
      "Implied-temporal checking--satisfiability problem has 1 branches.",
      "Computing initial states...",
      "Finished computing initial states: 1 distinct state generated at _.",
      "Progress(2) at _: 3 states generated, 2 distinct states found, 0 states left on queue.",
      "Checking temporal properties for the complete state space with 2 total distinct states at (_)",
      "Error: Temporal property Prop was violated.",
      "",
      "Error: The following behavior constitutes a counter-example:",
      "",
      "State 1: <Initial predicate>",
      "x = 0",
      "",
      "State 2: <Next line 5, col 9 to line 5, col 18 of module Lasso>",
      "x = 1",
      "",
      "Back to state 1: <Next line 5, col 9 to line 5, col 18 of module Lasso>",
      "",
      "Finished checking temporal properties in _ at _",
      "3 states generated, 2 distinct states found, 0 states left on queue.",
      "The depth of the complete state graph search is 2.",
      "Finished in _ at (_)",
    ],
  ],
  [
    "Lassos",
    13,
    [
      "Starting... (_)",
      "Implied-temporal checking--satisfiability problem has 2 branches.",
      "Computing initial states...",
      "Finished computing initial states: 1 distinct state generated at _.",
      "Progress(3) at _: 4 states generated, 3 distinct states found, 0 states left on queue.",
      "Checking 2 branches of temporal properties for the complete state space with 6 total distinct states at (_)",
      "Error: Temporal properties Reach, Settle, and Stop were violated.",
      "",
      "Error: The following behavior constitutes a counter-example:",
      "",
      "State 1: <Initial predicate>",
      "x = 0",
      "",
      "State 2: <Next line 5, col 9 to line 5, col 24 of module Lassos>",
      "x = 1",
      "",
      "State 3: <Next line 5, col 9 to line 5, col 24 of module Lassos>",
      "x = 2",
      "",
      "Back to state 1: <Next line 5, col 9 to line 5, col 24 of module Lassos>",
      "",
      "Finished checking temporal properties in _ at _",
      "4 states generated, 3 distinct states found, 0 states left on queue.",
      "The depth of the complete state graph search is 3.",
      "Finished in _ at (_)",
    ],
  ],
  [
    "SafetyProperty",
    12,
    [
      "Starting... (_)",
      "Implied-temporal checking--satisfiability problem has 1 branches.",
      "Computing initial states...",
      "Finished computing initial states: 1 distinct state generated at _.",
      "Error: Temporal property Bounded was violated.",
      "",
      "Error: The following behavior constitutes a counter-example:",
      "",
      "State 1: <Initial predicate>",
      "x = 0",
      "",
      "State 2: <Next line 5, col 9 to line 5, col 27 of module SafetyProperty>",
      "x = 1",
      "",
      "3 states generated, 3 distinct states found, 1 states left on queue.",
      "The depth of the complete state graph search is 3.",
      "Finished in _ at (_)",
    ],
  ],
  [
    "FailedInvariant",
    76,
    [
      "Starting... (_)",
      "Computing initial states...",
      "Finished computing initial states: 1 distinct state generated at _.",
      "Error: Evaluating invariant Inv failed.",
      "The second argument of \\div is 0.",
      "Error: The behavior up to this point is:",
      "State 1: <Initial predicate>",
      "x = 0",
      "",
      "State 2: <Next line 5, col 9 to line 5, col 27 of module FailedInvariant>",
      "x = 1",
      "",
      "State 3: <Next line 5, col 9 to line 5, col 27 of module FailedInvariant>",
      "x = 2",
      "",
      "3 states generated, 3 distinct states found, 0 states left on queue.",
      "The depth of the complete state graph search is 3.",
      "The average outdegree of the complete state graph is 1 (minimum is 1, the maximum 1 and the 95th percentile is 1).",
      "Finished in _ at (_)",
    ],
  ],
  [
    "EventualAction",
    255,
    [
      "Starting... (_)",
      "Warning: Declaring symmetry during liveness checking is dangerous. It might cause TLC to miss violations of the stated liveness properties. Please check liveness without symmetry defined.",
      "(Use the -nowarning option to disable this warning.)",
      "Error: Temporal formulas containing actions must be of forms <>[]A or []<>A.",
      "Finished in _ at (_)",
    ],
  ],
  [
    "NoNext",
    75,
    [
      "Starting... (_)",
      "Computing initial states...",
      "Finished computing initial states: 1 distinct state generated at _.",
      "Error: No next state actions defined to generate successor states from.",
      "Finished in _ at (_)",
    ],
  ],
  [
    "FailedAssert",
    14,
    [
      "Starting... (_)",
      "Computing initial states...",
      "Finished computing initial states: 1 distinct state generated at _.",
      "Error: The first argument of Assert evaluated to FALSE; the second argument was:",
      '"x is 1"',
      "Error: The behavior up to this point is:",
      "State 1: <Initial predicate>",
      "x = 0",
      "",
      "State 2: <Next line 6, col 5 to line 7, col 30 of module FailedAssert>",
      "x = 1",
      "",
      "Error: The error occurred when TLC was evaluating the nested",
      "expressions at the following positions:",
      "0. Line 6, column 5 to line 7, column 30 in FailedAssert",
      "1. Line 6, column 8 to line 6, column 17 in FailedAssert",
      "2. Line 7, column 8 to line 7, column 30 in FailedAssert",
      "",
      "",
      "2 states generated, 2 distinct states found, 0 states left on queue.",
      "The depth of the complete state graph search is 2.",
      "Finished in _ at (_)",
    ],
  ],
  [
    "FailedInitialInvariant",
    75,
    [
      "Starting... (_)",
      "Computing initial states...",
      "Error: The first argument of Assert evaluated to FALSE; the second argument was:",
      '"a is 1"',
      "Error: The error occurred when TLC was evaluating the nested",
      "expressions at the following positions:",
      "0. Line 5, column 5 to line 6, column 15 in FailedInitialInvariant",
      "1. Line 5, column 8 to line 5, column 17 in FailedInitialInvariant",
      "2. Line 6, column 8 to line 6, column 15 in FailedInitialInvariant",
      "3. Line 8, column 8 to line 8, column 30 in FailedInitialInvariant",
      "",
      "",
      "1 states generated, 1 distinct states found, 1 states left on queue.",
      "The depth of the complete state graph search is 1.",
      "Finished in _ at (_)",
    ],
  ],
  [
    "IllegalInitialState",
    255,
    [
      "Starting... (_)",
      "Computing initial states...",
      "Error: current state is not a legal state",
      "While working on the initial state:",
      "/\\ x = 1",
      "/\\ y = null",
      "",
      "Finished in _ at (_)",
    ],
  ],
  [
    "LivenessError",
    255,
    [
      "Starting... (_)",
      "Implied-temporal checking--satisfiability problem has 1 branches.",
      "Computing initial states...",
      "Finished computing initial states: 1 distinct state generated at _.",
      "Error: The error occurred when TLC was evaluating the nested",
      "expressions at the following positions:",
      "0. Line 9, column 14 to line 9, column 22 in LivenessError",
      "",
      "",
      "Error: TLC threw an unexpected exception.",
      "This was probably caused by an error in the spec or model.",
      "See the User Output or TLC Console for clues to what happened.",
      "The exception was a java.lang.RuntimeException",
      ": Attempted to check equality of integer 0 with non-integer:",
      '"abc"',
      "Error: The behavior up to this point is:",
      "State 1: <Initial predicate>",
      "/\\ x = 0",
      "/\\ y = 0",
      "",
      "2 states generated, 2 distinct states found, 1 states left on queue.",
      "The depth of the complete state graph search is 2.",
      "The average outdegree of the complete state graph is 1 (minimum is 1, the maximum 1 and the 95th percentile is 1).",
      "Finished in _ at (_)",
    ],
  ],
  [
    "Undefined",
    150,
    [
      "*** Warnings: 1",
      "",
      "line 5, col 17 to line 5, col 20 of module Undefined",
      "",
      "Multiple declarations or definitions for symbol F.  ",
      "This duplicates the one at line 5, col 11 to line 5, col 14 of module Undefined.",
      "",
      "",
      "",
      "Semantic errors:",
      "",
      "*** Errors: 2",
      "",
      "line 5, col 11 to line 5, col 14 of module Undefined",
      "",
      "Symbol F declared in RECURSIVE statement but not defined.",
      "",
      "",
      "line 5, col 17 to line 5, col 20 of module Undefined",
      "",
      "Symbol F declared in RECURSIVE statement but not defined.",
      "",
      "",
      "Starting... (_)",
      "Error: Parsing or semantic analysis failed.",
      "Finished in _ at (_)",
    ],
  ],
  [
    "UnfingerprintedEquality",
    75,
    [
      "Starting... (_)",
      "Computing initial states...",
      "Finished computing initial states: 1 distinct state generated at _.",
      "Error: TLC threw an unexpected exception.",
      "This was probably caused by an error in the spec or model.",
      "See the User Output or TLC Console for clues to what happened.",
      "The exception was a java.lang.RuntimeException",
      ": Attempted to check equality of the set {1, 2} with the value:",
      "0",
      "Error: The behavior up to this point is:",
      "State 1: <Initial predicate>",
      "x = 0",
      "",
      "Error: TLC was unable to fingerprint.",
      "",
      "Fingerprint Stack Trace:",
      "0. Line 6, column 5 to line 7, column 43 in UnfingerprintedEquality",
      "1. Line 6, column 8 to line 6, column 12 in UnfingerprintedEquality",
      "2. Line 7, column 8 to line 7, column 43 in UnfingerprintedEquality",
      "3. Line 7, column 13 to line 7, column 43 in UnfingerprintedEquality",
      "4. Line 7, column 16 to line 7, column 25 in UnfingerprintedEquality",
      "5. Line 7, column 16 to line 7, column 21 in UnfingerprintedEquality",
      "",
      "",
      "Reason:",
      "Attempted to check equality of the set {1, 2} with the value:",
      "0",
      "1 states generated, 1 distinct states found, 0 states left on queue.",
      "The depth of the complete state graph search is 1.",
      "Finished in _ at (_)",
    ],
  ],
  [
    "UnfingerprintedState",
    75,
    [
      "Starting... (_)",
      "Computing initial states...",
      "Error: Overflow when computing the number of elements in:",
      "SUBSET (1..36)",
      "While working on the initial state:",
      "x = SUBSET SUBSET (1..36)",
      "",
      "Error: TLC was unable to fingerprint.",
      "",
      "Fingerprint Stack Trace:",
      "1) line 4, col 20 to line 4, col 33 of module UnfingerprintedState",
      "0) line 4, col 13 to line 4, col 33 of module UnfingerprintedState",
      "",
      "Reason:",
      "Overflow when computing the number of elements in:",
      "SUBSET (1..36)",
      "1 states generated, 0 distinct states found, 0 states left on queue.",
      "The depth of the complete state graph search is 1.",
      "Finished in _ at (_)",
    ],
  ],
  [
    "UnspecifiedFairness",
    255,
    [
      "Starting... (_)",
      "Implied-temporal checking--satisfiability problem has 1 branches.",
      "Computing initial states...",
      "Finished computing initial states: 1 distinct state generated at _.",
      "Error: The error occurred when TLC was evaluating the nested",
      "expressions at the following positions:",
      "0. Line 9, column 14 to line 9, column 18 in UnspecifiedFairness",
      "1. Line 7, column 10 to line 7, column 15 in UnspecifiedFairness",
      "2. Line 9, column 12 to line 9, column 12 in UnspecifiedFairness",
      "",
      "",
      "Error: TLC threw an unexpected exception.",
      "This was probably caused by an error in the spec or model.",
      "See the User Output or TLC Console for clues to what happened.",
      "The exception was a java.lang.RuntimeException",
      ": The action formula A appearing in a WF_v(A) or SF_v(A) operator does not specify the primed value of the variable y occurring in the state formula v.",
      "",
      "Error: The behavior up to this point is:",
      "State 1: <Initial predicate>",
      "/\\ x = 0",
      "/\\ y = 0",
      "",
      "2 states generated, 2 distinct states found, 1 states left on queue.",
      "The depth of the complete state graph search is 2.",
      "The average outdegree of the complete state graph is 1 (minimum is 1, the maximum 1 and the 95th percentile is 1).",
      "Finished in _ at (_)",
    ],
  ],
  [
    "Warned",
    0,
    [
      "*** Warnings: 1",
      "",
      "line 14, col 1 to line 14, col 16 of module Naturals",
      "",
      "Multiple declarations or definitions for symbol Nat.  ",
      "This duplicates the one at line 3, col 1 to line 3, col 10 of module Warned.",
      "",
      "",
      "",
      "Starting... (_)",
      "Computing initial states...",
      "Finished computing initial states: 1 distinct state generated at _.",
      "Model checking completed. No error has been found.",
      "  Estimates of the probability that TLC did not check all reachable states",
      "  because two distinct states had the same fingerprint:",
      "  calculated (optimistic):  val = 5.4E-20",
      "2 states generated, 1 distinct states found, 0 states left on queue.",
      "The depth of the complete state graph search is 1.",
      "The average outdegree of the complete state graph is 0 (minimum is 0, the maximum 0 and the 95th percentile is 0).",
      "Finished in _ at (_)",
    ],
  ],
] as const;

describe("the CLI reports results like TLC", () => {
  it.each(TLC_REPORTS)("reports %s", (name, code, lines) => {
    const result = runCli("cli-output", name);
    expect(result.status).toBe(code);
    expect(getSteadyLines(result.stdout)).toEqual([...lines, ""]);
  });

  it("names no temporal property when the counterexample a VIEW merges satisfies them all", () => {
    const result = runCli("cli-output", "ViewLasso");
    expect(result.status).toBe(13);
    expect(result.stdout).toContain("Error: Temporal properties were violated.\n");
  });

  it("checks liveness on the complete state graph with -lncheck final", () => {
    const [, code, lines] = TLC_REPORTS.find((report) => report[0] === "Lasso") ?? [];
    const result = runCli("cli-output", "Lasso", ["-lncheck", "final"]);
    expect(result.status).toBe<number | undefined>(code);
    expect(getSteadyLines(result.stdout)).toEqual([...(lines ?? []), ""]);
  });

  // TLC's output with one worker for the specs of its ContinueTest and
  // DoInitFunctorInvariantContinueTest, and for a spec whose violating states lead to more.
  it.each(["Continue", "DoInitFunctorInvariantContinue", "ContinueSuccessors"])(
    "goes on past each violation in %s with -continue like TLC",
    (name) => {
      const result = runCliWith("tlc-continue", [`${name}.tla`, "-continue"]);
      expect(result.status).toBe(0);
      expect(getSteadyLines(result.stdout)).toEqual(
        readFileSync(join(FIXTURES, "tlc-continue", `${name}.out`), "utf8").split("\n"),
      );
    },
  );

  // TLC prints its dates in the local time zone, which TZ names.
  it.each([
    "UTC",
    "Etc/UCT",
    ":Etc/UTC",
    "Asia/Kolkata",
    "America/Los_Angeles",
    "Pacific/Kiritimati",
  ])("prints its dates in the time zone %s", (timeZone) => {
    const format = new Intl.DateTimeFormat("sv-SE", {
      timeZone: timeZone.replace(/^:/, ""),
      dateStyle: "short",
      timeStyle: "medium",
    });
    const before = format.format(new Date());
    const result = runCliWith("cli-output", ["Success.tla"], { TZ: timeZone });
    const after = format.format(new Date());
    expect(result.status).toBe(0);
    const finished = result.stdout.match(/^Finished in .+ at \((.+)\)$/m)?.[1] ?? "";
    // The run may cross into the next second or minute.
    expect([before, finished, after].toSorted()).toEqual([before, finished, after]);
  });

  it("rejects a spec whose file name differs from its module name like TLC", () => {
    const result = runCli("cli-module-name", "Renamed");
    const reason =
      "File name 'Renamed' does not match the name 'Other' of the top level module it contains.";
    expect(result.status).toBe(150);
    expect(getSteadyLines(result.stdout)).toEqual([
      "",
      "Fatal errors while parsing TLA+ spec in file Renamed",
      "",
      "Unknown location",
      "",
      reason,
      "*** Errors: 1",
      "",
      "Unknown location",
      "",
      reason,
      "",
      "",
      "",
      "Starting... (_)",
      "Error: Parsing or semantic analysis failed.",
      "Finished in _ at (_)",
      "",
    ]);
  });

  it("rejects a spec whose file name differs from its module name like TLC 1.7.4", () => {
    const result = runCliWith("cli-module-name", ["-Dtla-ts.tlc=1.7.4", "tlc2.TLC", "Renamed"]);
    expect(result.status).toBe(150);
    expect(getSteadyLines(result.stdout)).toEqual([
      "",
      "Fatal errors while parsing TLA+ spec in file Renamed",
      "",
      "tla2sany.semantic.AbortException",
      "*** Abort messages: 1",
      "",
      "Unknown location",
      "",
      "File name 'Renamed' does not match the name 'Other' of the top level module it contains.",
      "",
      "",
      "Starting... (_)",
      "Error: Parsing or semantic analysis failed.",
      "Finished in _ at (_)",
      "",
    ]);
  });

  it("prints SANY's message for an extended module it cannot parse like TLC", () => {
    const result = runCli("cli-parse-error", "Root");
    expect(result.status).toBe(150);
    expect(result.stdout.replace(/\(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d\)/g, "(DATE)")).toContain(
      [
        "***Parse Error***",
        'Encountered "]" at line 2, column 24 and token "|->" ',
        "",
        "Residual stack trace follows:",
        "ExtendableExpr starting at line 2, column 24.",
        "Expression starting at line 2, column 24.",
        "Field Value starting at line 2, column 18.",
        "Some [] Form starting at line 2, column 8.",
        "ExtendableExpr starting at line 2, column 8.",
        "",
        "",
        "Fatal errors while parsing TLA+ spec in file Root",
        "",
        "In module Base",
        "",
        "Could not parse module Base from file Base.tla",
        "*** Errors: 1",
        "",
        "In module Base",
        "",
        "Could not parse module Base from file Base.tla",
        "",
        "",
        "",
        "Starting... (DATE)",
        "Error: Parsing or semantic analysis failed.",
      ].join("\n"),
    );
  });

  it("rejects -lncheck without a strategy like TLC", () => {
    const result = runCli("cli-output", "Lasso", ["-lncheck"]);
    expect(result.status).toBe(1);
    expect(result.stdout.split("\n").slice(1)).toEqual([
      "Error: Error: expect a strategy such as final for -lncheck option.",
      "Usage: java tlc2.TLC [-help] [-option] inputfile",
      "",
    ]);
  });

  it("names a spec given by an absolute path by its file name, as TLC runs from its directory", () => {
    const directory = join(FIXTURES, "cli-output");
    const result = runCliWith("cli-output", [
      "-config",
      "Success.cfg",
      join(directory, "Missing.tla"),
    ]);
    expect(result.status).toBe(150);
    expect(result.stderr).toBe(
      `File does not exist: ${directory}/Missing.tla while looking in these directories: ${directory}, , classpath:/tla2sany/StandardModules, classpath:/\n`,
    );
    expect(result.stdout).toContain("\nFatal errors while parsing TLA+ spec in file Missing\n");
  });

  it("reads the system properties the Java launch sets with TLCGet, like TLC", () => {
    // TLC at d8fb231: `java -Dfoo=bar tlc2.TLC Property` violates Inv, and without foo it holds.
    const run = (properties: string[]) =>
      runCliWith("system-property", [...properties, "tlc2.TLC", "-noGenerateSpecTE", "Property"]);
    const set = run(["-Dother=1", "-Dfoo=bar"]);
    expect(set.status).toBe(12);
    expect(set.stdout).toContain("Error: Invariant Inv is violated by the initial state:\nx = 1\n");
    const unset = run(["-Dother=bar"]);
    expect(unset.status).toBe(0);
    expect(unset.stdout).toContain("Model checking completed. No error has been found.");
  });

  it("reports its version and runtime, then the files SANY parses, the modules it analyzes and the modules it lints", () => {
    const directory = join(FIXTURES, "cli-output");
    const args = [
      "-Djava.io.tmpdir=/tmp",
      "-cp",
      "/lib/tla2tools.jar",
      "tlc2.TLC",
      "-workers",
      "2",
      "-seed",
      "7",
      "Success",
    ];
    const result = runCliWith("cli-output", args);
    const lines = result.stdout.split("\n");
    expect(lines[0]).toMatch(/^TLC2 Version \d+\.\d+\.\d+ \(rev: tla-ts\)$/);
    expect(lines[1]).toMatch(
      /^Running breadth-first search Model-Checking with fp 0 and seed 7 with 2 workers on \d+ cores with \d+MB heap and 0MB offheap memory \[pid: \d+\] \(.+, prove-it native 64bit, MemFPSet, MemStateQueue\)\.$/,
    );
    expect(lines[2]).toBe(`Parsing file ${realpathSync(join(directory, "Success.tla"))}`);
    // TLC's trace exploration spec adds _TLCTrace to the modules the spec extends.
    const standardModules = ["Naturals", "_TLCTrace", "TLC", "TLCExt", "Sequences", "FiniteSets"];
    expect(lines.slice(3, 10)).toEqual(
      [...standardModules, "Integers"].map((name) =>
        expect.stringMatching(
          new RegExp(
            `^Parsing file ${realpathSync("/tmp")}/tlc-\\d+/${name}\\.tla \\(jar:file:/lib/tla2tools\\.jar!/tla2sany/StandardModules/${name}\\.tla\\)$`,
          ),
        ),
      ),
    );
    expect(lines.slice(10, 21)).toEqual([
      "Semantic processing of module Naturals",
      "Semantic processing of module Sequences",
      "Semantic processing of module FiniteSets",
      "Semantic processing of module TLC",
      "Semantic processing of module Integers",
      "Semantic processing of module TLCExt",
      "Semantic processing of module _TLCTrace",
      "Semantic processing of module Success",
      "Linting of module TLCExt",
      "Linting of module _TLCTrace",
      "Linting of module Success",
    ]);
    // TLC names its copies of the standard modules at random, and tla-ts the same way each run.
    expect(runCliWith("cli-output", args).stdout.split("\n")[3]).toBe(lines[3]);
    expect(
      runCliWith("cli-output", [...args, "-noTE"])
        .stdout.split("\n")
        .slice(4, 7),
    ).toEqual([
      "Semantic processing of module Naturals",
      "Semantic processing of module Success",
      "Linting of module Success",
    ]);
  });
});

// What SANY's XMLExporter prints to standard error for the same modules, and its exit code.
const XML_EXPORT_FAILURES = [
  [
    "Renamed.tla",
    2,
    [
      "",
      "Fatal errors while parsing TLA+ spec in file Renamed.tla",
      "",
      "Unknown location",
      "",
      "File name 'Renamed' does not match the name 'Other' of the top level module it contains.",
      "*** Errors: 1",
      "",
      "Unknown location",
      "",
      "File name 'Renamed' does not match the name 'Other' of the top level module it contains.",
      "",
      "",
      "",
      "ERROR: Failed to parse module.",
    ],
  ],
  [
    "Nesting.tla",
    2,
    [
      "",
      "Fatal errors while parsing TLA+ spec in file Nesting.tla",
      "",
      "In module Inner",
      "",
      "Cannot find source file for module Absent imported in module Inner.",
      "*** Errors: 1",
      "",
      "In module Inner",
      "",
      "Cannot find source file for module Absent imported in module Inner.",
      "",
      "",
      "",
      "ERROR: Failed to parse module.",
    ],
  ],
  [
    "Twice.tla",
    2,
    [
      "Semantic errors:",
      "",
      "*** Errors: 1",
      "",
      "line 3, col 1 to line 3, col 7 of module Twice",
      "",
      "Operator Op already defined or declared.",
      "",
      "",
      "ERROR: Failed to parse module.",
    ],
  ],
  [
    "LevelError.tla",
    2,
    [
      "Semantic errors:",
      "",
      "*** Errors: 1",
      "",
      "line 8, col 8 to line 8, col 16 of module LevelError",
      "",
      "Level error in applying operator I!Foo:",
      "The level of argument 1 exceeds the maximum level allowed by the operator.",
      "",
      "",
      "ERROR: Failed to parse module.",
    ],
  ],
  // XMLExporter prints this exception with Java's stack traces, of each node it was exporting
  // (tests/conformance/sany-stdout/xml-fixtures-o.json), which tla-front declines to write.
  [
    "DefineStep.tla",
    1,
    ["prove-it: not native yet: SANY's XMLExporter of the stack traces of XMLExporter's exception"],
  ],
  [
    "FormFeed.tla",
    7,
    [
      "ERROR: The spec contains the character U+000C in the StringValue element. XML 1.0 cannot represent that character in character data, not even as a numeric character reference, so the spec cannot be exported until the character is removed from it.",
    ],
  ],
  [
    "nested/Root.tla",
    2,
    [
      "",
      "Fatal errors while parsing TLA+ spec in file nested/Root.tla",
      "",
      "In module Root",
      "",
      "Cannot find source file for module Sibling imported in module Root.",
      "*** Errors: 1",
      "",
      "In module Root",
      "",
      "Cannot find source file for module Sibling imported in module Root.",
      "",
      "",
      "",
      "ERROR: Failed to parse module.",
    ],
  ],
  [
    "nested/Unparsed",
    2,
    [
      "***Parse Error***",
      'Encountered "====" at line 3, column 1 and token "+" ',
      "",
      "Residual stack trace follows:",
      "ExtendableExpr starting at line 3, column 1.",
      "ExtendableExpr starting at line 2, column 7.",
      "Expression starting at line 2, column 7.",
      "Definition starting at line 2, column 1.",
      "Module body starting at line 2, column 1.",
      "",
      "",
      "Fatal errors while parsing TLA+ spec in file nested/Unparsed",
      "",
      "In module Unparsed",
      "",
      "Could not parse module Unparsed from file nested/Unparsed.tla",
      "*** Errors: 1",
      "",
      "In module Unparsed",
      "",
      "Could not parse module Unparsed from file nested/Unparsed.tla",
      "",
      "",
      "",
      "ERROR: Failed to parse module.",
    ],
  ],
] as const;

const exportXml = (args: string[]) =>
  runCliWith("xml-export", ["tla2sany.xml.XMLExporter", "-o", ...args]);

describe("the CLI prints SANY's report as tla-front writes it", () => {
  // SANY's error corpus E4243_1_Required_0_Provided: TLC reports the substitute's arity, then the
  // constant it must substitute for, which the TypeScript report leaves out. The spec isn't among
  // the fixtures, which front-differential.ts holds the TypeScript report to.
  it.each([[[]], [["-tool"]]])("with %p", (args) => {
    const directory = mkdtempSync(join(tmpdir(), "prove-it-sany-"));
    copies.push(directory);
    writeFileSync(
      join(directory, "Substitute.tla"),
      "---- MODULE Substitute ----\n---- MODULE Inner ----\nCONSTANT F(_)\n====\nop == 0\nINSTANCE Inner WITH F <- op\n====\n",
    );
    writeFileSync(join(directory, "Substitute.cfg"), "");
    const result = spawnSync("bun", [CLI, "Substitute.tla", "-noGenerateSpecTE", ...args], {
      cwd: directory,
      encoding: "utf8",
    });
    expect(result.status).toBe(150);
    expect(result.stdout).toContain(
      "Expected arity 1 but found operator of arity 0.\n\n\nIn module --TLA+ BUILTINS--\n\nAn operator must be substituted for symbol 'F', and it must have arity 1.\n",
    );
  });
});

describe("the CLI exports XML like SANY's XMLExporter", () => {
  // SANY reads WF_B(A)(Act) with the subscript B(A), which the TypeScript front end rejects: the
  // export comes from tla-front, through the native engine.
  it("exports a spec only tla-front reads, as SANY's corpus FairnessTest", () => {
    const directory = mkdtempSync(join(tmpdir(), "prove-it-xml-"));
    copies.push(directory);
    writeFileSync(
      join(directory, "Fair.tla"),
      "---- MODULE Fair ----\nVARIABLE x\nB(a) == a\nF == WF_B(x)(x' = x)\n====\n",
    );
    const result = spawnSync("bun", [CLI, "tla2sany.xml.XMLExporter", "-o", "-t", "Fair.tla"], {
      cwd: directory,
      encoding: "utf8",
    });
    expect(result.stderr).toBe("");
    expect(result.status).toBe(0);
    expect(result.stdout).toStartWith(
      '<?xml version="1.0" encoding="UTF-8" standalone="no"?><modules><RootModule>Fair</RootModule>',
    );
  });

  it.each(XML_EXPORT_FAILURES)("fails on %s", (file, code, lines) => {
    const result = exportXml([file]);
    expect(result.status).toBe(code);
    expect(result.stdout).toBe("");
    expect(result.stderr).toBe([...lines, ""].join("\n"));
  });

  // Numbered.xml is what XMLExporter writes for Numbered.tla, which has a node of each kind SANY
  // numbers out of the order of the spec's text.
  it("writes the XML that XMLExporter writes, with SANY's UIDs in the order of its HashMap", () => {
    const result = exportXml(["Numbered.tla"]);
    expect(result.status).toBe(0);
    expect(result.stdout).toBe(readFileSync(join(FIXTURES, "xml-export", "Numbered.xml"), "utf8"));
  });

  // Commented.xml is what XMLExporter writes for Commented.tla with -t, -r and -u: on one line,
  // without what Commented has from Counted, and with the pre-comments out of their boxes.
  it("writes the XML of the root module alone, unboxed and on one line, as XMLExporter does", () => {
    const result = exportXml(["-t", "-r", "-u", "Commented.tla"]);
    expect(result.status).toBe(0);
    expect(result.stdout).toBe(readFileSync(join(FIXTURES, "xml-export", "Commented.xml"), "utf8"));
  });

  it("prints its usage for -help, and with an error for an argument it does not know", () => {
    const help = exportXml(["-help"]);
    expect(help.status).toBe(0);
    expect(help.stdout.split("\n").slice(0, 4)).toEqual([
      "",
      "\x1b[1mNAME\x1b[0m",
      "",
      "\ttla2sany.xml.XMLExporter - Emit SANY's parse tree as XML - Version 2.2 created 08 July 2020",
    ]);
    const unknown = exportXml(["-x", "Commented.tla"]);
    expect(unknown.status).toBe(1);
    expect(unknown.stderr).toBe(`ERROR: Only one TLA file to check allowed!\n${help.stdout}`);
  });

  it("finds the root module and the modules it extends in the -I directories", () => {
    const result = exportXml(["-I", "nested", "Root"]);
    expect(result.status).toBe(0);
    expect(result.stdout).toContain("<RootModule>Root</RootModule>");
  });

  it("names the file of a root module it cannot find and where it looked", () => {
    const directory = join(FIXTURES, "xml-export");
    const result = exportXml(["-I", "nested", "Missing"]);
    expect(result.status).toBe(2);
    expect(result.stderr.split("\n").slice(0, 7)).toEqual([
      `File does not exist: ${directory}/./Missing.tla while looking in these directories: ${directory}, nested, classpath:/tla2sany/StandardModules, classpath:/`,
      "",
      "Fatal errors while parsing TLA+ spec in file Missing",
      "",
      "Unknown location",
      "",
      "Cannot find source file for module Missing",
    ]);
  });
});

// tla2tools-1.7.4.jar holds only the manifest of TLC 1.7.4's jar, which is all tla-ts reads of it.
const JAR_174 = join(FIXTURES, "xml-export", "tla2tools-1.7.4.jar");

describe("the CLI checks a spec like TLC 1.7.4 when its jar is on the class path", () => {
  const check174 = (name: string) =>
    runCliWith("tlc-174", [
      "-cp",
      JAR_174,
      "tlc2.TLC",
      "-tool",
      "-workers",
      "1",
      "-fp",
      "0",
      "-lncheck",
      "final",
      `${name}.tla`,
    ]);

  it("reports the depth and outdegree after an invariant violation, labels actions without their parameters, and doesn't warn about a constant invariant", () => {
    const result = check174("Climb");
    expect(result.status).toBe(12);
    expect(getToolSequence(result.stdout)).toEqual([
      "2262",
      "2187",
      "2220",
      "2219",
      "2185",
      "2189",
      "2190",
      "2110",
      "2121",
      "2217",
      "2217",
      "2217",
      "2200",
      "2199",
      "2194",
      "2268",
      "2186",
    ]);
    expect(result.stdout).toContain(
      "2: <Step line 5, col 12 to line 5, col 21 of module Climb>\nx = 1\n",
    );
  });

  it("reports a temporal violation without naming the properties or the depth", () => {
    const result = check174("Cycle");
    expect(result.status).toBe(13);
    expect(result.stdout).toContain(
      "@!@!@STARTMSG 2116:1 @!@!@\nTemporal properties were violated.\n\n@!@!@ENDMSG 2116 @!@!@",
    );
    expect(getToolSequence(result.stdout).slice(-4)).toEqual(["2267", "2200", "2199", "2186"]);
  });

  it("prints what rebuilding a counterexample prints after its heading, the prefix at once and the cycle state by state", () => {
    const result = check174("CyclePrint");
    expect(result.status).toBe(13);
    const states = [0, 1, 2, 3].map(
      (value) =>
        `@!@!@STARTMSG 2217:4 @!@!@\n${value === 0 ? "1: <Initial predicate>" : `${value + 1}: <Next line 5, col 9 to line 5, col 63 of module CyclePrint>`}\nx = ${value}\n\n@!@!@ENDMSG 2217 @!@!@\n`,
    );
    expect(result.stdout).toContain(
      [
        "@!@!@STARTMSG 2264:1 @!@!@\nThe following behavior constitutes a counter-example:\n\n@!@!@ENDMSG 2264 @!@!@\n",
        '"init"\n<<"n", 0>>\n<<"n", 1>>\n',
        states[0],
        states[1],
        states[2],
        '<<"n", 2>>\n',
        states[3],
        '<<"n", 3>>\n',
        "@!@!@STARTMSG 2122:4 @!@!@\n3: Back to state",
      ].join(""),
    );
  });

  it("prints the sources of the values it fails to fingerprint rather than the call stack", () => {
    const result = check174("Unfingerprinted");
    expect(result.status).toBe(75);
    expect(result.stdout).toContain(
      "Fingerprint Stack Trace:\n0) line 8, col 18 to line 8, col 30 of module Unfingerprinted\n\nReason:\n",
    );
  });

  it("reports an error in building the liveness checker as an unexpected EvalException", () => {
    const result = check174("Undiameter");
    expect(result.status).toBe(255);
    expect(result.stdout).toContain(
      [
        "@!@!@STARTMSG 1000:1 @!@!@",
        "TLC threw an unexpected exception.",
        "This was probably caused by an error in the spec or model.",
        "See the User Output or TLC Console for clues to what happened.",
        "The exception was a tlc2.tool.EvalException",
        ": @!@!@STARTMSG 2145:0 @!@!@",
        "TLCGet(diameter) was undefined.",
        "@!@!@ENDMSG 2145 @!@!@",
        "@!@!@ENDMSG 1000 @!@!@",
      ].join("\n"),
    );
  });

  it("marks the message of a temporal formula it can't handle inside another", () => {
    const result = check174("Unhandled");
    expect(result.status).toBe(255);
    expect(result.stdout).toContain(
      [
        "@!@!@STARTMSG 2213:1 @!@!@",
        "TLC cannot handle the temporal formula line 7, col 9 to line 7, col 51 of module Unhandled:",
        "@!@!@STARTMSG 2213:0 @!@!@",
        "TLC cannot handle the temporal formula line 7, col 25 to line 7, col 51 of module Unhandled:",
        "Attempted to check if the value:",
        "2",
        "is an element of the integer 1",
        "@!@!@ENDMSG 2213 @!@!@",
        "@!@!@ENDMSG 2213 @!@!@",
      ].join("\n"),
    );
  });

  it("reports an error in the config as an unexpected exception", () => {
    const result = check174("Aliased");
    expect(result.status).toBe(255);
    expect(result.stdout).toContain(
      [
        "@!@!@STARTMSG 1000:1 @!@!@",
        "TLC threw an unexpected exception.",
        "This was probably caused by an error in the spec or model.",
        "See the User Output or TLC Console for clues to what happened.",
        "The exception was a tlc2.tool.ConfigFileException",
        ": @!@!@STARTMSG 5006:0 @!@!@",
        "TLC found an error in the configuration file at line 3",
        "It was expecting a keyword, but did not find it.",
        "@!@!@ENDMSG 5006 @!@!@",
      ].join("\n"),
    );
  });

  it("warns about the constraints of a liveness check and reports a depth of at least 1", () => {
    const bounded = check174("Bounded");
    expect(bounded.status).toBe(0);
    expect(getToolSequence(bounded.stdout).slice(4, 7)).toEqual(["2185", "2284", "2212"]);
    const unbounded = check174("Unbounded");
    expect(unbounded.status).toBe(0);
    expect(getToolSequence(unbounded.stdout).slice(4, 6)).toEqual(["2185", "2212"]);
    const empty = check174("Empty");
    expect(empty.status).toBe(0);
    expect(empty.stdout).toContain("The depth of the complete state graph search is 1.");
  });

  it("names the file it looked for a module in that it can't find", () => {
    const result = check174("Lost");
    expect(result.status).toBe(150);
    expect(result.stderr).toBe(
      `File does not exist: ${join(FIXTURES, "tlc-174", "Gone.tla")} while looking in these directories: jar:file:${pathToFileURL(JAR_174).pathname}!/tla2sany/StandardModules/\n`,
    );
    expect(result.stdout).toContain(
      "Unknown location\n\nCannot find source file for module Gone imported in module Lost.\n",
    );
  });
});

describe("the CLI reproduces the TLC that -Dtla-ts.tlc names without a jar", () => {
  const tlcArgs = ["tlc2.TLC", "-tool", "-workers", "1", "-fp", "0"];

  it.each(["Climb", "Cycle", "Aliased"])(
    "checks %s like TLC 1.7.4 with its jar on the class path",
    (name) => {
      const withJar = runCliWith("tlc-174", ["-cp", JAR_174, ...tlcArgs, `${name}.tla`]);
      const withProperty = runCliWith("tlc-174", ["-Dtla-ts.tlc=1.7.4", ...tlcArgs, `${name}.tla`]);
      expect(withProperty.status).toBe(withJar.status);
      expect(getToolSequence(withProperty.stdout)).toEqual(getToolSequence(withJar.stdout));
    },
  );

  it("leaves the jar out of the directories it looked for a missing module in", () => {
    const result = runCliWith("tlc-174", ["-Dtla-ts.tlc=1.7.4", ...tlcArgs, "Lost.tla"]);
    expect(result.status).toBe(150);
    expect(result.stderr).toBe(
      `File does not exist: ${join(FIXTURES, "tlc-174", "Gone.tla")} while looking in these directories: \n`,
    );
  });

  // TLC 1.7.4's XMLExporter is retired: only master's is native.
  it("declines TLC 1.7.4's XMLExporter", () => {
    for (const args of [["-Dtla-ts.tlc=1.7.4"], ["-cp", JAR_174]]) {
      const result = runCliWith("xml-export", [
        ...args,
        "tla2sany.xml.XMLExporter",
        "-o",
        "Counted.tla",
      ]);
      expect(result.status).toBe(1);
      expect(result.stdout).toBe("");
      expect(result.stderr).toBe("prove-it: not native yet: TLC 1.7.4\n");
    }
  });

  it("takes the TLC it names over that of the jar", () => {
    const run = (args: string[]) => runCliWith("tlc-174", [...args, ...tlcArgs, "Cycle.tla"]);
    const master = run(["-cp", JAR_174, "-Dtla-ts.tlc=master"]);
    expect(getToolSequence(master.stdout)).toEqual(getToolSequence(run([]).stdout));
    expect(getToolSequence(master.stdout)).not.toEqual(
      getToolSequence(run(["-cp", JAR_174]).stdout),
    );
  });
});

// TLC searches a set it has normalized, a constant's, by halving with the element's compareTo, and
// one it hasn't, a set enumeration's, element by element with equals. Each fails where TLC does,
// with the engine and without it. The .out files are TLC's output at TLC_COMMIT.
describe("the CLI fails a membership where TLC does", () => {
  it.each([["SearchedRecord"], ["SearchedTuple"], ["EnumeratedTuple"], ["EnumeratedModels"]])(
    "fails %s as TLC does",
    (name) => {
      const expected = readFileSync(join(FIXTURES, "membership", `${name}.out`), "utf8").split(
        "\n",
      );
      for (const engine of ["1", "0"]) {
        const result = runCliWith("membership", ["-nowarning", `${name}.tla`], {
          PROVE_IT_ENGINE: engine,
        });
        expect(result.status).toBe(75);
        expect(getSteadyLines(result.stdout)).toEqual(expected);
      }
    },
  );
});

describe("the CLI takes several specs and globs", () => {
  it("checks each spec a glob matches and exits with the first failure", () => {
    const result = runCliWith("cli-output", ["*.tla"]);
    expect(result.status).toBe(10);
    expect(getCheckedSpecs(result.stdout)).toEqual([
      "Checking AssumptionFalse.tla with AssumptionFalse.cfg",
      "Checking EventualAction.tla with EventualAction.cfg",
      "Checking FailedAssert.tla with FailedAssert.cfg",
      "Checking FailedInitialInvariant.tla with FailedInitialInvariant.cfg",
      "Checking FailedInvariant.tla with FailedInvariant.cfg",
      "Checking IllegalInitialState.tla with IllegalInitialState.cfg",
      "Checking InitialInvariant.tla with InitialInvariant.cfg",
      "Checking Lasso.tla with Lasso.cfg",
      "Checking Lassos.tla with Lassos.cfg",
      "Checking LivenessError.tla with LivenessError.cfg",
      "Checking NoNext.tla with NoNext.cfg",
      "Checking SafetyProperty.tla with SafetyProperty.cfg",
      "Checking Success.tla with Success.cfg",
      "Checking Undefined.tla with Undefined.cfg",
      "Checking UnfingerprintedEquality.tla with UnfingerprintedEquality.cfg",
      "Checking UnfingerprintedState.tla with UnfingerprintedState.cfg",
      "Checking UnspecifiedFairness.tla with UnspecifiedFairness.cfg",
      "Checking ViewLasso.tla with ViewLasso.cfg",
      "Checking Warned.tla with Warned.cfg",
    ]);
  });

  it("skips a module a glob matches when it has no configuration", () => {
    const result = runCliWith("tlc-spec", ["*.tla"]);
    expect(result.status).toBe(0);
    expect(getCheckedSpecs(result.stdout)).toEqual([
      "Checking Inst.tla with Inst.cfg",
      "Checking Param.tla with Param.cfg",
      "Checking Rich.tla with Rich.cfg",
      "Checking Subst.tla with Subst.cfg",
      "Checking Unnamed.tla with Unnamed.cfg",
    ]);
  });

  it("checks the spec beside a configuration", () => {
    const [, , lines] = TLC_REPORTS.find((report) => report[0] === "Success") ?? [];
    const result = runCliWith("cli-output", ["Success.cfg"]);
    expect(result.status).toBe(0);
    expect(getSteadyLines(result.stdout)).toEqual([...(lines ?? []), ""]);
  });

  it("rejects -config with several specs", () => {
    const result = runCliWith("cli-output", ["Lasso.tla", "Success.tla", "-config", "Success.cfg"]);
    expect(result.status).toBe(1);
    expect(result.stderr).toBe(
      "Error: -config applies to one specification, but several were given.\n",
    );
  });
});

describe("tlapm -N prints obligations as tlapm does", () => {
  // Each .toolbox file is what tlapm -N writes to stderr for the same arguments.
  const readExpected = (name: string) => readFileSync(join(FIXTURES, "obligations", name), "utf8");

  it("prints each obligation with its text", () => {
    const result = runTlapm("obligations", [
      "-N",
      "--toolbox",
      "0",
      "0",
      "--printallobs",
      "Proofs.tla",
    ]);
    expect(result.status).toBe(0);
    expect(result.stderr).toBe(readExpected("Proofs.toolbox"));
  });

  it("numbers omitted proofs but doesn't print them", () => {
    const result = runTlapm("obligations", ["-N", "--toolbox", "0", "0", "Omit.tla"]);
    expect(result.status).toBe(0);
    expect(result.stderr).toBe(readExpected("Omit.toolbox"));
  });

  it("generates only the proofs within the lines", () => {
    const result = runTlapm("obligations", ["-N", "--toolbox", "6", "7", "Omit.tla"]);
    expect(result.status).toBe(0);
    expect(result.stderr).toBe(readExpected("Omit-6-7.toolbox"));
  });

  it("warns when a module's name differs from its file's", () => {
    const result = runTlapm("obligations", [
      "-N",
      "--toolbox",
      "0",
      "0",
      "--printallobs",
      "Renamed.tla",
    ]);
    expect(result.status).toBe(0);
    expect(result.stderr).toBe(readExpected("Renamed.toolbox"));
  });

  it("reports the warnings tlapm reports", () => {
    const result = runTlapm("obligations", [
      "-N",
      "--toolbox",
      "0",
      "0",
      "--printallobs",
      "Warnings.tla",
    ]);
    expect(result.status).toBe(0);
    expect(result.stderr).toBe(readExpected("Warnings.toolbox"));
  });

  // Each .strict file is what tlapm -N --strict writes to stderr.
  it("reports incomplete proofs under --strict", () => {
    const result = runTlapm("obligations", ["-N", "--strict", "Incomplete.tla"]);
    expect(result.status).toBe(11);
    expect(result.stderr).toBe(readExpected("Incomplete.strict"));
  });

  it("reports a target without obligations under --strict", () => {
    const result = runTlapm("obligations", ["-N", "--strict", "--line", "2", "Proofs.tla"]);
    expect(result.status).toBe(12);
    expect(result.stderr).toBe(readExpected("Proofs-2.strict"));
  });

  // Notes.stdout and Notes.stderr are what tlapm -N writes.
  it("prints the notes tlapm prints outside toolbox mode", () => {
    const result = runTlapm("obligations", ["-N", "Notes.tla"]);
    expect(result.status).toBe(0);
    expect(result.stdout).toBe(readExpected("Notes.stdout"));
    expect(result.stderr).toBe(readExpected("Notes.stderr"));
  });

  it("prints tlapm's header in toolbox mode", () => {
    const result = runTlapm("obligations", ["-N", "--line", "3", "Omit.tla"]);
    expect(result.status).toBe(0);
    expect(result.stdout).toMatch(
      /^\n\\\* TLAPM version 9ed0376\n\\\* launched at \d{4}-\d\d-\d\d \d\d:\d\d:\d\d with command line:\n\\\* tla-ts tlapm -N --line 3 Omit\.tla\n\n$/,
    );
  });

  it("prints nothing outside toolbox mode", () => {
    const result = runTlapm("obligations", ["-N", "Proofs.tla"]);
    expect(result.status).toBe(0);
    expect(result.stdout + result.stderr).toBe("");
  });

  // Each .summary file is what tlapm --summary writes to stdout.
  it("summarizes the missing and omitted proofs of each theorem", () => {
    const result = runTlapm("obligations", ["--summary", "Incomplete.tla"]);
    expect(result.status).toBe(0);
    expect(result.stdout).toBe(readExpected("Incomplete.summary"));
    expect(result.stderr).toBe("");
  });

  // Each .stderr file is what tlapm -N writes to stderr, without the OCaml backtrace.
  it.each([
    "Declaration",
    "Hide",
    "Label",
    "NotFound",
    "Recursive",
    "Tab",
    "Unexpected",
    "UnknownModule",
  ])("prints the error tlapm prints for %s", (name) => {
    const result = runTlapm("obligation-errors", ["-N", `${name}.tla`]);
    expect(result.status).toBe(3);
    expect(result.stdout).toBe("");
    expect(result.stderr).toBe(
      readFileSync(join(FIXTURES, "obligation-errors", `${name}.stderr`), "utf8"),
    );
  });

  it("names a module it cannot find", () => {
    const result = runTlapm("obligations", ["-N", "Missing.tla"]);
    expect(result.status).toBe(3);
    expect(result.stdout).toBe("");
    expect(result.stderr).toBe(
      'File "<unknown>":\nError: File "Missing.tla" not found\n tlapm ending abnormally with Failure("Module.Parser.parse_file")\n\n',
    );
  });

  // tlapm reads bytes, so these two strings differ. Read with U+FFFD for each byte that isn't
  // UTF-8, they would be one, and the theorem proved: ED A0 80 and ED B0 80 encode U+D800 and
  // U+DC00, which a lossy decode reads as three U+FFFD each.
  const NOT_UTF8 = [
    ["\\xff = \\xfe", [0xff], [0xfe], "="],
    ["U+D800 = U+DC00", [0xed, 0xa0, 0x80], [0xed, 0xb0, 0x80], "="],
    ["U+D800 # U+DC00", [0xed, 0xa0, 0x80], [0xed, 0xb0, 0x80], "#"],
  ] as const;
  it.each(
    NOT_UTF8.flatMap(([name, ...strings]) => [
      ["the module", name, "M.tla", "", ...strings] as const,
      ["a module it extends", name, "./Lib.tla", "Lib, ", ...strings] as const,
    ]),
  )("declines %s that isn't UTF-8: %s", (_, _name, path, extended, left, right, operator) => {
    const directory = mkdtempSync(join(tmpdir(), "tla-ts-tlapm-"));
    const theorem = Buffer.concat([
      Buffer.from('THEOREM "'),
      Buffer.from(left),
      Buffer.from(`" ${operator} "`),
      Buffer.from(right),
      Buffer.from('" BY SMT\n'),
    ]);
    writeFileSync(
      join(directory, "M.tla"),
      Buffer.concat([
        Buffer.from(`---- MODULE M ----\nEXTENDS ${extended}TLAPS\n`),
        ...(extended === "" ? [theorem] : []),
        Buffer.from("====\n"),
      ]),
    );
    writeFileSync(
      join(directory, "Lib.tla"),
      Buffer.concat([Buffer.from("---- MODULE Lib ----\n"), theorem, Buffer.from("====\n")]),
    );
    const result = runTlapmIn(directory, ["M.tla"]);
    expect(result.stderr).toBe(
      `prove-it: not native yet: a byte that isn't UTF-8 outside a comment in ${path}\n`,
    );
    expect(result.stdout).toBe("");
    expect(result.status).toBe(1);
  });

  // tlapm's lexer skips what comes before a module's header and what a comment holds, so a byte
  // that isn't UTF-8 there reads as it did, one U+FFFD for one byte.
  it.each([
    ["before the header", [0xe9, 0x0a], ""],
    ["in a line comment", [], "\\* caf\xe9\n"],
    ["in a nested comment", [], "(* (* caf\xe9 *) \xff *)\n"],
    // The lexer the obligations are read with ends a `\*` comment at a line feed alone, where
    // tlapm's ends it at a carriage return too.
    ["after a carriage return in a line comment", [], "\\* abc\r\xe9\n"],
  ])("reads a byte that isn't UTF-8 %s as tlapm skips it", (_, before, inside) => {
    const getModule = (byte: number) =>
      Buffer.concat([
        Buffer.from(before.map((value) => (value === 0xe9 ? byte : value))),
        Buffer.from("---- MODULE M ----\nEXTENDS TLAPS\n", "latin1"),
        Buffer.from(inside.replaceAll("\xe9", String.fromCharCode(byte)), "latin1"),
        Buffer.from("THEOREM 1 = 1 OBVIOUS\n====\n"),
      ]);
    const run = (byte: number) => {
      const directory = mkdtempSync(join(tmpdir(), "tla-ts-tlapm-"));
      writeFileSync(join(directory, "M.tla"), getModule(byte));
      return runTlapmIn(directory, ["-N", "M.tla"]);
    };
    const read = run(0xe9);
    expect(read.stderr).not.toContain("not native yet");
    expect(read).toMatchObject({ status: 0, stdout: run(0x65).stdout, stderr: run(0x65).stderr });
  });

  // tlapm's columns count bytes, so a comment holding two bytes of a three-byte sequence puts what
  // follows it on the line two columns on.
  it("counts each byte that isn't UTF-8 in a comment as a column", () => {
    const run = (comment: Buffer) => {
      const directory = mkdtempSync(join(tmpdir(), "tla-ts-tlapm-"));
      writeFileSync(
        join(directory, "M.tla"),
        Buffer.concat([
          Buffer.from("---- MODULE M ----\nEXTENDS TLAPS\nTHEOREM "),
          comment,
          Buffer.from(" 1 = 1 OBVIOUS\n====\n"),
        ]),
      );
      return runTlapmIn(directory, ["-N", "--toolbox", "0", "0", "M.tla"]);
    };
    const truncated = run(Buffer.from([0x28, 0x2a, 0xe2, 0x82, 0x2a, 0x29]));
    expect(truncated.stderr).toContain("loc:3:22:3:29");
    expect(truncated.stderr).toBe(run(Buffer.from("(*ab*)")).stderr);
  });

  // tlapm's parser asks for no token past the first module's `====`, so its lexer never reads
  // what follows; a nested module's `====` doesn't end it.
  it.each([
    ["after the module's end", "THEOREM TRUE OBVIOUS\n====\n\xff\n", false],
    ["after the module's end, in a string", 'THEOREM TRUE OBVIOUS\n====\n"\xff"\n', false],
    [
      "in a string in a nested module",
      '---- MODULE Inner ----\nS == "\xff"\n====\nTHEOREM TRUE OBVIOUS\n====\n',
      true,
    ],
    [
      "after a nested module's end",
      '---- MODULE Inner ----\n====\nS == "\xff"\nTHEOREM TRUE OBVIOUS\n====\n',
      true,
    ],
    [
      "in a nested module's comment",
      "---- MODULE Inner ----\n(* \xff *)\n====\nTHEOREM TRUE OBVIOUS\n====\n",
      false,
    ],
  ])("reads a byte that isn't UTF-8 %s as tlapm lexes it", (_, body, isDeclined) => {
    const directory = mkdtempSync(join(tmpdir(), "tla-ts-tlapm-"));
    writeFileSync(
      join(directory, "M.tla"),
      Buffer.from(`---- MODULE M ----\nEXTENDS TLAPS\n${body}`, "latin1"),
    );
    const result = runTlapmIn(directory, ["-N", "M.tla"]);
    if (isDeclined) {
      expect(result.stderr).toBe(
        "prove-it: not native yet: a byte that isn't UTF-8 outside a comment in M.tla\n",
      );
      expect(result.status).toBe(1);
    } else {
      expect(result.stderr).not.toContain("not native yet");
      expect(result.status).toBe(0);
    }
  });

  it("declines a byte that isn't UTF-8 in a pragma", () => {
    const directory = mkdtempSync(join(tmpdir(), "tla-ts-tlapm-"));
    writeFileSync(
      join(directory, "M.tla"),
      Buffer.from(
        '---- MODULE M ----\nEXTENDS TLAPS\nF == TRUE (*{ by (prover:"\xff") }*)\nTHEOREM 1 = 1 BY F\n====\n',
        "latin1",
      ),
    );
    const result = runTlapmIn(directory, ["-N", "M.tla"]);
    expect(result.stderr).toBe(
      "prove-it: not native yet: a byte that isn't UTF-8 outside a comment in M.tla\n",
    );
    expect(result.status).toBe(1);
  });
});

// Each file in tlapm-cli is what tlapm 9ed0376 wrote: .stdout and .stderr without options, .strict
// to stderr with --strict, .toolbox to stderr with --threads 1 --toolbox 0 0, and .thy and
// .fingerprints to its cache. .reused is what it wrote to stderr with --threads 1 --toolbox 0 0
// over that cache, and .nofp and .cleanfp to stdout with --nofp and --cleanfp.
const readRecording = (name: string) => readFileSync(join(FIXTURES, "tlapm-cli", name), "utf8");

// tlapm copies to stdout what Zenon writes to stderr, which tla-ts's Zenon doesn't write.
const withoutZenonOutput = (output: string) => output.replaceAll(/^Zenon error: .*\n/gm, "");

describe("tlapm proves with tla-ts's provers and prints what tlapm prints", () => {
  // The time each backend took varies from run to run.
  const withoutTimeUsed = (output: string) =>
    output.replaceAll(/time-used: [\d.]+ \(\d+%\)/g, "time-used: <time>");

  it("reports that every obligation is proved", () => {
    const result = runTlapm("obligations", ["Proofs.tla"]);
    expect(result.status).toBe(0);
    expect(result.stdout).toBe(readRecording("Proofs.stdout"));
    expect(result.stderr).toBe(readRecording("Proofs.stderr"));
  });

  it("prints the obligations it couldn't prove and ends abnormally", () => {
    const result = runTlapm("tlapm-cli", ["Failures.tla"]);
    expect(result.status).toBe(3);
    expect(result.stdout).toBe(withoutZenonOutput(readRecording("Failures.stdout")));
    expect(result.stderr).toBe(readRecording("Failures.stderr"));
  });

  it("exits with --strict's status for a failed obligation", () => {
    const result = runTlapm("tlapm-cli", ["--strict", "Failures.tla"]);
    expect(result.status).toBe(10);
    expect(result.stderr).toBe(readRecording("Failures.strict"));
  });

  it("prints each prover's result in toolbox mode", () => {
    const result = runTlapm("tlapm-cli", ["--threads", "1", "--toolbox", "0", "0", "Failures.tla"]);
    expect(result.status).toBe(0);
    expect(result.stdout).toMatch(
      /^\n\\\* TLAPM version 9ed0376\n\\\* launched at [\d-]+ [\d:]+ with command line:\n\\\* tla-ts tlapm --threads 1 --toolbox 0 0 Failures\.tla\n\n\(\* created new "\.tlacache\/Failures\.tlaps\/Failures\.thy" \*\)\n\(\* fingerprints written in "\.tlacache\/Failures\.tlaps\/fingerprints" \*\)\n$/,
    );
    expect(withoutTimeUsed(result.stderr)).toBe(withoutTimeUsed(readRecording("Failures.toolbox")));
  });

  it("prints a failure it reuses for an obligation with the same fingerprint", () => {
    const result = runTlapm("tlapm-cli", ["--threads", "1", "--toolbox", "0", "0", "Twice.tla"]);
    expect(result.status).toBe(0);
    expect(withoutTimeUsed(result.stderr)).toBe(withoutTimeUsed(readRecording("Twice.toolbox")));
  });

  it("rejects the tlapm options it doesn't support", () => {
    const result = runTlapm("obligations", ["-C", "Proofs.tla"]);
    expect(result.status).toBe(1);
    expect(result.stderr).toBe("Error: tla-ts tlapm does not support the tlapm option -C.\n");
  });
});

describe("tlapm shares its cache with tlapm", () => {
  const TLAPM = process.env.TLAPM;

  // A copy of the fixtures whose cache holds the fingerprints tlapm wrote.
  const copyWithCache = () => {
    const directory = copyFixtures("tlapm-cli");
    mkdirSync(join(directory, ".tlacache/Failures.tlaps"), { recursive: true });
    cpSync(
      join(directory, "Failures.fingerprints"),
      join(directory, ".tlacache/Failures.tlaps/fingerprints"),
    );
    return directory;
  };

  // The fingerprints file without the date and the versions stored with each result.
  const readFingerprints = (path: string) => {
    const bytes = readFileSync(path);
    const table = readMarshaled(bytes, readMarshaled(bytes, 0).next).value;
    return JSON.stringify(table, (_, value) =>
      /^(9ed0376|Zenon version \[268\]|Isabelle2025|tla-ts .*)$/.test(value) ||
      (value?.fields?.length === 6 && value.fields.every(Number.isInteger))
        ? "<stored>"
        : value,
    );
  };

  it("writes the theory and the fingerprints tlapm writes", () => {
    const directory = copyFixtures("tlapm-cli");
    runTlapmIn(directory, ["Failures.tla"]);
    expect(readFileSync(join(directory, ".tlacache/Failures.tlaps/Failures.thy"), "utf8")).toBe(
      readRecording("Failures.thy"),
    );
    expect(readFingerprints(join(directory, ".tlacache/Failures.tlaps/fingerprints"))).toBe(
      readFingerprints(join(directory, "Failures.fingerprints")),
    );
  });

  it("reuses what tlapm concluded", () => {
    const result = runTlapmIn(copyWithCache(), [
      "--threads",
      "1",
      "--toolbox",
      "0",
      "0",
      "Failures.tla",
    ]);
    expect(result.status).toBe(0);
    expect(result.stdout).toContain(
      '(* loading fingerprints in ".tlacache/Failures.tlaps/fingerprints" *)\n',
    );
    expect(result.stderr).toBe(readRecording("Failures.reused"));
  });

  it.each(["--nofp", "--cleanfp"])("proves again under %s", (option) => {
    const result = runTlapmIn(copyWithCache(), [option, "Failures.tla"]);
    expect(result.status).toBe(3);
    expect(result.stdout).toBe(withoutZenonOutput(readRecording(`Failures.${option.slice(2)}`)));
    expect(result.stderr).toBe(readRecording("Failures.stderr"));
  });

  // Set TLAPM to the path of tlapm to check it against the cache tla-ts writes.
  it.if(TLAPM !== undefined)("writes fingerprints tlapm reuses", () => {
    const directory = copyFixtures("tlapm-cli");
    runTlapmIn(directory, ["Failures.tla"]);
    const result = spawnSync(
      TLAPM ?? "tlapm",
      ["--threads", "1", "--toolbox", "0", "0", "Failures.tla"],
      { cwd: directory, encoding: "utf8" },
    );
    expect(result.stderr).toBe(readRecording("Failures.reused"));
  });
});

// The message codes and the lines that Print writes, in the order TLC 1.8.0 prints them with -tool.
const getToolSequence = (output: string) =>
  output
    .split("\n")
    .filter((line) => line.startsWith("@!@!@STARTMSG") || line.startsWith("<<"))
    .map((line) => line.match(/^@!@!@STARTMSG (\d+):/)?.[1] ?? line);

describe("the CLI prints messages for a program to read like TLC", () => {
  const runTool = (name: string) =>
    runCli("tool-output", name, ["-tool", "-workers", "1", "-fp", "0", "-lncheck", "final"]);

  it("prints again what the spec prints as it rebuilds a safety trace", () => {
    const result = runTool("Steps");
    expect(result.status).toBe(12);
    const step = (count: number) => `<<"step", ${count}>>`;
    expect(getToolSequence(result.stdout)).toEqual([
      "2262",
      "2187",
      "2220",
      "2219",
      "2185",
      "2189",
      "2190",
      step(0),
      step(1),
      "2110",
      "2121",
      "2217",
      step(0),
      "2217",
      step(1),
      "2217",
      step(0),
      step(1),
      "2200",
      "2199",
      "2194",
      "2186",
    ]);
  });

  it("reports an invariant its replay of the initial states finds violated", () => {
    const result = runTool("Replayed");
    expect(result.status).toBe(255);
    expect(result.stdout).toContain(
      [
        "@!@!@STARTMSG 1000:1 @!@!@",
        "@!@!@STARTMSG 2184:0 @!@!@",
        "Attempted to apply Head to the empty sequence.",
        "@!@!@ENDMSG 2184 @!@!@",
        "@!@!@ENDMSG 1000 @!@!@",
        "@!@!@STARTMSG 2107:1 @!@!@",
        "Invariant Small is violated by the initial state:",
        "x = 1",
        "",
        "@!@!@ENDMSG 2107 @!@!@",
        "@!@!@STARTMSG 2200:0 @!@!@",
      ].join("\n"),
    );
  });

  it("reports the temporal properties it checks on the complete state graph", () => {
    const result = runTool("Loop");
    expect(result.status).toBe(13);
    const [init, up, reset] = ["init", "up", "reset"].map(
      (name) => (count: number) => `<<"${name}", ${count}>>`,
    );
    expect(getToolSequence(result.stdout)).toEqual([
      "2262",
      "2187",
      "2220",
      "2219",
      "2185",
      "2212",
      "2189",
      init(0),
      "2190",
      up(0),
      up(0),
      up(0),
      up(0),
      up(1),
      up(1),
      up(1),
      up(1),
      reset(2),
      reset(2),
      reset(2),
      reset(2),
      "2200",
      "2192",
      init(0),
      up(0),
      up(1),
      "2116",
      "2264",
      "2217",
      "2217",
      "2217",
      reset(2),
      "2122",
      "2267",
      "2200",
      "2199",
      "2194",
      "2186",
    ]);
    expect(result.stdout).toContain(
      "Implied-temporal checking--satisfiability problem has 1 branches.",
    );
    expect(result.stdout).toContain(
      "Checking temporal properties for the complete state space with 3 total distinct states",
    );
  });

  it("names a property an instance exports as written, as TLC does", () => {
    const getViolation = (config: string) =>
      runCliWith("instance-property", ["-nowarning", "-config", config, "Main.tla"])
        .stdout.split("\n")
        .find((line) => line.endsWith(" is violated."));
    // PSafe == A!Safe names A!Safe, but A!Safe2 == Safe names Safe inside the instance.
    expect(getViolation("Main.cfg")).toBe("Error: Invariant A!Safe is violated.");
    expect(getViolation("Inner.cfg")).toBe("Error: Invariant Safe is violated.");
  });

  it("warns about a state-level property and names an invariant that a property asserts", () => {
    const result = runTool("Always");
    expect(result.status).toBe(12);
    expect(getToolSequence(result.stdout)).toEqual([
      "2262",
      "2187",
      "2220",
      "2219",
      "2185",
      "2255",
      "2189",
      "2190",
      "2110",
      "2121",
      "2217",
      "2217",
      "2217",
      "2200",
      "2199",
      "2194",
      "2186",
    ]);
    expect(result.stdout).toContain("The formula Small is a state-level formula");
    expect(result.stdout).toContain("Invariant Small is violated.");
  });
});

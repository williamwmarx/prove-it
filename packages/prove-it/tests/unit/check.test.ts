import { describe, expect, it } from "bun:test";
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

import {
  check,
  type CheckProgress,
  parseConfig,
  parseModule,
  TlaConfigError,
  TlaSyntaxError,
} from "../../src";
import {
  createSanyError,
  createSemanticError,
  STACK_OVERFLOW_MESSAGE,
  TlaEvaluationError,
  TlaStackOverflowError,
  UNEXPECTED_EVAL_EXCEPTION,
  UNEXPECTED_EXCEPTION,
} from "../../src/errors";
import {
  checkOnEngine,
  expectDeclined,
  findError,
  getAssumptionFailure,
  getErrors,
  getNestedExpressions,
  getStatistics,
  runOnEngine,
  type TlcRunOptions,
} from "../native-check";

const FIXTURES = join(import.meta.dirname, "../fixtures");

// The frames of the stack trace and the reason TLC printed when it failed to fingerprint a value.
const getFingerprintFailure = (output: string) => {
  const error = findError(output, "TLC was unable to fingerprint.\n");
  if (error === undefined) return undefined;
  const [trace = "", reason] = error.split(/\n+Reason:\n/);
  return { frames: trace.split("\n").filter((line) => /^\d+[.)] /.test(line)), reason };
};

// What TLC printed after the last state of the behavior it reported.
const getTraceOutput = (output: string) => {
  const lines = findError(output, "The behavior up to this point is:\n")?.split("\n");
  if (lines === undefined) return undefined;
  const end = lines.indexOf(
    "",
    lines.findLastIndex((line) => /^State \d+: /.test(line)),
  );
  return end === -1 ? [] : lines.slice(end + 1);
};
const DIST = join(import.meta.dirname, "../../dist/index.js");

const getModuleOptions = (body: string, config = "") => ({
  source: `---- MODULE M ----\nEXTENDS Integers, Sequences, FiniteSets, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = x\n${body}\n====`,
  config: `${config}\nINIT Init\nNEXT Next`,
});

const checkModule = (body: string, config = "") => checkOnEngine(getModuleOptions(body, config));

const getFixtureOptions = (directory: string, name: string) => ({
  source: readFileSync(join(FIXTURES, directory, `${name}.tla`), "utf8"),
  config: readFileSync(join(FIXTURES, directory, `${name}.cfg`), "utf8"),
});

const checkFixture = (directory: string, name: string) =>
  checkOnEngine(getFixtureOptions(directory, name));

// The reason the native check declines an assumption that fails to evaluate for.
const getAssumptionDeclined = (reason: string) =>
  `an assumption that fails to evaluate: evaluating the assumption again: ${reason}`;

describe("check matches TLC", () => {
  // TLC prints C once, as it computes the constant definitions.
  it("takes the value of a constant definition that prints", async () => {
    const printed: string[] = [];
    await checkOnEngine({
      source:
        '---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nC == PrintT("C")\nInit == x = 0 /\\ C\nNext == x < 3 /\\ C /\\ x\' = x + 1\nInv == x >= 0 /\\ C\n====',
      config: "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
      onPrint: (text) => printed.push(text),
    });
    expect(printed).toEqual(['"C"']);
  });

  it("evaluates every assumption in the semantics fixture", async () => {
    const result = await checkFixture("semantics", "Semantics");
    expect(result.status).toBe("success");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([2, 1, 1]);
  });

  it.each([
    ["two theorems", "THEOREM Thm == x = 0\nTHEOREM Thm == x = 1"],
    ["an assumption and a theorem", "ASSUME Thm == TRUE\nTHEOREM Thm == x = 1"],
  ])("evaluates the first of %s with the same name as SANY binds it", async (_, facts) => {
    const result = await checkModule(`${facts}\nInv == Thm`, "INVARIANT Inv");
    expect(result.status).toBe("success");
  });

  it.each([
    ["extends", "EXTENDS Facts\nVARIABLE x", "THEOREM T == x = 1", "success"],
    ["instantiates before it", "VARIABLE x\nINSTANCE Facts", "THEOREM T == x = 1", "success"],
    [
      "instantiates after it",
      "VARIABLE x",
      "THEOREM T == x = 1\nINSTANCE Facts",
      "invariant-violation",
    ],
  ])(
    "binds a fact named as one of a module it %s to the first as SANY does",
    async (_, header, facts, status) => {
      const result = await checkOnEngine({
        source: `---- MODULE M ----\n${header}\nInit == x = 0\nNext == x' = x\n${facts}\nInv == T\n====`,
        config: "INIT Init\nNEXT Next\nINVARIANT Inv",
        loadModule: (name) =>
          name === "Facts" ? "---- MODULE Facts ----\nTHEOREM T == TRUE\n====" : undefined,
      });
      expect(result.status).toBe<string>(status);
    },
  );

  it("enumerates the bound of a quantifier over a lazy union as TLC does", async () => {
    const prints: string[] = [];
    const result = await checkOnEngine({
      source: `---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == (\\E <<a, b>> \\in {1, 3} \\X UNION {0..2, {1, 3}} : TRUE) /\\ x' = x\nASSUME \\A a \\in UNION {{3, 1}, 0..2} : PrintT(a)\nASSUME PrintT(CHOOSE a \\in UNION {{3}, 0..2} : TRUE)\n====`,
      config: "INIT Init\nNEXT Next",
      onPrint: (text) => prints.push(text),
    });
    expect(prints).toEqual(["0", "1", "2", "3", "0"]);
    expect(result.generatedStates).toBe(9);
  });

  it.each(["[Nat -> {}]", "[{} -> Nat]"])(
    "enumerates the sets of %s in turn as TLC does",
    async (set) => {
      const result = await checkOnEngine({
        source: `---- MODULE M ----\nEXTENDS Naturals\nASSUME \\A y \\in ${set} : TRUE\n====`,
        config: "",
      });
      expect(result.status).toBe("success");
    },
  );

  it("streams the sets that a set of tuples, records, or functions combines as TLC does", async () => {
    const result = await checkOnEngine({
      source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' \\in [b : UNION {{3, 1}, 0..1}, a : UNION {{2}, 1..2}]\n====`,
      config: "INIT Init\nNEXT Next",
    });
    expect(result.generatedStates).toBe(85);
  });

  it("decides sets of functions, records, and tuples from an empty argument", async () => {
    const result = await checkFixture("empty-sets", "EmptySets");
    expect(result.violations[0]?.headline).toBeUndefined();
    expect(result.status).toBe("success");
  });

  it("passes a string that spells an operator as a string argument", async () => {
    const texts = ["[]", "<>", "SUBSET", "UNION", "DOMAIN", "ENABLED", "UNCHANGED", "'", "^+"];
    const printed: string[] = [];
    const result = await checkOnEngine({
      source: `---- MODULE M ----\nEXTENDS TLC\n${texts.map((text) => `ASSUME PrintT("${text}")`).join("\n")}\n====`,
      config: "",
      onPrint: (text) => printed.push(text),
    });
    expect(result.status).toBe("success");
    expect(printed).toEqual(texts.map((text) => `"${text}"`));
  });

  it("checks invariants before action properties and constrained states", async () => {
    const results = await Promise.all(
      ["InvariantFirst", "ConstrainedInvariant"].map((name) =>
        checkOnEngine({
          source: readFileSync(join(FIXTURES, "ordering", "Ordering.tla"), "utf8"),
          config: readFileSync(join(FIXTURES, "ordering", `${name}.cfg`), "utf8"),
        }),
      ),
    );
    expect(
      results.map((result) => [
        result.status,
        result.violations[0]?.headline,
        result.generatedStates,
        result.distinctStates,
        result.depth,
      ]),
    ).toEqual([
      ["invariant-violation", "Invariant Small is violated.", 3, 3, 3],
      ["invariant-violation", "Invariant Small is violated.", 3, 2, 2],
    ]);
  });

  it("checks membership in a union of a non-enumerable set against the enumerable side first", async () => {
    expect((await checkModule('ASSUME 1 \\in Int \\cup {"none"}')).status).toBe(
      "assumption-violation",
    );
    expect((await checkModule("ASSUME 5 \\in UNION {Nat}")).status).toBe("success");
  });

  // TLC builds the union of two set enumerations or intervals, testing the right one's elements
  // in the left one, and otherwise tests the one it can enumerate first (OPCODE_cup).
  it.each([
    [
      '1 \\in (DOMAIN ("a" :> 0)) \\cup {1}',
      'Attempted to compare integer 1 with non-integer:\n"a"',
    ],
    [
      '1 \\in {1} \\cup (DOMAIN ("a" :> 0))',
      'Attempted to check equality of integer 1 with non-integer:\n"a"',
    ],
    [
      "1 \\in {1} \\cup (DOMAIN [a |-> 0])",
      'Attempted to check equality of integer 1 with non-integer:\n"a"',
    ],
    [
      '1 \\in (DOMAIN <<5>>) \\cup {"x"}',
      'Attempted to check if the value:\n"x"\nis in the integer interval 1..1',
    ],
    [
      '1 \\in (1..2) \\cup {"x"}',
      'Attempted to check if the value:\n"x"\nis in the integer interval 1..2',
    ],
    [
      '1 \\in ({1, 2} \\cap Nat) \\cup {"x"}',
      'Attempted to check equality of integer 1 with non-integer:\n"x"',
    ],
    [
      '{"a"} \\in {1} \\cup (SUBSET {"a"})',
      'Attempted to check equality of integer 1 with non-integer:\n{"a"}',
    ],
  ])("fails as TLC does testing %s", async (assumption, message) => {
    const result = await checkModule(`ASSUME ${assumption}`);
    expect([result.status, result.violations[0]?.headline]).toEqual([
      "assumption-violation",
      `Evaluating assumption line 6, col 8 to line 6, col ${7 + assumption.length} of module M failed.\n${message}`,
    ]);
  });

  it("tests a union with a power set, a set of records or a domain where TLC does", async () => {
    expect((await checkModule('ASSUME 1 \\in (SUBSET {"a"}) \\cup {1}')).status).toBe("success");
    expect((await checkModule("ASSUME 1 \\in [a : {1}] \\cup {1}")).status).toBe("success");
    expect((await checkModule("ASSUME 3 \\in (1..2) \\cup (DOMAIN <<5, 6, 7>>)")).status).toBe(
      "success",
    );
  });

  it("defers a set operation on a value that isn't a set until it enumerates the result", async () => {
    expect((await checkModule("ASSUME ({} \\cup 0) = 0")).status).toBe("success");
    const result = await checkModule("ASSUME Cardinality({1} \\cup 0) = 1");
    expect(result.violations[0]?.headline).toContain(
      "Attempted to enumerate S \\cup T when S:\n{1}\nand T:\n0\nare not both enumerable",
    );
  });

  it("compares power sets through their bases", async () => {
    expect((await checkModule("ASSUME SUBSET (1..23) \\subseteq SUBSET (1..42)")).status).toBe(
      "success",
    );
    expect((await checkModule("ASSUME ~(SUBSET (1..42) \\subseteq SUBSET (2..42))")).status).toBe(
      "success",
    );
    // TLC's SubsetValue.isSubsetEq compares the bases of power sets of power sets in turn.
    expect(
      (await checkModule("ASSUME SUBSET SUBSET (1..30) \\subseteq SUBSET SUBSET (0..30)")).status,
    ).toBe("success");
    expect(
      (await checkModule("ASSUME ~(SUBSET SUBSET (0..30) \\subseteq SUBSET SUBSET (1..30))"))
        .status,
    ).toBe("success");
  });

  // TLC checks this module without an error.
  it("reads each of SANY's Unicode operators as its ASCII spelling, and ℕ as a name", async () => {
    const result = await checkModule(
      [
        "a \\approx b == <<a, b>>",
        "a \\sqcup b == {a, b}",
        "a (+) b == a + b",
        "a ^+ == a + 1",
        "ℕ ≜ Nat",
        "ASSUME (1 ≈ 2) = ⟨1, 2⟩ ∧ (1 ⊔ 2) = {1, 2} ∧ (1 ⊕ 2) = 3 ∧ 3⁺ = 4",
        "ASSUME 0‥2 = {0, 1, 2} ∧ 7 ÷ 2 = 3 ∧ ⟨1⟩ ∘ ⟨2⟩ = ⟨1, 2⟩ ∧ 3 ∈ ℕ ∧ [n ∈ {1} ↦ n] = ⟨1⟩",
        "Prop ≜ □[x' = x]_x ∧ □(x ∈ ℕ) ∧ (□◇⟨x' ≠ x⟩_x ∨ x = 0)",
      ].join("\n"),
      "PROPERTY Prop",
    );
    expect(result.status).toBe("success");
  });

  it("reports a module that cannot be found as a syntax error", async () => {
    await expect(
      check({
        source: "---- MODULE M ----\nEXTENDS Missing\n====",
        config: "",
        loadModule: () => undefined,
      }),
    ).rejects.toThrow(TlaSyntaxError);
  });

  it("exposes TLC's level, counters, and registers through TLCGet and TLCSet", async () => {
    await expectDeclined(
      getFixtureOptions("runtime", "Runtime"),
      'the engine stopped: unsupported: TLCGet("diameter") in the search',
    );
    const result = await checkOnEngine({
      source: readFileSync(join(FIXTURES, "runtime", "Runtime.tla"), "utf8"),
      config: readFileSync(join(FIXTURES, "runtime", "Distinct.cfg"), "utf8"),
    });
    expect([
      result.status,
      result.generatedStates,
      result.distinctStates,
      result.depth,
      result.violations[0]?.states.map((step) => step.variables.x?.value),
    ]).toEqual<unknown[]>(["invariant-violation", 10, 6, 3, [1, 3, 5]]);
    await expectDeclined(
      {
        source: readFileSync(join(FIXTURES, "runtime", "Runtime.tla"), "utf8"),
        config: readFileSync(join(FIXTURES, "runtime", "Generated.cfg"), "utf8"),
      },
      "the engine stopped: unsupported: TLCGet of a key the search doesn't keep",
    );
  });

  it("treats Any as a set containing every value", async () => {
    expect(
      (
        await checkModule(
          'ASSUME <<1, {2}>> \\in Any /\\ [a |-> 1] \\in [a : Any] /\\ ToString(Any) = "ANY"',
        )
      ).status,
    ).toBe("success");
  });

  it("checks _POSSIBLE predicates and postconditions after the search", async () => {
    const getOptions = (name: string) => ({
      source: readFileSync(join(FIXTURES, "postconditions", "Postconditions.tla"), "utf8"),
      config: readFileSync(join(FIXTURES, "postconditions", `${name}.cfg`), "utf8"),
      onPrint: () => {},
    });
    const results = await Promise.all(
      ["Holds", "False"].map((name) => checkOnEngine(getOptions(name))),
    );
    expect(
      results.map((result) => [
        result.status,
        result.violations[0]?.headline,
        result.distinctStates,
      ]),
    ).toEqual<unknown[]>([
      ["success", undefined, 4],
      [
        "postcondition-violation",
        "Postcondition FiveStates at line 18, col 15 to line 18, col 36 of module Postconditions is false.",
        4,
      ],
    ]);
    await expectDeclined(
      getOptions("Unwitnessed"),
      "a _POSSIBLE predicate the search didn't witness",
    );
  });

  it("generates no states for a specification without variables", async () => {
    const result = await checkOnEngine({
      source: "---- MODULE M ----\nSpec == [][TRUE]_<<>>\n====",
      config: "SPECIFICATION Spec",
    });
    expect([result.status, result.generatedStates, result.distinctStates, result.depth]).toEqual([
      "success",
      0,
      0,
      0,
    ]);
  });

  it("runs only the PlusCal actions whose label guard matches, with TLC's counts", async () => {
    const result = await checkOnEngine({
      source: [
        "---- MODULE M ----",
        "EXTENDS Integers",
        "VARIABLES pc, count",
        'A(self) == pc[self] = "a" /\\ count < 3 /\\ pc\' = [pc EXCEPT ![self] = "b"] /\\ count\' = count + 1',
        'B(self) == pc[self] = "b" /\\ pc\' = [pc EXCEPT ![self] = "c"] /\\ UNCHANGED count',
        'C(self) == pc[self] = "c" /\\ pc\' = [pc EXCEPT ![self] = "a"] /\\ UNCHANGED count',
        "Reset(self) == count > 2 /\\ count' = 0 /\\ UNCHANGED pc",
        "Proc(self) == A(self) \\/ B(self) \\/ C(self)",
        'Init == pc = [p \\in {1, 2} |-> "a"] /\\ count = 0',
        "Next == \\E self \\in {1, 2} : Proc(self) \\/ Reset(self)",
        "====",
      ].join("\n"),
      config: "INIT Init\nNEXT Next",
    });
    expect([result.status, result.generatedStates, result.distinctStates, result.depth]).toEqual([
      "success",
      85,
      36,
      12,
    ]);
  });

  it("runs only the actions whose label guard after other guards matches, with TLC's counts", async () => {
    const result = await checkOnEngine({
      source: [
        "---- MODULE M ----",
        "EXTENDS Integers",
        "VARIABLES pc, count, turn",
        'A(self) == turn = self /\\ pc[self] = "a" /\\ count < 3 /\\ pc\' = [pc EXCEPT ![self] = "b"] /\\ count\' = count + 1 /\\ UNCHANGED turn',
        'B(self) == turn = self /\\ pc[self] = "b" /\\ pc\' = [pc EXCEPT ![self] = "c"] /\\ UNCHANGED <<count, turn>>',
        'C(self) == turn = self /\\ pc[self] = "c" /\\ pc\' = [pc EXCEPT ![self] = "a"] /\\ UNCHANGED count /\\ turn\' = 3 - self',
        "Reset(self) == count > 2 /\\ count' = 0 /\\ UNCHANGED <<pc, turn>>",
        "Proc(self) == A(self) \\/ B(self) \\/ C(self)",
        'Init == pc = [p \\in {1, 2} |-> "a"] /\\ count = 0 /\\ turn \\in {1, 2}',
        "Next == \\E self \\in {1, 2} : Proc(self) \\/ Reset(self)",
        "====",
      ].join("\n"),
      config: "INIT Init\nNEXT Next",
    });
    expect([result.status, result.generatedStates, result.distinctStates, result.depth]).toEqual([
      "success",
      36,
      24,
      10,
    ]);
  });

  it("reports an error in a guard before a label that doesn't match like TLC", async () => {
    const result = await checkOnEngine({
      source: [
        "---- MODULE M ----",
        "VARIABLES pc, x",
        'A(self) == x = "s" /\\ pc[self] = "b" /\\ UNCHANGED <<pc, x>>',
        'B(self) == pc[self] = "a" /\\ pc\' = [pc EXCEPT ![self] = "b"] /\\ UNCHANGED x',
        'Init == pc = [p \\in {1} |-> "a"] /\\ x = 0',
        "Next == \\E self \\in {1} : A(self) \\/ B(self)",
        "====",
      ].join("\n"),
      config: "INIT Init\nNEXT Next",
    });
    expect([result.status, result.violations[0]?.headline]).toEqual([
      "error",
      `${UNEXPECTED_EXCEPTION}Attempted to check equality of integer 0 with non-integer:\n"s"`,
    ]);
  });

  it("reports a name that is not a boolean before a label that doesn't match like TLC", async () => {
    const result = await checkOnEngine({
      source: [
        "---- MODULE M ----",
        "VARIABLES pc, x",
        'A(self) == x /\\ pc[self] = "z" /\\ UNCHANGED <<pc, x>>',
        'B(self) == pc[self] = "a" /\\ pc\' = [pc EXCEPT ![self] = "b"] /\\ UNCHANGED x',
        'Init == pc = [p \\in {1} |-> "a"] /\\ x = 0',
        "Next == \\E self \\in {1} : A(self) \\/ B(self)",
        "====",
      ].join("\n"),
      config: "INIT Init\nNEXT Next",
    });
    expect([result.status, result.violations[0]?.headline]).toEqual([
      "error",
      `${UNEXPECTED_EXCEPTION}In computing next states, TLC expected a boolean expression,\nbut instead found 0.\nline 3, col 12 to line 3, col 12 of module M`,
    ]);
  });

  it("runs every disjunct of an action before a label that doesn't match like TLC", async () => {
    const result = await checkOnEngine({
      source: [
        "---- MODULE M ----",
        "VARIABLES pc, x",
        'Ready == x = 0 \\/ x = "s"',
        'A(self) == Ready /\\ pc[self] = "z" /\\ UNCHANGED <<pc, x>>',
        'B(self) == pc[self] = "a" /\\ pc\' = [pc EXCEPT ![self] = "b"] /\\ UNCHANGED x',
        'Init == pc = [p \\in {1} |-> "a"] /\\ x = 0',
        "Next == \\E self \\in {1} : A(self) \\/ B(self)",
        "====",
      ].join("\n"),
      config: "INIT Init\nNEXT Next",
    });
    expect([result.status, result.violations[0]?.headline]).toEqual([
      "error",
      `${UNEXPECTED_EXCEPTION}Attempted to check equality of integer 0 with non-integer:\n"s"`,
    ]);
  });

  it("reports a label that is not a string where the first action compares it like TLC", async () => {
    const result = await checkOnEngine({
      source: [
        "---- MODULE M ----",
        "VARIABLE pc",
        'A(self) == pc[self] = "a" /\\ pc\' = [pc EXCEPT ![self] = 2]',
        'B(self) == pc[self] = "b" /\\ UNCHANGED pc',
        'Init == pc = [p \\in {1} |-> "a"]',
        "Next == \\E self \\in {1} : A(self) \\/ B(self)",
        "====",
      ].join("\n"),
      config: "INIT Init\nNEXT Next",
    });
    expect([result.status, result.violations[0]?.headline]).toEqual([
      "error",
      `${UNEXPECTED_EXCEPTION}Attempted to check equality of integer 2 with non-integer:\n"a"`,
    ]);
  });

  it("generates a successor for each witness of an existential under a universal action", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nWitness(i) == \\E j \\in 1..3 : j >= i\nInit == x = 0\nNext == x < 2 /\\ (\\A i \\in {1, 2} : Witness(i)) /\\ x' = x + 1\n====",
      config: "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
    });
    expect([result.generatedStates, result.distinctStates]).toEqual([13, 3]);
  });

  it("evaluates the conjuncts left once an action assigns every variable, unless warnings are off", async () => {
    const results = await Promise.all(
      [true, false].map((isWarningEnabled) =>
        checkOnEngine({
          source:
            "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nWitness(i) == \\E j \\in 1..3 : j >= i\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1 /\\ \\A i \\in {1, 2} : Witness(i)\n====",
          config: "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
          isWarningEnabled,
        }),
      ),
    );
    expect(results.map((result) => [result.generatedStates, result.distinctStates])).toEqual([
      [3, 3],
      [13, 3],
    ]);
  });

  it.each([
    ["Naturals", "{} >= 0", ">", "{}"],
    ["Integers", "{} >= 0", ">=", "{}"],
    ["Naturals, TLCExt", "{} >= 0", ">=", "{}"],
  ])(
    "names >= in an error as the Java method TLC loads with %s does",
    async (modules, assumption, name, value) => {
      const result = await checkOnEngine({
        source: `---- MODULE M ----\nEXTENDS ${modules}\nASSUME ${assumption}\n====`,
        config: "",
      });
      expect(result.violations[0]?.headline).toBe(
        getAssumptionFailure(
          3,
          assumption,
          `The first argument of ${name} should be an integer, but instead it is:\n${value}`,
        ),
      );
    },
  );

  it("declines to name >= in an error as the Java method TLC loads with Bags does", async () => {
    await expectDeclined(
      { source: '---- MODULE M ----\nEXTENDS Bags\nASSUME SubBag(<<"a">>) = {}\n====', config: "" },
      "an assumption that fails to evaluate: evaluating the assumption again: SubBag's >=, which may be Naturals' or Integers'",
    );
  });

  it("reports a depth of 1 when the constraint excludes every initial state", async () => {
    const results = await Promise.all(
      [1, 2].map((workers) =>
        checkOnEngine({
          source:
            "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 1\nNext == x' = x\nConstraint == x = 0\n====",
          config: "INIT Init\nNEXT Next\nCONSTRAINT Constraint",
          workers,
        }),
      ),
    );
    expect(
      results.map((result) => [result.generatedStates, result.distinctStates, result.depth]),
    ).toEqual([
      [1, 0, 1],
      [1, 0, 1],
    ]);
  });

  it("prints empty intervals and keys that are not field names like TLC", async () => {
    const prints: string[] = [];
    await checkOnEngine({
      source:
        '---- MODULE M ----\nEXTENDS Integers, TLC\nVARIABLE x\nASSUME PrintT(0..-2)\nASSUME PrintT(("<<>>" :> 0) @@ ("a b" :> 1))\nASSUME PrintT(("x1" :> 2) @@ ("y" :> 3))\nASSUME PrintT("x\u00b2" :> 4)\nInit == x = 0\nNext == UNCHANGED x\n====',
      config: "INIT Init\nNEXT Next",
      onPrint: (text) => prints.push(text),
    });
    expect(prints).toEqual([
      "{}",
      '("<<>>" :> 0 @@ "a b" :> 1)',
      "[x1 |-> 2, y |-> 3]",
      '("x\u00b2" :> 4)',
    ]);
  });

  // TLC prints "x\u0663" :> 5 as the record [x\u0663 |-> 5]: Java's Character takes the Arabic-Indic
  // digit for a digit, which the engine doesn't know past Latin-1.
  it("declines a key whose letters Unicode's categories decide", async () => {
    await expectDeclined(
      getModuleOptions('ASSUME PrintT("x\u0663" :> 5)'),
      "printing a value whose text depends on how TLC built it",
    );
  });

  it("orders and compares intervals by size and then low bound like TLC", async () => {
    const prints: string[] = [];
    await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Integers, FiniteSets, TLC\nVARIABLE x\nASSUME PrintT(<<{2..3, 1..3, 3..2, 1..0, 0..1, 5..4}, 1..3 = 1..3, 3..2 = 1..0, 1..2 = 2..3, Cardinality({1..0, 3..2}), [1..2 -> {0}] \\subseteq [1..2 -> {0, 1}]>>)\nInit == x = 0\nNext == UNCHANGED x\n====",
      config: "INIT Init\nNEXT Next",
      onPrint: (text) => prints.push(text),
    });
    expect(prints).toEqual(["<<{{}, 0..1, 2..3, 1..3}, TRUE, TRUE, FALSE, 1, TRUE>>"]);
  });

  it("bundles the Reals module, whose Real is not a set TLC can check", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Reals, Toolbox\nVARIABLE x\nASSUME 1 \\in Real\nInit == x = 0\nNext == x' = x\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect(result.status).toBe("assumption-violation");
  });

  it("fingerprints states by their VIEW and keeps the fair steps it hides", async () => {
    const result = await checkFixture("view", "View");
    expect([result.status, result.generatedStates, result.distinctStates, result.depth]).toEqual([
      "success",
      5,
      4,
      4,
    ]);
  });

  // A1 reaches a state with the same VIEW as the successor of A2 that violates the property.
  it("labels the successor that violates an action property by its values under a VIEW", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nVARIABLES x, y\nInit == x = 0 /\\ y = 0\nA1 == x' = x /\\ y' = y\nA2 == x' = x /\\ y' = 1\nSpec == Init /\\ [][A1 \\/ A2]_<<x, y>>\nP == [][y' = y]_<<x, y>>\nView == x\n====",
      config: "SPECIFICATION Spec\nPROPERTY P\nVIEW View",
    });
    expect(result.violations[0]?.states.map((step) => step.label)).toEqual([
      "Initial predicate",
      "A2 line 5, col 7 to line 5, col 22 of module M",
    ]);
  });

  // TLC's output for each config.
  it.each([
    [
      "VIEW View",
      ["([b |-> 0, a |-> 0] :> 1)", "([b |-> 0, a |-> 0] :> 1)", "([a |-> 1, b |-> 1] :> 1)"],
    ],
    [
      "VIEW ViewOfS",
      ["([a |-> 0, b |-> 0] :> 1)", "([a |-> 0, b |-> 0] :> 1)", "([a |-> 1, b |-> 1] :> 1)"],
    ],
    [
      "SYMMETRY Symmetry",
      ["([a |-> 0, b |-> 0] :> 1)", "([a |-> 0, b |-> 0] :> 1)", "([a |-> 1, b |-> 1] :> 1)"],
    ],
  ])("prints the records of a trace under %s in the order TLC sorts them", async (reduction, s) => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals, TLC\nCONSTANT P\nVARIABLES x, r, s, t\nGet(v) == v.a + v.b\nInit == x = 0 /\\ r = [b |-> 0, a |-> 0] /\\ s = ([b |-> 0, a |-> 0] :> 1) /\\ t = {[b |-> 1, a |-> 1]}\nNext == x < 2 /\\ x' = x + 1 /\\ r' = [b |-> x, a |-> x] /\\ s' = ([b |-> x, a |-> x] :> 1) /\\ t' = {[b |-> x, a |-> 1]}\nView == x\nViewOfS == <<x, s>>\nSymmetry == Permutations(P)\nInv == x < 2\n====",
      config: `CONSTANT P = {p1, p2}\nINIT Init\nNEXT Next\nINVARIANT Inv\n${reduction}`,
    });
    expect(
      result.violations[0]?.states.map((step) =>
        ["r", "s", "t"].map((name) => step.variables[name]?.text),
      ),
    ).toEqual([
      ["[a |-> 0, b |-> 0]", s[0], "{[a |-> 1, b |-> 1]}"],
      ["[a |-> 0, b |-> 0]", s[1], "{[a |-> 1, b |-> 0]}"],
      ["[a |-> 1, b |-> 1]", s[2], "{[a |-> 1, b |-> 1]}"],
    ]);
  });

  it("evaluates a VIEW on the symmetry representative TLC picks by its variable order", async () => {
    const result = await checkFixture("view", "ViewSymmetry");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([7, 4, 4]);
  });

  it("orders model values, strings, and record fields like TLC when picking a representative", async () => {
    const result = await checkFixture("view", "ViewSymmetryOrder");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([139, 14, 3]);
  });

  it("ranks a string literal as written where SANY parses it", async () => {
    const printed: string[] = [];
    await checkOnEngine({
      source:
        '---- MODULE M ----\nEXTENDS TLC\nVARIABLE x\nA == "b"\nB == "a"\nASSUME PrintT({ToString("a"), ToString("b")})\nInit == x = 0\nNext == UNCHANGED x\n====',
      config: "INIT Init\nNEXT Next",
      onPrint: (text) => printed.push(text),
    });
    expect(printed).toEqual(['{"\\"b\\"", "\\"a\\""}']);
  });

  it("declines to order strings, record fields, and model values by when TLC interns them", async () => {
    await expectDeclined(
      { ...getFixtureOptions("strings", "StringOrder"), onPrint: () => {} },
      "the engine stopped: an invariant violated",
    );
  });

  it.each(["UnicodeStringFingerprint", "UnicodeRecordFingerprint", "UnicodeFunctionFingerprint"])(
    "merges states whose strings differ only above U+00FF like TLC's fingerprint in %s",
    async (name) => {
      const result = await checkFixture("strings", name);
      expect([result.generatedStates, result.distinctStates]).toEqual([3, 1]);
    },
  );

  it("computes TLCFP with TLC's fingerprint", async () => {
    const result = await checkOnEngine({
      source: `---- MODULE M ----
EXTENDS Integers, TLCExt
CONSTANT a
ASSUME TLCFP(1) = -1504394061
ASSUME TLCFP("m1") = 952772174
ASSUME TLCFP(<<1, "m1", TRUE>>) = -1323233619
ASSUME TLCFP([f |-> {a}]) = 820346972
ASSUME TLCFP(a) = -887695703
====`,
      config: "CONSTANT a = a",
    });
    expect(result.status).toBe("success");
  });

  it("lists a trace's variables in TLC's order", async () => {
    const result = await checkOnEngine({
      source: readFileSync(join(FIXTURES, "randomization", "RandomModelValue.tla"), "utf8"),
      config: readFileSync(join(FIXTURES, "randomization", "RandomModelValue.cfg"), "utf8"),
    });
    expect(Object.keys(result.violations[0]?.states[0]?.variables ?? {})).toEqual([
      "owner",
      "zeta",
    ]);
  });

  it("explores states that depend on the order of strings in CHOOSE", async () => {
    const result = await checkFixture("strings", "StringSets");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([76, 31, 5]);
  });

  it("declines to rank strings created while checking in the order they are created", async () => {
    await expectDeclined(
      getFixtureOptions("strings", "RuntimeStrings"),
      "the engine stopped: an order of strings the search made",
    );
  });

  it("does not carry one check's string order into the next", async () => {
    const earlier = await checkModule(
      'Picked == CHOOSE s \\in {"zzq", "aaq"} : TRUE\nASSUME Picked = "zzq"',
    );
    expect(earlier.status).toBe("success");
    const reversed = await checkModule(
      'ASSUME "aaq" # "zzq"\nASSUME (CHOOSE s \\in {"zzq", "aaq"} : TRUE) = "aaq"',
    );
    expect(reversed.status).toBe("success");
    expect((await checkFixture("strings", "StringSets")).distinctStates).toBe(31);
  });

  it("declines a lasso under VIEW that cannot be rebuilt from fingerprints", async () => {
    await expectDeclined(
      getFixtureOptions("view", "Recover"),
      "no step from state 3 is the trace's next",
    );
  });

  it("enumerates subsets for x \\subseteq S in the initial predicate and next-state relation", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nVARIABLE x\nInit == x \\subseteq {1, 2}\nNext == x' \\subseteq {1, 2, 3}\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect([result.status, result.generatedStates, result.distinctStates, result.depth]).toEqual([
      "success",
      68,
      8,
      2,
    ]);
  });

  it("assigns operator constants from tables in the configuration", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nCONSTANT F(_)\nVARIABLE x\nInit == x = 0\nNext == x' = F(x)\nInv == x /= 2\n====",
      config: "INIT Init\nNEXT Next\nCONSTANT\n  F(0) = 1\n  F(1) = 2\n  F(2) = 2\nINVARIANT Inv",
    });
    expect([
      result.status,
      result.violations[0]?.states.map((step) => step.variables.x?.value),
    ]).toEqual(["invariant-violation", [0, 1, 2]]);
  });

  it("declines to convert values to JSON as TLC's Json module does", async () => {
    const assumptions = [
      'ToJson(<<3, 2, 1>>) = "[3,2,1]"',
      'ToJson({3, 2, 1}) = "[1,2,3]"',
      'ToJsonObject([a |-> TRUE, b |-> FALSE]) = "{\\"a\\":true,\\"b\\":false}"',
      'ToJson(3 :> "c" @@ 2 :> "b" @@ 1 :> "a") = "[\\"a\\",\\"b\\",\\"c\\"]"',
      'ToJson([n \\in {3, 2, 1} |-> 2 * n + 1]) = "[3,5,7]"',
      'ToJsonArray({}) = "[]"',
    ];
    await expectDeclined(
      {
        source: `---- MODULE M ----\nEXTENDS Integers, TLC, Json\nVARIABLE x\n${assumptions.map((assumption) => `ASSUME ${assumption}`).join("\n")}\nInit == x = 0\nNext == x' = x\n====`,
        config: "INIT Init\nNEXT Next",
      },
      "an assumption that fails to evaluate: evaluating the assumption again: the builtin ToJson",
    );
  });

  it.each(["Extensions", "ExtensionsShort"])(
    "declines the TLCExt operators of the %s config",
    async (name) => {
      await expectDeclined(
        {
          source: readFileSync(join(FIXTURES, "runtime", "Extensions.tla"), "utf8"),
          config: readFileSync(join(FIXTURES, "runtime", `${name}.cfg`), "utf8"),
        },
        "an assumption that fails to evaluate: evaluating the assumption again: the builtin AssertEq",
      );
    },
  );

  it("rejects comparisons of differently-typed model values", async () => {
    const result = await checkOnEngine({
      source:
        '---- MODULE M ----\nEXTENDS TLCExt\nVARIABLE v\nInit == v = {TLCModelValue("A_a"), TLCModelValue("B_a")}\nNext == UNCHANGED v\n====',
      config: "INIT Init\nNEXT Next",
    });
    expect(result.violations[0]?.headline).toContain(
      "Attempted to compare the differently-typed model values B_a and A_a",
    );
  });

  it("explores the mutex state space", async () => {
    const result = await checkFixture("mutex", "Mutex");
    expect(result.status).toBe("success");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([18, 10, 4]);
  });

  it("explores a commit protocol over model values", async () => {
    const result = await checkFixture("commit", "Commit");
    expect(result.status).toBe("success");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([890, 251, 11]);
  });

  it("stops exploring states that fail a constraint", async () => {
    const result = await checkFixture("queue", "Queue");
    expect(result.status).toBe("success");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([181, 105, 9]);
  });

  it("reports the shortest trace to an invariant violation", async () => {
    const result = await checkFixture("water-jugs", "WaterJugs");
    expect(result.status).toBe("invariant-violation");
    expect(result.violations[0]?.headline).toBe("Invariant GoalNotReached is violated.");
    const trace = result.violations[0]?.states ?? [];
    expect(trace).toHaveLength(7);
    expect(trace[0]?.label).toBe("Initial predicate");
    expect(trace[6]?.variables.large?.text).toBe("4");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([73, 14, 7]);
  });

  it("reports a membership invariant that one changed entry violates", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Integers\nVARIABLE f\nInit == f = [p \\in 1..2 |-> [q \\in 1..2 |-> 0]]\nNext == \\E p, q \\in 1..2 : f' = [f EXCEPT ![p][q] = @ + 1]\nTypeOK == f \\in [1..2 -> [1..2 -> 0..2]]\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT TypeOK",
    });
    expect(result.violations[0]?.headline).toBe("Invariant TypeOK is violated.");
    const trace = result.violations[0]?.states ?? [];
    expect(trace.at(-1)?.variables.f?.text).toBe("<<<<3, 0>>, <<0, 0>>>>");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([22, 16, 4]);
  });

  it("labels each step with the action TLC splits the next-state relation into", async () => {
    const getLabels = async (definitions: string, config = "INIT Init\nNEXT Next") => {
      const result = await checkOnEngine({
        source: `---- MODULE M ----\nEXTENDS Integers, TLC\nVARIABLE x\nInit == x = 0\n${definitions}\nInv == x < 2\n====`,
        config: `${config}\nINVARIANT Inv`,
      });
      return result.violations[0]?.states.map((step) => step.label);
    };
    expect(await getLabels("A(i) == x' = x + i\nNext == \\E i \\in {1, 2} : A(i)")).toEqual([
      "Initial predicate",
      "A(2) line 5, col 9 to line 5, col 18 of module M",
    ]);
    expect(await getLabels("Next == x' = x + 1 \\/ x' = x + 2")).toEqual([
      "Initial predicate",
      "Next line 5, col 23 to line 5, col 32 of module M",
    ]);
    expect(await getLabels("Spec == Init /\\ [][x' = x + 1]_x", "SPECIFICATION Spec")).toEqual([
      "Initial predicate",
      "Action line 5, col 20 to line 5, col 29 of module M",
      "Action line 5, col 20 to line 5, col 29 of module M",
    ]);
  });

  // TLC's labels: a SPECIFICATION that an INSTANCE substitutes into is one unnamed action.
  it.each([
    ["Spec", "Action line 4, col 1 to line 4, col 14 of module M"],
    ["OwnSpec", "Next line 4, col 1 to line 4, col 14 of module M"],
    ["NamedSpec", "Action line 7, col 1 to line 7, col 19 of module M"],
  ])("labels the steps of SPECIFICATION %s through an INSTANCE like TLC", async (spec, label) => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nINSTANCE Inner\nInv == x < 2\nOwnSpec == Init /\\ [][Next]_x\nI == INSTANCE Inner\nNamedSpec == I!Spec\n====",
      config: `SPECIFICATION ${spec}\nINVARIANT Inv`,
      loadModule: (name) =>
        name === "Inner"
          ? "---- MODULE Inner ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1 \\/ x' = x + 2\nSpec == Init /\\ [][Next]_x\n===="
          : undefined,
    });
    expect(result.violations[0]?.states.map((step) => step.label)).toEqual([
      "Initial predicate",
      label,
    ]);
  });

  it("labels steps after evaluating the initial predicate again like TLC", async () => {
    const result = await checkFixture("tlc-get-non-determinism", "TLCGetNonDeterminism");
    expect(result.violations[0]?.states.map((step) => step.label)).toEqual([
      "Initial predicate",
      ...Array.from(
        { length: 3 },
        () => "Next line 23, col 9 to line 26, col 25 of module TLCGetNonDeterminism",
      ),
    ]);
  });

  it("counts the states left on the queue when a violation stops the search", async () => {
    const result = await checkFixture("water-jugs", "WaterJugs");
    expect(result.queuedStates).toBe(1);
  });

  it("reports deadlock with the trace that reaches it", async () => {
    const result = await checkFixture("counter", "Counter");
    expect(result.status).toBe("deadlock");
    expect(result.violations[0]?.states.map((step) => step.label)).toEqual([
      "Initial predicate",
      "Increment line 10, col 14 to line 11, col 34 of module Counter",
      "Increment line 10, col 14 to line 11, col 34 of module Counter",
      "Increment line 10, col 14 to line 11, col 34 of module Counter",
    ]);
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([4, 4, 4]);
  });

  it("stops computing ENABLED at the first successor like TLC", async () => {
    const printed: string[] = [];
    const result = await checkOnEngine({
      source:
        '---- MODULE M ----\nEXTENDS TLC\nVARIABLE x\nInit == x = 0\nNext == UNCHANGED x\nInv == ENABLED (x\' = 1 \\/ (PrintT("second") /\\ Assert(FALSE, "boom")))\n====',
      config: "INIT Init\nNEXT Next\nINVARIANT Inv",
      onPrint: (text) => printed.push(text),
    });
    expect(result.status).toBe("success");
    expect(printed).toEqual([]);
  });

  it("stops branching on initial conjuncts once every variable is assigned", async () => {
    const result = await checkFixture("initial-states", "InitialStates");
    expect(result.status).toBe("success");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([5, 2, 1]);
  });

  it("assigns variables through definitions, parameters, function applications, and <<A>>_v", async () => {
    const result = await checkFixture("assignments", "Assignments");
    expect(result.status).toBe("success");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([98, 24, 5]);
  });

  it("assigns a primed variable passed as an operator argument", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x, y\nSend(p, old, new) == new = p\nInit == x = 0 /\\ y = 0\nNext == \\E p \\in {1, 2} : Send(p, x, x') /\\ y' = y\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect([result.status, result.generatedStates, result.distinctStates]).toEqual([
      "success",
      7,
      3,
    ]);
  });

  it("reduces states under a symmetry set", async () => {
    const result = await checkFixture("symmetry", "Symmetry");
    expect(result.status).toBe("success");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([42, 10, 7]);
  });

  it("reduces a set of records that a permutation partly moves", async () => {
    const result = await checkFixture("symmetry", "SymmetricMessages");
    expect(result.status).toBe("success");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([641, 80, 9]);
  });

  it("checks liveness on the symmetry-reduced graph", async () => {
    const result = await checkFixture("symmetry", "SymmetricLiveness");
    expect(result.status).toBe("liveness-violation");
    expect(result.violations[0]?.headline).toBe("Temporal property Live was violated.\n");
    expect(result.violations[0]?.states.map((step) => step.variables.x?.value)).toEqual([
      { "@model": "m1" },
    ]);
  });

  it("reports a symmetry that names a constant like TLC", async () => {
    await expect(checkModule("CONSTANT P", "CONSTANT P = {p1, p2}\nSYMMETRY P")).rejects.toThrow(
      new TlaEvaluationError(
        `${UNEXPECTED_EXCEPTION}The symmetry function P must specify a set of permutations.`,
      ),
    );
  });

  it("rebuilds a step under symmetry from the first action that takes it as TLC does", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals, Sequences, TLC\nCONSTANTS p1, p2\nVARIABLES x, y\nInit == x = 0 /\\ y = 0\nA1 == y' = 1 /\\ x' = x\nA2 == y' = Head(<<>>) /\\ x' = x\nSpec == Init /\\ [][A1 \\/ A2]_<<x, y>>\nProp == [][x' # x]_<<x, y>>\nSym == Permutations({p1, p2})\n====",
      config: "CONSTANTS p1 = p1 p2 = p2\nSPECIFICATION Spec\nPROPERTY Prop\nSYMMETRY Sym",
    });
    expect(result.status).toBe("liveness-violation");
    expect(
      result.violations[0]?.states.map((step) => [step.label, step.variables.y?.text]),
    ).toEqual([
      ["Initial predicate", "0"],
      ["A1 line 6, col 7 to line 6, col 22 of module M", "1"],
    ]);
  });

  it.each([
    ["<>(\\E k \\in {} : x = 0) /\\ <>(\\E k \\in {} : x = 0)", 1],
    ["<>(IF TRUE THEN TRUE ELSE x = 0) /\\ <>(IF TRUE THEN TRUE ELSE x = 0)", 1],
    [
      "<>(\\E k \\in {1} : \\E j \\in {} : x = k) /\\ <>(\\E k \\in {1} : \\E j \\in {} : x = k)",
      2,
    ],
  ])("finds the branches of %s like TLC", async (property, branches) => {
    const progress: CheckProgress[] = [];
    await checkOnEngine({
      source: `---- MODULE M ----\nVARIABLE x\nInit == x = 0\nNext == x' = x\nProp == ${property}\n====`,
      config: "INIT Init\nNEXT Next\nPROPERTY Prop",
      onProgress: (event) => {
        if (event.kind === "liveness-prepared") progress.push(event);
      },
    });
    expect(progress).toEqual([{ kind: "liveness-prepared", branches }]);
  });

  it("warns about a permuted set with fewer than two elements", async () => {
    const warnings: CheckProgress[] = [];
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS TLC\nCONSTANTS S, T\nVARIABLE x\nInit == x = 0\nNext == x' = x\nSym == Permutations(S) \\cup Permutations(T)\n====",
      config: "CONSTANTS S = {s1, s2}\nT = {t1}\nINIT Init\nNEXT Next\nSYMMETRY Sym",
      onProgress: (progress) => {
        if (progress.kind === "warning") warnings.push(progress);
      },
    });
    expect(result.status).toBe("success");
    expect(warnings).toEqual([
      {
        kind: "warning",
        code: 2300,
        text: "The set T has been defined to be a symmetry set but contains less than two elements.",
      },
    ]);
  });

  it("rejects substituting a constant with a state-level definition", async () => {
    await expect(checkModule("CONSTANT C\nFoo == x", "CONSTANT C <- Foo")).rejects.toThrow(
      TlaConfigError,
    );
    expect((await checkModule("CONSTANT C\nFoo == 1", "CONSTANT C <- Foo")).status).toBe("success");
    // TLC rejects a state-level substitute only when evaluating it at startup fails.
    await expectDeclined(
      getModuleOptions('CONSTANT C\nFoo == TLCGet("level")', "CONSTANT C <- Foo"),
      "a configuration substitute with effects, which TLC evaluates at every use: C <- Foo",
    );
    await expect(
      checkModule('CONSTANT C\nFoo == TLCGet("diameter")', "CONSTANT C <- Foo"),
    ).rejects.toThrow(TlaConfigError);
    await expectDeclined(
      getModuleOptions("CONSTANT C\nFoo == RandomElement({1})", "CONSTANT C <- Foo"),
      "a configuration substitute with effects, which TLC evaluates at every use: C <- Foo",
    );
  });

  it("checks a model with a substitute that JsonDeserialize defines, which nothing reads", async () => {
    const result = await checkOnEngine({
      source:
        '---- MODULE M ----\nEXTENDS Json\nCONSTANT C\nVARIABLE x\nTrace == JsonDeserialize("missing.json")\nInit == x = 0\nNext == x\' = x\n====',
      config: "CONSTANT C <- Trace\nINIT Init\nNEXT Next",
    });
    expect([result.status, result.generatedStates, result.distinctStates]).toEqual([
      "success",
      2,
      1,
    ]);
  });

  it("overrides definitions and ignores undeclared names assigned by the configuration", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x \\in Nat \\cap {0, 9}\nNext == x' = x\n====",
      config: "CONSTANT Foo = 1\nCONSTANT Nat = {0, 1}\nINIT Init\nNEXT Next",
    });
    expect([result.status, result.generatedStates, result.distinctStates]).toEqual([
      "success",
      2,
      1,
    ]);
  });

  it("substitutes infix operator constants", async () => {
    const result = await checkModule(
      "CONSTANT _++_\nPlusPlus(a, b) == <<a, b>>\nASSUME (1 ++ 2) = <<1, 2>>",
      "CONSTANT ++ <- PlusPlus",
    );
    expect(result.status).toBe("success");
  });

  it("follows definition overrides inside the specification", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nVARIABLE x\nInit == x = 0\nMCInit == x = 1\nSpec == Init /\\ [][x' = x]_x\nInv == x = 1\n====",
      config: "CONSTANT Init <- MCInit\nSPECIFICATION Spec\nINVARIANT Inv",
    });
    expect(result.status).toBe("success");
    expect([result.generatedStates, result.distinctStates]).toEqual([2, 1]);
  });

  it("checks the Github687spec configs from TLC's tests", async () => {
    const getOptions = (name: string) => ({
      source: readFileSync(join(FIXTURES, "github687", "Github687spec.tla"), "utf8"),
      config: readFileSync(join(FIXTURES, "github687", `Github687spec${name}.cfg`), "utf8"),
    });
    expect(
      await Promise.all(
        ["A", "B", "C", "InitNext", "Prime"].map(async (name) => {
          const result = await checkOnEngine(getOptions(name));
          return [result.status, result.generatedStates, result.distinctStates];
        }),
      ),
    ).toEqual([
      ["success", 21, 7],
      ["success", 14, 7],
      ["success", 21, 7],
      ["success", 21, 7],
      ["liveness-violation", 14, 7],
    ]);
    await expect(checkOnEngine(getOptions("D"))).rejects.toThrow(
      new TlaConfigError("The spec is trivially false because ModInsanityCheck is false."),
    );
  });

  it("rejects constant conjuncts of the specification and properties that aren't TRUE", async () => {
    const getOptions = (definitions: string, config: string) => ({
      source: `---- MODULE M ----\nEXTENDS Naturals\nCONSTANT C\nVARIABLE x\nInit == x = 0\nNext == x' = 1 - x\nTrue == 1 < 2\nFalse == 1 > 2\nFive == 5\n${definitions}\n====`,
      config: `CONSTANT C = FALSE\n${config}`,
    });
    const checkSpec = (definitions: string, config: string) =>
      checkOnEngine(getOptions(definitions, config));
    const base = "Spec == Init /\\ [][Next]_x";
    expect(
      (await checkOnEngine(getOptions(`${base} /\\ TRUE /\\ True`, "SPECIFICATION Spec")))
        .generatedStates,
    ).toBe(3);
    await expect(checkSpec(`${base} /\\ FALSE`, "SPECIFICATION Spec")).rejects.toThrow(
      new TlaConfigError("The spec is trivially false because FALSE is false."),
    );
    await expect(checkSpec(`${base} /\\ C`, "SPECIFICATION Spec")).rejects.toThrow(
      new TlaConfigError("The spec is trivially false because C is false."),
    );
    await expect(checkSpec(`${base} /\\ Five`, "SPECIFICATION Spec")).rejects.toThrow(
      new TlaConfigError("The operator Five, which equals 5,\ncannot be used as a spec"),
    );
    const getPropertyOptions = (property: string) =>
      getOptions(
        `${base}\nProp == [](x \\in {0, 1}) /\\ ${property}`,
        "SPECIFICATION Spec\nPROPERTY Prop",
      );
    const checkProperty = (property: string) => checkOnEngine(getPropertyOptions(property));
    expect((await checkOnEngine(getPropertyOptions("True"))).status).toBe("success");
    await expect(checkProperty("False")).rejects.toThrow(
      new TlaConfigError("The spec is trivially false because False is false."),
    );
    await expect(checkProperty("Five")).rejects.toThrow(
      new TlaConfigError("The operator Five, which equals 5,\ncannot be used as a property"),
    );
  });

  it.each([
    "Prop == LET E == {x} IN [](\\A e \\in E : e < 1)",
    "Holds(S) == [](\\A e \\in S : e < 1)\nProp == Holds({x})",
  ])("checks a []P property whose LET or argument reads a variable: %s", async (property) => {
    const result = await checkOnEngine({
      source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1\nSpec == Init /\\ [][Next]_x\n${property}\n====`,
      config: "SPECIFICATION Spec\nPROPERTY Prop\nCHECK_DEADLOCK FALSE",
    });
    expect([result.status, result.generatedStates, result.distinctStates]).toEqual([
      "invariant-violation",
      2,
      2,
    ]);
  });

  it.each([
    [
      "Bad(r) == r \\div 0 = 1\nNext == \\E m \\in {}, r \\in {1} : Bad(r) /\\ x' = m",
      "deadlock",
      1,
      1,
    ],
    [
      "Ok(r) == r # x\nNext == \\E m \\in 1..2, r \\in 0..2 : Ok(r) /\\ x < 3 /\\ x' = (m + r) % 4",
      "success",
      13,
      4,
    ],
  ])(
    "checks the guards of a multi-bound \\E that read only the outer bound: %s",
    async (next, status, generatedStates, distinctStates) => {
      const result = await checkOnEngine({
        source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\n${next}\n====`,
        config: `INIT Init\nNEXT Next${status === "success" ? "\nCHECK_DEADLOCK FALSE" : ""}`,
      });
      expect([result.status, result.generatedStates, result.distinctStates]).toEqual<unknown[]>([
        status,
        generatedStates,
        distinctStates,
      ]);
    },
  );

  it("names the source of each set whose method failed when it replays a step", () => {
    const run = runOnEngine({
      source:
        "---- MODULE M ----\nVARIABLE x\nInit == x = 0\nNext == x' = IF {x} \\subseteq {{}} THEN 1 ELSE 2\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect(getFingerprintFailure(run.output)).toEqual({
      frames: [
        "0. Line 4, column 9 to line 4, column 48 in M",
        "1. Line 4, column 14 to line 4, column 48 in M",
        "2. Line 4, column 17 to line 4, column 34 in M",
        "3. Line 4, column 17 to line 4, column 19 in M",
        "4. Line 4, column 31 to line 4, column 34 in M",
        "5. Line 4, column 32 to line 4, column 33 in M",
      ],
      reason: "Attempted to check equality of the set {} with the value:\n0",
    });
  });

  it("applies an operator to each value @ takes in the same state", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE f\nInc(n) == n + 1\nBump(g, k) == [g EXCEPT ![k] = Inc(@)]\nInit == f = <<1, 2>>\nNext == f[1] < 3 /\\ f' = Bump(Bump(f, 1), 2)\nInv == f[2] = f[1] + 1\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE",
    });
    expect(result.status).toBe("success");
    expect([result.generatedStates, result.distinctStates]).toEqual([3, 3]);
  });

  it("reports an undefined symmetry and one that isn't a set of permutations like TLC", async () => {
    await expect(checkModule("", "SYMMETRY P")).rejects.toThrow(
      new TlaConfigError(
        "The symmetry function P specified in the configuration file\nis not defined in the specification.",
      ),
    );
    for (const [definition, message] of [
      ["P == 1", "The symmetry operator must specify a set of functions."],
      ["P == {1}", "The symmetry values must be function records."],
    ]) {
      await expect(checkModule(definition, "SYMMETRY P")).rejects.toThrow(
        new TlaEvaluationError(`${UNEXPECTED_EXCEPTION}${message}`),
      );
    }
    await expectDeclined(
      getModuleOptions("P(a) == a", "SYMMETRY P"),
      "a SYMMETRY definition with parameters",
    );
  });

  it("reports a failing constant part of a property while processing the spec like TLC", async () => {
    const properties = [
      "<>(1 = {})",
      "<>[](x = 2 => 1 = {})",
      "<>[](IF x = 1 THEN x = 2 ELSE 1 = {})",
    ];
    for (const property of properties) {
      await expect(
        checkOnEngine({
          source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 3\nSpec == Init /\\ [][Next]_x\nProp == ${property}\n====`,
          config: "SPECIFICATION Spec\nPROPERTY Prop",
        }),
      ).rejects.toThrow(
        new TlaEvaluationError(
          `${UNEXPECTED_EXCEPTION}Attempted to check equality of integer 1 with non-integer:\n{}`,
        ),
      );
    }
  });

  it("reports the unassigned constant TLC finds first", async () => {
    const cases = [
      [
        "CONSTANT TableId\nCONSTANT Snapshot\nCONSTANT BranchId",
        "CONSTANT TableId = 1",
        "BranchId",
      ],
      ["CONSTANTS Zeta, Alpha, Mid, N", "CONSTANT Mid = 1", "Zeta"],
      ["CONSTANTS N, Procs, Values, Acceptors, Quorums", "CONSTANT Procs = 1", "Quorums"],
    ];
    for (const [body, config, name] of cases) {
      await expect(checkModule(body, config)).rejects.toThrow(
        new TlaConfigError(
          `The constant parameter ${name} is not assigned a value by the configuration file.`,
        ),
      );
    }
  });

  it("names why a state-level substitute failed like TLC", async () => {
    await expect(
      checkModule(
        "CONSTANT C\nFoo == IF CHOOSE n \\in {} : TRUE THEN x ELSE x",
        "CONSTANT C <- Foo",
      ),
    ).rejects.toThrow(
      new TlaConfigError(
        "The configuration file substitutes constant C with non-constant Foo - specifically: Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\nline 7, col 11 to line 7, col 32 of module M",
      ),
    );
    await expect(
      checkModule("CONSTANT C\nFoo == (1 \\div 0) + x", "CONSTANT C <- Foo"),
    ).rejects.toThrow(
      new TlaConfigError("The configuration file substitutes constant C with non-constant Foo"),
    );
  });
});

describe("formatValue matches TLC", () => {
  it("prints functions as records only when every key is a field name", async () => {
    const printed: string[] = [];
    const result = await checkOnEngine({
      source: readFileSync(join(FIXTURES, "formatting", "Format.tla"), "utf8"),
      config: readFileSync(join(FIXTURES, "formatting", "Format.cfg"), "utf8"),
      onPrint: (text) => printed.push(text),
    });
    expect(result.status).toBe("success");
    expect(printed).toEqual(
      readFileSync(join(FIXTURES, "formatting", "Format.out"), "utf8")
        .trim()
        .split("\n"),
    );
  });

  it("prints an empty function that isn't a tuple like TLC", async () => {
    const printed: string[] = [];
    await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Integers, Sequences, TLC\nE == [k \\in {} |-> k]\nASSUME \\A i \\in 1..5 : PrintT(<<[k \\in 1..0 |-> k], E @@ E, Tail(<<1>>), E \\o E, <<E>>>>[i])\n====",
      config: "",
      onPrint: (text) => printed.push(text),
    });
    expect(printed).toEqual(["<<>>", "<<>>", "<<>>", "<<>>", "<<<<>>>>"]);
  });

  it("prints a record whatever its fields, and a function with a key that isn't a name like TLC", async () => {
    const printed: string[] = [];
    await checkOnEngine({
      source:
        '---- MODULE M ----\nEXTENDS TLC\nASSUME PrintT(<<[_ |-> 1], [[_ |-> 1] EXCEPT !._ = 2], "_" :> 1, [_ |-> 1] @@ [b |-> 2]>>)\n====',
      config: "",
      onPrint: (text) => printed.push(text),
    });
    expect(printed).toEqual(['<<[_ |-> 1], [_ |-> 2], ("_" :> 1), ("_" :> 1 @@ "b" :> 2)>>']);
  });
});

const getStepsOptions = (definitions: string, config: string) => ({
  source: `---- MODULE M ----\nEXTENDS Integers, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\n${definitions}\n====`,
  config,
});

const checkStepsOnEngine = (definitions: string, config: string) =>
  checkOnEngine(getStepsOptions(definitions, config));

const getStepsRun = (definitions: string, config: string, args?: string[]): TlcRunOptions => ({
  source: `---- MODULE M ----\nEXTENDS Integers, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\n${definitions}\n====`,
  config,
  args,
});

// TLC's report of an assumption, written with its ASSUME at `line`, that fails to evaluate.
const getAssumeFailure = (line: number, assume: string, message: string) => {
  const before = assume.slice(0, assume.length - assume.slice("ASSUME".length).trimStart().length);
  const start = before.split("\n");
  const lines = assume.split("\n");
  const end = lines.length === 1 ? assume.length : (lines.at(-1) ?? "").length;
  return `Evaluating assumption line ${line + start.length - 1}, col ${(start.at(-1) ?? "").length + 1} to line ${line + lines.length - 1}, col ${end} of module M failed.\n${message}`;
};

describe("evaluation errors match TLC", () => {
  // TLC words these by the Java class of the function, which follows how the spec built it.
  it.each([
    ['IF "a" :> 1 THEN 1 ELSE 2', "(a function  of the form (d1 :> e1 @@ ... @@ dN :> eN))"],
    ["IF [a |-> 1] THEN 1 ELSE 2", "(a record)"],
    ["IF <<1, 2>> THEN 1 ELSE 2", "(a tuple)"],
    [
      '1 \\in ("a" :> 1)',
      "Attempted to check if the value:\n1\nis an element of the function [a |-> 1]",
    ],
    [
      "1 \\in [k \\in {} |-> k]",
      "Attempted to check if the value:\n1\nis an element of the function <<>>",
    ],
    ["1 \\in [a |-> 1]", "Attempted to check if element:\n1\nis in the record:\n[a |-> 1]"],
    ["1 \\in <<1>>", "Attempted to check set membership in a tuple value."],
  ])("words the function in %s like TLC", async (expression, message) => {
    const result = await checkOnEngine({
      source: `---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = x /\\ (${expression}) = TRUE\n====`,
      config: "INIT Init\nNEXT Next",
    });
    expect(result.violations[0]?.headline).toContain(message);
  });

  it("declines to word the function in IF [k \\in 1..2 |-> k] THEN 1 ELSE 2", async () => {
    await expectDeclined(
      {
        source:
          "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = x /\\ (IF [k \\in 1..2 |-> k] THEN 1 ELSE 2) = TRUE\n====",
        config: "INIT Init\nNEXT Next",
      },
      "the engine stopped: expected a boolean: evaluating the failure again: expected a boolean, not a function",
    );
  });

  it.each([
    ["[a |-> 1]", "a failure TLC reports as a FingerprintException"],
    ['"a" :> 1', "equality of values TLC can't compare"],
    ['"a b" :> 1', "equality of values TLC can't compare"],
  ])("declines a failed comparison of %s with a set", async (value, reason) => {
    await expectDeclined(
      {
        source: `---- MODULE M ----\nEXTENDS TLC\nVARIABLE x\nInit == x = ${value}\nNext == UNCHANGED x\nInv == x = {}\n====`,
        config: "INIT Init\nNEXT Next\nINVARIANT Inv",
      },
      `the engine stopped: equality of values TLC can't compare: evaluating the failure again: ${reason}`,
    );
  });

  // TLC evaluates UNCHANGED e, [A]_e and <<A>>_e in the current state before the next one
  // (Tool.evalAppl), so the first failure is the current state's.
  it.each(["[FALSE]_(e)", "IF UNCHANGED (e) THEN TRUE ELSE TRUE", "<<TRUE>>_(e)"])(
    "evaluates %s in the current state first like TLC",
    async (form) => {
      const subscript = 'IF x = 0 THEN Assert(FALSE, "before") ELSE Assert(FALSE, "after")';
      const result = await checkOnEngine({
        source: `---- MODULE M ----\nEXTENDS TLC\nVARIABLE x\nInit == x = 0\nNext == x' = 1 /\\ ${form.replace("(e)", `(${subscript})`)}\n====`,
        config: "INIT Init\nNEXT Next",
      });
      expect(result.violations[0]?.headline).toContain('"before"');
    },
  );

  // TLC 1.8.0 takes a value a configuration substitutes for an operator with parameters, as
  // mongodb-txns' Storage.cfg substitutes FALSE for actions, and leaves the arguments unevaluated.
  it("takes a value substituted for an operator with parameters like TLC", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nA(n) == x' = n\nInit == x = 0\nNext == \\/ x < 3 /\\ x' = x + 1\n        \\/ \\E n \\in {0} : A(1 \\div n)\n====",
      config: "INIT Init\nNEXT Next\nCONSTANT A <- FALSE\nCHECK_DEADLOCK FALSE",
    });
    expect([result.status, result.generatedStates, result.distinctStates]).toEqual([
      "success",
      4,
      4,
    ]);
  });

  it("reports a CASE with no true guard like TLC", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nVARIABLE x\nASSUME CASE 1 = 2 -> 3\nInit == x = 0\nNext == UNCHANGED x\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect(result.violations[0]?.headline).toBe(
      getAssumptionFailure(
        3,
        "CASE 1 = 2 -> 3",
        "Attempted to evaluate a CASE with no conditions true.\nline 3, col 8 to line 3, col 22 of module M",
      ),
    );
  });

  it.each([
    [
      "(CHOOSE v : TRUE) = 1",
      "TLC attempted to evaluate an unbounded CHOOSE.\nMake sure that the expression is of form CHOOSE x \\in S: P(x).\nline 3, col 9 to line 3, col 23 of module M",
    ],
  ])("reports an unbounded %s like TLC", async (assumption, message) => {
    const result = await checkOnEngine({
      source: `---- MODULE M ----\nVARIABLE x\nASSUME ${assumption}\nInit == x = 0\nNext == UNCHANGED x\n====`,
      config: "INIT Init\nNEXT Next",
    });
    expect(result.violations[0]?.headline).toBe(getAssumptionFailure(3, assumption, message));
  });

  it("declines an unbounded \\A v, w : v = w", async () => {
    await expectDeclined(
      {
        source:
          "---- MODULE M ----\nVARIABLE x\nASSUME \\A v, w : v = w\nInit == x = 0\nNext == UNCHANGED x\n====",
        config: "INIT Init\nNEXT Next",
      },
      getAssumptionDeclined("evaluating a an unbounded quantifier"),
    );
  });

  // TLC's TLCEval evaluates its argument in its Java method.
  it("reports a failure inside TLCEval as the method's", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nF(n) == TLCEval(1 \\div n)\nASSUME TLCEval(F(0)) = 1\nInit == x = 0\nNext == UNCHANGED x\n====",
      config: "INIT Init\nNEXT Next",
    });
    const wrapper =
      "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLCEval.tlcEval(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel),\nbut it produced the following error:\n";
    expect(result.violations[0]?.headline).toBe(
      getAssumptionFailure(
        5,
        "TLCEval(F(0)) = 1",
        `${wrapper.repeat(2)}The second argument of \\div is 0.`,
      ),
    );
  });

  // TLC's Json.textSerialize evaluates IOUtils's Serialize unless the format is NDJSON.
  it.each([
    [
      '[format |-> "TXT"]',
      "Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn],\nbut can't enumerate the value of the `exitValue' field:\nInt",
    ],
    ["42", "The third argument of ndJsonSerialize should be a sequence, but instead it is:\n42"],
    ["<<>>", "Attempted to access nonexistent field 'format' of record\n[]"],
  ])("reports a failure in IOUtils's Serialize with %s as Json's", async (options, error) => {
    const result = await checkOnEngine({
      source: `---- MODULE M ----\nEXTENDS Naturals, IOUtils\nVARIABLE x\nASSUME Serialize(1, "/tmp/x", ${options}).exitValue = 0\nInit == x = 0\nNext == UNCHANGED x\n====`,
      config: "INIT Init\nNEXT Next",
      loadModule: (name) =>
        name === "IOUtils"
          ? "---- MODULE IOUtils ----\nEXTENDS Integers\nSerialize(value, dest, options) == CHOOSE r \\in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE\n===="
          : undefined,
    });
    expect(result.violations[0]?.headline).toBe(
      getAssumptionFailure(
        4,
        `Serialize(1, "/tmp/x", ${options}).exitValue = 0`,
        `Attempted to apply the operator overridden by the Java method\npublic static synchronized tlc2.value.impl.Value tlc2.module.Json.textSerialize(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel),\nbut it produced the following error:\n${error}`,
      ),
    );
  });

  it("reports a CASE with no true guard in the next-state relation like TLC", () => {
    const run = runOnEngine({
      source:
        "---- MODULE M ----\nVARIABLE x\nInit == x = 0\nNext == CASE x = 5 -> x' = 0\n  [] x = 6 -> x' = 1\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect(getErrors(run.output)[0]).toBe(
      "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: In computing next states, TLC encountered a CASE with no conditions true.\nline 4, col 9 to line 5, col 20 of module M",
    );
    expect(run.exitCode).toBe(75);
  });

  it("reports the behavior up to a state whose invariant fails to evaluate", () => {
    const run = runOnEngine(
      getStepsRun("Inv == 1 \\div (2 - x) >= 0", "INIT Init\nNEXT Next\nINVARIANT Inv"),
    );
    expect(getErrors(run.output)).toEqual([
      "Evaluating invariant Inv failed.\nThe second argument of \\div is 0.",
      "The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Next line 5, col 9 to line 5, col 27 of module M>\nx = 1\n\nState 3: <Next line 5, col 9 to line 5, col 27 of module M>\nx = 2",
    ]);
    expect(getStatistics(run.output)).toEqual([
      "3 states generated, 3 distinct states found, 0 states left on queue.",
      "The depth of the complete state graph search is 3.",
      "The average outdegree of the complete state graph is 1 (minimum is 1, the maximum 1 and the 95th percentile is 1).",
    ]);
    expect(run.exitCode).toBe(76);
  });

  it.each([
    [
      "0 \\in [{1} -> {2}]",
      "Attempted to check if \n0\nwhich is not a TLC function value, is in the set of functions:\n{<<2>>}",
    ],
    [
      "0 \\in SUBSET {1}",
      "Attempted to check if the non-enumerable value\n0\nis element of\n{{}, {1}}",
    ],
    [
      "Nat \\in SUBSET {1}",
      "Attempted to check if the non-enumerable value\nNat\nis element of\n{{}, {1}}",
    ],
    ["0 \\in Seq({1})", "Attempted to check if the value:\n0\nis an element of Seq({1})."],
  ])("reports a value that can't be an element of %s like TLC", async (expression, message) => {
    const result = await checkModule(`ASSUME ${expression}`);
    expect(result.violations[0]?.headline).toBe(getAssumptionFailure(6, expression, message));
  });

  // TLC's etest15: TLC normalizes the value of a constant definition as it starts, and searches the
  // sorted domain of a function over it.
  it("compares a value with the elements of a constant definition's set like TLC", async () => {
    const result = await checkModule(
      "S == {<<y>> : y \\in {1, 2, 3, 4}}\nASSUME [<<y>> \\in S |-> y + 1][2] = 3",
    );
    expect(result.violations[0]?.headline).toBe(
      getAssumptionFailure(
        7,
        "[<<y>> \\in S |-> y + 1][2] = 3",
        "Attempted to compare integer 2 with non-integer:\n<<3>>",
      ),
    );
  });

  // TLC's FingerprintExceptionHang: the replay of the failed expansion adds the successors TLC
  // hasn't seen and checks their invariants, which fail to fingerprint.
  it("counts the states that the replay of a failed invariant adds", () => {
    const run = runOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nCONSTANTS Nodes\nVARIABLES nodeState\nLegalSets == {{}}\nTypeOK == nodeState \\in [Nodes -> [set: LegalSets]]\nInit == nodeState = [n \\in Nodes |-> [set |-> {}]]\nNext == \\E n \\in Nodes : nodeState' = [nodeState EXCEPT ![n].set = 1]\n====",
      config:
        "CONSTANT Nodes = {A, B}\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT TypeOK",
    });
    expect(getErrors(run.output)[0]).toBe(
      "Evaluating invariant TypeOK failed.\nAttempted to compare integer 1 with non-integer:\n{}",
    );
    expect(getFingerprintFailure(run.output)?.frames).toEqual([
      "0. Line 6, column 11 to line 6, column 51 in M",
      "1. Line 6, column 25 to line 6, column 51 in M",
      "2. Line 6, column 35 to line 6, column 50 in M",
    ]);
    expect(getStatistics(run.output)[0]).toBe(
      "2 states generated, 3 distinct states found, 0 states left on queue.",
    );
    expect(run.exitCode).toBe(75);
  });

  // A set with a source raises a FingerprintException when TLC's replay fails to enumerate it.
  it.each<[string, string[] | undefined]>([
    [
      "x' \\in ({1} \\cup 2)",
      [
        "0. Line 5, column 9 to line 5, column 27 in M",
        "1. Line 5, column 17 to line 5, column 26 in M",
      ],
    ],
    ["x' = Cardinality({n \\in ({1} \\cup 2) : TRUE})", undefined],
  ])("prints the frames of a set the replay of %s fails to enumerate like TLC", (next, frames) => {
    const run = runOnEngine({
      source: `---- MODULE M ----\nEXTENDS Naturals, FiniteSets\nVARIABLE x\nInit == x = 0\nNext == ${next}\n====`,
      config: "INIT Init\nNEXT Next",
    });
    expect(getFingerprintFailure(run.output)?.frames).toEqual(frames);
  });

  it("declines a set the replay of x' \\in UNION {Nat} fails to enumerate", () => {
    const run = runOnEngine(
      {
        source:
          "---- MODULE M ----\nEXTENDS Naturals, FiniteSets\nVARIABLE x\nInit == x = 0\nNext == x' \\in UNION {Nat}\n====",
        config: "INIT Init\nNEXT Next",
      },
      "the engine declined: unsupported: enumerating a set TLC keeps lazy (UNION at line 5)",
    );
    expect(run.exitCode).toBe(1);
  });

  // A tuple, record or set with a source raises a FingerprintException when the replay fails to
  // apply it.
  it.each([
    [
      "<<1, 2>>[3]",
      [
        "0. Line 5, column 9 to line 5, column 24 in M",
        "1. Line 5, column 14 to line 5, column 24 in M",
        "2. Line 5, column 14 to line 5, column 21 in M",
      ],
    ],
    [
      "[a |-> 1][1]",
      [
        "0. Line 5, column 9 to line 5, column 25 in M",
        "1. Line 5, column 14 to line 5, column 25 in M",
        "2. Line 5, column 14 to line 5, column 22 in M",
      ],
    ],
    [
      "[{1} EXCEPT ![1] = 1]",
      [
        "0. Line 5, column 9 to line 5, column 34 in M",
        "1. Line 5, column 14 to line 5, column 34 in M",
        "2. Line 5, column 15 to line 5, column 17 in M",
      ],
    ],
  ])(
    "reports the source of a value the replay of x' = %s fails to apply like TLC",
    (value, frames) => {
      const run = runOnEngine({
        source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = ${value}\n====`,
        config: "INIT Init\nNEXT Next",
      });
      expect(getFingerprintFailure(run.output)?.frames).toEqual(frames);
    },
  );

  it.each([
    ['[<<1, 2>> EXCEPT !["a"] = 1]', "the engine stopped: EXCEPT outside the domain"],
    [
      "{1, 2}[1]",
      "the engine stopped: applied a non-function: evaluating the failure again: applied a non-function: {1, 2}",
    ],
  ])("declines the replay of x' = %s that fails to apply a value", (value, reason) => {
    const run = runOnEngine(
      {
        source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = ${value}\n====`,
        config: "INIT Init\nNEXT Next",
      },
      reason,
    );
    expect(run.exitCode).toBe(1);
  });

  // Reducible#diff and cap of a set enumeration or interval with a source raise a
  // FingerprintException when they fail to test an element for membership in the other set.
  it.each([
    [
      "{k : k \\in {3}} \\ (3 \\cup {1})",
      [
        "0. Line 5, column 9 to line 5, column 55 in M",
        "1. Line 5, column 9 to line 5, column 14 in M",
        "2. Line 5, column 19 to line 5, column 55 in M",
        "3. Line 5, column 20 to line 5, column 49 in M",
        "4. Line 5, column 20 to line 5, column 34 in M",
        "5. Line 5, column 39 to line 5, column 48 in M",
      ],
    ],
    [
      "{k : k \\in {3}} \\cap (3 \\cup {1})",
      [
        "0. Line 5, column 9 to line 5, column 58 in M",
        "1. Line 5, column 9 to line 5, column 14 in M",
        "2. Line 5, column 19 to line 5, column 58 in M",
        "3. Line 5, column 20 to line 5, column 52 in M",
        "4. Line 5, column 20 to line 5, column 34 in M",
        "5. Line 5, column 42 to line 5, column 51 in M",
      ],
    ],
    [
      "(3 \\cup {1}) \\cap {k : k \\in {3}}",
      [
        "0. Line 5, column 9 to line 5, column 58 in M",
        "1. Line 5, column 9 to line 5, column 14 in M",
        "2. Line 5, column 19 to line 5, column 58 in M",
        "3. Line 5, column 20 to line 5, column 52 in M",
        "4. Line 5, column 38 to line 5, column 52 in M",
        "5. Line 5, column 21 to line 5, column 30 in M",
      ],
    ],
  ])("reports the set whose method computes %s and fails like TLC", (set, frames) => {
    const run = runOnEngine({
      source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x /\\ (${set}) = {}\n====`,
      config: "INIT Init\nNEXT Next",
    });
    expect(getFingerprintFailure(run.output)?.frames).toEqual(frames);
  });

  // Reducible#cup, cap and diff test each element for membership in the other set, which a set
  // enumeration TLC hasn't normalized checks with equals.
  it.each([
    ['{3} \\cup {"a"}', 'Attempted to check equality of integer 3 with non-integer:\n"a"'],
    ['(1..2) \\cap {"a"}', 'Attempted to check equality of string "a" with non-string:\n1'],
    ['{"a"} \\ {3}', 'Attempted to check equality of integer 3 with non-integer:\n"a"'],
  ])("fails to compute %s with TLC's reason", (set, reason) => {
    const run = runOnEngine({
      source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x /\\ (${set}) = {}\n====`,
      config: "INIT Init\nNEXT Next",
    });
    expect(getFingerprintFailure(run.output)?.reason).toBe(reason);
  });

  // The equals method of a member with a source heads the failure of a membership test, and the
  // compareTo method of an element with a source the failure to sort a set.
  it.each([
    [
      "({[a |-> 1]} \\cap {{1}}) = {}",
      [
        "0. Line 5, column 9 to line 5, column 47 in M",
        "1. Line 5, column 9 to line 5, column 14 in M",
        "2. Line 5, column 19 to line 5, column 47 in M",
        "3. Line 5, column 20 to line 5, column 41 in M",
        "4. Line 5, column 20 to line 5, column 30 in M",
        "5. Line 5, column 37 to line 5, column 41 in M",
        "6. Line 5, column 38 to line 5, column 40 in M",
      ],
    ],
    [
      '{("a" :> 1), <<2>>} = {}',
      [
        "0. Line 5, column 9 to line 5, column 42 in M",
        "1. Line 5, column 9 to line 5, column 14 in M",
        "2. Line 5, column 19 to line 5, column 42 in M",
        "3. Line 5, column 19 to line 5, column 37 in M",
        "4. Line 5, column 32 to line 5, column 36 in M",
      ],
    ],
  ])("reports the value that fails to compare in %s like TLC", (predicate, frames) => {
    const run = runOnEngine({
      source: `---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = x /\\ ${predicate}\n====`,
      config: "INIT Init\nNEXT Next",
    });
    expect(getFingerprintFailure(run.output)?.frames).toEqual(frames);
  });

  it.each(["({<<1>>} \\cup {2}) = {}", "2 \\in {<<1>>}"])(
    "declines the value that fails to compare in %s",
    (predicate) => {
      const run = runOnEngine(
        {
          source: `---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = x /\\ ${predicate}\n====`,
          config: "INIT Init\nNEXT Next",
        },
        "the engine stopped: values TLC can't compare: evaluating the failure again: a failure TLC reports as a FingerprintException",
      );
      expect(run.exitCode).toBe(1);
    },
  );

  // TLC builds a function in a method of the FcnLambdaValue that CallStackTool gives a source, so
  // the replay fails to fingerprint it when its body fails.
  it.each<[string, string, string[] | undefined]>([
    [
      "x = [k \\in {1, 2} |-> k \\div 0]",
      "x' = x",
      [
        "0. Line 4, column 9 to line 4, column 39 in M",
        "1. Line 4, column 13 to line 4, column 39 in M",
        "2. Line 4, column 31 to line 4, column 38 in M",
      ],
    ],
    [
      "x = 0",
      "x' = [k \\in 1..2 |-> k \\div 0]",
      [
        "0. Line 5, column 9 to line 5, column 38 in M",
        "1. Line 5, column 14 to line 5, column 38 in M",
        "2. Line 5, column 30 to line 5, column 37 in M",
      ],
    ],
    [
      "x = 0",
      "x' = [k \\in {1, 2} |-> <<1, 2>>[k + 1]]",
      [
        "0. Line 5, column 9 to line 5, column 47 in M",
        "1. Line 5, column 14 to line 5, column 47 in M",
        "2. Line 5, column 32 to line 5, column 46 in M",
        "3. Line 5, column 32 to line 5, column 39 in M",
      ],
    ],
    [
      "x = 0",
      "x' = [j \\in {1} |-> [k \\in {1, 2} |-> k \\div 0]]",
      [
        "0. Line 5, column 9 to line 5, column 56 in M",
        "1. Line 5, column 14 to line 5, column 56 in M",
        "2. Line 5, column 29 to line 5, column 55 in M",
        "3. Line 5, column 47 to line 5, column 54 in M",
      ],
    ],
    ["x = 0", "x' = [k \\in Nat |-> k \\div 0][1]", undefined],
  ])(
    "reports a function whose body fails in %s or %s as one TLC can't fingerprint",
    (init, next, frames) => {
      const run = runOnEngine({
        source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == ${init}\nNext == ${next}\n====`,
        config: "INIT Init\nNEXT Next",
      });
      expect(getFingerprintFailure(run.output)?.frames).toEqual(frames);
      expect(run.exitCode).toBe(frames ? 75 : 255);
    },
  );

  // An operand that fails fails before TLC compares.
  it.each(["x' = Filter /\\ x' = {}", "x' = 1 /\\ {} = (1 \\div 0)"])(
    "fails on the left side of %s before TLC fingerprints it",
    (next) => {
      const run = runOnEngine({
        source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nFilter == {n \\in SUBSET {1} : 1 \\div 0 = 1}\nNext == ${next}\n====`,
        config: "INIT Init\nNEXT Next",
      });
      expect(getFingerprintFailure(run.output)).toBeUndefined();
    },
  );

  // TLC compares the sets as Value#equals does, and never takes a faster comparison that
  // fails first.
  it("records the replay of a filter that fails to compare once", () => {
    const run = runOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = {n \\in SUBSET {1} : 1 \\div 0 = 1} /\\ x' = {}\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect(getNestedExpressions(run.output)).toEqual([
      "0. Line 5, column 9 to line 5, column 57 in M",
      "1. Line 5, column 9 to line 5, column 46 in M",
      "2. Line 5, column 51 to line 5, column 57 in M",
      "3. Line 5, column 34 to line 5, column 45 in M",
      "4. Line 5, column 34 to line 5, column 41 in M",
    ]);
  });

  // SpecProcessor.processConfigSpec keeps a definition that is a state predicate whole, so TLC's
  // call stack starts at the list the definition wrote (TLC's own run of this model).
  it("records the specification's initial predicate as the definition wrote it", () => {
    const run = runOnEngine({
      source:
        '---- MODULE M ----\nEXTENDS Integers, TLC\nVARIABLE x\nInit ==\n  /\\ x \\in {0, 1, 2}\n  /\\ 3 \\div (x - 1) >= 0\n  /\\ Assert(x # 2, "two")\nNext == x\' = (x + 1) % 3\nSpec == Init /\\ [][Next]_x\n====',
      config: "SPECIFICATION Spec",
    });
    expect(getNestedExpressions(run.output)).toEqual([
      "0. Line 5, column 3 to line 7, column 25 in M",
      "1. Line 5, column 6 to line 5, column 20 in M",
      "2. Line 6, column 6 to line 6, column 24 in M",
      "3. Line 6, column 6 to line 6, column 19 in M",
    ]);
  });

  // Tool.processUnchangedImplTuple puts the elements after the first in front of the conjuncts left,
  // in order.
  it("records the variables of an UNCHANGED tuple in order", () => {
    const run = runOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLES a, b, c\nInit == a = 0 /\\ b = 0 /\\ c = 0\nNext == UNCHANGED <<a, b, c>> /\\ 1 \\div 0 = 1\n====",
      config: "INIT Init\nNEXT Next",
    });
    // a, b and c, at columns 21, 24 and 27.
    expect(getNestedExpressions(run.output)).toEqual([
      "0. Line 5, column 9 to line 5, column 45 in M",
      "1. Line 5, column 9 to line 5, column 29 in M",
      "2. Line 5, column 19 to line 5, column 29 in M",
      "3. Line 5, column 21 to line 5, column 21 in M",
      "4. Line 5, column 24 to line 5, column 24 in M",
      "5. Line 5, column 27 to line 5, column 27 in M",
      "6. Line 5, column 34 to line 5, column 45 in M",
      "7. Line 5, column 34 to line 5, column 41 in M",
    ]);
  });

  // Tool.processUnchangedImplVar binds each unassigned variable and compares each assigned one, so a
  // later variable that changed drops the variables bound before it.
  it("keeps nested tuples and operators in an UNCHANGED as TLC does", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLES x, y, z\nvars == <<x, y>>\nInit == x = 0 /\\ y = 0 /\\ z = 0\nNext ==\n  \\/ z' = (z + 1) % 3 /\\ UNCHANGED <<vars, <<x>>>>\n  \\/ y' \\in {y, 1} /\\ UNCHANGED <<<<z>>, vars>>\n  \\/ x < 2 /\\ x' = x + 1 /\\ UNCHANGED <<z, <<y>>, x>>\n  \\/ x < 2 /\\ x' = x + 1 /\\ UNCHANGED <<z, y>>\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect([
      result.violations[0],
      result.generatedStates,
      result.distinctStates,
      result.depth,
    ]).toEqual<unknown[]>([undefined, 25, 9, 5]);
  });

  it.each(["G(2)[1]", "G(1)[3]"])(
    "declines applying a function TLC keeps lazy, whose body fails elsewhere, in x' = %s",
    async (application) => {
      await expectDeclined(
        getStepsOptions(
          `G(n) == [k \\in {1, 2} |-> 10 \\div (k - n)]\nStep == x' = ${application}`,
          "INIT Init\nNEXT Step",
        ),
        "the engine stopped: division by zero: evaluating the failure again: the body of a function TLC keeps lazy",
      );
    },
  );

  it.each([
    [
      "Step == [k \\in {1, 2} |-> x' = k][3]",
      "[k \\in {1, 2} |-> <expression line 6, col 27 to line 6, col 32 of module M>],\nthe first argument is:\n3which is not in its domain.\nline 6, col 9 to line 6, col 33 of module M",
    ],
  ])(
    "applies a function outside its domain in an action as TLC does in %j",
    async (step, message) => {
      const result = await checkStepsOnEngine(step, "INIT Init\nNEXT Step");
      expect(result.violations[0]?.headline).toBe(
        `TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: In applying the function\n${message}`,
      );
    },
  );

  it("declines applying a function over a tuple outside its domain in an action", async () => {
    await expectDeclined(
      getStepsOptions(
        "Step == [k \\in {1}, <<a, b>> \\in {<<1, 2>>} |-> x' = a][1, <<3, 4>>]",
        "INIT Init\nNEXT Step",
      ),
      "the engine declined: unsupported: walking a lazy function over a tuple",
    );
  });

  it.each([
    [
      "Step == <<1>>[1] /\\ UNCHANGED x",
      "INIT Init\nNEXT Step",
      `${UNEXPECTED_EXCEPTION}In computing next states, TLC expected a boolean expression,\nbut didn't find one.\nline 6, col 9 to line 6, col 16 of module M`,
    ],
    [
      "Step == 1[1] /\\ UNCHANGED x",
      "INIT Init\nNEXT Step",
      `${UNEXPECTED_EXCEPTION}In computing next states, a non-function (an integer) was applied as a function.\nline 6, col 9 to line 6, col 12 of module M`,
    ],
    [
      "Start == [k \\in {1} |-> x = 0][1]",
      "INIT Start\nNEXT Next",
      "In evaluation, the identifier x is either undefined or not an operator.\nline 6, col 25 to line 6, col 25 of module M",
    ],
  ])("applies the value of a function in %j as TLC does", async (definitions, config, message) => {
    const result = await checkStepsOnEngine(definitions, config);
    expect(result.violations[0]?.headline).toBe(message);
  });

  it("computes a function definition that isn't recursive at once as TLC does", async () => {
    const result = await checkStepsOnEngine(
      "F[k \\in {1}] == x = 0\nStart == F[1]",
      "INIT Start\nNEXT Next",
    );
    expect(result.violations[0]?.headline).toBe(
      "In evaluation, the identifier x is either undefined or not an operator.\nline 6, col 17 to line 6, col 17 of module M",
    );
  });

  it("applies a function built over a set enumeration as the record TLC builds", async () => {
    const result = await checkStepsOnEngine(
      "Start == x = [k \\in {1, 2} |-> 0]\nStep == x' = x /\\ x[3] = 0",
      "INIT Start\nNEXT Step",
    );
    expect(result.violations[0]?.headline).toBe(
      "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: Attempted to apply function:\n<<0, 0>>\nto argument 3, which is not in the domain of the function.",
    );
  });

  it.each([
    "Step == x' = [k \\in {1, 2} |-> 1] /\\ x'[3] = 0",
    "Step == x' = [k \\in SUBSET {1} |-> 1] /\\ x'[{2}] = 0",
  ])("declines applying a successor's function outside its domain in %j", async (definitions) => {
    await expectDeclined(
      getStepsOptions(definitions, "INIT Init\nNEXT Step"),
      "the engine stopped: applied a function outside its domain: evaluating the failure again: applied a function outside its domain",
    );
  });

  // FcnLambdaValue#fingerPrint caches the FcnRcdValue that applies the function from then on.
  it("applies a function as TLC does once it fingerprints it", async () => {
    const result = await checkStepsOnEngine(
      "Start == x = [k \\in SUBSET {1} |-> 0]\nStep == x' = x /\\ x[{2}] = 0",
      "INIT Start\nNEXT Step",
    );
    expect(result.violations[0]?.headline).toBe(
      "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: Attempted to apply function:\n({} :> 0 @@ {1} :> 0)\nto argument {2}, which is not in the domain of the function.",
    );
  });

  it("reports a non-function applied as a function in computing next states like TLC", async () => {
    const result = await checkStepsOnEngine(
      "Step == x' = (IF x = 0 THEN [k \\in {1, 2} |-> k] ELSE 0)[1]",
      "INIT Init\nNEXT Step",
    );
    expect(result.violations[0]?.headline).toBe(
      "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: A non-function (an integer) was applied as a function.\nline 6, col 14 to line 6, col 59 of module M",
    );
  });

  it("reports a set TLC can't enumerate in computing next states like TLC", async () => {
    const result = await checkStepsOnEngine("Step == x' \\in Nat", "INIT Init\nNEXT Step");
    expect(result.violations[0]?.headline).toBe(
      "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: In computing next states, the right side of \\IN is not enumerable.\nline 6, col 9 to line 6, col 18 of module M",
    );
  });

  it("fails to fingerprint an initial state x = {n \\in Nat : n > 1} like TLC", () => {
    const run = runOnEngine(
      getStepsRun("Start == x = {n \\in Nat : n > 1}", "INIT Start\nNEXT Next"),
    );
    expect(getErrors(run.output)[0]).toBe(
      "Attempted to enumerate { x \\in S : p(x) } when S:\nNat\nis not enumerable\nWhile working on the initial state:\nx = {n \\in Nat : <expression line 6, col 27 to line 6, col 31 of module M> }",
    );
    expect(getFingerprintFailure(run.output)?.frames).toBeUndefined();
    expect(getStatistics(run.output)).toEqual([
      "1 states generated, 0 distinct states found, 0 states left on queue.",
      "The depth of the complete state graph search is 1.",
    ]);
    expect(run.exitCode).toBe(75);
  });

  it.each([
    ["Nat", "the engine stopped: enumerated Nat"],
    ["{Nat}", "the engine stopped: unsupported: a state holding a function TLC keeps lazy"],
    ["SUBSET Nat", "the engine stopped: enumerated Nat"],
  ])("declines an initial state x = %s TLC fails to fingerprint", (expression, reason) => {
    const run = runOnEngine(
      getStepsRun(`Start == x = ${expression}`, "INIT Start\nNEXT Next"),
      reason,
    );
    expect(run.exitCode).toBe(1);
  });

  it("prints a set filter it can't enumerate as its bound and the location of its predicate", async () => {
    const result = await checkStepsOnEngine(
      "Start == x = {n \\in Nat : n > 1}",
      "INIT Start\nNEXT Next",
    );
    expect(result.violations[0]?.headline).toEndWith(
      "\nWhile working on the initial state:\nx = {n \\in Nat : <expression line 6, col 27 to line 6, col 31 of module M> }\n",
    );
  });

  it("declines a state outside the model that TLC doesn't fingerprint", async () => {
    await expectDeclined(
      getStepsOptions(
        "Start == x = SUBSET Nat\nC == x \\in {}",
        "INIT Start\nNEXT Next\nCONSTRAINT C",
      ),
      "the engine stopped: enumerated Nat",
    );
  });

  it("declines a successor it can't fingerprint", () => {
    const run = runOnEngine(
      getStepsRun("Step == x' = IF x = 1 THEN {Nat} ELSE x + 1", "INIT Init\nNEXT Step"),
      "the engine stopped: unsupported: a state holding a function TLC keeps lazy",
    );
    expect(run.exitCode).toBe(1);
  });

  it("declines a function TLC builds lazily whose body fails as TLC fingerprints it", () => {
    const run = runOnEngine(
      getStepsRun("Step == x' = [k \\in SUBSET {1} |-> 1 \\div 0]", "INIT Init\nNEXT Step"),
      "the engine stopped: division by zero: evaluating the failure again: the body of a function TLC keeps lazy",
    );
    expect(run.exitCode).toBe(1);
  });

  it("declines a function TLC builds lazily in a disabled action", async () => {
    await expectDeclined(
      getStepsOptions(
        "Step == x' = [k \\in SUBSET {1} |-> 1 \\div 0] /\\ FALSE",
        "INIT Init\nNEXT Step",
      ),
      "the engine stopped: division by zero: evaluating the failure again: the body of a function TLC keeps lazy",
    );
  });

  // TLC evaluates the whole predicate, not each conjunct on its own.
  it("fails at a non-boolean conjunct of INVARIANT P as the conjunction does", async () => {
    const result = await checkStepsOnEngine(
      "P == /\\ x < 3\n     /\\ IF x = 1 THEN 1 ELSE TRUE",
      "INIT Init\nNEXT Next\nINVARIANT P",
    );
    expect(result.violations[0]?.headline).toContain(
      "A non-boolean expression (an integer) was used as a formula in a conjunction.\nline 7, col 9 to line 7, col 33 of module M",
    );
  });

  it("declines a non-boolean conjunct of CONSTRAINT P", async () => {
    await expectDeclined(
      getStepsOptions(
        "P == /\\ x < 3\n     /\\ IF x = 1 THEN 1 ELSE TRUE",
        "INIT Init\nNEXT Next\nCONSTRAINT P",
      ),
      "the engine stopped: a constraint, a VIEW or an action property that fails on a successor",
    );
  });

  it("declines a failed constraint that prints", () => {
    const run = runOnEngine(
      getStepsRun(
        'C == PrintT(<<"c", x>>) /\\ (IF x = 2 THEN 1 \\in 2 ELSE TRUE)',
        "INIT Init\nNEXT Next\nCONSTRAINT C",
      ),
      "the engine stopped: a constraint, a VIEW or an action property that fails on a successor",
    );
    expect(run.exitCode).toBe(1);
  });

  // TLC rebuilds the trace for the postcondition only after a violation.
  it("prints only the replay after the trace when INVARIANT P fails to evaluate", () => {
    const run = runOnEngine(
      getStepsRun(
        'Step == Next /\\ PrintT(<<"s", x>>)\nSpec == Init /\\ [][Step]_x\nP == x < 2 \\/ 1 \\div 0 = 0',
        "SPECIFICATION Spec\nINVARIANT P",
      ),
    );
    expect(getTraceOutput(run.output)).toEqual(['<<"s", 1>>']);
  });

  it.each([
    'Step == Next /\\ PrintT(<<"s", x>>)\nSpec == Init /\\ [][Step]_x\nP == [][x\' < 2 \\/ 1 \\div 0 = 0]_x',
    "P == [][1 \\div (2 - x) >= 0]_x\nSpec == Init /\\ [][Next]_x",
  ])("declines an action property that fails to evaluate: %s", (definitions) => {
    const run = runOnEngine(
      getStepsRun(definitions, "SPECIFICATION Spec\nPROPERTY P"),
      "the engine stopped: a constraint, a VIEW or an action property that fails on a successor",
    );
    expect(run.exitCode).toBe(1);
  });

  it("reports the behavior up to a state whose successors fail to evaluate", () => {
    const run = runOnEngine(
      getStepsRun('Step == Next /\\ Assert(x < 1, "boom")', "INIT Init\nNEXT Step"),
    );
    expect(getErrors(run.output).slice(0, 2)).toEqual([
      'The first argument of Assert evaluated to FALSE; the second argument was:\n"boom"',
      "The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Step line 6, col 9 to line 6, col 37 of module M>\nx = 1",
    ]);
    expect(getStatistics(run.output)).toEqual([
      "2 states generated, 2 distinct states found, 0 states left on queue.",
      "The depth of the complete state graph search is 2.",
    ]);
    expect(run.exitCode).toBe(14);
  });

  it("reports a check that is not a boolean at the location of its predicate", async () => {
    const getMessage = async (definitions: string, config: string) =>
      (await checkStepsOnEngine(definitions, `INIT Init\nNEXT Next\n${config}`)).violations[0]
        ?.headline;
    expect(await getMessage("Inv == x + 1", "INVARIANT Inv")).toBe(
      "TLC expected a boolean value, but did not find one. line 6, col 8 to line 6, col 12 of module M\nWhile working on the initial state:\nx = 0\n",
    );
    expect(await getMessage("Inv == 1", "INVARIANT Inv")).toBe(
      "TLC expected a boolean value, but did not find one. 1\nWhile working on the initial state:\nx = 0\n",
    );
    expect(await getMessage("C == x' + 1", "ACTION_CONSTRAINT C")).toBe(
      "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: TLC expected a boolean value, but did not find one. line 6, col 6 to line 6, col 11 of module M",
    );
    await expectDeclined(
      getStepsOptions(
        "Spec == Init /\\ [][Next]_x\nP == [][x' + 1]_x",
        "SPECIFICATION Spec\nPROPERTY P",
      ),
      "the engine stopped: a constraint, a VIEW or an action property that fails on a successor",
    );
  });

  it("names the initial state a check fails on unless a standard module fails", () => {
    const config = "INIT Init\nNEXT Next\nINVARIANT Inv";
    const core = runOnEngine(getStepsRun("Inv == (CHOOSE y \\in {} : TRUE) = x", config));
    const standard = runOnEngine(getStepsRun("Inv == 1 \\div x = 0", config));
    expect(getErrors(core.output)[0]).toBe(
      "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\nline 6, col 9 to line 6, col 30 of module M\nWhile working on the initial state:\nx = 0",
    );
    expect(getErrors(standard.output)[0]).toBe("The second argument of \\div is 0.");
    for (const run of [core, standard]) {
      expect(findError(run.output, "The behavior up to this point is:\n")).toBeUndefined();
      expect(getStatistics(run.output)).toEqual([
        "1 states generated, 1 distinct states found, 1 states left on queue.",
        "The depth of the complete state graph search is 1.",
      ]);
      expect(run.exitCode).toBe(75);
    }
  });

  it("checks only the assumptions of a model without variables or an initial predicate", async () => {
    const result = await checkOnEngine({
      source: "---- MODULE M ----\nASSUME TRUE\n====",
      config: "",
    });
    expect(result.status).toBe("success");
    expect([result.generatedStates, result.distinctStates, result.depth]).toEqual([0, 0, 0]);
    await expect(
      checkOnEngine({ source: "---- MODULE M ----\nVARIABLE x\n====", config: "" }),
    ).rejects.toThrow(TlaConfigError);
  });

  it("reports an assumption that fails to evaluate and skips axioms", async () => {
    const result = await checkModule("AXIOM 1 = 2\nASSUME CHOOSE n \\in {} : TRUE");
    expect(result.status).toBe("assumption-violation");
    expect(result.violations[0]?.headline).toMatch(
      /^Evaluating assumption line 7, col 8 to line 7, col 29 of module M failed\.\nAttempted to compute the value of an expression of form\nCHOOSE x \\in S: P/,
    );
  });

  // TLC fingerprints a state only once the constraints hold of it (isInModel), so one they
  // exclude never fails to fingerprint (TLC's own run of this model finds no error).
  it("declines a state the constraints exclude that TLC doesn't fingerprint", async () => {
    await expectDeclined(
      {
        source:
          "---- MODULE M ----\nEXTENDS Integers\nVARIABLES x, y\nInit == \\/ (x = SUBSET (1..31) /\\ y = 0) \\/ (x = 0 /\\ y = 1)\nNext == UNCHANGED <<x, y>>\nC == y = 1\n====",
        config: "INIT Init\nNEXT Next\nCONSTRAINT C",
      },
      "the engine stopped: an overflow counting the elements of a power set: evaluating the failure again: it didn't fail",
    );
  });

  // TLC's replay, and Tool.getState as it prints the trace, take all of the action's successors
  // before they fingerprint one, so both meet the assertion that fails after the successor TLC
  // couldn't fingerprint (TLC's own run of this model, which exits 14).
  it("declines what fails after a successor TLC can't fingerprint", () => {
    const run = runOnEngine(
      {
        source:
          '---- MODULE M ----\nEXTENDS Integers, TLC\nVARIABLE x\nInit == x = 0\nNext == x = 0 /\\ \\E i \\in {1, 2} : x\' = IF i = 1 THEN SUBSET (1..31) ELSE Assert(FALSE, "boom")\n====',
        config: "INIT Init\nNEXT Next",
      },
      "the engine stopped: an overflow counting the elements of a power set: evaluating the failure again: an action that fails or prints after a successor TLC can't fingerprint",
    );
    expect(run.exitCode).toBe(1);
  });

  // Under a VIEW TLC fingerprints the view's value alone, so the union a variable holds is never
  // normalized and streams {3} first each time (TLC's own run of this model).
  it("declines a set a variable holds under a VIEW", async () => {
    await expectDeclined(
      {
        source:
          "---- MODULE M ----\nEXTENDS Integers, FiniteSets\nVARIABLES x, n, s\nInit == x = {} /\\ n = 0 /\\ s = (SUBSET {1, 2}) \\cup {{3}}\nNext == n < 3 /\\ x' \\in s /\\ Cardinality(x') = 1 /\\ n' = n + 1 /\\ s' = s\nInv == n < 2\nV == <<n>>\n====",
        config: "INIT Init\nNEXT Next\nINVARIANT Inv\nVIEW V",
      },
      "the engine declined: unsupported: enumerating a lazy set of the state under a VIEW",
    );
  });

  it("fails on zero to the power of zero in an invariant of a later state", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Integers\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 3\nInv == x < 1 \\/ 0 ^ (x - 1) = 1\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT Inv",
    });
    expect(result.violations[0]?.headline).toBe(
      "Evaluating invariant Inv failed.\n0^0 is undefined.",
    );
  });

  it.each([
    [
      "ASSUME {1} \\in {s \\in SUBSET {1} : 1 \\div 0 = 0}",
      "Cannot decide if element:\n{1}\n is element of:\n{{}, {1}}\nand satisfies the predicate line 6, col 36 to line 6, col 47 of module M",
    ],
    [
      "ASSUME [n \\in Nat |-> n].a = 1",
      "Attempted to compute the number of elements in the overridden value Nat.",
    ],
    [
      "ASSUME [n \\in Nat |-> n] \\in Seq(Nat)",
      "To convert a function of form [x \\in S |-> f(x)] to a tuple, the set S must be enumerable.",
    ],
  ])("words %s as TLC's lazy values do", async (assumption, message) => {
    const result = await checkModule(assumption);
    expect(result.status).toBe("assumption-violation");
    expect(result.violations[0]?.headline).toBe(
      getAssumptionFailure(6, assumption.slice("ASSUME ".length), message),
    );
  });

  it("puts a typed model value before an overridden set", async () => {
    const result = await checkModule("CONSTANT m\nASSUME ~(Nat = m)", "CONSTANT m = A_b");
    expect(result.status).toBe("success");
  });

  it("words arithmetic, sequence, and membership errors like TLC", async () => {
    const overflow = getAssumptionDeclined("integer overflow");
    const notSequence = getAssumptionDeclined("expected a sequence, not 1");
    const notInteger = (kind: string) =>
      getAssumptionDeclined(`expected an integer, not a ${kind}`);
    const subsetOfNonSet = getAssumptionDeclined("SUBSET of a non-set");
    const declined: Record<string, string> = {
      "2147483647 + 1 = 0": overflow,
      "-2147483647 - 2 = 0": overflow,
      "65536 * 65536 = 0": overflow,
      "2 ^ 31 = 0": overflow,
      "-(-2147483647 - 1) = 0": overflow,
      "Append(1, 2) = 0": notSequence,
      "1 \\o <<1>> = 0": notSequence,
      '"ab" \\o <<1>> = 0': getAssumptionDeclined('expected a sequence, not "ab"'),
      "SelectSeq(<<1>>, LAMBDA e: 1) = <<>>": getAssumptionDeclined(
        "a SelectSeq test that isn't a boolean",
      ),
      '"a" + 1 = 0': notInteger("string"),
      '1 \\div "a" = 0': notInteger("string"),
      '1 .. "a" = {}': notInteger("string"),
      '-"a" = 0': notInteger("string"),
      "{1} * 2 = 0": notInteger("set"),
      "Nat + 1 = 0": notInteger("set"),
      "[{1} -> {1}] + 1 = 0": notInteger("set"),
      "({1} \\X {1}) + 1 = 0": notInteger("set"),
      "2 % <<1>> = 0": notInteger("function"),
      "2 ^ [a |-> 1] = 0": notInteger("function"),
      "[e \\in Nat |-> e] + 1 = 0": notInteger("function"),
      "1 - TRUE = 0": notInteger("boolean"),
      "(SUBSET 0)..2 = {}": subsetOfNonSet,
      "SUBSET 0 = {}": subsetOfNonSet,
      'SUBSET "a" = {}': subsetOfNonSet,
      "SUBSET <<1, 2>> = {}": subsetOfNonSet,
      "{} \\subseteq 0": getAssumptionDeclined("it didn't fail"),
    };
    const cases = [
      ["1 \\div 0 = 0", "The second argument of \\div is 0."],
      ["1 % 0 = 0", "The second argument of % should be a positive number, but instead it is:\n0"],
      [
        "2 ^ (-1) = 0",
        "The second argument of ^ should be a natural number, but instead it is:\n-1",
      ],
      ["0 ^ 0 = 0", "0^0 is undefined."],
      ["2147483647 + 1 = 0", "Overflow when computing 2147483647+1"],
      ["-2147483647 - 2 = 0", "Overflow when computing -2147483647-2"],
      ["65536 * 65536 = 0", "Overflow when computing 65536*65536"],
      ["2 ^ 31 = 0", "Overflow when computing 2^31"],
      ["-(-2147483647 - 1) = 0", "Overflow when computing --2147483648"],
      ["(-2147483647 - 1) \\div (-1) = 0", "Overflow when computing -2147483648 \\div -1"],
      ['"a" < 1', 'The first argument of < should be an integer, but instead it is:\n"a"'],
      ['1 >= "a"', 'The second argument of >= should be an integer, but instead it is:\n"a"'],
      [
        "1 /\\ (TRUE)",
        "Attempted to evaluate an expression of form P /\\ Q when P was\nan integer.\nline 6, col 8 to line 6, col 18 of module M",
      ],
      [
        "FALSE \\/ (1) \\/ TRUE",
        "Attempted to evaluate an expression of form P \\/ Q when Q was\nan integer.\nline 6, col 8 to line 6, col 19 of module M",
      ],
      ["Head(<<>>) = 0", "Attempted to apply Head to the empty sequence."],
      ["Tail(<<>>) = 0", "Attempted to apply Tail to the empty sequence."],
      ["Len(1) = 0", "The argument of Len should be a sequence, but instead it is:\n1"],
      [
        "Append(1, 2) = 0",
        "Evaluating an expression of the form Append(s, v) when s is not a sequence:\n1",
      ],
      [
        "1 \\o <<1>> = 0",
        "Evaluating an expression of the form s \\o t when s is not a sequence:\n1",
      ],
      [
        '"ab" \\o <<1>> = 0',
        "Evaluating an expression of the form t \\o s when s is not a string:\n<<1>>",
      ],
      [
        "SubSeq(<<1, 2>>, 1, 3) = <<>>",
        "The third argument of SubSeq must be in the domain of its first argument:\n<<1, 2>>\n, but instead it is\n3",
      ],
      [
        "SubSeq(<<>>, 1, 1) = <<>>",
        "The second argument of SubSeq must be in the domain of its first argument:\n<<>>\n, but instead it is\n1",
      ],
      [
        "SelectSeq(<<1>>, LAMBDA e: 1) = <<>>",
        "The second argument of SelectSeq should be a operator, but instead it is:\n1",
      ],
      ["Cardinality(Nat) = 0", "Attempted to compute cardinality of the value\nNat"],
      ...[
        ['"a" + 1 = 0', "Plus", "StringValue"],
        ['1 \\div "a" = 0', "Divide", "StringValue"],
        ["{1} * 2 = 0", "Times", "SetEnumValue"],
        ["2 % <<1>> = 0", "Mod", "TupleValue"],
        ["2 ^ [a |-> 1] = 0", "Expt", "RecordValue"],
        ["1 - TRUE = 0", "Minus", "BoolValue"],
        ["Nat + 1 = 0", "Plus", "UserValue"],
        ["[{1} -> {1}] + 1 = 0", "Plus", "SetOfFcnsValue"],
        ["({1} \\X {1}) + 1 = 0", "Plus", "SetOfTuplesValue"],
        ["[e \\in Nat |-> e] + 1 = 0", "Plus", "FcnLambdaValue"],
      ].map((item) => [
        item[0],
        `Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.Integers.${item[1]}(tlc2.value.impl.IntValue,tlc2.value.impl.IntValue),\nbut it produced the following error:\nCannot cast tlc2.value.impl.${item[2]} to tlc2.value.impl.IntValue`,
      ]),
      [
        '1 .. "a" = {}',
        "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntervalValue tlc2.module.Integers.DotDot(tlc2.value.impl.IntValue,tlc2.value.impl.IntValue),\nbut it produced the following error:\nCannot cast tlc2.value.impl.StringValue to tlc2.value.impl.IntValue",
      ],
      [
        '-"a" = 0',
        "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.Integers.Neg(tlc2.value.impl.IntValue),\nbut it produced the following error:\nCannot cast tlc2.value.impl.StringValue to tlc2.value.impl.IntValue",
      ],
      [
        'IsFiniteSet("a")',
        'Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to check if the string "a" is a finite set.',
      ],
      ['"a" \\in Nat', 'Attempted to check if the value:\n"a"\nis an element of Nat.'],
      ['"a" \\in 1..2', 'Attempted to check if the value:\n"a"\nis in the integer interval 1..2'],
      ["1 \\in TRUE", "Attempted to check if the value:\n1\nis an element of the boolean TRUE"],
      ["1 \\in [a |-> 1]", "Attempted to check if element:\n1\nis in the record:\n[a |-> 1]"],
      ["1 \\in <<1>>", "Attempted to check set membership in a tuple value."],
      [
        "(SUBSET 0)..2 = {}",
        "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntervalValue tlc2.module.Integers.DotDot(tlc2.value.impl.IntValue,tlc2.value.impl.IntValue),\nbut it produced the following error:\nCannot cast tlc2.value.impl.SubsetValue to tlc2.value.impl.IntValue",
      ],
      ["SUBSET 0 = {}", "Attempted to compute the number of elements in the integer 0."],
      ['SUBSET "a" = {}', 'Attempted to compute the number of elements in the string "a".'],
      [
        "SUBSET <<1, 2>> = {}",
        "Attempted to compute the value of an expression of form\nSUBSET S, but S is a non-enumerable value:\n<<1, 2>>",
      ],
      [
        "1 \\in [{1} -> {2}]",
        "Attempted to check if \n1\nwhich is not a TLC function value, is in the set of functions:\n{<<2>>}",
      ],
      ["{{}} \\cup {1} = {}", "Attempted to check equality of the set {} with the value:\n1"],
      ["{1} \\ {{}} = {}", "Attempted to check equality of the set {} with the value:\n1"],
      ["Nat = 1", "Attempted to compare overridden value Nat with non-overridden value:\n1"],
      [
        "Seq({1}) = <<1>>",
        "Attempted to compare overridden value Seq({1}) with non-overridden value:\n<<1>>",
      ],
      [
        "(1..30) = <<1>>",
        "Attempted to check equality of the set { 1,\n  2,\n  3,\n  4,\n  5,\n  6,\n  7,\n  8,\n  9,\n  10,\n  11,\n  12,\n  13,\n  14,\n  15,\n  16,\n  17,\n  18,\n  19,\n  20,\n  21,\n  22,\n  23,\n  24,\n  25,\n  26,\n  27,\n  28,\n  29,\n  30 } with the value:\n<<1>>",
      ],
      ["{{}} \\cap {1} = {}", "Attempted to check equality of integer 1 with non-integer:\n{}"],
      [
        "0 \\in SUBSET {1}",
        "Attempted to check if the non-enumerable value\n0\nis element of\n{{}, {1}}",
      ],
      [
        "Nat \\in SUBSET Nat",
        "Attempted to check if the non-enumerable value\nNat\nis element of\nSUBSET Nat",
      ],
      [
        "{1, 2} \\subseteq 0",
        "Attempted to check if the value:\n1\nis an element of the integer 0",
      ],
      [
        "{1} \\subseteq [a |-> 1]",
        "Attempted to check if element:\n1\nis in the record:\n[a |-> 1]",
      ],
      ["{} \\subseteq 0", undefined],
    ];
    const checked = cases.filter((item) => declined[item[0] ?? ""] === undefined);
    const messages = await Promise.all(
      checked.map(async (item) => (await checkModule(`ASSUME ${item[0]}`)).violations[0]?.headline),
    );
    expect(messages).toEqual<unknown[]>(
      checked.map((item) => item[1] && getAssumptionFailure(6, item[0] ?? "", item[1])),
    );
    await Promise.all(
      Object.entries(declined).map((entry) =>
        expectDeclined(getModuleOptions(`ASSUME ${entry[0]}`), entry[1]),
      ),
    );
  });

  it("declines a failed Append", async () => {
    await expectDeclined(
      {
        source: "---- MODULE M ----\nEXTENDS Sequences\nASSUME Append(1, 2) = 0\n====",
        config: "",
      },
      getAssumptionDeclined("expected a sequence, not 1"),
    );
  });

  const EXPECTED_BOOLEAN = "TLC expected a boolean expression,\nbut instead found";

  // TLC evaluates the conjuncts left once every variable has a value, and walks the others.
  it.each([
    ["x = 0 /\\ 3", "x' = x", `In computing initial states, ${EXPECTED_BOOLEAN} 3.\n3`],
    [
      "x = 0 /\\ Op(x)",
      "x' = x",
      `In computing initial states, ${EXPECTED_BOOLEAN} 1.\nline 5, col 18 to line 5, col 22 of module M`,
    ],
    [
      "x = 0",
      "x' = x /\\ (0 \\div 3)",
      `In computing next states, ${EXPECTED_BOOLEAN} 0.\nline 6, col 20 to line 6, col 27 of module M`,
    ],
    ["3 /\\ x = 0", "x' = x", "The init state relation is not a boolean expression.\n3"],
    ["x = 0", "3 /\\ x' = x", "The next state relation is not a boolean expression.\n3"],
  ])("words a conjunct of %s or %s that isn't a boolean like TLC", async (init, next, message) => {
    const result = await checkOnEngine({
      source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nOp(a) == a + 1\nInit == ${init}\nNext == ${next}\n====`,
      config: "INIT Init\nNEXT Next",
    });
    expect(result.violations[0]?.headline).toContain(message);
  });

  it("declines a conjunct of x' = x /\\ \\b11 that isn't a boolean", async () => {
    await expectDeclined(
      {
        source:
          "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nOp(a) == a + 1\nInit == x = 0\nNext == x' = x /\\ \\b11\n====",
        config: "INIT Init\nNEXT Next",
      },
      "the engine stopped: a conjunct that isn't a boolean: evaluating the failure again: expected a boolean, not a integer",
    );
  });

  it.each([
    [
      "CASE 1 -> x = 0",
      "x' = x",
      "In computing initial states, a non-boolean expression (an integer) was used as a guard condition of a CASE.\nline 5, col 19 to line 5, col 23 of module M",
    ],
    [
      "CASE FALSE -> x = 0",
      "x' = x",
      "In computing initial states, TLC encountered a CASE with no conditions true.\nline 5, col 9 to line 5, col 27 of module M",
    ],
    [
      "x = 0",
      "CASE 1 -> x' = x",
      "In computing next states, a non-boolean expression (an integer) was used as a guard condition of a CASE.\nline 6, col 19 to line 6, col 24 of module M",
    ],
    [
      "IF 1 THEN x = 0 ELSE x = 1",
      "x' = x",
      "In computing initial states, a non-boolean expression (an integer) was used as the condition of an IF.\nline 5, col 9 to line 5, col 34 of module M",
    ],
    [
      "x = 0",
      "IF 1 THEN x' = 0 ELSE x' = 1",
      "In computing next states, a non-boolean expression (an integer) was used as the condition of an IF.line 6, col 9 to line 6, col 36 of module M",
    ],
    [
      "x \\in Nat",
      "x' = x",
      "In computing initial states, the right side of \\IN is not enumerable.\nline 5, col 9 to line 5, col 17 of module M",
    ],
  ])("words a failed CASE, IF or \\IN in %s or %s like TLC", async (init, next, message) => {
    const result = await checkOnEngine({
      source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nOp(a) == a + 1\nInit == ${init}\nNext == ${next}\n====`,
      config: "INIT Init\nNEXT Next",
    });
    expect(result.violations[0]?.headline).toContain(message);
  });

  it.each([
    [
      "CASE x -> x' = x",
      "In computing ENABLED, a non-boolean expression(an integer) was used as a guard condition of a CASE.\nline 5, col 16 to line 5, col 21 of module M",
    ],
    [
      "IF x THEN x' = x ELSE x' = 1",
      "In computing ENABLED, a non-boolean expression(an integer) was used as the guard condition of an IF.\nline 5, col 6 to line 5, col 33 of module M",
    ],
    [
      "x' \\in Nat",
      "The right side of \\IN is not enumerable.\nline 5, col 6 to line 5, col 15 of module M",
    ],
  ])("words a failed %s in a fair action like TLC", async (action, message) => {
    const result = await checkOnEngine({
      source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nA == ${action}\nSpec == Init /\\ [][x' = x]_x /\\ WF_x(A)\nP == <>(x = 0)\n====`,
      config: "SPECIFICATION Spec\nPROPERTY P",
    });
    expect(result.violations[0]?.headline).toContain(message);
  });

  // TLC's enabled walks the action, and words a literal it walks to differently.
  it.each([
    ["3", "Attempted to compute ENABLED on a non-boolean expression.\n3"],
    [
      "x + 3",
      `In computing ENABLED, ${EXPECTED_BOOLEAN} 3.\nline 5, col 31 to line 5, col 35 of module M`,
    ],
  ])("words a conjunct of a fair action that is %s like TLC", async (value, message) => {
    const result = await checkOnEngine({
      source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nA == x' = x /\\ (IF x = 0 THEN ${value} ELSE TRUE)\nSpec == Init /\\ [][x' = x]_x /\\ WF_x(A)\nP == <>(x = 0)\n====`,
      config: "SPECIFICATION Spec\nPROPERTY P",
    });
    expect(result.violations[0]?.headline).toContain(message);
  });

  const getFairPrintRun = (action: string, config: string) => ({
    source: `---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nA == PrintT(x) /\\ ${action}\nSpec == Init /\\ [][A]_x /\\ WF_x(A)\nP == [](x = 0 => <>(x = 1))\nInv == x < 1\n====`,
    config: `SPECIFICATION Spec\nPROPERTY P\n${config}`,
  });

  it("declines the action of ENABLED that prints on a counterexample", async () => {
    await expectDeclined(
      {
        source:
          '---- MODULE M ----\nEXTENDS TLC\nVARIABLE y\nInit == y = 0\nA == y\' = 0 /\\ PrintT("A")\nNext == A\nProp == [](ENABLED A => <>FALSE)\n====',
        config: "INIT Init\nNEXT Next\nPROPERTY Prop",
        onPrint: () => {},
      },
      "the engine stopped: printing where the native checker doesn't check the temporal properties: a predicate the engine leaves to the interpreter",
    );
  });

  it("adds a state to the behavior graph after a violation by a successor it never stored", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nVARIABLE x\nInit == x = 0\nA == x' = 0\nNext == A \\/ x' = 1\nSpec == Init /\\ [][Next]_x\nInv == x # 1\nLive == [](ENABLED A => <>FALSE)\n====",
      config: "SPECIFICATION Spec\nINVARIANT Inv\nPROPERTY Live",
    });
    expect([result.status, result.violations[0]?.headline]).toEqual([
      "invariant-violation",
      "Invariant Inv is violated.",
    ]);
  });

  // CallStackTool gives a set a source, so TLC's worker fails with a FingerprintException as it adds
  // the state to the behavior graph again, which it doesn't catch, and TLC replays the next states.
  it("declines adding a state to the behavior graph that fails to fingerprint", () => {
    const run = runOnEngine(
      {
        source:
          "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nA == (\\E k \\in {1} \\cup SUBSET 3 : TRUE) /\\ x' = x\nSpec == Init /\\ [][A]_x /\\ SF_x(A)\nLive == <>(x = 0)\n====",
        config: "SPECIFICATION Spec\nPROPERTY Live",
      },
      "the engine stopped: enumerated a non-set: evaluating the failure again: SUBSET of a non-set",
    );
    expect(run.exitCode).toBe(1);
  });

  it("declines adding a state whose next states fail to the behavior graph", () => {
    const run = runOnEngine(
      getFairPrintRun("(x' = 1 \\/ x' = 1 \\div 0)", ""),
      "the engine stopped: division by zero: a late node of a state whose next states fail, which TLC fails on again",
    );
    expect(run.exitCode).toBe(1);
  });

  it.each([
    ["an invariant violation", "INVARIANT Inv", ["0", "0", "0", "0", "0", "0", "0", "0"]],
    ["a deadlock", "", ["0", "1", "2"]],
  ])("prints what adding a state to the behavior graph prints after %s", (_, config, expected) => {
    const run = runOnEngine(getFairPrintRun("x < 2 /\\ x' = x + 1", config));
    expect(getTraceOutput(run.output)).toEqual(expected);
  });

  it.each([
    ["(1 :> 2 @@ 3 :> 4)", 'y["a"]', 'check equality of integer 1 with non-integer:\n"a"'],
    [
      "[i \\in {2 * k : k \\in 1..40} |-> i]",
      'y["a"]',
      'Attempted to compare integer 40 with non-integer:\n"a"',
    ],
    ["<<1, 2>>", 'y["a"]', 'Attempted to access tuple at a non integral index: "a"'],
    ["[a |-> 1]", "y[1]", "Attempted to access record by a non-string argument: 1"],
    ["<<1, 2>>", "[y EXCEPT ![1][1] = 2]", "apply EXCEPT construct to the value 1."],
    ["{1, 2}", "y.a", 'Attempted to select field "a" from a non-record value {1, 2}'],
    ["<<1, 2>>", "y.a", 'integer domain to the non-integer argument "a"'],
  ])(
    "words a key of the wrong type for y = %s and x' = %s like TLC",
    async (value, next, message) => {
      const result = await checkOnEngine({
        source: `---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLES x, y\nInit == x = 0 /\\ y = ${value}\nNext == x' = ${next} /\\ UNCHANGED y\n====`,
        config: "INIT Init\nNEXT Next",
      });
      expect(result.violations[0]?.headline).toContain(message);
    },
  );

  it("declines a key of the wrong type for y = [i \\in 1..2 |-> i]", async () => {
    await expectDeclined(
      {
        source:
          '---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLES x, y\nInit == x = 0 /\\ y = [i \\in 1..2 |-> i]\nNext == x\' = y["a"] /\\ UNCHANGED y\n====',
        config: "INIT Init\nNEXT Next",
      },
      "the engine stopped: applied a function outside its domain: evaluating the failure again: values TLC can't compare",
    );
  });

  it("declines SUBSET of a function with an empty domain", async () => {
    await expectDeclined(
      getModuleOptions("ASSUME SUBSET <<>> = {{}}"),
      getAssumptionDeclined("SUBSET of a non-set"),
    );
  });

  it.each([true, false])(
    "declines naming the Java class of .. when TLC records a trace is %s",
    async (isTraceRecorded) => {
      await expectDeclined(
        {
          source: '---- MODULE M ----\nEXTENDS Naturals\nASSUME 1 .. "a" = {}\n====',
          config: "",
          isTraceRecorded,
        },
        getAssumptionDeclined("expected an integer, not a string"),
      );
    },
  );

  // tlc2.module.Naturals#Divide rounds some negative quotients toward 0, and doesn't report an
  // overflow, unlike tlc2.module.Integers#Divide.
  it.each([
    [false, "Naturals", ["<<0, 0, -2>>", "-2147483648"]],
    [true, "Naturals", ["<<-1, -1, -2>>"]],
    [false, "Integers", ["<<-1, -1, -2>>"]],
  ])(
    "divides negative integers as TLC does when it records a trace (%s) for a spec of %s",
    async (isTraceRecorded, module, quotients) => {
      const printed: string[] = [];
      await checkOnEngine({
        source: `---- MODULE M ----\nEXTENDS ${module}, TLC\nASSUME PrintT(<<1 \\div (0 - 2), (0 - 1) \\div 2, (0 - 3) \\div 2>>)\nASSUME PrintT((0 - 2147483647 - 1) \\div (0 - 1))\n====`,
        config: "",
        isTraceRecorded,
        onPrint: (text) => printed.push(text),
      });
      expect(printed).toEqual(quotients);
    },
  );

  it("locates IF, CHOOSE, conjunction, DOMAIN, and field errors like TLC", async () => {
    const declined: Record<string, string> = {
      "ASSUME CHOOSE e \\in Seq({1}) : TRUE": getAssumptionDeclined("enumerated an infinite set"),
      "ASSUME CHOOSE e \\in 3 : TRUE": getAssumptionDeclined("expected a set, not a integer"),
      "ASSUME\n    /\\ TRUE\n    /\\ {1}": getAssumptionDeclined("expected a boolean, not a set"),
    };
    const cases = [
      [
        "ASSUME IF 1 THEN TRUE ELSE FALSE",
        "A non-boolean expression (an integer) was used as the condition of an IF.\nline 6, col 8 to line 6, col 32 of module M",
      ],
      [
        "ASSUME CHOOSE e \\in {} : TRUE",
        "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\nline 6, col 8 to line 6, col 29 of module M",
      ],
      [
        "ASSUME CHOOSE e \\in Seq({1}) : TRUE",
        "Attempted to compute the value of an expression of\nform CHOOSE x \\in S: P, but S was not enumerable.\nline 6, col 8 to line 6, col 35 of module M",
      ],
      ["ASSUME \\A e \\in 1 : TRUE", "TLC encountered a non-enumerable quantifier bound\n1.\n1"],
      [
        "ASSUME {e \\in 1 : TRUE} = {}",
        "Attempted to enumerate { x \\in S : p(x) } when S:\n1\nis not enumerable",
      ],
      [
        "ASSUME CASE 1 -> TRUE",
        "A non-boolean expression (an integer) was used as a condition of a CASE. 1",
      ],
      [
        "ASSUME CHOOSE e \\in 3 : TRUE",
        "Attempted to compute the value of an expression of\nform CHOOSE x \\in S: P, but S was not enumerable.\nline 6, col 8 to line 6, col 28 of module M",
      ],
      [
        "ASSUME 1 /\\ TRUE",
        "Attempted to evaluate an expression of form P /\\ Q when P was\nan integer.\nline 6, col 8 to line 6, col 16 of module M",
      ],
      [
        "ASSUME TRUE /\\ 1 /\\ TRUE",
        "Attempted to evaluate an expression of form P /\\ Q when Q was\nan integer.\nline 6, col 8 to line 6, col 16 of module M",
      ],
      [
        "ASSUME\n    /\\ TRUE\n    /\\ {1}",
        "A non-boolean expression (a set of the form {e1, ... ,eN}) was used as a formula in a conjunction.\nline 8, col 8 to line 8, col 10 of module M",
      ],
      [
        "ASSUME\n    /\\ TRUE\n    /\\ 1",
        "A non-boolean expression (an integer) was used as a formula in a conjunction.\n1",
      ],
      [
        "ASSUME DOMAIN 1 = {}",
        "Attempted to apply the operator DOMAIN to a non-function\n(an integer)\nline 6, col 8 to line 6, col 15 of module M",
      ],
      [
        "ASSUME [a |-> 1].b = 0",
        'Attempted to select nonexistent field "b" from the record\n[a |-> 1]\nline 6, col 8 to line 6, col 18 of module M',
      ],
    ];
    const checked = cases.filter((item) => declined[item[0] ?? ""] === undefined);
    const messages = await Promise.all(
      checked.map(async (item) => (await checkModule(item[0] ?? "")).violations[0]?.headline),
    );
    expect(messages).toEqual(
      checked.map((item) => getAssumeFailure(6, item[0] ?? "", item[1] ?? "")),
    );
    await Promise.all(
      Object.entries(declined).map((entry) => expectDeclined(getModuleOptions(entry[0]), entry[1])),
    );
  });

  it("treats a function as a finite set like TLC", async () => {
    expect((await checkModule("ASSUME IsFiniteSet(<<1>>) /\\ IsFiniteSet([a |-> 1])")).status).toBe(
      "success",
    );
  });

  it.each(["[n \\in -12..12 |-> n][13] = 0", '[n \\in {"a"} |-> n]["b"] = 0'])(
    "declines an argument outside the domain of a function construction in %s",
    async (assumption) => {
      await expectDeclined(
        getModuleOptions(`ASSUME ${assumption}`),
        getAssumptionDeclined("applied a function outside its domain"),
      );
    },
  );

  it("reports an overflowing cardinality without enumerating the set", async () => {
    const result = await checkModule("ASSUME Cardinality(SUBSET (1..31)) > 0");
    expect(result.violations[0]?.headline).toBe(
      getAssumptionFailure(
        6,
        "Cardinality(SUBSET (1..31)) > 0",
        "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value),\nbut it produced the following error:\nOverflow when computing the number of elements in:\nSUBSET (1..31)",
      ),
    );
  });

  it("wraps a failure inside an operator that another operator's Java method calls", async () => {
    const result = await checkModule(
      "ASSUME SelectSeq(<<1>>, LAMBDA e : Cardinality(SUBSET (1..31)) > e) = <<>>",
    );
    expect(result.violations[0]?.headline).toBe(
      getAssumptionFailure(
        6,
        "SelectSeq(<<1>>, LAMBDA e : Cardinality(SUBSET (1..31)) > e) = <<>>",
        "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.Sequences.SelectSeq(tlc2.value.impl.Value,tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value),\nbut it produced the following error:\nOverflow when computing the number of elements in:\nSUBSET (1..31)",
      ),
    );
  });

  it("declines membership in a set enumeration TLC can't sort element by element", async () => {
    await expectDeclined(
      getModuleOptions(
        'ASSUME 1 \\in {1, "a"}\nASSUME [e \\in {1, "a"} |-> e][1] = 1\nASSUME "a" \\in {1, "a"}',
      ),
      getAssumptionDeclined("it didn't fail"),
    );
  });

  it("shows a record in the order the spec writes it until TLC sorts it", async () => {
    const prints: string[] = [];
    await checkOnEngine({
      source:
        '---- MODULE M ----\nEXTENDS TLC\nASSUME PrintT([fld2 |-> 0])\nASSUME PrintT(ToString([fld1 |-> 1, fld2 |-> 2]))\nASSUME PrintT(ToString(("fld1" :> 1) @@ ("fld3" :> 3) @@ ("fld2" :> 2)))\nASSUME PrintT([fld1 |-> 1, fld2 |-> 2])\n====',
      config: "",
      onPrint: (text) => prints.push(text),
    });
    expect(prints.slice(1)).toEqual([
      '"[fld1 |-> 1, fld2 |-> 2]"',
      '"[fld1 |-> 1, fld3 |-> 3, fld2 |-> 2]"',
      "[fld2 |-> 2, fld1 |-> 1]",
    ]);
  });

  it("declines a TLCEval argument TLC can't sort, inside an instance that substitutes or not", async () => {
    const inner =
      '---- MODULE Inner ----\nEXTENDS TLC\nCONSTANT K\nMixed == 1 \\in TLCEval({1, "a"})\n====';
    await expectDeclined(
      {
        source: "---- MODULE M ----\nEXTENDS TLC\nINSTANCE Inner WITH K <- 1\nASSUME Mixed\n====",
        config: "",
        loadModule: (name) => (name === "Inner" ? inner : undefined),
      },
      getAssumptionDeclined("it didn't fail"),
    );
    await expectDeclined(
      getModuleOptions('ASSUME 1 \\in TLCEval({1, "a"})'),
      getAssumptionDeclined("it didn't fail"),
    );
  });

  it("rejects a mistyped membership outside an assumption", async () => {
    const result = await checkOnEngine({
      source:
        '---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = "a" /\\ x \\in Nat\nNext == x\' = x\n====',
      config: "INIT Init\nNEXT Next",
    });
    expect(result.status).toBe("error");
  });

  it("treats untyped model values as outside built-in sets", async () => {
    const result = await checkModule(
      'CONSTANT m\nASSUME ~(m \\in Nat) /\\ ~(m \\in Int) /\\ ~(m \\in STRING) /\\ ~(m \\in 1..3) /\\ ~(m \\in Seq({1}))\nASSUME ~("a" \\in 3..1)',
      "CONSTANT m = m",
    );
    expect(result.status).toBe("success");
  });

  it.each([
    ["Nat", "Nat"],
    ["Seq({1})", "Seq({1})"],
    ["[a : {1}]", "{[a |-> 1]}"],
    ["{1} \\X {1}", "{<<1, 1>>}"],
  ])("rejects a typed model value's membership in %s", async (set, shown) => {
    const result = await checkModule(`CONSTANT m\nASSUME m \\in ${set}`, "CONSTANT m = A_b");
    expect(result.status).toBe("assumption-violation");
    expect(result.violations[0]?.headline).toBe(
      getAssumptionFailure(
        7,
        `m \\in ${set}`,
        `Attempted to check if the typed model value A_b is an element of\n${shown}`,
      ),
    );
  });

  it("rejects a typed model value's membership in an interval", async () => {
    const result = await checkModule("CONSTANT m\nASSUME m \\in 1..3", "CONSTANT m = A_b");
    expect(result.violations[0]?.headline).toBe(
      getAssumptionFailure(
        7,
        "m \\in 1..3",
        "Attempted to check if the value:\nA_b\nis in the integer interval 1..3",
      ),
    );
  });

  it.each(['"a" \\in Nat', "1 \\in STRING", "{} \\in 1..4", "FALSE \\in Int"])(
    "rejects %s",
    async (membership) => {
      const result = await checkModule(`ASSUME ${membership}`);
      expect(result.status).toBe("assumption-violation");
      expect(result.violations[0]?.headline).toStartWith(
        getAssumptionFailure(6, membership, "Attempted to check if the value"),
      );
    },
  );

  it.each([
    ["1 \\in TRUE", "Attempted to check if the value:\n1\nis an element of the boolean TRUE"],
    ["1 \\notin 5", "Attempted to check if the value:\n1\nis an element of the integer 5"],
    ['1 \\in "abc"', 'Attempted to check if the value:\n1\nis an element of the string "abc"'],
    ["1 \\in m", "Attempted to check if the value:\n1\nis an element of the model value m"],
    ["1 \\in <<1, 2>>", "Attempted to check set membership in a tuple value."],
    ["1 \\in [a |-> 1]", "Attempted to check if element:\n1\nis in the record:\n[a |-> 1]"],
  ])("words %s like TLC", async (membership, message) => {
    const result = await checkModule(`CONSTANT m\nASSUME ${membership}`, "CONSTANT m = m");
    expect(result.status).toBe("assumption-violation");
    expect(result.violations[0]?.headline).toBe(getAssumptionFailure(7, membership, message));
  });

  it.each([
    ["TLCGet(42)", "the engine stopped: TLCGet of a register TLC hasn't set"],
    ['TLCGet("nope")', "the engine stopped: unsupported: TLCGet of a key the search doesn't keep"],
    ["TLCGet(<<1>>)", "the engine stopped: TLCGet of a key that isn't a natural number"],
  ])("declines a failing %s", (value, reason) => {
    const run = runOnEngine(
      {
        source: `---- MODULE M ----\nEXTENDS TLC\nVARIABLE x\nInit == x = ${value}\nNext == UNCHANGED x\n====`,
        config: "INIT Init\nNEXT Next",
      },
      reason,
    );
    expect(run.exitCode).toBe(1);
  });

  it("reports a property that is an action like TLC", async () => {
    // TLC's test-model/ActionLevelProp.tla and its ActionLevelProp*Test cases.
    const source = [
      "---- MODULE ActionLevelProp ----",
      "EXTENDS Naturals",
      "",
      "VARIABLE x",
      "vars == x",
      "",
      "Init ==",
      "    x = 0",
      "",
      "Next ==",
      "    /\\ x < 5",
      "    /\\ x' = x + 1",
      "",
      "Spec ==",
      "    Init /\\ [][Next]_vars",
      "",
      "------",
      "",
      "ActionLivePropA ==",
      "    x' > x",
      "",
      "ActionLivePropB ==",
      "\tNext",
      "",
      "ActionLivePropC ==",
      "    Next \\/ UNCHANGED vars",
      "",
      "ActionLivePropD ==",
      "    [Next]_vars",
      "",
      "ActionLivePropE ==",
      "    <<Next>>_vars",
      "",
      "====",
    ].join("\n");
    // TLC rejects the configuration before it searches.
    const getFailure = (property: string) =>
      checkOnEngine({ source, config: `SPECIFICATION Spec\nPROPERTY ${property}` }).then(
        () => undefined,
        (error: unknown) => (error instanceof TlaConfigError ? error.message : error),
      );
    const formula = (name: string, at: string) =>
      `The formula ${name} at ${at} is an action-level formula (i.e., it contains no temporal operators). Only temporal-level (or state-level) formulas are allowed under PROPERTY or PROPERTIES.`;
    const book = "https://lamport.azurewebsites.net/tla/book.html";
    const rewrite = (name: string, at: string) =>
      `${formula(name, at)} To check that action ${name} holds in *every* step of the behavior, define a temporal property: Let A be the formula at ${at}; rewrite A as [][A]_v, where v is a state function (typically the tuple of variables) (compare page 90 of Specifying Systems at ${book}).`;
    const at = (line: number, from: number, to: number) =>
      `line ${line}, col ${from} to line ${line}, col ${to} of module ActionLevelProp`;
    expect(await getFailure("ActionLivePropA")).toBe(rewrite("ActionLivePropA", at(20, 5, 10)));
    // TLC names a conjunct of the action by its location.
    expect(await getFailure("ActionLivePropB")).toBe(rewrite(at(12, 8, 17), at(12, 8, 17)));
    expect(await getFailure("ActionLivePropC")).toBe(rewrite("ActionLivePropC", at(26, 5, 26)));
    expect(await getFailure("ActionLivePropD")).toBe(
      `${formula("ActionLivePropD", at(29, 5, 15))} To check that action ActionLivePropD holds in *every* step of the behavior, define a temporal property by applying the "always" temporal operator ([]) to the formula at ${at(29, 5, 15)} (compare page 90 of Specifying Systems at ${book}).`,
    );
    expect(await getFailure("ActionLivePropE")).toBe(
      `${formula("ActionLivePropE", at(32, 5, 17))} To check that infinitely many ActionLivePropE steps occur, define a temporal property by applying the "always eventually" temporal operator combination ([]<>) to the formula at ${at(32, 5, 17)} (compare page 91 of Specifying Systems at ${book}).`,
    );
  });

  it("reports action composition as unsupported like TLC", () => {
    const run = runOnEngine({
      source:
        "---- MODULE M ----\nVARIABLE x\nInit == x = 0\nNext == x' = 1\nInv == ENABLED (Next \\cdot Next)\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT Inv",
    });
    expect([getErrors(run.output)[0], run.exitCode]).toEqual([
      "The current version of TLC does not support action composition.  An incomplete implementation can be enabled via the tlc2.tool.impl.Tool.cdot=true java property.\nWhile working on the initial state:\nx = 0",
      75,
    ]);
  });

  it("declines a stack overflow in the next-state relation", async () => {
    await expectDeclined(
      {
        source:
          "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nRECURSIVE R(_)\nR(n) == R(n + 1)\nInit == x = 0\nNext == x' = R(0)\n====",
        config: "INIT Init\nNEXT Next",
      },
      "the engine stopped: recursion too deep",
    );
  });

  it("reports a successor the next-state relation leaves incomplete like TLC", async () => {
    const getOptions = (next: string) => ({
      source: `---- MODULE M ----\nVARIABLES x, y, z\nInit == x = 0 /\\ y = 0 /\\ z = 0\nA1 == x' = 1\nA2 == x' = 2 /\\ y' = 2 /\\ z' = 2\nNext == ${next}\n====`,
      config: "INIT Init\nNEXT Next",
    });
    const single = runOnEngine(getOptions("x' = 1 /\\ y' = 1"));
    expect([getErrors(single.output)[0], single.exitCode, getStatistics(single.output)[0]]).toEqual(
      [
        "Successor state is not completely specified by the next-state action. The following variable is not defined: z.",
        75,
        "2 states generated, 1 distinct states found, 0 states left on queue.",
      ],
    );
    const several = await checkOnEngine(getOptions("A1 \\/ A2"));
    expect(several.violations[0]?.headline).toBe(
      "Successor state is not completely specified by action A1 of the next-state relation. The following variables are not defined: y, z.\n",
    );
    expect(
      several.violations[0]?.states.map((step) => [step.label, step.variables.y?.text]),
    ).toEqual([
      ["Initial predicate", "0"],
      ["A1 line 4, col 7 to line 4, col 12 of module M", "null"],
    ]);
  });

  it("reports a value where the initial or next-state relation expects a formula like TLC", async () => {
    const getOptions = (init: string, next: string) => ({
      source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == ${init}\nNext == ${next}\n====`,
      config: "INIT Init\nNEXT Next",
    });
    const getRunFailure = (init: string, next: string) => {
      const run = runOnEngine(getOptions(init, next));
      return [getErrors(run.output)[0], run.exitCode];
    };
    expect(getRunFailure("x = 0 /\\ x + 3", "x' = x")).toEqual([
      "In computing initial states, TLC expected a boolean expression,\nbut instead found 3.\nline 4, col 18 to line 4, col 22 of module M",
      75,
    ]);
    expect(getRunFailure("x = 0", "x' = 1 /\\ x + 2")).toEqual([
      `${UNEXPECTED_EXCEPTION}In computing next states, TLC expected a boolean expression,\nbut instead found 2.\nline 5, col 19 to line 5, col 23 of module M`,
      75,
    ]);
    await expectDeclined(
      getOptions("x = 0", "3"),
      "the engine stopped: a guard that isn't a boolean: evaluating the failure again: a next-state relation the IR holds no actions of",
    );
  });

  const getConstraintRun = (constraint: string, kind: string) => ({
    source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\nC == ${constraint}\n====`,
    config: `INIT Init\nNEXT Next\n${kind} C`,
  });

  it("declines a failing constraint on a successor as a CONSTRAINT", () => {
    const run = runOnEngine(
      getConstraintRun("x < 1 \\/ x[1] = 0", "CONSTRAINT"),
      "the engine stopped: a constraint, a VIEW or an action property that fails on a successor",
    );
    expect(run.exitCode).toBe(1);
  });

  it("reports a failing ACTION_CONSTRAINT on a successor like a failure of the next-state relation", () => {
    const run = runOnEngine(getConstraintRun("x' < 1 \\/ x[1] = 0", "ACTION_CONSTRAINT"));
    expect([getErrors(run.output).slice(0, 2), run.exitCode]).toEqual([
      [
        "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: A non-function (an integer) was applied as a function.\nline 6, col 16 to line 6, col 19 of module M",
        "The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Next line 5, col 9 to line 5, col 18 of module M>\nx = 1",
      ],
      75,
    ]);
  });

  it("reports a successor it cannot fingerprint as a failure of the state it expands", () => {
    const run = runOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Integers\nVARIABLE x\nInit == x = 0\nNext == x' = SUBSET (SUBSET (1..32))\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect([getErrors(run.output).slice(0, 2), run.exitCode]).toEqual([
      [
        "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: Overflow when computing the number of elements in:\nSUBSET (1..32)",
        "The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0",
      ],
      75,
    ]);
  });

  it("reports a SUBSET too large to enumerate like TLC", () => {
    const run = runOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Integers\nVARIABLE x\nInit == x = SUBSET (SUBSET (1..36))\nNext == x' = x\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect([getErrors(run.output)[0], run.exitCode]).toEqual([
      "Overflow when computing the number of elements in:\nSUBSET (1..36)\nWhile working on the initial state:\nx = SUBSET SUBSET (1..36)",
      75,
    ]);
  });

  it("reports a variable read before the initial predicate assigns it like TLC", () => {
    const run = runOnEngine({
      source:
        "---- MODULE M ----\nVARIABLES x, y\nInit == y = x /\\ x = 0\nNext == UNCHANGED <<x, y>>\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect([getErrors(run.output)[0], run.exitCode]).toEqual([
      "In evaluation, the identifier x is either undefined or not an operator.\nline 3, col 13 to line 3, col 13 of module M",
      75,
    ]);
  });

  it("reports a variable drawn from a set it can't enumerate like TLC", () => {
    const run = runOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x \\in Nat\nNext == UNCHANGED x\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect([getErrors(run.output)[0], run.exitCode]).toEqual([
      "In computing initial states, the right side of \\IN is not enumerable.\nline 4, col 9 to line 4, col 17 of module M",
      75,
    ]);
  });

  it("reports a CASE with no true guard in the initial predicate like TLC", () => {
    const run = runOnEngine({
      source: "---- MODULE M ----\nVARIABLE x\nInit == CASE FALSE -> x = 0\nNext == x' = x\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect([getErrors(run.output)[0], run.exitCode]).toEqual([
      "In computing initial states, TLC encountered a CASE with no conditions true.\nline 3, col 9 to line 3, col 27 of module M",
      75,
    ]);
  });

  it("reports a failure of the next-state relation as an unexpected exception like TLC", () => {
    const runs = ["x' = CHOOSE n \\in {} : TRUE", "x' = 1 \\div 0"].map((next) =>
      runOnEngine({
        source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == ${next}\n====`,
        config: "INIT Init\nNEXT Next",
      }),
    );
    expect(runs.map((run) => [getErrors(run.output)[0], run.exitCode])).toEqual([
      [
        `${UNEXPECTED_EXCEPTION}Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\nline 5, col 14 to line 5, col 35 of module M`,
        75,
      ],
      ["The second argument of \\div is 0.", 255],
    ]);
  });

  it("declines quantifying over a power set too large to build", async () => {
    await expectDeclined(
      getModuleOptions(
        [
          "ASSUME \\E s \\in SUBSET (1..40) : Cardinality(s) = 2",
          "ASSUME ~\\A s \\in SUBSET (1..40) : Cardinality(s) < 1",
          "ASSUME (CHOOSE s \\in SUBSET (1..40) : Cardinality(s) = 1) = {1}",
          "ASSUME (CHOOSE s \\in SUBSET (1..32) : Cardinality(s) = 2 /\\ 5 \\in s) = {1, 5}",
        ].join("\n"),
      ),
      getAssumptionDeclined("a power set too large to build"),
    );
  });

  it.each([
    ["Nat", "UNCHANGED x"],
    ["{}", "x' = SUBSET Nat"],
  ])(
    "declines a state holding a set it can't enumerate to fingerprint: x = %s, %s",
    (init, next) => {
      const run = runOnEngine(
        {
          source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = ${init}\nNext == ${next}\n====`,
          config: "INIT Init\nNEXT Next",
        },
        "the engine stopped: enumerated Nat",
      );
      expect(run.exitCode).toBe(1);
    },
  );

  it("applies a set operator to a value that isn't a set until it needs its elements, like TLC", async () => {
    const result = await checkModule(
      [
        "ASSUME 1 \\in ({1} \\cup 0)",
        "ASSUME 1 \\in (0 \\cup {1})",
        'ASSUME 1 \\in ((1..2) \\cup "a")',
        "ASSUME ({} \\cup 0) = 0",
        "ASSUME ({} \\cap 0) = {}",
      ].join("\n"),
    );
    expect(result.violations).toEqual([]);
    const messages = await Promise.all(
      ["2 \\in ({1} \\cup 0)", "1 \\in (0 \\ {1})", "Cardinality({1} \\cup 0) = 1"].map(
        async (expression) => (await checkModule(`ASSUME ${expression}`)).violations[0]?.headline,
      ),
    );
    expect(messages).toEqual(
      [
        "Attempted to check if the value:\n2\nis an element of the integer 0",
        "Attempted to check if the value:\n1\nis an element of the integer 0",
        "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to enumerate S \\cup T when S:\n{1}\nand T:\n0\nare not both enumerable",
      ].map((message, index) =>
        getAssumptionFailure(
          6,
          ["2 \\in ({1} \\cup 0)", "1 \\in (0 \\ {1})", "Cardinality({1} \\cup 0) = 1"][index] ??
            "",
          message,
        ),
      ),
    );
  });

  it.each(["Naturals", "Naturals, Sequences", "Naturals, Integers", "Naturals, TLCExt"])(
    "declines naming the Java class in an arithmetic error of a spec that extends %s",
    async (modules) => {
      await expectDeclined(
        {
          source: `---- MODULE M ----\nEXTENDS ${modules}\nASSUME 1 + "a" = 1\n====`,
          config: "",
        },
        getAssumptionDeclined("expected an integer, not a string"),
      );
    },
  );

  it("locates IF, CHOOSE, conjunction, DOMAIN, application, and field errors like TLC", async () => {
    const declined: Record<string, string> = {
      "ASSUME\n    /\\ TRUE\n    /\\ {1}": getAssumptionDeclined("expected a boolean, not a set"),
    };
    const cases = [
      [
        "ASSUME IF 1 THEN TRUE ELSE FALSE",
        "A non-boolean expression (an integer) was used as the condition of an IF.\nline 6, col 8 to line 6, col 32 of module M",
      ],
      [
        "ASSUME CHOOSE e \\in {} : TRUE",
        "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\nline 6, col 8 to line 6, col 29 of module M",
      ],
      [
        "ASSUME 1 /\\ TRUE",
        "Attempted to evaluate an expression of form P /\\ Q when P was\nan integer.\nline 6, col 8 to line 6, col 16 of module M",
      ],
      [
        "ASSUME TRUE /\\ 1 /\\ TRUE",
        "Attempted to evaluate an expression of form P /\\ Q when Q was\nan integer.\nline 6, col 8 to line 6, col 16 of module M",
      ],
      [
        "ASSUME\n    /\\ TRUE\n    /\\ {1}",
        "A non-boolean expression (a set of the form {e1, ... ,eN}) was used as a formula in a conjunction.\nline 8, col 8 to line 8, col 10 of module M",
      ],
      [
        "ASSUME\n    /\\ TRUE\n    /\\ 1",
        "A non-boolean expression (an integer) was used as a formula in a conjunction.\n1",
      ],
      [
        "ASSUME DOMAIN 1 = {}",
        "Attempted to apply the operator DOMAIN to a non-function\n(an integer)\nline 6, col 8 to line 6, col 15 of module M",
      ],
      [
        "ASSUME [a |-> 1].b = 0",
        'Attempted to select nonexistent field "b" from the record\n[a |-> 1]\nline 6, col 8 to line 6, col 18 of module M',
      ],
      [
        "ASSUME 3[1] = 0",
        "A non-function (an integer) was applied as a function.\nline 6, col 8 to line 6, col 11 of module M",
      ],
      [
        'ASSUME "ab"[1, 2] = 0',
        "A non-function (a string) was applied as a function.\nline 6, col 8 to line 6, col 17 of module M",
      ],
      [
        "ASSUME {1}.b = 0",
        'Attempted to select field "b" from a non-record value {1}\nline 6, col 8 to line 6, col 12 of module M',
      ],
    ];
    const checked = cases.filter((item) => declined[item[0] ?? ""] === undefined);
    const messages = await Promise.all(
      checked.map(async (item) => (await checkModule(item[0] ?? "")).violations[0]?.headline),
    );
    expect(messages).toEqual(
      checked.map((item) => getAssumeFailure(6, item[0] ?? "", item[1] ?? "")),
    );
    await Promise.all(
      Object.entries(declined).map((entry) => expectDeclined(getModuleOptions(entry[0]), entry[1])),
    );
  });

  it("reports an argument outside the domain of a tuple, record, or function like TLC", async () => {
    const declined: Record<string, string> = {
      "[n \\in 0..2 |-> n].b": getAssumptionDeclined("values TLC can't compare"),
    };
    const cases = [
      ["<<1, 2>>[3]", "Attempted to access index 3 of tuple\n<<1, 2>>\nwhich is out of bounds."],
      ['<<1, 2>>["a"]', 'Attempted to access tuple at a non integral index: "a"'],
      ["[a |-> 1][2]", "Attempted to access record by a non-string argument: 2"],
      ['[a |-> 1]["b"]', "Attempted to access nonexistent field 'b' of record\n[a |-> 1]"],
      [
        "(1 :> 2)[3]",
        "Attempted to apply function:\n<<2>>\nto argument 3, which is not in the domain of the function.",
      ],
      ["<<>>.b", 'Attempted to apply function with integer domain to the non-integer argument "b"'],
      [
        "[n \\in 0..2 |-> n].b",
        'Attempted to apply function with integer domain to the non-integer argument "b"',
      ],
      [
        "[n \\in {} |-> n].b",
        'Attempted to apply function:\n<<>>\nto argument "b", which is not in the domain of the function.',
      ],
    ];
    const checked = cases.filter((item) => declined[item[0] ?? ""] === undefined);
    const messages = await Promise.all(
      checked.map(
        async (item) => (await checkModule(`ASSUME ${item[0]} = 0`)).violations[0]?.headline,
      ),
    );
    expect(messages).toEqual(
      checked.map((item) => getAssumptionFailure(6, `${item[0]} = 0`, item[1] ?? "")),
    );
    await Promise.all(
      Object.entries(declined).map((entry) =>
        expectDeclined(getModuleOptions(`ASSUME ${entry[0]} = 0`), entry[1]),
      ),
    );
  });
});

describe("DOMAIN matches TLC", () => {
  const printDomain = async (expression: string) => {
    const printed: string[] = [];
    await checkOnEngine({
      source: `---- MODULE M ----\nEXTENDS Integers, TLC\nASSUME PrintT(${expression})\n====`,
      config: "",
      onPrint: (text) => printed.push(text),
    });
    return printed;
  };

  it.each([
    ['DOMAIN <<"a", "b">>', "1..2"],
    ["DOMAIN [i \\in 1..2 |-> i]", "1..2"],
    ["DOMAIN [x \\in {1, 2} |-> x]", "{1, 2}"],
    ["DOMAIN [[i \\in 1..2 |-> i] EXCEPT ![2] = 5]", "1..2"],
    ["DOMAIN CHOOSE f \\in [1..2 -> {0}] : TRUE", "1..2"],
    ["DOMAIN [x \\in (1..2) \\cap (1..3) |-> x]", "{1, 2}"],
    ["DOMAIN (<<1>> @@ <<1, 2>>)", "{1, 2}"],
    ["LET f[n \\in 1..3] == IF n = 1 THEN 1 ELSE n * f[n - 1] IN DOMAIN f", "1..3"],
    ["DOMAIN <<>>", "{}"],
    ["ToString(DOMAIN <<1, 2>>)", '"1..2"'],
    ["\\A i \\in DOMAIN <<1, 2, 3>> : i \\in DOMAIN <<4, 5, 6>>", "TRUE"],
  ])("prints %s as %s", async (expression, text) => {
    expect(await printDomain(expression)).toEqual([text]);
  });

  it("keeps the interval in a state", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nVARIABLE b\nInit == b = DOMAIN <<7, 8>>\nNext == UNCHANGED b\nInv == b # b\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT Inv",
    });
    expect(result.violations[0]?.states[0]?.variables.b?.text).toBe("1..2");
  });
});

describe("rejecting literals matches TLC", () => {
  const getOptions = (source: string) => ({
    source: `---- MODULE M ----\n${source}\nNext == x' = x\n====`,
    config: "INIT Init\nNEXT Next",
  });
  const checkSource = (source: string) => checkOnEngine(getOptions(source));

  it("parses decimal literals", () => {
    const module = parseModule("---- MODULE M ----\nHalf == 1.5\nRange == 1..2\n====");
    expect(module.definitions.map((definition) => definition.body.kind)).toEqual([
      "Decimal",
      "Apply",
    ]);
  });

  it.each([
    ["an evaluated decimal", "EXTENDS Reals\nVARIABLE x\nInit == x = 1.5"],
    ["a decimal that is never evaluated", "VARIABLE x\nHalf == 1.5\nInit == x = 0"],
    ["a decimal in an unused LET", "VARIABLE x\nF == LET h == 1.5 IN 0\nInit == x = 0"],
    ["a decimal in an unnamed theorem", "VARIABLE x\nTHEOREM 1.5 = 1.5\nInit == x = 0"],
    [
      "a decimal in an instance substitution",
      "---- MODULE Inner ----\nCONSTANT c\n====\nVARIABLE x\nI == INSTANCE Inner WITH c <- 1.5\nInit == x = 0",
    ],
    [
      "a decimal in an unused nested module",
      "VARIABLE x\n---- MODULE Inner ----\nHalf == 1.5\n====\nInit == x = 0",
    ],
  ])("declines %s", async (_, source) => {
    await expectDeclined(getOptions(source), "the engine stopped before it searched (exit 151)");
  });

  it("accepts decimals in proofs and ASSUME PROVE theorems", async () => {
    const result = await checkSource(
      "VARIABLE x\nTHEOREM TRUE\n<1>1. 1.5 = 1.5\n  OBVIOUS\n<1>2. QED\n  BY <1>1\nTHEOREM ASSUME NEW c PROVE c = 1.5\nInit == x = 0",
    );
    expect(result.status).toBe("success");
  });

  it.each([
    ["an unused definition", "VARIABLE x\nBig == 2147483648\nInit == x = 0", 255],
    ["an assumption", "VARIABLE x\nASSUME 2147483648 > 0\nInit == x = 0", 150],
    ["a negated literal", "EXTENDS Integers\nVARIABLE x\nInit == x = -2147483648", 255],
    [
      "an unused nested module",
      "VARIABLE x\n---- MODULE Inner ----\nBig == 2147483648\n====\nInit == x = 0",
      255,
    ],
    ["a hexadecimal literal", "VARIABLE x\nBig == \\hFFFFFFFFF\nInit == x = 0", 255],
    ["a long literal", "VARIABLE x\nBig == 99999999999999999999\nInit == x = 0", 255],
  ])("declines an integer literal too big for TLC in %s", async (_, source, exitCode) => {
    await expectDeclined(
      getOptions(source),
      `the engine stopped before it searched (exit ${exitCode})`,
    );
  });

  it("reads based numerals", async () => {
    const result = await checkSource(
      "VARIABLE x\nASSUME \\h1F = 31 /\\ \\b101 = 5 /\\ \\o17 = 15\nInit == x = 0",
    );
    expect(result.status).toBe("success");
  });

  it("accepts the largest integer literal and big literals in proofs", async () => {
    const result = await checkSource(
      "EXTENDS Naturals\nVARIABLE x\nTHEOREM TRUE\n<1>1. 2147483648 > 0\n  OBVIOUS\n<1>2. QED\n  BY <1>1\nInit == x = 2147483647",
    );
    expect(result.status).toBe("success");
  });
});

describe("name resolution matches SANY", () => {
  const getOptions = (source: string) => ({
    source: `---- MODULE M ----\n${source}\nVARIABLE x\nInit == x = 0\nNext == x' = x\n====`,
    config: "INIT Init\nNEXT Next",
  });
  const checkSource = (source: string) => checkOnEngine(getOptions(source));

  it.each([
    ["EXTENDS Strings", "Strings"],
    ["N == INSTANCE Nowhere", "Nowhere"],
  ])("fails to parse a spec that imports a module it cannot find: %s", async (source, name) => {
    await expect(checkSource(source)).rejects.toThrow(
      createSanyError(
        [
          {
            location: "In module M",
            message: `Cannot find source file for module ${name} imported in module M.`,
          },
        ],
        true,
      ),
    );
  });

  it.each([
    ["an operator from a module that is not extended", "EXTENDS Naturals\nf == 1 :> 2"],
    ["an operator that a standard module only instantiates locally", "EXTENDS TLC\nf == 1 + 1"],
    ["a definition before it is defined", "EXTENDS Naturals\nf == g + 1\ng == 1"],
    ["an operator with the wrong number of arguments", "g(a) == a\nf == g(1, 2)"],
    ["a record with duplicate fields", "f == [a |-> 1, b |-> 2, a |-> 1]"],
    ["an expression as a fact in a HIDE", "THEOREM bar == <<1, 2>>\nUSE bar\nHIDE bar, TRUE"],
    [
      "a definition as a fact in a HIDE step",
      "foo == 1\nTHEOREM T == TRUE\n<1>1. HIDE foo\n<1> QED",
    ],
    ["an unknown operator in a theorem", "THEOREM Undefined"],
    ["an unknown operator in a proof step", "THEOREM TRUE\n<1>1. Undefined\n  OBVIOUS\n<1> QED"],
    ["a higher-order operator as an operator argument", "D(Op(_)) == Op(42)\nFoo == D(D)"],
    ["an expression as an operator argument", "D(Op(_)) == Op(42)\nFoo == D(1)"],
    ["an operator as an expression argument", "F(a) == a\nG(a) == a\nFoo == F(G)"],
    ["an operator argument with the wrong arity", "D(Op(_)) == Op(42)\nG(a, b) == a\nFoo == D(G)"],
    [
      "a NEW symbol after the proof of its step",
      "THEOREM TRUE\n<1>1. ASSUME NEW c PROVE c = c\n  OBVIOUS\n<1>2. c = c\n<1> QED",
    ],
  ])("rejects %s", async (_, source) => {
    await expect(checkSource(source)).rejects.toThrow(TlaSyntaxError);
  });

  it.each([
    "RECURSIVE F\nF == LET F == 2 IN F",
    "EXTENDS Naturals\nOne(a) == a\nf == One(\\cup) /\\ One(-.) /\\ One(SUBSET) /\\ One(1) + One",
    "One(a) == a\nf == One(UNCHANGED) /\\ One(') /\\ One(^+)",
    "K(a) == LET C(b) == a IN C(1)\nHigh(Op(_)) == Op(1)\nM(a) == INSTANCE Naturals\nA == High(K(1)!C) /\\ U1\nB == High(M(1)!+)",
    "RECURSIVE F(_)\nF(n) == n\nF(n) == n\nG == 1",
  ])("declines %j, which SANY rejects", async (source) => {
    await expectDeclined(getOptions(source), "the engine stopped before it searched (exit 150)");
  });

  it("accepts USE and HIDE of theorems, assumptions, steps, and definitions", async () => {
    const result = await checkSource(
      "EXTENDS Naturals\nfoo == 1\nUSE foo, foo > 0 DEF foo\nASSUME A == foo \\in Nat\nHIDE A\nTHEOREM T == foo = 1\nHIDE T DEF foo\nTHEOREM U == ASSUME NEW n \\in Nat PROVE n >= 0\n<1>1. n >= 0\n  OBVIOUS\n<1>2. HIDE <1>1, T\n<1> QED\n  BY <1>1",
    );
    expect(result.status).toBe("success");
  });

  it("resolves NEW, SUFFICES, PICK, DEFINE, and theorem labels in the steps they scope", async () => {
    const result = await checkSource(
      [
        "EXTENDS Naturals",
        "THEOREM Thm == ASSUME NEW S PROVE lab :: S = S",
        "<1> SUFFICES ASSUME NEW n \\in Nat PROVE n + 0 = n OBVIOUS",
        "<1>1. PICK m \\in Nat : m = n OBVIOUS",
        "<1> DEFINE k == m + n",
        "<1>2. ASSUME NEW c PROVE Thm!lab /\\ k = c",
        "  <2>1. c = c OBVIOUS",
        "  <2> QED",
        "<1> QED BY <1>2",
      ].join("\n"),
    );
    expect(result.status).toBe("success");
  });

  it("reads instance-qualified subscripts", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\n---- MODULE Inner ----\nVARIABLE x\nvars == <<x>>\nNext == x' = (x + 1) % 3\n====\nI == INSTANCE Inner\nSpec == x = 0 /\\ [][I!Next]_I!vars /\\ WF_I!vars(I!Next)\nProp == <>(x = 2)\nTHEOREM Spec => WF_I!vars(I!Next)\n====",
      config: "SPECIFICATION Spec\nPROPERTY Prop",
    });
    expect([result.status, result.generatedStates, result.distinctStates]).toEqual([
      "success",
      4,
      3,
    ]);
  });

  it.each([
    ["a bound variable before a definition of that name", "F == \\E B \\in {1} : TRUE\nB == 1"],
    [
      "sibling quantifiers with one name",
      "F == (\\E y \\in {1} : TRUE) /\\ (\\E y \\in {2} : TRUE)",
    ],
    [
      "a LET definition whose body binds its own name",
      "F == LET e == CHOOSE e \\in {1} : TRUE IN e",
    ],
    ["a LET definition named after the definition it is in", "F == LET F == 2 IN F"],
    [
      "a definition named after a recursive LET definition before it",
      "G == LET RECURSIVE F(_)\n         F(n) == n\n     IN F(1)\nF == LET F == 2 IN F",
    ],
    [
      "a LET parameter named after a later LET definition",
      "F == LET A(B) == B\n         B == 1\n     IN A(B)",
    ],
    [
      "a recursive LET definition",
      "F == LET RECURSIVE G(_)\n         G(n) == IF n = 0 THEN 0 ELSE G(0)\n     IN G(1)",
    ],
    [
      "operator arguments of the arity a parameter takes",
      "D(Op(_)) == Op(42)\nG(a) == a\nF == D(G) = D(LAMBDA a : a)",
    ],
  ])("accepts %s", async (_, source) => {
    expect((await checkSource(source)).status).toBe("success");
  });

  // TLC's SANY gives SUBSET the precedence 8, below \X.
  it("reads SUBSET before \\X by the precedence of SANY", async () => {
    const source =
      "---- MODULE M ----\nVARIABLE x\nASSUME SUBSET {1} \\X {2} = {{}, {<<1, 2>>}}\nInit == x = 0\nNext == UNCHANGED x\n====";
    const config = "INIT Init\nNEXT Next";
    expect((await checkOnEngine({ source, config })).status).toBe("success");
  });

  it("defines prefix, postfix, and <: operators", async () => {
    const result = await checkSource(
      "EXTENDS Naturals\nn ^+ == n + 1\n-. n == 10 - n\na <: b == a - b\nASSUME (2^+) = 3 /\\ -4 = 6 /\\ (5 <: 2) = 3",
    );
    expect(result.status).toBe("success");
  });

  it("applies operators in prefix form and reads keywords as field names", async () => {
    const result = await checkSource(
      'EXTENDS Naturals\nn ^+ == n + 1\nASSUME +(4, 6) = 10 /\\ ^+(2) = 3\nASSUME [[x \\in {"THEN"} |-> 1] EXCEPT !.THEN = 2].THEN = 2',
    );
    expect(result.status).toBe("success");
  });

  it("takes infix operators as parameters", async () => {
    const result = await checkSource(
      "EXTENDS Naturals\nFoo(a, _--_) == a -- 1\nASSUME Foo(7, +) = 8 /\\ Foo(7, *) = 7",
    );
    expect(result.status).toBe("success");
  });

  it("accepts recursive functions, named assumptions, and operator aliases", async () => {
    const result = await checkSource(
      "EXTENDS Naturals\nRECURSIVE fact\ntwice[n \\in Nat] == fact[n] * 2\nfact[n \\in Nat] == IF n = 0 THEN 1 ELSE n * fact[n - 1]\nASSUME Positive == twice[3] = 12\nASSUME Positive\na \\oplus b == a + b\nASSUME 1 (+) 2 = 3",
    );
    expect(result.status).toBe("success");
  });

  it("keeps a recursive function lazy, so it computes only the arguments a spec applies it to", async () => {
    const result = await checkSource(
      "EXTENDS Naturals\nsteps[n \\in 0..20] == IF n = 1 THEN 0 ELSE IF n % 2 = 0 THEN 1 + steps[n \\div 2] ELSE 1 + steps[3 * n + 1]\nASSUME steps[5] = 5",
    );
    expect(result.status).toBe("success");
  });

  it("rejects RandomSubsetSet, which TLC's Randomization module does not define", async () => {
    await expect(
      checkSource('EXTENDS Randomization\nASSUME RandomSubsetSet(2, "0.5", {1, 2}) = {}'),
    ).rejects.toThrow(TlaSyntaxError);
  });

  it.each([
    ["f == g", [["line 2, col 6 to line 2, col 6", "Unknown operator: `g'."]]],
    [
      "f == 1 + 1",
      [
        [
          "line 2, col 8 to line 2, col 8",
          "Could not find declaration or definition of symbol '+'.",
        ],
        ["line 2, col 6 to line 2, col 10", "Couldn't resolve infix operator symbol `+'."],
      ],
    ],
    [
      "f == -1",
      [
        [
          "line 2, col 6 to line 2, col 6",
          "Could not find declaration or definition of symbol '-.'.",
        ],
        ["line 2, col 6 to line 2, col 7", "Couldn't resolve prefix operator symbol `-.'."],
      ],
    ],
    [
      "f == 1 (+) 2 /\\ 1 \\circ 2 /\\ 1 (\\X) 2",
      [
        [
          "line 2, col 8 to line 2, col 10",
          "Could not find declaration or definition of symbol '(+)'.",
        ],
        ["line 2, col 6 to line 2, col 12", "Couldn't resolve infix operator symbol `(+)'."],
        [
          "line 2, col 19 to line 2, col 23",
          "Could not find declaration or definition of symbol '\\circ'.",
        ],
        ["line 2, col 17 to line 2, col 25", "Couldn't resolve infix operator symbol `\\circ'."],
        [
          "line 2, col 32 to line 2, col 35",
          "Could not find declaration or definition of symbol '(\\X)'.",
        ],
        ["line 2, col 30 to line 2, col 37", "Couldn't resolve infix operator symbol `(\\X)'."],
      ],
    ],
    [
      "g == 1^+",
      [
        [
          "line 2, col 7 to line 2, col 8",
          "Could not find declaration or definition of symbol '^+'.",
        ],
        ["line 2, col 6 to line 2, col 8", "Couldn't resolve postfix operator symbol `^+'."],
      ],
    ],
    ["Ab == 1\nf == Abc", [["line 3, col 6 to line 3, col 8", "Unknown operator: `Abc'."]]],
    ["Foo == x = 1\nVARIABLE x", [["line 2, col 8 to line 2, col 8", "Unknown operator: `x'."]]],
    [
      "EXTENDS Naturals\nf == -1",
      [
        [
          "line 3, col 6 to line 3, col 6",
          "Could not find declaration or definition of symbol '-.'.",
        ],
        ["line 3, col 6 to line 3, col 7", "Couldn't resolve prefix operator symbol `-.'."],
      ],
    ],
    [
      "EXTENDS Naturals\ng == 1^+",
      [
        [
          "line 3, col 7 to line 3, col 8",
          "Could not find declaration or definition of symbol '^+'.",
        ],
        ["line 3, col 6 to line 3, col 8", "Couldn't resolve postfix operator symbol `^+'."],
      ],
    ],
    [
      "Foo(a) == a\ng == Foo(1,  2)",
      [["line 3, col 9 to line 3, col 15", "The operator Foo requires 1 arguments."]],
    ],
    [
      "THEOREM T == TRUE\nHIDE T, TRUE, {}",
      ["line 3, col 9 to line 3, col 12", "line 3, col 15 to line 3, col 16"].map((location) => [
        location,
        "The only expression allowed as a fact in a HIDE is \nthe name of a theorem, assumption, or step.",
      ]),
    ],
    [
      "Foo(a) == a\ng == Foo",
      [["line 3, col 6 to line 3, col 8", "The operator Foo requires 1 arguments."]],
    ],
    [
      "f == A /\\ B /\\ C(1)\ng == D",
      [
        ["line 2, col 6 to line 2, col 6", "Unknown operator: `A'."],
        ["line 2, col 11 to line 2, col 11", "Unknown operator: `B'."],
        ["line 2, col 16 to line 2, col 16", "Unknown operator: `C'."],
        ["line 3, col 6 to line 3, col 6", "Unknown operator: `D'."],
      ],
    ],
    [
      "Op(a, b) == a\nf == Op(F) /\\ Op(G, H, I) /\\ Op /\\ J",
      [
        ["line 3, col 8 to line 3, col 10", "The operator Op requires 2 arguments."],
        ["line 3, col 17 to line 3, col 25", "The operator Op requires 2 arguments."],
        ["line 3, col 30 to line 3, col 31", "The operator Op requires 2 arguments."],
        ["line 3, col 36 to line 3, col 36", "Unknown operator: `J'."],
      ],
    ],
    [
      "f == (A + B) /\\ C\ng == -D /\\ E",
      [
        [
          "line 2, col 9 to line 2, col 9",
          "Could not find declaration or definition of symbol '+'.",
        ],
        ["line 2, col 7 to line 2, col 11", "Couldn't resolve infix operator symbol `+'."],
        ["line 2, col 17 to line 2, col 17", "Unknown operator: `C'."],
        [
          "line 3, col 6 to line 3, col 6",
          "Could not find declaration or definition of symbol '-.'.",
        ],
        ["line 3, col 6 to line 3, col 7", "Couldn't resolve prefix operator symbol `-.'."],
        ["line 3, col 12 to line 3, col 12", "Unknown operator: `E'."],
      ],
    ],
    [
      "f == [a |-> Q, a |-> R, b |-> S, b |-> T] /\\ [c : U, c : V]",
      [
        ["line 2, col 13 to line 2, col 13", "Unknown operator: `Q'."],
        ["line 2, col 16 to line 2, col 16", "Non-unique fields in constructor."],
        ["line 2, col 22 to line 2, col 22", "Unknown operator: `R'."],
        ["line 2, col 31 to line 2, col 31", "Unknown operator: `S'."],
        ["line 2, col 34 to line 2, col 34", "Non-unique fields in constructor."],
        ["line 2, col 40 to line 2, col 40", "Unknown operator: `T'."],
        ["line 2, col 51 to line 2, col 51", "Unknown operator: `U'."],
        ["line 2, col 54 to line 2, col 54", "Non-unique fields in constructor."],
        ["line 2, col 58 to line 2, col 58", "Unknown operator: `V'."],
      ],
    ],
    [
      "F(a) == a\nG(a) == a\nf == F(G) /\\ LET L(y) == y IN F(L) /\\ A",
      [
        ["line 4, col 8 to line 4, col 8", "The operator G requires 1 arguments."],
        ["line 4, col 33 to line 4, col 33", "The operator L requires 1 arguments."],
        ["line 4, col 39 to line 4, col 39", "Unknown operator: `A'."],
      ],
    ],
    [
      "f == LET L == K IN L /\\ M\ng == \\A y \\in N : \\E z \\in O : P(y, z)",
      [
        ["line 2, col 15 to line 2, col 15", "Unknown operator: `K'."],
        ["line 2, col 25 to line 2, col 25", "Unknown operator: `M'."],
        ["line 3, col 15 to line 3, col 15", "Unknown operator: `N'."],
        ["line 3, col 28 to line 3, col 28", "Unknown operator: `O'."],
        ["line 3, col 32 to line 3, col 32", "Unknown operator: `P'."],
      ],
    ],
    [
      "THEOREM ASSUME NEW a \\in A, B PROVE C(a)\n<1>1. D\n<1> DEFINE G == H\n<1>2. QED\nASSUME S",
      [
        ["line 2, col 26 to line 2, col 26", "Unknown operator: `A'."],
        ["line 2, col 29 to line 2, col 29", "Unknown operator: `B'."],
        ["line 2, col 37 to line 2, col 37", "Unknown operator: `C'."],
        ["line 3, col 7 to line 3, col 7", "Unknown operator: `D'."],
        ["line 4, col 17 to line 4, col 17", "Unknown operator: `H'."],
        ["line 6, col 8 to line 6, col 8", "Unknown operator: `S'."],
      ],
    ],
    [
      "---- MODULE Inner ----\nCONSTANT a, b\n====\nI == INSTANCE Inner WITH b <- B, a <- [f |-> A, f |-> 1]",
      [
        ["line 5, col 31 to line 5, col 31", "Unknown operator: `B'."],
        ["line 5, col 46 to line 5, col 46", "Unknown operator: `A'."],
        ["line 5, col 49 to line 5, col 49", "Non-unique fields in constructor."],
      ],
    ],
    [
      "High(Op(_)) == Op(1)\nF(a) == a\nG(a, b) == a\nf == High(A) /\\ High(G) /\\ F(LAMBDA y : y) /\\ High(1) /\\ High(High)",
      [
        ["line 5, col 11 to line 5, col 11", "Unknown operator: `A'."],
        [
          "line 5, col 6 to line 5, col 12",
          "Argument number 1 to operator 'High' \nshould be a 1-parameter operator.",
        ],
        ["line 5, col 22 to line 5, col 22", "Expected arity 1 but found operator of arity 2."],
        [
          "line 5, col 17 to line 5, col 23",
          "Argument number 1 to operator 'High' \nshould be a 1-parameter operator.",
        ],
        [
          "line 5, col 30 to line 5, col 41",
          "LAMBDA expression used where an expression is required.",
        ],
        [
          "line 5, col 52 to line 5, col 52",
          "An expression appears as argument number 1 (counting from 1) to operator 'High', in a position an operator is required.",
        ],
        [
          "line 5, col 47 to line 5, col 53",
          "Argument number 1 to operator 'High' \nshould be a 1-parameter operator.",
        ],
        [
          "line 5, col 58 to line 5, col 67",
          "Argument number 1 to operator 'High' \nshould be a 1-parameter operator.",
        ],
      ],
    ],
    [
      "EXTENDS Naturals, Sequences\nTwo(a, b) == a\nf == LET G(y) == y IN G(1) + G\nP(Op(_)) == Op(Op) /\\ Op + 1\ng == SelectSeq(<<>>, Two) /\\ SelectSeq(<<>>, LAMBDA a, b : a)",
      [
        ["line 4, col 30 to line 4, col 30", "The operator G requires 1 arguments."],
        ["line 5, col 16 to line 5, col 17", "The operator Op requires 1 arguments."],
        ["line 5, col 23 to line 5, col 24", "The operator Op requires 1 arguments."],
        ["line 6, col 22 to line 6, col 24", "Expected arity 1 but found operator of arity 2."],
        [
          "line 6, col 6 to line 6, col 25",
          "Argument number 2 to operator 'SelectSeq' \nshould be a 1-parameter operator.",
        ],
        [
          "line 6, col 30 to line 6, col 38",
          "Lambda expression with arity 2 used as argument 2 of operator `SelectSeq', \nbut an operator of arity 1 is required.",
        ],
        [
          "line 6, col 30 to line 6, col 61",
          "Argument number 2 to operator 'SelectSeq' \nshould be a 1-parameter operator.",
        ],
      ],
    ],
    [
      "---- MODULE Inner ----\nH(Op(_)) == Op(1)\nOne(a) == a\n====\nI == INSTANCE Inner\nINSTANCE Inner\nf == I!H(I!One) /\\ I!One(I!One) /\\ I!H(LAMBDA a, b : a) /\\ H(I!H) /\\ One(One)",
      [
        ["line 8, col 26 to line 8, col 30", "The operator I!One requires 1 arguments."],
        [
          "line 8, col 38 to line 8, col 38",
          "Lambda expression with arity 2 used as argument 1 of operator `I!H', \nbut an operator of arity 1 is required.",
        ],
        [
          "line 8, col 36 to line 8, col 55",
          "Argument number 1 to operator 'I!H' \nshould be a 1-parameter operator.",
        ],
        [
          "line 8, col 60 to line 8, col 65",
          "Argument number 1 to operator 'H' \nshould be a 1-parameter operator.",
        ],
        ["line 8, col 74 to line 8, col 76", "The operator One requires 1 arguments."],
      ],
    ],
    [
      "---- MODULE Inner ----\nCONSTANT a\nB == a\nC(p) == a\nTHEOREM T == TRUE\n====\nK(q) == INSTANCE Inner WITH a <- q\nF == K!B = U1 /\\ K(1)!C = U2 /\\ K(1, 2)!B = U3 /\\ K!C(1, 2) = U4\nG == LET L(q) == INSTANCE Inner WITH a <- q IN L!B = U5 /\\ L(1)!C(2, 3) = U6\nUSE K!T, K(1)!T, U7",
      [
        ["line 9, col 6 to line 9, col 8", "The operator K requires 1 arguments."],
        ["line 9, col 12 to line 9, col 13", "Unknown operator: `U1'."],
        ["line 9, col 18 to line 9, col 23", "The operator K!C requires 1 arguments."],
        ["line 9, col 27 to line 9, col 28", "Unknown operator: `U2'."],
        ["line 9, col 34 to line 9, col 39", "The operator K requires 1 arguments."],
        ["line 9, col 45 to line 9, col 46", "Unknown operator: `U3'."],
        ["line 9, col 51 to line 9, col 59", "The operator K requires 1 arguments."],
        ["line 9, col 63 to line 9, col 64", "Unknown operator: `U4'."],
        ["line 10, col 48 to line 10, col 50", "The operator L requires 1 arguments."],
        ["line 10, col 54 to line 10, col 55", "Unknown operator: `U5'."],
        ["line 10, col 66 to line 10, col 71", "The operator L!C requires 1 arguments."],
        ["line 10, col 75 to line 10, col 76", "Unknown operator: `U6'."],
        ["line 11, col 5 to line 11, col 7", "The operator K requires 1 arguments."],
        ["line 11, col 18 to line 11, col 19", "Unknown operator: `U7'."],
      ],
    ],
    [
      "THEOREM TRUE\n<1>1. CASE TRUE\n  <2>1. TRUE BY <1>1, <1>2\n  <2>2. QED BY <2>1\n<1>2. TRUE BY <2>1, <1>3\n<1>3. QED BY <1>1, <1>2, <1>3, <1>9",
      [
        ["line 4, col 23 to line 4, col 26", "Unknown operator: `<1>2'."],
        ["line 6, col 15 to line 6, col 18", "Unknown operator: `<2>1'."],
        ["line 6, col 21 to line 6, col 24", "Unknown operator: `<1>3'."],
        ["line 7, col 32 to line 7, col 35", "Unknown operator: `<1>9'."],
      ],
    ],
    [
      "EXTENDS Naturals\na ⊕ b == a + b\nA == ⟨1, 2⟩ ∘ U1\nB == ∀ y ∈ ℕ : y ≥ 0 ⇒ y ⁺\nC == ⊕ ∪ {1 ‥ 2, 1 ⊕ 2}\nM == INSTANCE Naturals\nD == M ! ⊕(1, 2)",
      [
        [
          "line 4, col 13 to line 4, col 13",
          "Could not find declaration or definition of symbol '∘'.",
        ],
        ["line 4, col 6 to line 4, col 16", "Couldn't resolve infix operator symbol `∘'."],
        ["line 5, col 12 to line 5, col 12", "Unknown operator: `ℕ'."],
        [
          "line 5, col 26 to line 5, col 26",
          "Could not find declaration or definition of symbol '⁺'.",
        ],
        ["line 5, col 24 to line 5, col 26", "Couldn't resolve postfix operator symbol `⁺'."],
        ["line 6, col 6 to line 6, col 6", "The operator \\oplus requires 2 arguments."],
        ["line 8, col 6 to line 8, col 10", "Unknown operator: `M!\\oplus'."],
      ],
    ],
    [
      "THEOREM TRUE\n<1>1. USE TRUE\n<1>2. DEFINE G == 1\n<1>3. TRUE BY <1>1, <1>2, U1\n<1>4. <1>1\n  OBVIOUS\n<1>5. HIDE <1>4\n<1> QED BY <1>5",
      [
        ["line 5, col 15 to line 5, col 18", "Step number of non-fact used as a fact"],
        ["line 5, col 21 to line 5, col 24", "Step number of non-fact used as a fact"],
        ["line 5, col 27 to line 5, col 28", "Unknown operator: `U1'."],
        [
          "line 6, col 7 to line 6, col 10",
          "Step number of non-expression step used as an expression.",
        ],
        ["line 9, col 12 to line 9, col 15", "Step number of non-fact used as a fact"],
      ],
    ],
  ])("reports %j at the range SANY reports", async (source, errors) => {
    await expect(checkSource(source)).rejects.toThrow(
      createSanyError(
        errors.map(([location, message]) => ({ location: `${location} of module M`, message })),
      ),
    );
  });

  it.each([
    [
      "a definition defined twice",
      "B == 1\nB == 2",
      [
        {
          location: "line 3, col 1 to line 3, col 6 of module M",
          message: "Operator B already defined or declared.",
        },
      ],
      [
        {
          location: "line 3, col 1 to line 3, col 6 of module M",
          message:
            "Multiple declarations or definitions for symbol B.  \nThis duplicates the one at line 2, col 1 to line 2, col 6 of module M.",
        },
      ],
    ],
    [
      "a definition of a declared constant",
      "CONSTANT B\nB == 1",
      [
        {
          location: "line 3, col 1 to line 3, col 6 of module M",
          message: "Operator B already defined or declared.",
        },
        {
          location: "line 3, col 1 to line 3, col 6 of module M",
          message:
            "Multiply-defined symbol 'B': this definition or declaration conflicts \nwith the one at line 2, col 10 to line 2, col 10 of module M.",
        },
      ],
      [],
    ],
    [
      "a constant declared after a definition",
      "B == 1\nCONSTANT B",
      [
        {
          location: "line 3, col 10 to line 3, col 10 of module M",
          message:
            "Multiply-defined symbol 'B': this definition or declaration conflicts \nwith the one at line 2, col 1 to line 2, col 6 of module M.",
        },
      ],
      [],
    ],
    [
      "a constant and a variable with one name",
      "CONSTANT y\nVARIABLE y",
      [
        {
          location: "line 3, col 10 to line 3, col 10 of module M",
          message:
            "Multiply-defined symbol 'y': this definition or declaration conflicts \nwith the one at line 2, col 10 to line 2, col 10 of module M.",
        },
      ],
      [],
    ],
    [
      "an operator parameter named after a definition",
      "B == 1\nF(B) == B",
      [
        {
          location: "line 3, col 3 to line 3, col 3 of module M",
          message:
            "Multiply-defined symbol 'B': this definition or declaration conflicts \nwith the one at line 2, col 1 to line 2, col 6 of module M.",
        },
      ],
      [],
    ],
    [
      "a LET definition named after a definition",
      "B == 1\nF == LET B == 2 IN B",
      [
        {
          location: "line 3, col 10 to line 3, col 15 of module M",
          message: "Operator B already defined or declared.",
        },
      ],
      [
        {
          location: "line 3, col 10 to line 3, col 15 of module M",
          message:
            "Multiple declarations or definitions for symbol B.  \nThis duplicates the one at line 2, col 1 to line 2, col 6 of module M.",
        },
      ],
    ],
    [
      "a bound variable named after a variable",
      "VARIABLE y\nF == \\E y \\in {1} : TRUE",
      [
        {
          location: "line 3, col 9 to line 3, col 9 of module M",
          message:
            "Multiply-defined symbol 'y': this definition or declaration conflicts \nwith the one at line 2, col 10 to line 2, col 10 of module M.",
        },
      ],
      [],
    ],
    [
      "nested bound variables with one name",
      "F == \\E y \\in {1} : \\E y \\in {2} : TRUE",
      [
        {
          location: "line 2, col 24 to line 2, col 24 of module M",
          message:
            "Multiply-defined symbol 'y': this definition or declaration conflicts \nwith the one at line 2, col 9 to line 2, col 9 of module M.",
        },
      ],
      [],
    ],
    [
      "an operator of an extended module",
      "EXTENDS Naturals\na + b == a",
      [
        {
          location: "line 3, col 1 to line 3, col 10 of module M",
          message: "Operator + already defined or declared.",
        },
      ],
      [
        {
          location: "line 3, col 1 to line 3, col 10 of module M",
          message:
            "Multiple declarations or definitions for symbol +.  \nThis duplicates the one at line 15, col 1 to line 15, col 19 of module Naturals.",
        },
      ],
    ],
    [
      "a built-in operator",
      "BOOLEAN == 1",
      [
        {
          location: "line 2, col 1 to line 2, col 12 of module M",
          message: "Operator BOOLEAN already defined or declared.",
        },
        {
          location: "line 2, col 1 to line 2, col 12 of module M",
          message: "Symbol BOOLEAN is a built-in operator, and cannot be redefined.",
        },
      ],
      [],
    ],
    [
      "a constant named after a built-in operator",
      "CONSTANT BOOLEAN",
      [
        {
          location: "line 2, col 10 to line 2, col 16 of module M",
          message: "Symbol BOOLEAN is a built-in operator, and cannot be redefined.",
        },
      ],
      [],
    ],
    [
      "a variable named after a built-in operator",
      "VARIABLE TRUE",
      [
        {
          location: "line 2, col 10 to line 2, col 13 of module M",
          message: "Symbol TRUE is a built-in operator, and cannot be redefined.",
        },
      ],
      [],
    ],
    [
      "a constant named after an operator of an extended module",
      "EXTENDS Naturals\nCONSTANT Nat",
      [
        {
          location: "line 3, col 10 to line 3, col 12 of module M",
          message:
            "Multiply-defined symbol 'Nat': this definition or declaration conflicts \nwith the one at line 14, col 1 to line 14, col 16 of module Naturals.",
        },
      ],
      [],
    ],
    [
      "a nested module constant named after an enclosing variable",
      "VARIABLE y\n---- MODULE Inner ----\nCONSTANT y\n====",
      [
        {
          location: "line 4, col 10 to line 4, col 10 of module M",
          message:
            "Multiply-defined symbol 'y': this definition or declaration conflicts \nwith the one at line 2, col 10 to line 2, col 10 of module M.",
        },
      ],
      [],
    ],
    [
      "a definition after an instance that imports it",
      "INSTANCE Naturals\nNat == 1",
      [
        {
          location: "line 3, col 1 to line 3, col 8 of module M",
          message: "Operator Nat already defined or declared.",
        },
      ],
      [
        {
          location: "line 3, col 1 to line 3, col 8 of module M",
          message:
            "Multiple declarations or definitions for symbol Nat.  \nThis duplicates the one at line 14, col 1 to line 14, col 16 of module Naturals.",
        },
      ],
    ],
    [
      "a named instance and a definition with one name",
      "I == 1\nI == INSTANCE Naturals",
      [
        {
          location: "line 3, col 1 to line 3, col 22 of module M",
          message:
            "Multiply-defined symbol 'I': this definition or declaration conflicts \nwith the one at line 2, col 1 to line 2, col 6 of module M.",
        },
      ],
      [],
    ],
    [
      "duplicate operator parameters",
      "F(a, a) == a",
      [
        {
          location: "line 2, col 6 to line 2, col 6 of module M",
          message:
            "Multiply-defined symbol 'a': this definition or declaration conflicts \nwith the one at line 2, col 3 to line 2, col 3 of module M.",
        },
      ],
      [],
    ],
    [
      "a LAMBDA parameter named after a definition",
      "B == 1\nG(Op(_)) == Op(1)\nF == G(LAMBDA B : B)",
      [
        {
          location: "line 4, col 15 to line 4, col 15 of module M",
          message:
            "Multiply-defined symbol 'B': this definition or declaration conflicts \nwith the one at line 2, col 1 to line 2, col 6 of module M.",
        },
      ],
      [],
    ],
    [
      "a function bound named after a definition",
      "y == 1\nf[y \\in {1}] == y",
      [
        {
          location: "line 3, col 3 to line 3, col 3 of module M",
          message:
            "Multiply-defined symbol 'y': this definition or declaration conflicts \nwith the one at line 2, col 1 to line 2, col 6 of module M.",
        },
      ],
      [],
    ],
    [
      "duplicate names in a tuple pattern",
      "F == \\E <<a, a>> \\in {<<1, 2>>} : TRUE",
      [
        {
          location: "line 2, col 14 to line 2, col 14 of module M",
          message:
            "Multiply-defined symbol 'a': this definition or declaration conflicts \nwith the one at line 2, col 11 to line 2, col 11 of module M.",
        },
      ],
      [],
    ],
    [
      "a LET definition named after an enclosing one",
      "F == LET A == 1 IN LET A == 2 IN A",
      [
        {
          location: "line 2, col 24 to line 2, col 29 of module M",
          message: "Operator A already defined or declared.",
        },
      ],
      [
        {
          location: "line 2, col 24 to line 2, col 29 of module M",
          message:
            "Multiple declarations or definitions for symbol A.  \nThis duplicates the one at line 2, col 10 to line 2, col 15 of module M.",
        },
      ],
    ],
    [
      "a LOCAL definition of an extended operator",
      "EXTENDS FiniteSets\nLOCAL Cardinality(S) == 0",
      [
        {
          location: "line 3, col 1 to line 3, col 25 of module M",
          message: "Operator Cardinality already defined or declared.",
        },
      ],
      [
        {
          location: "line 3, col 1 to line 3, col 25 of module M",
          message:
            "Multiple declarations or definitions for symbol Cardinality.  \nThis duplicates the one at line 21, col 1 to line 27, col 11 of module FiniteSets.",
        },
      ],
    ],
    [
      "a nested module definition named after an outer one",
      "B == 1\n---- MODULE Inner ----\nB == 2\n====\nI == INSTANCE Inner",
      [
        {
          location: "line 4, col 1 to line 4, col 6 of module M",
          message: "Operator B already defined or declared.",
        },
      ],
      [
        {
          location: "line 4, col 1 to line 4, col 6 of module M",
          message:
            "Multiple declarations or definitions for symbol B.  \nThis duplicates the one at line 2, col 1 to line 2, col 6 of module M.",
        },
      ],
    ],
    [
      "a definition of another arity",
      "B == 1\nB(a) == a",
      [
        {
          location: "line 3, col 1 to line 3, col 9 of module M",
          message: "Operator B already defined or declared.",
        },
        {
          location: "line 3, col 1 to line 3, col 9 of module M",
          message:
            "Multiply-defined symbol 'B': this definition or declaration conflicts \nwith the one at line 2, col 1 to line 2, col 6 of module M.",
        },
      ],
      [],
    ],
    [
      "a function defined twice",
      "f[n \\in {1}] == n\nf[n \\in {1}] == n",
      [
        {
          location: "line 3, col 1 to line 3, col 17 of module M",
          message: "Function name `f' already defined or declared.",
        },
      ],
      [],
    ],
    [
      "an operator named after a function",
      "f[n \\in {1}] == n\nf == 1",
      [
        {
          location: "line 3, col 1 to line 3, col 6 of module M",
          message: "Operator f already defined or declared.",
        },
      ],
      [
        {
          location: "line 3, col 1 to line 3, col 6 of module M",
          message:
            "Multiple declarations or definitions for symbol f.  \nThis duplicates the one at line 2, col 1 to line 2, col 17 of module M.",
        },
      ],
    ],
    [
      "a parameter named after a built-in operator",
      "F(TRUE) == 1",
      [
        {
          location: "line 2, col 3 to line 2, col 6 of module M",
          message: "Symbol TRUE is a built-in operator, and cannot be redefined.",
        },
      ],
      [],
    ],
    [
      "a theorem named after a definition",
      "B == 1\nTHEOREM B == TRUE",
      [
        {
          location: "line 3, col 1 to line 3, col 17 of module M",
          message:
            "Multiply-defined symbol 'B': this definition or declaration conflicts \nwith the one at line 2, col 1 to line 2, col 6 of module M.",
        },
      ],
      [],
    ],
    [
      "a definition named after a theorem",
      "THEOREM B == TRUE\nB == 1",
      [
        {
          location: "line 3, col 1 to line 3, col 6 of module M",
          message: "Operator B already defined or declared.",
        },
        {
          location: "line 3, col 1 to line 3, col 6 of module M",
          message:
            "Multiply-defined symbol 'B': this definition or declaration conflicts \nwith the one at line 2, col 1 to line 2, col 17 of module M.",
        },
      ],
      [],
    ],
    [
      "a NEW symbol named after a definition",
      "B == 1\nTHEOREM ASSUME NEW B PROVE TRUE",
      [
        {
          location: "line 3, col 20 to line 3, col 20 of module M",
          message:
            "Multiply-defined symbol 'B': this definition or declaration conflicts \nwith the one at line 2, col 1 to line 2, col 6 of module M.",
        },
      ],
      [],
    ],
    [
      "a module defined twice",
      "---- MODULE Inner ----\n====\n---- MODULE Inner ----\n====",
      [
        {
          location: "line 4, col 1 to line 5, col 4 of module M",
          message:
            "Multiply-defined module 'Inner': this definition or declaration conflicts \nwith the one at line 2, col 1 to line 3, col 4 of module M.",
        },
      ],
      [],
    ],
    [
      "duplicate instance parameters",
      "---- MODULE Inner ----\nCONSTANT c\n====\nI(c, c) == INSTANCE Inner",
      [
        {
          location: "line 5, col 6 to line 5, col 6 of module M",
          message:
            "Multiply-defined symbol 'c': this definition or declaration conflicts \nwith the one at line 5, col 3 to line 5, col 3 of module M.",
        },
      ],
      [],
    ],
    [
      "a definition and a declaration of two extended modules",
      "---- MODULE A ----\nFoo == 1\nBaz == 1\n====\n---- MODULE B ----\nFoo(a) == 2\nCONSTANT Baz\n====\n---- MODULE C ----\nEXTENDS A, B\n====",
      [
        {
          location: "line 8, col 10 to line 8, col 12 of module M",
          message:
            "The declaration of 'Baz' conflicts with \nits definition at line 4, col 1 to line 4, col 8 of module M.",
        },
      ],
      [
        {
          location: "line 7, col 1 to line 7, col 11 of module M",
          message:
            "Warning: the definition of 'Foo' conflicts with \nits definition at line 3, col 1 to line 3, col 8 of module M.",
        },
      ],
    ],
    [
      "errors in instance substitutions between definitions",
      "---- MODULE Inner ----\nCONSTANT a, b\n====\nFoo == U\nI == INSTANCE Inner WITH a <- A, b <- B\nBar == V",
      [
        {
          location: "line 5, col 8 to line 5, col 8 of module M",
          message: "Unknown operator: `U'.",
        },
        {
          location: "line 6, col 31 to line 6, col 31 of module M",
          message: "Unknown operator: `A'.",
        },
        {
          location: "line 6, col 39 to line 6, col 39 of module M",
          message: "Unknown operator: `B'.",
        },
        {
          location: "line 7, col 8 to line 7, col 8 of module M",
          message: "Unknown operator: `V'.",
        },
      ],
      [],
    ],
    [
      "illegal, repeated, and missing substitutions",
      "---- MODULE Inner ----\nCONSTANT a, b, c\n====\nFoo == U\nI == INSTANCE Inner WITH a <- A, d <- 1, c <- 2, c <- C\nLOCAL INSTANCE Inner WITH a <- 1, c <- 2\nBar == V",
      [
        {
          location: "line 5, col 8 to line 5, col 8 of module M",
          message: "Unknown operator: `U'.",
        },
        {
          location: "line 6, col 31 to line 6, col 31 of module M",
          message: "Unknown operator: `A'.",
        },
        {
          location: "line 6, col 34 to line 6, col 34 of module M",
          message:
            "Identifier 'd' is not a legal target of a substitution. \nA legal target must be a declared CONSTANT or VARIABLE in the module being instantiated. \n(Also, check for warnings about multiple declarations of this same identifier.)",
        },
        {
          location: "line 6, col 55 to line 6, col 55 of module M",
          message: "Unknown operator: `C'.",
        },
        {
          location: "line 6, col 55 to line 6, col 55 of module M",
          message: "Multiple substitutions for symbol 'c' in substitution.",
        },
        {
          location: "line 6, col 1 to line 6, col 55 of module M",
          message:
            "Substitution missing for symbol b declared at line 3, col 13 to line 3, col 13 of module M \nand instantiated in module M.",
        },
        {
          location: "line 7, col 1 to line 7, col 40 of module M",
          message:
            "Substitution missing for symbol b declared at line 3, col 13 to line 3, col 13 of module M \nand instantiated in module M.",
        },
        {
          location: "line 8, col 8 to line 8, col 8 of module M",
          message: "Unknown operator: `V'.",
        },
      ],
      [],
    ],
    [
      "substitutions of an INSTANCE in a LET or a proof",
      "---- MODULE Inner ----\nCONSTANT a, b\nB == a\n====\nI == INSTANCE Inner WITH a <- 1, b <- 2\nF == LET J == INSTANCE Inner WITH a <- A, c <- 1, a <- 2 IN J!B /\\ U\nTHEOREM TRUE\n<1> DEFINE K == INSTANCE Inner WITH b <- lab :: 1\n<1> INSTANCE Inner WITH a <- 1, d <- 2\n<1>1. B = V /\\ K!B = 1\n<1> INSTANCE Inner WITH a <- 1, b <- 2\n<1> QED",
      [
        {
          location: "line 7, col 40 to line 7, col 40 of module M",
          message: "Unknown operator: `A'.",
        },
        {
          location: "line 7, col 43 to line 7, col 43 of module M",
          message:
            "Identifier 'c' is not a legal target of a substitution. \nA legal target must be a declared CONSTANT or VARIABLE in the module being instantiated. \n(Also, check for warnings about multiple declarations of this same identifier.)",
        },
        {
          location: "line 7, col 56 to line 7, col 56 of module M",
          message: "Multiple substitutions for symbol 'a' in substitution.",
        },
        {
          location: "line 7, col 10 to line 7, col 56 of module M",
          message:
            "Substitution missing for symbol b declared at line 3, col 13 to line 3, col 13 of module M \nand instantiated in module M.",
        },
        {
          location: "line 7, col 68 to line 7, col 68 of module M",
          message: "Unknown operator: `U'.",
        },
        {
          location: "line 9, col 42 to line 9, col 49 of module M",
          message: "Label not in definition or proof step.",
        },
        {
          location: "line 9, col 12 to line 9, col 49 of module M",
          message:
            "Substitution missing for symbol a declared at line 3, col 10 to line 3, col 10 of module M \nand instantiated in module M.",
        },
        {
          location: "line 10, col 33 to line 10, col 33 of module M",
          message:
            "Identifier 'd' is not a legal target of a substitution. \nA legal target must be a declared CONSTANT or VARIABLE in the module being instantiated. \n(Also, check for warnings about multiple declarations of this same identifier.)",
        },
        {
          location: "line 10, col 5 to line 10, col 38 of module M",
          message:
            "Substitution missing for symbol b declared at line 3, col 13 to line 3, col 13 of module M \nand instantiated in module M.",
        },
        {
          location: "line 11, col 11 to line 11, col 11 of module M",
          message: "Unknown operator: `V'.",
        },
      ],
      [
        {
          location: "line 12, col 5 to line 12, col 38 of module M",
          message:
            "Multiple declarations or definitions for symbol B.  \nThis duplicates the one at line 10, col 5 to line 10, col 38 of module M.",
        },
      ],
    ],
    [
      "an error in a nested module before a module defined twice",
      "Foo == 1\n---- MODULE Inner ----\nCONSTANT Foo\nB == 1\n====\n---- MODULE Inner ----\n====\nB == 2\nH == U",
      [
        {
          location: "line 4, col 10 to line 4, col 12 of module M",
          message:
            "Multiply-defined symbol 'Foo': this definition or declaration conflicts \nwith the one at line 2, col 1 to line 2, col 8 of module M.",
        },
        {
          location: "line 7, col 1 to line 8, col 4 of module M",
          message:
            "Multiply-defined module 'Inner': this definition or declaration conflicts \nwith the one at line 3, col 1 to line 6, col 4 of module M.",
        },
        {
          location: "line 10, col 6 to line 10, col 6 of module M",
          message: "Unknown operator: `U'.",
        },
      ],
      [],
    ],
    [
      "warnings in nested modules between the enclosing module's",
      "EXTENDS Naturals\nCONSTANT c\nCONSTANT c\n---- MODULE Inner ----\nEXTENDS Naturals\nPlus(a, b) == a + b\nPlus(a, b) == a - b\n====\n---- MODULE A1 ----\nFoo == 1\n====\n---- MODULE A2 ----\nFoo == 2\n====\n---- MODULE Both ----\nEXTENDS A1, A2\n====\nCONSTANT d\nCONSTANT d\nBar == U",
      [
        {
          location: "line 8, col 1 to line 8, col 19 of module M",
          message: "Operator Plus already defined or declared.",
        },
        {
          location: "line 21, col 8 to line 21, col 8 of module M",
          message: "Unknown operator: `U'.",
        },
      ],
      [
        {
          location: "line 4, col 10 to line 4, col 10 of module M",
          message:
            "Multiple declarations or definitions for symbol c.  \nThis duplicates the one at line 3, col 10 to line 3, col 10 of module M.",
        },
        {
          location: "line 8, col 1 to line 8, col 19 of module M",
          message:
            "Multiple declarations or definitions for symbol Plus.  \nThis duplicates the one at line 7, col 1 to line 7, col 19 of module M.",
        },
        {
          location: "line 14, col 1 to line 14, col 8 of module M",
          message:
            "Warning: the definition of 'Foo' conflicts with \nits definition at line 11, col 1 to line 11, col 8 of module M.",
        },
        {
          location: "line 20, col 10 to line 20, col 10 of module M",
          message:
            "Multiple declarations or definitions for symbol d.  \nThis duplicates the one at line 19, col 10 to line 19, col 10 of module M.",
        },
      ],
    ],
    [
      "a nested module's declaration of a name the enclosing module declares twice",
      "CONSTANT c\nCONSTANT c\n---- MODULE Inner ----\nCONSTANT c\n====\nBar == U",
      [
        {
          location: "line 7, col 8 to line 7, col 8 of module M",
          message: "Unknown operator: `U'.",
        },
      ],
      [3, 5].map((line) => ({
        location: `line ${line}, col 10 to line ${line}, col 10 of module M`,
        message:
          "Multiple declarations or definitions for symbol c.  \nThis duplicates the one at line 2, col 10 to line 2, col 10 of module M.",
      })),
    ],
    [
      "a semantic error after a nested module with a level error",
      "---- MODULE Inner ----\nVARIABLE y\nB == ENABLED (y' = y)\nC == []B\nD == C'\n====\nE == U",
      [
        {
          location: "line 8, col 6 to line 8, col 6 of module M",
          message: "Unknown operator: `U'.",
        },
      ],
      [],
    ],
  ])("rejects %s like SANY", async (_, source, errors, warnings) => {
    await expect(checkSource(source)).rejects.toMatchObject({ sany: { errors, warnings } });
  });

  it.each([
    [
      "a definition before an instance that imports it",
      "Nat == 1\nINSTANCE Naturals",
      "*** Warnings: 1\n\nline 14, col 1 to line 14, col 16 of module Naturals\n\nMultiple declarations or definitions for symbol Nat.  \nThis duplicates the one at line 2, col 1 to line 2, col 8 of module M.\n\n\n",
    ],
    [
      "a named instance defined twice",
      "J == INSTANCE Naturals\nJ == INSTANCE Naturals",
      "*** Warnings: 1\n\nline 3, col 1 to line 3, col 22 of module M\n\nMultiple declarations or definitions for symbol J.  \nThis duplicates the one at line 2, col 1 to line 2, col 22 of module M.\n\n\n",
    ],
    [
      "an assumption named twice",
      "ASSUME A == TRUE\nASSUME A == TRUE",
      "*** Warnings: 1\n\nline 3, col 1 to line 3, col 16 of module M\n\nMultiple declarations or definitions for symbol A.  \nThis duplicates the one at line 2, col 1 to line 2, col 16 of module M.\n\n\n",
    ],
    [
      "a definition of two extended modules",
      "---- MODULE A ----\nFoo == 1\n====\n---- MODULE B ----\nFoo(a) == 2\n====\n---- MODULE C ----\nEXTENDS A, B\nF == Foo\n====\nI == INSTANCE C",
      "*** Warnings: 1\n\nline 6, col 1 to line 6, col 11 of module M\n\nWarning: the definition of 'Foo' conflicts with \nits definition at line 3, col 1 to line 3, col 8 of module M.\n\n\n",
    ],
    [
      "a definition an instance copies from an extended module with parameters",
      "---- MODULE P ----\nVARIABLE sv\nShared == 0\n====\n---- MODULE In1 ----\nEXTENDS P\n====\n---- MODULE Q ----\nEXTENDS P\nINSTANCE In1\n====",
      "*** Warnings: 1\n\nline 11, col 1 to line 11, col 12 of module M\n\nMultiple declarations or definitions for symbol Shared.  \nThis duplicates the one at line 4, col 1 to line 4, col 11 of module M.\n\n\n",
    ],
    [
      "two NEW symbols with one name",
      "THEOREM ASSUME NEW a, NEW a PROVE TRUE",
      "*** Warnings: 1\n\nline 2, col 27 to line 2, col 27 of module M\n\nMultiple declarations or definitions for symbol a.  \nThis duplicates the one at line 2, col 20 to line 2, col 20 of module M.\n\n\n",
    ],
    [
      "a variable and a constant of two extended modules",
      "---- MODULE A ----\nVARIABLE Baz\n====\n---- MODULE B ----\nCONSTANT Baz\n====\n---- MODULE C ----\nEXTENDS A, B\nF == Baz\n====",
      "*** Warnings: 1\n\nline 6, col 10 to line 6, col 12 of module M\n\nWarning: the declaration of 'Baz' conflicts with \nits declaration at line 3, col 10 to line 3, col 12 of module M.\n\n\n",
    ],
  ])("warns of %s like SANY", async (_, source, warnings) => {
    const printed: string[] = [];
    const result = await checkOnEngine({
      source: `---- MODULE M ----\n${source}\nVARIABLE x\nInit == x = 0\nNext == x' = x\n====`,
      config: "INIT Init\nNEXT Next",
      onPrint: (text) => printed.push(text),
    });
    expect([result.status, printed[0]]).toEqual(["success", warnings]);
  });

  it("declines RECURSIVE declarations it never defines, which SANY rejects", async () => {
    await expectDeclined(
      {
        source:
          "---- MODULE M ----\nVARIABLE x\nInit == x = 0\nNext == x' = x\nRECURSIVE F(_), F(_)\n====",
        config: "INIT Init\nNEXT Next",
      },
      "the engine stopped before it searched (exit 150)",
    );
  });
});

describe("level checking matches SANY", () => {
  const getOptions = (definition: string) => ({
    source: `---- MODULE M ----\nVARIABLE x\nF == ${definition}\nInit == x = 0\nNext == x' = x\n====`,
    config: "INIT Init\nNEXT Next",
  });
  const checkDefinition = (definition: string) => checkOnEngine(getOptions(definition));

  // Cases from SANY's test215, which outlaws raw actions in temporal formulas.
  it.each([
    ["x' ~> []x", "Action used where only temporal formula or state predicate allowed"],
    ["[]x -+-> x'", "Action used where only temporal formula or state predicate allowed"],
    ["<>(x')", "<> followed by action not of form <<A>>_v"],
    ["[](x')", "[] followed by action not of form [A]_v"],
    ["\\A i \\in {}, j \\in x' : []x", "Action-level bound of quantified temporal formula"],
    ["(x')'", "Level error in applying operator '"],
    ["ENABLED []x", "Level error in applying operator ENABLED"],
  ])("rejects %s", async (definition, message) => {
    await expect(checkDefinition(definition)).rejects.toThrow(message);
  });

  it.each(["x ~> []x", "<><<x'>>_x", "[][x']_x", "\\A i \\in x' : x'", "[](LET A == x' IN A)"])(
    "accepts %s",
    async (definition) => {
      expect((await checkOnEngine(getOptions(definition))).status).toBe("success");
    },
  );

  // SANY bounds a sequence argument by the level its LAMBDA allows for the elements.
  it.each([
    "SelectSeq(s, LAMBDA a : a' = 1)",
    "SortSeq(s, LAMBDA a, b : a' = b)",
    "SortSeq(s, LAMBDA a, b : a = b')",
  ])("rejects a primed sequence where %s primes its elements", async (application) => {
    await expect(
      checkOnEngine({
        source: `---- MODULE M ----\nEXTENDS Sequences, TLC\nVARIABLE x\nF(s) == ${application}\nG == F(x')\nInit == x = 0\nNext == x' = x\n====`,
        config: "INIT Init\nNEXT Next",
      }),
    ).rejects.toThrow(
      createSemanticError(
        "Level error in applying operator F:\nThe level of argument 1 exceeds the maximum level allowed by the operator.",
        {
          module: "M",
          start: { line: 5, column: 6 },
          end: { line: 5, column: 10 },
        },
      ),
    );
  });

  // A mutation of tests/fixtures/counter/Counter.tla, recorded with TLC at d8fb231: an ASSUME
  // that ends a definition's conjunction list primes a variable.
  it("rejects an assumption above constant level, at the assumption, like SANY", async () => {
    await expect(
      check({
        source:
          "------------------------------ MODULE Counter ------------------------------\nEXTENDS Naturals\n\nCONSTANT Limit\n\nVARIABLE count\n\nInit == count = 0\n\nIncrement == /\\ count < Limit\n        ASSUME       /\\ count' = count + 1\n\nNext == Increment\n=============================================================================\n",
        config: "CONSTANT Limit = 3\nINIT Init\nNEXT Next",
      }),
    ).rejects.toThrow(
      createSemanticError(
        "Level error: assumptions must be level 0 (Constant), \nbut this one has level 2.",
        { module: "Counter", start: { line: 11, column: 9 }, end: { line: 11, column: 42 } },
      ),
    );
  });

  it("rejects an argument above the level an instantiated operator allows, naming it like SANY", async () => {
    await expect(
      checkOnEngine({
        source:
          "---- MODULE M ----\nVARIABLE x\n---- MODULE Inner ----\nVARIABLE y\nFoo == y' = 0\n====\nI(z) == INSTANCE Inner WITH y <- z\nFooBar == I(x')!Foo\nInit == x = 0\nNext == x' = x\n====",
        config: "INIT Init\nNEXT Next",
      }),
    ).rejects.toThrow("Level error in applying operator I!Foo:");
  });

  it.each([
    [
      "b == x' ~> []x\nh == <>(x')\nbar == [](x')\nn == \\A i \\in {}, j \\in x' : []x",
      [
        [
          "line 3, col 6 to line 3, col 14",
          "Action used where only temporal formula or state predicate allowed.",
        ],
        ["line 4, col 6 to line 4, col 11", "<> followed by action not of form <<A>>_v."],
        ["line 5, col 8 to line 5, col 13", "[] followed by action not of form [A]_v."],
        ["line 6, col 25 to line 6, col 26", "Action-level bound of quantified temporal formula."],
      ],
    ],
    [
      "Foo == [ab |-> 1, c |-> 2, ab |-> 3, c |-> 4]\nBar == [a : {1}, a : {2}]",
      [
        ["line 3, col 28 to line 3, col 29", "Non-unique fields in constructor."],
        ["line 3, col 38 to line 3, col 38", "Non-unique fields in constructor."],
        ["line 4, col 18 to line 4, col 18", "Non-unique fields in constructor."],
      ],
    ],
    [
      "THEOREM ASSUME NEW y, []y PROVE <>y\n<1>1. TAKE z \\in {x}\n<1>2. CASE []y\n  <2>1. HAVE x = 4\n  <2>2. QED\n<1>3. PICK c \\in {x} : <>(x = c)\n<1>4. QED",
      [
        [
          "line 6, col 9 to line 6, col 18",
          "Non-constant TAKE, WITNESS, or HAVE for temporal goal.",
        ],
        ["line 8, col 18 to line 8, col 20", "Non-constant bound of temporal PICK."],
        [
          "line 4, col 7 to line 4, col 20",
          "Non-constant TAKE, WITNESS, or HAVE for temporal goal.",
        ],
        ["line 5, col 7 to line 5, col 14", "Non-constant CASE for temporal goal."],
      ],
    ],
    [
      "THEOREM [](x = 0)\n<1>1. HAVE x = 1\n<1>2. QED\n---- MODULE Inner ----\nCONSTANT c\nASSUME c = {}\n====\nI == INSTANCE Inner WITH c <- [](x = 0)",
      [
        [
          "line 4, col 7 to line 4, col 16",
          "Non-constant TAKE, WITNESS, or HAVE for temporal goal.",
        ],
        [
          "line 10, col 1 to line 10, col 39",
          "Level error in instantiating module 'Inner':\nThe level of the expression or operator substituted for 'c' \nmust be at most 2.",
        ],
      ],
    ],
  ])("reports every error SANY reports in %j", async (definitions, errors) => {
    await expect(
      checkOnEngine({
        source: `---- MODULE M ----\nVARIABLE x\n${definitions}\nInit == x = 0\nNext == x' = x\n====`,
        config: "INIT Init\nNEXT Next",
      }),
    ).rejects.toThrow(
      createSanyError(
        errors.map(([location, message]) => ({ location: `${location} of module M`, message })),
      ),
    );
  });

  it("reports an error in instantiating a module before a constant the configuration leaves out, like TLC", async () => {
    await expect(
      checkOnEngine({
        source:
          "---- MODULE M ----\nVARIABLE x\nCONSTANT K\n---- MODULE Inner ----\nCONSTANT c\nASSUME c = {}\n====\nI == INSTANCE Inner WITH c <- [](x = 0)\nInit == x = 0\nNext == x' = x\n====",
        config: "INIT Init\nNEXT Next",
      }),
    ).rejects.toThrow("Level error in instantiating module 'Inner':");
  });

  const getParameterizedInstance = (definition: string) =>
    `---- MODULE M ----\nVARIABLE x\n---- MODULE Inner ----\nVARIABLE y\nOp(a) == <<a, y>>\n====\nI(a) == INSTANCE Inner WITH y <- a\nF(G(_, _)) == G(1, 2)\n${definition}\nInit == x = 0\nNext == x' = x\n====`;

  it("passes an operator of a parameterized instance as an operator argument, like SANY", async () => {
    const result = await checkOnEngine({
      source: getParameterizedInstance("X == F(I!Op)"),
      config: "INIT Init\nNEXT Next",
    });
    expect(result.status).toBe("success");
  });

  it.each([
    ["X == I!Op", 9],
    ["X == I!Op(1)", 12],
  ])("rejects %s without the arguments of the instance, like SANY", async (definition, end) => {
    await expect(
      checkOnEngine({
        source: getParameterizedInstance(definition),
        config: "INIT Init\nNEXT Next",
      }),
    ).rejects.toThrow(
      createSemanticError("The operator I requires 1 arguments.", {
        module: "M",
        start: { line: 9, column: 6 },
        end: { line: 9, column: end },
      }),
    );
  });
});

describe("parseConfig matches TLC", () => {
  it("reads operator symbols and names that start with digits", () => {
    const config = parseConfig("CONSTANT ++ <- PlusPlus\n  Plus <- +\n  \\o <- +\nINVARIANT 1Inv");
    expect(config.substitutions).toEqual([
      { name: "++", target: "PlusPlus" },
      { name: "Plus", target: "+" },
      { name: "\\o", target: "+" },
    ]);
    expect(config.invariants).toEqual(["1Inv"]);
  });

  it("reads _POSSIBLE and POSTCONDITION names", () => {
    const config = parseConfig("SPECIFICATION Spec\n_POSSIBLE Done Started\nPOSTCONDITION Post");
    expect([config.possible, config.postconditions]).toEqual([["Done", "Started"], ["Post"]]);
  });

  it("reads _PERIODIC and _RL_REWARD names and checks their definitions", async () => {
    const config = parseConfig("INIT Init\n_PERIODIC Periodic\n_RL_REWARD Reward");
    expect([config.periodic, config.rlReward]).toEqual(["Periodic", "Reward"]);
    await expect(checkModule("Argument(n) == n", "_PERIODIC Nope")).rejects.toThrow(
      new TlaConfigError(
        "The periodic Nope specified in the configuration file\nis not defined in the specification.",
      ),
    );
    await expect(checkModule("Argument(n) == n", "_RL_REWARD Argument")).rejects.toThrow(
      new TlaConfigError(
        "TLC requires rlreward not to take any argument, but one was given: Argument",
      ),
    );
    const result = await checkModule(
      "Periodic == x < 100\nReward == 1",
      "_PERIODIC Periodic\n_RL_REWARD Reward",
    );
    expect(result.status).toBe("success");
  });

  it("rejects keywords that appear twice", () => {
    ["CHECK_DEADLOCK", "_PERIODIC", "_RL_REWARD"].forEach((keyword) =>
      expect(() => parseConfig(`${keyword} FALSE\n${keyword} TRUE`)).toThrow(
        new TlaConfigError(
          `TLC found an error in the configuration file at line 2\nThe keyword ${keyword} appeared twice.`,
        ),
      ),
    );
  });

  it("reports TLC's errors for a file it can't read", () => {
    expect(() => parseConfig("CONSTANT Humans = {%1%}")).toThrow(
      new TlaConfigError(
        "TLC found an error in the configuration file at line 1\nIt was expecting }, but did not find it.",
      ),
    );
    expect(() => parseConfig("INIT Init\nNEXT Next\nSYMBOLIC_INTEGERS Int")).toThrow(
      new TlaConfigError(
        "TLC found an error in the configuration file at line 3\nIt was expecting a keyword, but did not find it.",
      ),
    );
    expect(() => parseConfig('INIT Init\n"unterminated\nNEXT Next')).toThrow(
      new TlaConfigError(
        'TLC found an error in the configuration file:\nLexical error at line 2, column 14.  Encountered: "\\n" (10), after : "\\"unterminated"',
      ),
    );
  });

  it("reads values the way TLC does", () => {
    expect(parseConfig('CONSTANT S = "a\\"b\\\\n"').constants[0].value).toEqual({
      kind: "String",
      value: 'a\\"b\\\\n',
    });
    ["CONSTANT N = -1", "CONSTANT S = {1,}"].forEach((source) =>
      expect(() => parseConfig(source)).toThrow(TlaConfigError),
    );
    // SANY's lexer reads ℕ as a name.
    expect(parseConfig("INVARIANT ℕ").invariants).toEqual(["ℕ"]);
  });

  it("reports a malformed configuration with TLC's messages", () => {
    const atLine = (line: number, detail: string) =>
      `TLC found an error in the configuration file at line ${line}\n${detail}`;
    const lexical = (detail: string) =>
      `TLC found an error in the configuration file:\nLexical error at ${detail}`;
    const cases = [
      ["INIT\n", atLine(1, "The keyword INIT was not followed by an identifier.")],
      ["CONSTANT N = -1\nINIT Init\n", atLine(2, "It was expecting = or <-, but did not find it.")],
      // TLC reads ← with SANY's lexer, and compares it as written with <-.
      ["CONSTANT N ← 1\nINIT Init\n", atLine(1, "It was expecting = or <-, but did not find it.")],
      ["CHECK_DEADLOCK 3\n", atLine(1, "It was expecting TRUE or FALSE, but did not find it.")],
      ["CONSTANT N = {1, 2\nINIT Init\n", atLine(2, "It was expecting }, but did not find it.")],
      ["CONSTANT N =\n", atLine(2, "It was expecting a value, but did not find it.")],
      ["INIT Init ~\n", atLine(1, "It was expecting a keyword, but did not find it.")],
      ["(* open\nINIT Init\n", lexical('line 4, column 0.  Encountered: <EOF> after : ""')],
      ["INIT Init\n`x\n", lexical('line 2, column 1.  Encountered: "`" (96), after : ""')],
      [
        'CONSTANT N = "a\nINIT Init\n',
        lexical('line 1, column 16.  Encountered: "\\n" (10), after : "\\"a"'),
      ],
    ];
    for (const item of cases) {
      expect(() => parseConfig(item[0])).toThrow(new TlaConfigError(item[1]));
    }
  });
});

describe("initial predicate and next-state relation match TLC", () => {
  const checkSource = (body: string, config: string) =>
    checkOnEngine({ source: `---- MODULE M ----\n${body}\n====`, config });

  it("explores no states when a spec without variables has no initial predicate", async () => {
    const result = await checkSource("ASSUME TRUE\nSpec == [][TRUE]_<<>>", "SPECIFICATION Spec");
    expect([result.status, result.generatedStates, result.distinctStates, result.depth]).toEqual([
      "success",
      0,
      0,
      0,
    ]);
  });

  it("requires an initial predicate when the spec has variables", async () => {
    await expect(
      checkSource("VARIABLE x\nSpec == [][x' = x]_x", "SPECIFICATION Spec"),
    ).rejects.toThrow(/did not specify the initial state predicate/);
  });

  it("rejects a constant initial predicate or next-state action", async () => {
    await expect(
      checkSource("VARIABLE x\nInit == TRUE\nNext == x' = x", "INIT Init\nNEXT Next"),
    ).rejects.toThrow(/The initial predicate Init cannot be a constant/);
    await expect(
      checkSource("VARIABLE x\nInit == x = 0\nNext == TRUE", "INIT Init\nNEXT Next"),
    ).rejects.toThrow(/The next state action Next cannot be a constant/);
  });

  it("takes a constant next-state action that TLC fails to compute for an operator", async () => {
    const result = await checkStepsOnEngine(
      "Step == <<TRUE>>[1] /\\ <<1>>[1]",
      "INIT Init\nNEXT Step",
    );
    expect(result.violations[0]?.headline).toBe(
      `${UNEXPECTED_EXCEPTION}In computing next states, TLC expected a boolean expression,\nbut didn't find one.\nline 6, col 24 to line 6, col 31 of module M`,
    );
  });

  it("checks the configuration in the order TLC reads it, before any assumption", async () => {
    await expect(
      checkSource(
        "VARIABLE x\nASSUME FALSE\nInit == x = 0\nNext == TRUE\nInv == {}",
        "INIT Init\nNEXT Next\nINVARIANT Inv\nPROPERTY Q",
      ),
    ).rejects.toThrow(new TlaConfigError("The invariant of Inv is equal to {}"));
    await expect(
      checkSource(
        "VARIABLE x\nInit == x = 0\nNext == x' = x\nQ(a) == TRUE",
        "INIT Init\nNEXT Next\nPROPERTY Q\nCONSTRAINT Nope",
      ),
    ).rejects.toThrow(new TlaConfigError("TLC requires Q not to take any argument."));
    await expect(
      checkSource(
        "VARIABLE x\nInit == x = 0\nNext == x' = x\nC == FALSE",
        "INIT Init\nNEXT Next\nCONSTRAINT C",
      ),
    ).rejects.toThrow(new TlaConfigError("The constraint of C is equal to FALSE"));
  });

  it("rejects an invariant that is not a state predicate", async () => {
    await expect(
      checkSource(
        "VARIABLE x\nInit == x = 0\nNext == x' = x\nInv == []TRUE",
        "INIT Init\nNEXT Next\nINVARIANT Inv",
      ),
    ).rejects.toThrow(
      new TlaConfigError(
        "The invariant Inv is not a state predicate (one with no primes or temporal operators).",
      ),
    );
    await expect(
      checkSource(
        "VARIABLE x\nInit == x = 0\nNext == x' = x\nInv == x' = x",
        "INIT Init\nNEXT Next\nINVARIANT Inv",
      ),
    ).rejects.toThrow(
      new TlaConfigError(
        "The invariant Inv is not a state predicate (one with no primes or temporal operators).\nNote that a bug can cause TLC to incorrectly report this error.\nIf you believe your TLA+ or PlusCal specification to be correct,\nplease check if this bug described in LevelNode.java starting at line 590ff affects you.",
      ),
    );
  });

  it("binds a variable once for each time a lazy UNION streams an element", async () => {
    const set = "UNION {SUBSET {1}, {{}}}";
    const result = await checkSource(
      `VARIABLE x\nInit == x \\in ${set}\nNext == x' \\in ${set}`,
      "INIT Init\nNEXT Next",
    );
    expect([result.generatedStates, result.distinctStates]).toEqual([9, 2]);
  });

  it("keeps a set operation lazy unless TLC can reduce both sets", async () => {
    const getCounts = async (set: string) => {
      const result = await checkSource(
        `EXTENDS Naturals\nVARIABLE x\nInit == x \\in ${set}\nNext == UNCHANGED x`,
        "INIT Init\nNEXT Next",
      );
      return [result.generatedStates, result.distinctStates];
    };
    expect(await getCounts("(SUBSET {1}) \\cup SUBSET {2}")).toEqual([7, 3]);
    expect(await getCounts("(1..3) \\cup SUBSET {}")).toEqual([8, 4]);
    expect(await getCounts("{1} \\cup {1, 2}")).toEqual([4, 2]);
  });

  it("streams a lazy UNION's duplicates until TLC caches the set", async () => {
    const nexts = [
      "y' \\in UNION {UNION {0..2, {1}}, {7}}",
      "\\E e \\in UNION {UNION {0..2, {1}}, {7}} : y' = e",
      "y' \\in {1} \\X UNION {UNION {0..2, {1}}, {1, 2}}",
    ];
    const results = await Promise.all(
      nexts.map((next) =>
        checkOnEngine({
          source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLES x, y\nInit == x = 0 /\\ y = 0\nNext == (${next}) /\\ UNCHANGED x\n====`,
          config: "INIT Init\nNEXT Next",
        }),
      ),
    );
    expect(results.map((result) => result.generatedStates)).toEqual([21, 17, 25]);
  });

  it("keeps the names a recursive function binds apart in each call", async () => {
    const result = await checkSource(
      "EXTENDS Sequences\nVARIABLE v\nPerms(S) == LET p[s \\in SUBSET S] == IF s = {} THEN {<<>>} ELSE LET q == [x \\in s |-> {Append(t, x) : t \\in p[s \\ {x}]}] IN UNION {q[x] : x \\in s} IN p[S]\nInit == v = <<>>\nNext == \\E t \\in Perms({1, 2, 3}) : v' = t",
      "INIT Init\nNEXT Next",
    );
    expect(result.distinctStates).toBe(7);
  });

  it("walks the body of a LET's function that an action applies, as TLC does", async () => {
    // Where both disjuncts of the function's body hold, TLC generates the successor twice.
    const result = await checkSource(
      "EXTENDS Integers\nVARIABLES m, x\nInit == m \\in [{1, 2} -> -1..2] /\\ x = -5\nSafe(b) == LET f[c \\in 0..2] == c = 0 \\/ \\A i \\in {1, 2} : m[i] >= c IN f[b]\nNext == \\E b \\in 0..2 : Safe(b) /\\ x' = b /\\ UNCHANGED m",
      "INIT Init\nNEXT Next",
    );
    expect([result.generatedStates, result.distinctStates]).toEqual([93, 37]);
  });

  it("evaluates a LET definition's UNION again at each reference in an action", async () => {
    const result = await checkSource(
      "EXTENDS Naturals, FiniteSets\nVARIABLES x, y\nInit == x = 0 /\\ y = 0\nNext == LET u == UNION {UNION {0..2, {1}}, {7}} IN Cardinality(u) > 0 /\\ y' \\in u /\\ UNCHANGED x",
      "INIT Init\nNEXT Next",
    );
    expect(result.generatedStates).toBe(21);
  });

  it("reports initial states without a next-state action", async () => {
    await expect(checkSource("VARIABLE x\nInit == x \\in {1, 2}", "INIT Init")).rejects.toThrow(
      /No next state actions defined to generate successor states from/,
    );
  });

  it.each([
    ["[](FALSE)", "Invariant FALSE is violated by the initial state:"],
    ["[]Bad", "Invariant Bad is violated by the initial state:"],
    ["[](Op(1))", "Invariant Property is violated by the initial state:"],
    ["Op(1)", "Property Op is violated by the initial state:"],
    [
      "Two(0)",
      "Property line 6, col 11 to line 6, col 15 of module M is violated by the initial state:",
    ],
    [
      "[](x = 0) /\\ [](x = 1)",
      "Invariant line 8, col 26 to line 8, col 34 of module M is violated by the initial state:",
    ],
    [
      "[](x = 0) /\\ (x = 1)",
      "Property line 8, col 27 to line 8, col 31 of module M is violated by the initial state:",
    ],
    [
      "\\A n \\in {0, 1} : x # n",
      "Property line 8, col 31 to line 8, col 35 of module M is violated by the initial state:",
    ],
    [
      "[](x < 9) /\\ [][x = 7]_x",
      "Action property line 8, col 26 to line 8, col 36 of module M is violated.",
    ],
  ])("names the part of property %s that fails as TLC does", async (property, headline) => {
    const result = await checkSource(
      `EXTENDS Integers\nVARIABLE x\nBad == x = 1\nOp(n) == x = n\nTwo(n) == x # n /\\ x # n + 1\nSpec == x = 0 /\\ [][x' = x + 1 /\\ x < 3]_x\nProperty == ${property}`,
      "SPECIFICATION Spec\nPROPERTY Property\nCHECK_DEADLOCK FALSE",
    );
    expect(result.violations[0]?.headline).toBe(headline);
  });

  it("names the invariant a property asserts by the operator an extended module defines", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Base\nSpec == x = 0 /\\ [][x' = x + 1 /\\ x < 3]_x\nProperty == []Small\n====",
      config: "SPECIFICATION Spec\nPROPERTY Property\nCHECK_DEADLOCK FALSE",
      loadModule: (name) =>
        name === "Base"
          ? "---- MODULE Base ----\nEXTENDS Integers\nVARIABLE x\nSmall == x < 2\n===="
          : undefined,
    });
    expect(result.violations[0]?.headline).toBe("Invariant Small is violated.");
  });

  it("declines a property that quantifies over no elements, a tautology", async () => {
    await expectDeclined(
      {
        source:
          "---- MODULE M ----\nVARIABLE x\nSpec == x = 0 /\\ [][x' = x]_x\nProperty == \\A n \\in {} : x # n\n====",
        config: "SPECIFICATION Spec\nPROPERTY Property",
      },
      "a property TLC finds a tautology",
    );
  });

  it.each([
    ["x \\in UNION UNION (SUBSET {{}, {{}}})", "UNCHANGED x", [3, 1]],
    ["x \\in UNION UNION {SUBSET {1}, {{1}}}", "UNCHANGED x", [3, 1]],
    ["x = 0", "x = 0 /\\ x' \\in UNION UNION (SUBSET {{1}, {1, 2}})", [7, 3]],
  ])("streams a lazy UNION of a lazy UNION with Init %s", async (init, next, counts) => {
    const result = await checkSource(
      `VARIABLE x\nInit == ${init}\nNext == ${next}`,
      "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
    );
    expect([result.generatedStates, result.distinctStates]).toEqual(counts);
  });

  it.each([
    ["UNION {UNION (SUBSET {{1}, {1, 2}}), {1}}", [8, 3]],
    ["UNION {{1}, UNION (SUBSET {{1}, {1, 2}})}", [6, 3]],
  ])("streams a lazy UNION in %s until a sort compares it as TLC does", async (set, counts) => {
    const result = await checkSource(
      `VARIABLE x\nInit == x \\in ${set}\nNext == UNCHANGED x`,
      "INIT Init\nNEXT Next",
    );
    expect([result.generatedStates, result.distinctStates]).toEqual(counts);
  });
});

describe("check matches TLC master", () => {
  it("leaves out the outdegree of the state whose invariant it failed to evaluate", () => {
    const run = runOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == \\E n \\in {1, 2} : x' = x + n\nInv == x # 3 \\/ CHOOSE n \\in {} : TRUE\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT Inv",
    });
    expect(getStatistics(run.output).at(-1)).toBe(
      "The average outdegree of the complete state graph is 2 (minimum is 1, the maximum 2 and the 95th percentile is 2).",
    );
  });

  const getPropertyOptions = (property: string) => ({
    source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x, b\nInit == x = 0 /\\ b = FALSE\nNext == x' = x /\\ b' = ~b\nSpec == Init /\\ [][Next]_<<x, b>>\n${property}\n====`,
    config: "SPECIFICATION Spec\nPROPERTY P",
  });

  // TLC names a part of a property by its location, or by the definition it is the body of.
  it.each([
    ["P == []b", "Invariant b is violated by the initial state:"],
    ["P == []FALSE", "Invariant FALSE is violated by the initial state:"],
    [
      "P == [](x # 0) /\\ TRUE",
      "Invariant line 7, col 6 to line 7, col 14 of module M is violated by the initial state:",
    ],
    [
      "P == x # 0 /\\ TRUE",
      "Property line 7, col 6 to line 7, col 10 of module M is violated by the initial state:",
    ],
    ["Q == [][b' = b]_b\nP == Q /\\ TRUE", "Action property Q is violated."],
    [
      "P == \\A c \\in {0, 1} : x # c",
      "Property line 7, col 24 to line 7, col 28 of module M is violated by the initial state:",
    ],
  ])("names the violated part of a property as TLC does: %s", async (property, headline) => {
    const result = await checkOnEngine(getPropertyOptions(property));
    expect(result.violations[0]?.headline).toBe(headline);
  });

  it("declines a property that quantifies over the empty set, a tautology", async () => {
    await expectDeclined(
      getPropertyOptions("P == \\A c \\in {} : []b"),
      "a property TLC finds a tautology",
    );
  });

  // TLC evaluates the constant parts of the properties as it builds the liveness checker.
  const getConstantPartOptions = (property: string) => ({
    source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nSpec == Init /\\ [][x' = x]_x\nP == ${property}\n====`,
    config: "SPECIFICATION Spec\nPROPERTY P",
  });

  it("declines an error in the constant part of the property <>(1 \\notin SUBSET 1)", async () => {
    await expectDeclined(
      getConstantPartOptions("<>(1 \\notin SUBSET 1)"),
      "an operator, which the constant evaluator doesn't compute",
    );
  });

  it.each([
    ["<>(1 + 1)", "line 6, col 9 to line 6, col 13 of module M"],
    ["<>(\\b101 /\\ TRUE)", "\\b101"],
  ])(
    "reports an error in the constant part of the property %s like TLC",
    async (property, part) => {
      await expect(checkOnEngine(getConstantPartOptions(property))).rejects.toThrow(
        new TlaEvaluationError(`TLC expected a boolean value, but did not find one. ${part}`),
      );
    },
  );

  it("declines TLCGet of the revision", async () => {
    await expectDeclined(
      {
        source:
          '---- MODULE M ----\nEXTENDS TLC\nVARIABLE x\nInit == x = TLCGet("revision").tag\nNext == UNCHANGED x\n====',
        config: "INIT Init\nNEXT Next",
      },
      "the engine stopped: unsupported: TLCGet of a key the search doesn't keep",
    );
  });

  it("sizes a set of functions with an empty range without its domain", async () => {
    const result = await checkOnEngine({
      source:
        "---- MODULE M ----\nEXTENDS Naturals, FiniteSets\nVARIABLE x\nInit == x = Cardinality([Nat -> {}])\nNext == UNCHANGED x\n====",
      config: "INIT Init\nNEXT Next",
    });
    expect(result.status).toBe("success");
  });

  it("rebuilds the trace, so it prints the states' output again", () => {
    const run = runOnEngine({
      source:
        '---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0 /\\ PrintT("init")\nNext == x = 5 /\\ x\' = x\n====',
      config: "INIT Init\nNEXT Next",
    });
    expect(getTraceOutput(run.output)).toEqual(['"init"']);
  });

  it("expands a specification that applies an operator to arguments", async () => {
    const result = await checkOnEngine({
      source: "---- MODULE M ----\nVARIABLE x\nS(v) == v = 0 /\\ [][v' = v]_v\nSpec == S(x)\n====",
      config: "SPECIFICATION Spec",
    });
    expect(result.status).toBe("success");
  });

  it("reads the level of the state it explores in a constraint", async () => {
    const result = await checkOnEngine({
      source:
        '---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x\' = x + 1\nC == TLCGet("level") < 3\n====',
      config: "INIT Init\nNEXT Next\nCONSTRAINT C\nCHECK_DEADLOCK FALSE",
    });
    expect(result.distinctStates).toBe(2);
  });

  it("evaluates TLCGet in a temporal property as it checks it", async () => {
    const result = await checkOnEngine({
      source:
        '---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x\' = 1 - x\nSpec == Init /\\ [][Next]_x\nP == <>[](x = 1 /\\ TLCGet("diameter") > 0)\n====',
      config: "SPECIFICATION Spec\nPROPERTY P",
    });
    expect(result.status).toBe("liveness-violation");
  });

  it("evaluates the arguments of a recursive temporal operator it expands", async () => {
    const getOptions = (property: string) => ({
      source: `---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = 1 - x\nSpec == Init /\\ [][Next]_x\nRECURSIVE R(_)\nR(n) == IF n = 0 THEN <>(x = 1) ELSE R(n - 1)\nP == ${property}\n====`,
      config: "SPECIFICATION Spec\nPROPERTY P",
    });
    expect((await checkOnEngine(getOptions("R(2)"))).status).toBe("liveness-violation");
    await expect(checkOnEngine(getOptions("R(x)"))).rejects.toThrow(
      new TlaEvaluationError(STACK_OVERFLOW_MESSAGE),
    );
  });

  it.each([
    // The shape of TLC's CyclicRedefineVars: Init <- ReInit, whose body names Init.
    [
      "Init == x = FALSE\nNext == x' = ~x\nSpec == Init /\\ [][Next]_x\nReInit == x \\in BOOLEAN /\\ Init",
      "SPECIFICATION Spec\nCONSTANT Init <- ReInit",
      new TlaStackOverflowError(),
    ],
    // TLC reports an EvalException in the values a property quantifies over.
    [
      "Init == x = 0\nNext == x' = 1 - x\nSpec == Init /\\ [][Next]_x\nP == \\A k \\in {1 \\div 0} : <>(x = k)",
      "SPECIFICATION Spec\nPROPERTY P",
      new TlaEvaluationError(`${UNEXPECTED_EVAL_EXCEPTION}The second argument of \\div is 0.`),
    ],
    // TLC can't handle a quantified formula whose body fails.
    [
      "Init == x = 0\nNext == x' = 1 - x\nSpec == Init /\\ [][Next]_x\nP == \\E k \\in 0..1 : <>(2 \\in 1)",
      "SPECIFICATION Spec\nPROPERTY P",
      new TlaEvaluationError(
        "TLC cannot handle the temporal formula line 7, col 6 to line 7, col 32 of module M",
      ),
    ],
    [
      "Init == x = 0\nNext == x' = 1 - x\nSpec == Init /\\ [][Next]_x\nP == \\A k \\in 1 : <>(x = k)",
      "SPECIFICATION Spec\nPROPERTY P",
      new TlaEvaluationError(
        "TLC cannot handle the temporal formula line 7, col 6 to line 7, col 27 of module M:\nTLC encountered a non-enumerable quantifier bound\n1.\n1",
      ),
    ],
  ])(
    "reports a spec TLC rejects before it searches like TLC: %s",
    async (definitions, config, error) => {
      const thrown = await checkOnEngine({
        source: `---- MODULE M ----\nEXTENDS Integers\nVARIABLE x\n${definitions}\n====`,
        config,
      }).then(
        () => undefined,
        (reason: unknown) => reason,
      );
      expect(thrown).toBeInstanceOf(error.constructor);
      expect((thrown as Error).message).toBe(error.message);
    },
  );

  // TLC doesn't evaluate a definition with a temporal operator before it checks the property.
  it("declines a property quantified over no values, a tautology", async () => {
    await expectDeclined(
      {
        source:
          "---- MODULE M ----\nEXTENDS Integers\nVARIABLE x\nInit == x = 0\nNext == x' = 1 - x\nSpec == Init /\\ [][Next]_x\nP == \\A k \\in {} : <>TRUE\n====",
        config: "SPECIFICATION Spec\nPROPERTY P",
      },
      "a property TLC finds a tautology",
    );
  });
});

describe("check without code generation from strings", () => {
  it("checks a spec like it does with code generation", async () => {
    const options = {
      source:
        "---- MODULE M ----\nVARIABLE present\nInit == present = FALSE\nNext == UNCHANGED present\nInv == ~present \\/ present\n====",
      config: "INIT Init\nNEXT Next\nINVARIANT Inv",
    };
    const script = `const tlaTs = await import(${JSON.stringify(pathToFileURL(DIST).href)});
console.log(JSON.stringify(await tlaTs.check(${JSON.stringify(options)})));`;
    const output = execFileSync(
      "node",
      ["--disallow-code-generation-from-strings", "--input-type=module", "--eval", script],
      { encoding: "utf8" },
    );
    expect(JSON.parse(output)).toEqual(JSON.parse(JSON.stringify(await check(options))));
  });
});

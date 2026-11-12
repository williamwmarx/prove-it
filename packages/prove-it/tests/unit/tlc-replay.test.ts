import { describe, expect, it } from "bun:test";

import type { Expression } from "../../src/ast";
import { checkParsed } from "../../src/parallel";
import type { TlcVersion } from "../../src/tlc/version";
import {
  getErrors,
  getNestedExpressions,
  getStatistics,
  runOnEngine,
  type TlcRunOptions,
} from "../native-check";

const HEADER = [
  "EXTENDS Naturals, Sequences, TLC, FiniteSets",
  "VARIABLE x",
  'Name == <<"zero", "one">>',
  "Rec == [a |-> 1, b |-> 2]",
  'Map == 1 :> "a" @@ 2 :> "b"',
  "Op(i) == Name[i]",
].join("\n");

// The positions TLC prints for a call stack, which skip a node that repeats the one before it.
const formatCallStack = (expressions: Expression[] | undefined) =>
  expressions
    ?.filter((expression, index) => expression !== expressions[index - 1])
    .map((expression) => {
      const range = expression.location.range;
      return range
        ? `${range.start.line}.${range.start.column}-${range.end.line}.${range.end.column}`
        : "?";
    });

const checkSpec = (definitions: string, config: string, version?: TlcVersion) =>
  checkParsed({
    source: `---- MODULE M ----\n${HEADER}\n${definitions}\n====`,
    config,
    version,
    onPrint: () => {},
  });

const getFailure = async (
  definitions: string,
  config = "INIT Init\nNEXT Next",
  version?: TlcVersion,
) => {
  const result = await checkSpec(definitions, config, version);
  return {
    callStack: formatCallStack(result.failure?.callStack),
    exitCode: result.failure?.exitCode,
  };
};

const getRunOptions = (definitions: string, config = "INIT Init\nNEXT Next"): TlcRunOptions => ({
  source: `---- MODULE M ----\n${HEADER}\n${definitions}\n====`,
  config,
});

// The call stack the CLI printed, in the form formatCallStack writes.
const getCallStack = (output: string) =>
  getNestedExpressions(output)?.map((line) =>
    line.replace(
      /^\d+\. Line (\d+), column (\d+) to line (\d+), column (\d+) in \w+$/,
      "$1.$2-$3.$4",
    ),
  );

// The call stack and exit code of the CLI's run on the engine.
const getRunFailure = (definitions: string, config?: string, declinedFor?: string) => {
  const run = runOnEngine(getRunOptions(definitions, config), declinedFor);
  return { callStack: getCallStack(run.output), exitCode: run.exitCode };
};

const INTEGER_DECLINED =
  "the engine stopped: expected an integer: evaluating the failure again: expected an integer, not a string";
const CONSTRAINT_DECLINED =
  "the engine stopped: a constraint, a VIEW or an action property that fails on a successor";

// Each call stack is the one TLC 1.8.0 prints for the same spec.
describe("the call stack of a replayed failure matches TLC", () => {
  it("walks the conjuncts and quantifiers of the next-state relation", () => {
    expect(
      getRunFailure(
        "Init == x = 0\nNext == \\E i \\in {1, 2} : x' = x + Op(x + i)",
        undefined,
        INTEGER_DECLINED,
      ),
    ).toEqual({ callStack: ["9.27-9.44", "9.32-9.44"], exitCode: 75 });
  });

  it("enters the definition that an action applies", () => {
    expect(
      getRunFailure(
        "Step(n) == x' = n + Name[n + 2]\nInit == x = 0\nNext == Step(x)",
        undefined,
        INTEGER_DECLINED,
      ),
    ).toEqual({ callStack: ["10.9-10.15", "8.12-8.31", "8.17-8.31"], exitCode: 75 });
  });

  it("walks the body of a function that an action applies", () => {
    expect(getRunFailure("Init == x = 0\nNext == [p \\in {1} |-> 0][1] /\\ x' = x")).toEqual({
      callStack: ["9.9-9.38", "9.9-9.28", "9.24-9.24"],
      exitCode: 75,
    });
  });

  it("keeps the conjuncts of a bulleted list that held", () => {
    expect(
      getRunFailure('Init == x = 0\nNext == /\\ Name[x + 1] # "z"\n        /\\ x\' = x + 1'),
    ).toEqual({ callStack: ["9.9-10.21", "9.12-9.28", "9.12-9.22"], exitCode: 75 });
  });

  it("ends each prefix of an infix conjunction after the parentheses of its last operand", () => {
    expect(
      getRunFailure("Init == x = 0\nNext == (x < 3) /\\ (x' = x + 1) /\\ TRUE /\\ (x' # Name[3])"),
    ).toEqual({
      callStack: [
        "9.9-9.57",
        "9.9-9.39",
        "9.9-9.31",
        "9.10-9.14",
        "9.21-9.30",
        "9.45-9.56",
        "9.50-9.56",
      ],
      exitCode: 75,
    });
  });

  it("checks an initial state inside the initial predicate", () => {
    expect(
      getRunFailure(
        "Init == x = 0\nNext == x' = x + 1\nInv == Name[x + 1] = Name[x]",
        "INIT Init\nNEXT Next\nINVARIANT Inv",
      ),
    ).toEqual({ callStack: ["8.9-8.13", "10.8-10.28", "10.22-10.28"], exitCode: 75 });
  });

  it("checks the constraints of a successor after the action", () => {
    expect(
      getRunFailure(
        'Init == x = 0\nNext == x\' = x + 1\nSmall == Name[x + 1] # "z"',
        "INIT Init\nNEXT Next\nCONSTRAINT Small",
        CONSTRAINT_DECLINED,
      ),
    ).toEqual({ callStack: ["10.10-10.26", "10.10-10.20"], exitCode: 75 });
  });

  it("exits with the code of a standard module's failure in an action property", () => {
    const failure = getRunFailure(
      "Init == x = 0\nNext == x < 3 /\\ x' = x + 1\nSpec == Init /\\ [][Next]_x\nProp == [][1 \\div (1 - x) = 1]_x",
      "SPECIFICATION Spec\nPROPERTY Prop",
      CONSTRAINT_DECLINED,
    );
    expect(failure).toEqual({
      callStack: ["11.11-11.32", "11.12-11.29", "11.12-11.25"],
      exitCode: 255,
    });
  });

  // TLC's worker adds a state to the behavior graph even after its next states fail or violate a
  // property, which evaluates ENABLED for the fairness of the spec.
  const FAIRNESS = "Spec == Init /\\ [][Next]_x /\\ WF_x(Fair)\nLive == []<>(x = 0)";

  const LIVE_STACK = ["13.36-13.39", "12.9-12.12", "11.9-11.14", "11.9-11.9"];

  const getLiveDefinitions = (value: string) =>
    `Init == x = 0\nA == x' = ${value}\nB == x' = x\nNext == A \\/ B\nFair == Next\n${FAIRNESS}`;

  // Without a replay, TLC exits with the code of the error rather than of a failed replay.
  it.each([
    ["1 \\div x", [...LIVE_STACK, "9.6-9.18", "9.11-9.18"]],
    ["CHOOSE y \\in {} : TRUE", [...LIVE_STACK, "9.6-9.32", "9.11-9.32"]],
  ])(
    "prints where adding a state whose next states fail to the behavior graph fails (%s)",
    (value, callStack) => {
      expect(getRunFailure(getLiveDefinitions(value), "SPECIFICATION Spec\nPROPERTY Live")).toEqual(
        { callStack, exitCode: 255 },
      );
    },
  );

  it.each([
    ["1.7.4" as const, "1 \\div x", ["9.6-9.18", "9.11-9.18"], 255],
    ["1.7.4" as const, "CHOOSE y \\in {} : TRUE", ["9.6-9.32", "9.11-9.32"], 75],
  ])(
    "prints where adding a state whose next states fail to the behavior graph fails (TLC %s, %s)",
    async (version, value, callStack, exitCode) => {
      expect(
        await getFailure(getLiveDefinitions(value), "SPECIFICATION Spec\nPROPERTY Live", version),
      ).toEqual({ callStack, exitCode });
    },
  );

  // TLC's enabled walks every conjunct, even once the action has assigned every variable.
  it("walks the conjuncts of a fair action after it assigns every variable", () => {
    expect(
      getRunFailure(
        "Init == x = 0\nA == x' = x /\\ (IF x = 0 THEN 3 ELSE TRUE)\nSpec == Init /\\ [][x' = x]_x /\\ WF_x(A)\nP == <>(x = 0)",
        "SPECIFICATION Spec\nPROPERTY P",
      ),
    ).toEqual({
      callStack: ["10.38-10.38", "9.6-9.42", "9.6-9.11", "9.17-9.41", "9.31-9.31"],
      exitCode: 255,
    });
  });

  const getGraphDefinitions = (bound: number) =>
    `Init == x = 0\nFair == x' = 1 \\div (x - 1)\nNext == x < ${bound} /\\ x' = x + 1\nInv == x < 2\n${FAIRNESS}`;

  it("prints where adding a state to the behavior graph fails after a deadlock", () => {
    const run = runOnEngine(
      getRunOptions(getGraphDefinitions(1), "SPECIFICATION Spec\nPROPERTY Live\nINVARIANT Inv"),
    );
    expect([run.exitCode, getCallStack(run.output)]).toEqual([
      11,
      ["12.36-12.39", "9.9-9.27", "9.14-9.27"],
    ]);
  });

  // The engine doesn't yet print where adding the state fails after an invariant violation.
  it.each([
    [undefined, "invariant-violation", ["12.36-12.39", "9.9-9.27", "9.14-9.27"]],
    ["1.7.4" as const, "invariant-violation", undefined],
  ])(
    "prints where adding a state to the behavior graph fails after a violation (TLC %s, %s)",
    async (version, status, callStack) => {
      const result = await checkSpec(
        getGraphDefinitions(3),
        "SPECIFICATION Spec\nPROPERTY Live\nINVARIANT Inv",
        version,
      );
      expect([result.status, formatCallStack(result.liveCallStack)]).toEqual<unknown[]>([
        status,
        callStack,
      ]);
    },
  );

  it.each([
    [undefined, [1, 1]],
    ["1.7.4" as const, [0, 1]],
  ])(
    "counts a deadlocked state it fails to add to the behavior graph as expanded (TLC %s)",
    async (version, outDegrees) => {
      const result = await checkSpec(
        `Init == x = 0\nFair == x' = 1 \\div (x - 1)\nNext == x < 1 /\\ x' = x + 1\n${FAIRNESS}`,
        "SPECIFICATION Spec\nPROPERTY Live",
        version,
      );
      expect(result.violationOutDegrees?.slice(0, 2)).toEqual(outDegrees);
    },
  );
});

describe("the replay of a failed initial state matches TLC", () => {
  // The states generated, and the progress the replay printed after the error.
  const replayInit = (init: string, inv: string, declinedFor?: string) => {
    const run = runOnEngine(
      getRunOptions(
        `Init == ${init}\nNext == x' = x\nInv == ${inv}`,
        "INIT Init\nNEXT Next\nINVARIANT Inv",
      ),
      declinedFor,
    );
    return [
      getStatistics(run.output)[0],
      getErrors(run.output)[0]
        ?.split("\n")
        .filter((line) => /^Computed \d+ initial states\.\.\.$/.test(line)),
    ];
  };

  it("reports its progress again as it generates the initial states", () => {
    expect(replayInit("x \\in 1..6", "x < 5 \\/ (CHOOSE y \\in {} : TRUE)")).toEqual([
      "5 states generated, 5 distinct states found, 5 states left on queue.",
      ["Computed 2 initial states...", "Computed 4 initial states..."],
    ]);
  });

  it("counts every initial state after it fails to fingerprint one", () => {
    expect(
      replayInit(
        "x \\in [a : 0..1, b : BOOLEAN]",
        "3 \\notin (1 \\cup {1})",
        "the engine stopped: a set operation on a value that isn't a set: evaluating the failure again: an assignment from a set TLC streams",
      ),
    ).toEqual([
      "4 states generated, 1 distinct states found, 1 states left on queue.",
      ["Computed 2 initial states..."],
    ]);
  });
});

describe("the replay of an initial state that fails to join the behavior graph matches TLC", () => {
  // The replay skips the state that failed, which TLC has already added to its set of states, and
  // fails on the next one.
  const JOIN = [
    "Init == x \\in {0, 1}\nA == x' = Name[x + 3]\nSpec == Init /\\ [][A]_x\nP == [](ENABLED A => <>(x = 0))",
    "SPECIFICATION Spec\nPROPERTY P",
  ] as const;

  it("adds a new state to the graph", () => {
    const run = runOnEngine(getRunOptions(...JOIN));
    expect([getCallStack(run.output), getStatistics(run.output)[0]]).toEqual([
      ["8.9-8.20", "11.9-11.17", "11.17-11.17", "9.6-9.21", "9.11-9.21"],
      "2 states generated, 2 distinct states found, 2 states left on queue.",
    ]);
  });

  it("adds a new state to the graph in TLC 1.7.4", async () => {
    const result = await checkSpec(...JOIN, "1.7.4");
    expect([
      formatCallStack(result.failure?.callStack),
      result.generatedStates,
      result.distinctStates,
      result.queuedStates,
    ]).toEqual([["8.9-8.20", "11.9-11.17", "11.17-11.17", "9.6-9.21", "9.11-9.21"], 2, 2, 2]);
  });
});

// testdata/decide.txt: decideIsabelle's verdict and statistics on the fixture theories and the
// unit test's variants, under a step limit and no deadline, for the Rust port's differential test.
// Where JavaScript's stack overflows (Paxos-109 under its natural steps), the steps vary from run
// to run, and the Rust test only checks that the port gives up.
import { decideIsabelle } from "../../src/prover/isabelle/decide";
import { createSteps, type Statistics } from "../../src/prover/verdict";
import { joinLines, readFixture } from "./terms";

const HEADER = [
  "# decideIsabelle on the fixture theories and the variants isabelle.test.ts decides, recorded with",
  "# timeLimitMs Infinity and steps createSteps(limit): case, step limit, verdict, stop (- for none),",
  "# steps. Each case runs under its natural steps, then under half of them.",
];

const FIXTURES = [
  "AllocatorImplementation_proof-127",
  "AllocatorImplementation_proof-33",
  "AtomicBakeryWithoutSMT-465",
  "AtomicBakeryWithoutSMT-6",
  "FiniteSetTheorems_proofs-453",
  "Level_test-1",
  "NaturalsInduction_proofs-1",
  "Paxos-109",
  "Sets-183",
  "TLAPS-2",
  "constantfcn_test-1",
  "function_except_tuple_soundness_gh201_test-1",
];

const getCases = (): [string, string][] => {
  const falseGoal = readFixture("function_except_tuple_soundness_gh201_test-1").replace(
    /^assumes .*\n/m,
    "",
  );
  return [
    ...FIXTURES.map((name): [string, string] => [`thy:${name}`, readFixture(name)]),
    [
      "and:constantfcn_test-1",
      readFixture("constantfcn_test-1").replace(/^shows ".*?"/m, 'shows "\\<and"'),
    ],
    ...[
      "AllocatorImplementation_proof-33",
      "AllocatorImplementation_proof-127",
      "FiniteSetTheorems_proofs-453",
      "Sets-183",
    ].map((name): [string, string] => [
      `noassms:${name}`,
      readFixture(name).replace("using assms by", "by"),
    ]),
    ...["auto", "blast", "iprover", "force", "clarsimp auto?"].map((method): [string, string] => [
      `false:${method}`,
      falseGoal.replace("using assms by auto", `by ${method}`),
    ]),
  ];
};

const run = (text: string, limit: number) => {
  const statistics: Statistics = {};
  const start = performance.now();
  const verdict = (() => {
    try {
      return decideIsabelle(text, {
        timeLimitMs: Infinity,
        steps: createSteps(limit),
        statistics,
      });
    } catch (error) {
      return `throw ${error}`;
    }
  })();
  return { verdict, statistics, ms: performance.now() - start };
};

const show = (name: string, limit: number, result: ReturnType<typeof run>) =>
  [name, limit, result.verdict, result.statistics.stop ?? "-", result.statistics.steps].join("\t");

export const getDecideExpectations = () => {
  const lines = [...HEADER];
  for (const [name, text] of getCases()) {
    const natural = run(text, Infinity);
    const steps = Number(natural.statistics.steps);
    console.error(
      `${name}: natural ${natural.verdict} ${natural.statistics.stop ?? "-"} ${steps} in ${natural.ms.toFixed(0)} ms`,
    );
    const limited = run(text, steps);
    console.error(`  limited ${show(name, steps, limited)} in ${limited.ms.toFixed(0)} ms`);
    lines.push(show(name, steps, limited));
    if (steps >= 2) {
      const half = Math.floor(steps / 2);
      const interrupted = run(text, half);
      console.error(`  half ${show(name, half, interrupted)} in ${interrupted.ms.toFixed(0)} ms`);
      lines.push(show(name, half, interrupted));
    }
  }
  return { "decide.txt": joinLines(lines) };
};

// Writes the table that prove-smt's `decide` is compared with (design/prover.md, 2.3): decideSmt's
// verdict and statistics on every script of tests/fixtures/smt, with no deadline and a fixed step
// limit, as the decider differential compares the two ports in miniature. prove-smt's
// tests/smt.rs replays it:
//   bun scripts/smt-decide-reference.ts
//
// Each line is `<fixture> ts=<verdict> <statistics> inert=<verdict> <statistics>`, the statistics
// as name=value in the order decideSmt writes them, or `error=<name>: <message>` where it throws.
// `ts` is decideSmt itself. The Rust port's arithmetic theory is still a stub, which makes none of
// the numerals, nodes and variables that TheoryLra's init makes, takes none of the steps of its
// methods and draws no random values. So `inert` is decideSmt with the theory made as inert: init
// is skipped, and each outermost call of a theory method gives back the steps it took and the
// random seed of its context. The Rust port answers `ts`'s verdict and `inert`'s statistics on every
// script it does not decline; once theory_lra lands it must answer `ts`, and `inert` goes.
import { readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import { Context } from "../src/prover/smt/solver/context";
import { decideSmt } from "../src/prover/smt/solver/solver";
import { TheoryLra } from "../src/prover/smt/solver/theory-lra";
import { createSteps, type Statistics } from "../src/prover/verdict";

const STEP_LIMIT = 5_000_000;

const THEORY_METHODS = [
  "canPropagate",
  "propagate",
  "pushScopeEh",
  "popScopeEh",
  "finalCheckEh",
  "restartEh",
  "initSearchEh",
  "initModel",
  "mkValue",
];

const inert = { isOn: false, depth: 0 };

for (const name of THEORY_METHODS) {
  const original: unknown = Reflect.get(TheoryLra.prototype, name);
  if (typeof original !== "function") continue;
  Reflect.set(TheoryLra.prototype, name, function (this: object, ...args: unknown[]) {
    const context: unknown = Reflect.get(this, "context");
    if (!inert.isOn || inert.depth > 0 || !(context instanceof Context))
      return Reflect.apply(original, this, args);
    const limit = context.manager.limit;
    const steps: unknown = Reflect.get(limit, "steps");
    const count = limit.count;
    const seed: unknown = Reflect.get(context, "randomSeed");
    inert.depth++;
    const result: unknown = Reflect.apply(original, this, args);
    inert.depth--;
    if (typeof steps === "object" && steps !== null) Reflect.set(steps, "count", count);
    Reflect.set(context, "randomSeed", seed);
    return result;
  });
}
const init: unknown = Reflect.get(TheoryLra.prototype, "init");
Reflect.set(TheoryLra.prototype, "init", function (this: object) {
  return inert.isOn || typeof init !== "function" ? undefined : Reflect.apply(init, this, []);
});

const getDecision = (text: string) => {
  const statistics: Statistics = {};
  try {
    const verdict = decideSmt(text, {
      timeLimitMs: Number.POSITIVE_INFINITY,
      steps: createSteps(STEP_LIMIT),
      statistics,
    });
    const entries = Object.entries(statistics).map((entry) => `${entry[0]}=${entry[1]}`);
    return [verdict, ...entries].join(" ");
  } catch (error) {
    return error instanceof Error ? `error=${error.name}: ${error.message}` : `error=${error}`;
  }
};

const directory = join(import.meta.dir, "../tests/fixtures/smt");
const lines = readdirSync(directory)
  .filter((name) => name.endsWith(".smt"))
  .toSorted()
  .map((name) => {
    const text = readFileSync(join(directory, name), "utf8");
    inert.isOn = false;
    const decision = getDecision(text);
    inert.isOn = true;
    const inertDecision = getDecision(text);
    return `${name} ts=${decision} inert=${inertDecision}`;
  });
writeFileSync(
  join(import.meta.dir, "../native/crates/prover/smt/tests/tables/decide.txt"),
  `${lines.join("\n")}\n`,
);

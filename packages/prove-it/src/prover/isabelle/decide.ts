// Decides a theory tlapm writes for Isabelle, as tlapm's Isabelle backend runs it: use_thy on the
// heap of Isabelle/TLA+ succeeds or fails.

import { isStackOverflow, TlaIsabelleError } from "../../errors";
import { createSteps, type DecideOptions, type Statistics, type Verdict } from "../verdict";
import { parseProofText, terminalProof } from "./isar/method";
import { getFacts, initGoal } from "./isar/proof";
import { readStatement } from "./isar/statement";
import { parseTheory } from "./isar/theory";
import type { Limits } from "./pure/interrupt";
import { protect } from "./pure/logic";
import { seqHead } from "./pure/seq";
import { aconv } from "./pure/term";
import { getProofContext } from "./tla/context";
import { loadLogic } from "./tla/logic";

const getVerdict = (
  text: string,
  limits: Limits,
  statistics: Statistics,
): Exclude<Verdict, "sat"> => {
  try {
    const theory = parseTheory(text);
    const logic = loadLogic();
    const statement = readStatement(logic, theory);
    const facts = theory.isUsingAssms ? getFacts(limits, statement) : [];
    const result = seqHead(
      terminalProof(
        getProofContext(logic, limits),
        parseProofText(theory.method),
        facts,
        initGoal(statement),
      ),
    );
    // Proof.conclude_goal: the theorem must be the statement, from its assumptions only.
    return result !== undefined &&
      result.tpairs.length === 0 &&
      aconv(result.prop, protect(statement.conclusion)) &&
      result.hyps.every((hyp) => statement.assumptions.some((assumption) => aconv(hyp, assumption)))
      ? "unsat"
      : "unknown";
  } catch (error) {
    // Poly/ML grows its stack instead, until Isabelle runs out of memory, which tlapm counts as a
    // failure.
    if (error instanceof TlaIsabelleError) statistics.stop = error.exception;
    if (isStackOverflow(error)) statistics.stop = "stack";
    if (statistics.stop === undefined) throw error;
    return "unknown";
  }
};

// The statistics are the steps, and what stopped a proof that gave up.
export const decideIsabelle = (text: string, options: DecideOptions): Exclude<Verdict, "sat"> => {
  const limits = {
    deadline: Date.now() + options.timeLimitMs,
    signal: options.signal,
    steps: options.steps ?? createSteps(),
  };
  const statistics = options.statistics ?? {};
  const verdict = getVerdict(text, limits, statistics);
  statistics.steps = limits.steps.count;
  return verdict;
};

// Ported from Z3 (src/smt/smt_solver.cpp, src/smt/smt_kernel.cpp, src/smt/smt_setup.cpp), MIT
// license, see z3-license.txt. Decides an SMT-LIB problem the way `z3 -smt2 AUTO_CONFIG=false
// smt.MBQI=true` does for tlapm's UFNIA obligations.
import { isStackOverflow, SmtCanceledError, SmtUnsupportedError } from "../../../errors";
import { createSteps, type DecideOptions, type Verdict } from "../../verdict";
import { AssertedFormulas } from "./asserted-formulas";
import { AstManager } from "./ast";
import { Context } from "./context";
import { L_FALSE, L_TRUE } from "./lbool";
import { recordLpTrace } from "./lp-trace";
import { applyUfniaTactic } from "./quant-tactics";
import { ResourceLimit } from "./rlimit";
import { parseSmtlib } from "./smtlib-parser";

interface SmtCheck {
  verdict: Verdict;
  numInstances: number;
}

// The verdict, and the number of quantifier instances the search made.
export const checkSmt = (
  text: string,
  options: DecideOptions,
  limit = new ResourceLimit(Date.now() + options.timeLimitMs, options.signal, options.steps),
): SmtCheck => {
  const manager = new AstManager(limit);
  // combined_solver gives each assertion to the incremental smt kernel as well, which rewrites it
  // when it is asserted and keeps it, though check-sat then runs the tactic on the assertions. The
  // kernel's model finder counts a step of the resource limit when it is made, and
  // solver::assert_expr counts one for each assertion.
  const incremental = new AssertedFormulas(manager);
  manager.limit.inc();
  const problem = parseSmtlib(text, manager, (assertion) => {
    manager.limit.inc();
    incremental.assertExpr(assertion);
  });
  if (!problem.hasCheckSat) return { verdict: "unknown", numInstances: 0 };
  const goal = applyUfniaTactic(manager, problem.assertions);
  // and_then runs smt_tactic only on a goal that the preprocessing left undecided.
  if (goal.isInconsistent || goal.forms.size === 0) {
    manager.limit.release();
    return { verdict: goal.isInconsistent ? "unsat" : "sat", numInstances: 0 };
  }
  // smt_tactic makes the context, which makes its asserted formulas first, and asserts the goal.
  // setup_context then makes the theories, before the formulas are reduced.
  const asserted = new AssertedFormulas(manager);
  const context = new Context(manager, { isMbqi: true, relevancyLevel: 2 });
  for (const assertion of goal.forms.items) asserted.assertExpr(assertion);
  context.setupContext();
  context.internalizeAssertions(asserted);
  const result = context.search();
  manager.limit.release();
  return {
    verdict: result === L_FALSE ? "unsat" : result === L_TRUE ? "sat" : "unknown",
    numInstances: context.qmanager.getNumInstances(),
  };
};

// Throws SmtParseError on malformed input. Input outside the subset the solver supports is unknown,
// and so is a search that runs past the time or step limit, that the signal aborts, or that
// exhausts the heap or the stack. The statistics are the steps of Z3's resource limit, the
// quantifier instances, and what stopped a search that gave up.
export const decideSmt = (text: string, options: DecideOptions): Verdict => {
  const limit = new ResourceLimit(
    Date.now() + options.timeLimitMs,
    options.signal,
    options.steps ?? createSteps(),
  );
  const statistics = options.statistics ?? {};
  const getVerdict = (): Verdict => {
    try {
      const check = checkSmt(text, options, limit);
      statistics.instances = check.numInstances;
      return check.verdict;
    } catch (error) {
      if (error instanceof SmtUnsupportedError) statistics.stop = "unsupported";
      if (isStackOverflow(error)) statistics.stop = "stack";
      if (!(error instanceof SmtCanceledError) && statistics.stop === undefined) throw error;
      return "unknown";
    }
  };
  const verdict = recordLpTrace(text, getVerdict);
  statistics.steps = limit.count;
  if (limit.stopReason !== undefined) statistics.stop = limit.stopReason;
  return verdict;
};

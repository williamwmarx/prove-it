// Ported from Z3 (src/util/rlimit.{h,cpp}, the checkpoints of src/math/polynomial and
// src/nlsat/nlsat_solver.cpp), MIT license, see z3-license.txt. m_limit: the resource limit that
// the nlsat solver shares with its polynomial, upolynomial and algebraic number managers. Every
// step counts against the resource limit and against the budget of the check, which Z3 sets with
// a scoped_rlimit on a child limit. A manager made without a solver has its own limit, which
// never stops.
import { SmtCanceledError } from "../../../../errors";
import type { ResourceLimit } from "../rlimit";

export class NlsatLimit {
  steps = 0;

  constructor(
    private limit: ResourceLimit | null = null,
    private budget = Infinity,
  ) {}

  // inc: counts a step and returns whether the work may go on.
  inc() {
    this.steps++;
    return !((this.limit !== null && !this.limit.inc()) || this.steps > this.budget);
  }

  // checkpoint: counts a step, and throws once the work is canceled.
  checkpoint() {
    if (!this.inc()) throw new SmtCanceledError();
  }

  // The end of nla's scoped_limits and scoped_rlimit around a check: the steps taken later count
  // against neither the budget nor the resource limit.
  detach() {
    this.limit = null;
    this.budget = Infinity;
  }
}

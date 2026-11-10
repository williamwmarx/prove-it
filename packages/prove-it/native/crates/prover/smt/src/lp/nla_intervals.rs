// Ported from Z3 (src/math/lp/nla_intervals.h, src/math/lp/nla_intervals.cpp), MIT license, see
// z3-license.txt. Evaluates a nex expression over the bounds of its variables. When the interval
// excludes zero, the expression cannot vanish, so the bounds behind the interval and the
// dependencies of the row conflict with the row's equation, and the conflict becomes a lemma.
//
// STUB(P3b-lp): ported next. nla_core calls nothing on it; horner and grobner call check_nex and
// set_var_interval, which its port adds.

#[derive(Default)]
pub struct Intervals {}

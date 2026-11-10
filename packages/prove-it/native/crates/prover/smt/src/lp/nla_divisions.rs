// Ported from Z3 (src/math/lp/nla_divisions.h, src/math/lp/nla_divisions.cpp), MIT license, see
// z3-license.txt. The lemmas of nla on div, mod and /: monotonicity in the dividend and the
// divisor, bounded divisions by numerals, and divisibility closures over a shared divisor. The
// check is skipped while nla uses nlsat's model.
//
// The registration of divisions and its undo are ported; the checks are STUB(P3b-lp): ported next.
// TS pushes `() => divisions.pop()` on the emonics trail; here `CoreUndo::PopIdivision`,
// `PopBoundedDivision` and `PopDivisibility`, which `Nla::pop` applies.
use crate::lp::lar_solver::NULL_LPVAR;
use crate::lp::nla_core::Nla;
use crate::lp::nla_emonics::CoreUndo;

// A division q = x / y with r its remainder, or a divisibility fact r = mod(x, y), q = div(x, y).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Division {
    pub quotient: usize,
    pub dividend: usize,
    pub divisor: usize,
    pub remainder: usize,
}

fn has_null_column(division: &Division) -> bool {
    division.quotient == NULL_LPVAR
        || division.dividend == NULL_LPVAR
        || division.divisor == NULL_LPVAR
        || division.remainder == NULL_LPVAR
}

#[derive(Default)]
pub struct Divisions {
    pub(crate) idivisions: Vec<Division>,
    pub(crate) bounded_divisions: Vec<Division>,
    // Divisibility facts, whose quotient is div(x, y) and remainder mod(x, y).
    pub(crate) divisibility: Vec<Division>,
}

impl Divisions {
    // The theory calls the three add functions: each is an entry point of nla, so it drains the
    // changed bounds first (see nla_core.rs).
    pub fn add_idivision(nla: &mut Nla<'_, '_>, division: Division) {
        nla.drain_changed_bounds();
        if has_null_column(&division) {
            return;
        }
        nla.divisions.idivisions.push(division);
        nla.emons.push_core_undo(CoreUndo::PopIdivision);
    }

    pub fn add_bounded_division(nla: &mut Nla<'_, '_>, division: Division) {
        nla.drain_changed_bounds();
        if has_null_column(&division) {
            return;
        }
        let lra = &nla.lra;
        if lra.has_term(division.dividend) || lra.has_term(division.divisor) {
            return;
        }
        if lra.has_term(division.quotient) {
            return;
        }
        nla.divisions.bounded_divisions.push(division);
        nla.emons.push_core_undo(CoreUndo::PopBoundedDivision);
    }

    pub fn add_divisibility(nla: &mut Nla<'_, '_>, division: Division) {
        nla.drain_changed_bounds();
        if has_null_column(&division) {
            return;
        }
        nla.divisions.divisibility.push(division);
        nla.emons.push_core_undo(CoreUndo::PopDivisibility);
    }

    // STUB(P3b-lp): ported next. Generates no lemma.
    pub fn check(_nla: &mut Nla<'_, '_>) {}

    // p <= q * div(r, q) + q - 1 => div(p, q) <= div(r, q), and p >= q * div(r, q) =>
    // div(r, q) <= div(p, q), for a bounded p, a value q and r = eval(p).
    // STUB(P3b-lp): ported next. Generates no lemma.
    pub fn check_bounded_divisions(_nla: &mut Nla<'_, '_>) {}
}

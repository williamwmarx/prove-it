//! The LP call trace's encoding of lp's values, as `src/prover/smt/solver/lp-trace.ts`
//! serializes them (its header specifies the format), shared by the replayer.

use prove_num::Rational;

use crate::lp::bound_propagator::ImpliedBound;
use crate::lp::dependency::{Dependency, linearize};
use crate::lp::explanation::Explanation;
use crate::lp::int_solver::LiaMove;
use crate::lp::json::Json;
use crate::lp::lar_solver::BoundInfo;
use crate::lp::lar_term::LarTerm;
use crate::lp::nla_core::{NlaEquality, NlaFixedEquality};
use crate::lp::nla_types::{Ineq, Lemma};
use crate::lp::numeric_pair::Impq;
use crate::nlsat::algebraic::{Anum, AnumValue};
use crate::nlsat::mpbq::Mpbq;
use crate::util::error::SmtError;
use crate::util::lbool::LBool;

// The trace's encoding of lp's values (lp-trace.ts's serialize).

/// An index or a count; `usize::MAX` (`NULL_LPVAR` and the other `-1` sentinels) is -1.
pub fn get_number(value: usize) -> Json {
    Json::Number(if value == usize::MAX {
        -1.0
    } else {
        value as f64
    })
}

pub fn get_rational(value: &Rational) -> Json {
    Json::String(value.to_string())
}

pub fn get_impq(value: &Impq) -> Json {
    Json::Array(vec![get_rational(&value.x), get_rational(&value.y)])
}

/// A dependency's leaves in the order of `linearize`, `null` for none.
pub fn get_dependency(dep: &Dependency) -> Json {
    match dep {
        None => Json::Null,
        Some(_) => Json::object([(
            "dep",
            Json::Array(
                linearize(std::slice::from_ref(dep))
                    .into_iter()
                    .map(|leaf| Json::Number(f64::from(leaf)))
                    .collect(),
            ),
        )]),
    }
}

pub fn get_explanation(explanation: &Explanation) -> Json {
    let expl = (
        "expl",
        Json::Array(explanation.iter().map(get_number).collect()),
    );
    if explanation.pairs().is_empty() {
        return Json::object([expl]);
    }
    Json::object([
        expl,
        (
            "pairs",
            Json::Array(
                explanation
                    .pairs()
                    .iter()
                    .map(|pair| Json::Array(vec![get_number(pair.0), get_rational(&pair.1)]))
                    .collect(),
            ),
        ),
    ])
}

pub fn get_term(term: &LarTerm) -> Json {
    Json::object([
        ("col", get_number(term.column)),
        (
            "coeffs",
            Json::Array(
                term.iter()
                    .map(|entry| Json::Array(vec![get_number(entry.0), get_rational(entry.1)]))
                    .collect(),
            ),
        ),
    ])
}

/// What `LarSolver.getBound` returns when the column has the bound.
pub fn get_bound_info(bound: &BoundInfo) -> Json {
    Json::object([
        ("dep", get_dependency(&bound.dep)),
        ("value", get_rational(&bound.value)),
        ("isStrict", Json::Bool(bound.is_strict)),
    ])
}

/// An ImpliedBound of BoundPropagator's ibounds, as the iteration of them reads it.
pub fn get_implied_bound(bound: &ImpliedBound) -> Json {
    Json::object([
        ("column", get_number(bound.column)),
        ("bound", get_rational(&bound.bound)),
        ("isLower", Json::Bool(bound.is_lower)),
        ("isStrict", Json::Bool(bound.is_strict)),
        ("explain", Json::object([("fn", Json::Bool(true))])),
    ])
}

/// What `ImpliedBound.explain` returns.
pub fn get_bound_explanation(explanation: &[(Rational, Dependency)]) -> Json {
    Json::Array(
        explanation
            .iter()
            .map(|entry| Json::Array(vec![get_rational(&entry.0), get_dependency(&entry.1)]))
            .collect(),
    )
}

/// A LiaMove as TypeScript's `{ kind, ... }`.
pub fn get_lia_move(lia_move: &LiaMove) -> Json {
    let kind = |name: &str| ("kind", Json::String(name.into()));
    match lia_move {
        LiaMove::Sat => Json::object([kind("sat")]),
        LiaMove::Undef => Json::object([kind("undef")]),
        LiaMove::Conflict => Json::object([kind("conflict")]),
        LiaMove::Continue => Json::object([kind("continue")]),
        LiaMove::Cut { offset, is_upper } => Json::object([
            kind("cut"),
            ("offset", get_rational(offset)),
            ("isUpper", Json::Bool(*is_upper)),
        ]),
        LiaMove::Branch { is_upper, offset } => Json::object([
            kind("branch"),
            ("isUpper", Json::Bool(*is_upper)),
            ("offset", get_rational(offset)),
        ]),
    }
}

/// An lbool as TypeScript's number: 1, -1 or 0.
pub fn get_lbool(value: LBool) -> Json {
    Json::Number(f64::from(value.to_i8()))
}

pub fn get_ineq(ineq: &Ineq) -> Json {
    Json::object([
        ("cmp", Json::Number(f64::from(ineq.cmp))),
        ("term", get_term(&ineq.term)),
        ("rs", get_rational(&ineq.rs)),
    ])
}

pub fn get_lemma(lemma: &Lemma) -> Json {
    Json::object([
        (
            "ineqs",
            Json::Array(lemma.ineqs.iter().map(get_ineq).collect()),
        ),
        ("expl", get_explanation(&lemma.expl)),
    ])
}

pub fn get_equality(equality: &NlaEquality) -> Json {
    Json::object([
        ("first", get_number(equality.first)),
        ("second", get_number(equality.second)),
        ("explanation", get_explanation(&equality.explanation)),
    ])
}

pub fn get_fixed_equality(equality: &NlaFixedEquality) -> Json {
    Json::object([
        ("lpVar", get_number(equality.lp_var)),
        ("value", get_rational(&equality.value)),
        ("explanation", get_explanation(&equality.explanation)),
    ])
}

fn get_mpbq(value: &Mpbq) -> Json {
    Json::object([
        ("num", Json::String(value.num.to_string())),
        ("k", Json::Number(f64::from(value.k))),
    ])
}

/// An algebraic number as `{"anum": value}`, a cell with the fields of TypeScript's AlgebraicCell.
pub fn get_anum(anum: &Anum) -> Json {
    let value = match &*anum.value() {
        AnumValue::Rational(value) => get_rational(value),
        AnumValue::Cell(cell) => Json::object([
            (
                "p",
                Json::Array(
                    cell.p
                        .iter()
                        .map(|coeff| Json::String(coeff.to_string()))
                        .collect(),
                ),
            ),
            ("lower", get_mpbq(&cell.lower)),
            ("upper", get_mpbq(&cell.upper)),
            ("isMinimal", Json::Bool(cell.is_minimal)),
            ("isSignLowerNeg", Json::Bool(cell.is_sign_lower_neg)),
            ("isNotRational", Json::Bool(cell.is_not_rational)),
            ("rootIndex", Json::Number(f64::from(cell.root_index))),
        ]),
    };
    Json::object([("anum", value)])
}

/// A function the theory passes to lp, or stores in an lp field, by its callback name.
pub fn get_callback(name: &str) -> Json {
    Json::object([("cb", Json::String(name.into()))])
}

/// An lp object the theory passes, by its id.
pub fn get_reference(id: &str) -> Json {
    Json::object([("ref", Json::String(id.into()))])
}

/// The `Name: message` of the TypeScript error an SmtError stands for.
pub fn get_error(error: &SmtError) -> String {
    let name = match error {
        SmtError::Canceled => "SmtCanceledError",
        SmtError::Unsupported(_) => "SmtUnsupportedError",
        SmtError::Invariant(_) => "SmtInvariantError",
        SmtError::Parse(_) => "SmtParseError",
        SmtError::NlsatUnsupported(_) => "NlsatUnsupportedError",
        SmtError::PddMemoryOut => "PddMemoryOutError",
    };
    format!("{name}: {error}")
}

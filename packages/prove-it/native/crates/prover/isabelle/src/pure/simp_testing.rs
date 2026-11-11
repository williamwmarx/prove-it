//! Helpers for the simplifier's and the provers' tests: the statements of the fixtures as goals.

use crate::isar::statement::read_statement;
use crate::isar::theory::parse_theory;
use crate::tla::logic::load_logic;

use super::logic::list_implies;
use super::term::Term;

macro_rules! fixtures {
    ($($name:literal),* $(,)?) => {
        [$((
            $name,
            include_str!(concat!("../../../../../../tests/fixtures/isabelle/", $name, ".thy")),
        )),*]
    };
}

/// The statement of a fixture as a goal: its assumptions imply its conclusion.
pub(crate) fn fixture_goal(name: &str) -> Term {
    let (_, text) = fixtures!(
        "AllocatorImplementation_proof-127",
        "AllocatorImplementation_proof-33",
        "AtomicBakeryWithoutSMT-465",
        "AtomicBakeryWithoutSMT-6",
        "FiniteSetTheorems_proofs-453",
        "NaturalsInduction_proofs-1",
        "Paxos-109",
        "Sets-183",
        "TLAPS-2",
        "constantfcn_test-1",
        "function_except_tuple_soundness_gh201_test-1",
    )
    .into_iter()
    .find(|(known, _)| *known == name)
    .unwrap_or_else(|| panic!("no fixture {name}"));
    let statement = read_statement(&load_logic(), &parse_theory(text).unwrap()).unwrap();
    list_implies(&statement.assumptions, statement.conclusion)
}

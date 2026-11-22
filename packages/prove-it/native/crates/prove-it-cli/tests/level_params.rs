//! TLC's verdict where SANY's level of a formula differs from TLC's level bound of it: an operator
//! application takes the levels of the arguments its body reads, and a LET its body's level, where
//! the bound counts every argument and every definition. `processConfigProps` sorts a property by
//! the bound, and the liveness checker and `_POSSIBLE` take SANY's level.
//! Full outputs were recorded with TLC d8fb231 and JDK 21.0.13+9.

mod common;

#[test]
fn levels_a_property_as_sany_and_tlc_do() {
    common::check_recorded(
        "level-params",
        21,
        &[
            "-fp",
            "0",
            "-seed",
            "4",
            "-lncheck",
            "final",
            "-noGenerateSpecTE",
        ],
    );
}

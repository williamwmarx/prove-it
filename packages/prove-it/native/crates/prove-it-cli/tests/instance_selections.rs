//! A subexpression selected through an INSTANCE whose substitution is a LAMBDA: SANY selects in
//! the body as written and wraps the part in the instance's SubstInNode, so `I!Val!1!1` of
//! `Val == {F(C)}` under `F <- LAMBDA y : y + 1` is `C` substituted, not the application, and a
//! failure in it is reported through the INSTANCE's frame.
//! Full outputs were recorded with TLC d8fb231 and JDK 21.0.13+9.

mod common;

#[test]
fn selects_through_a_lambda_substitution_as_sany_does() {
    common::check_recorded(
        "instance-selections",
        6,
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

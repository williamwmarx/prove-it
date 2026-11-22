//! SANY's semantic checks where its code decides otherwise than its messages suggest: where
//! `Generator.processExcept` places the tuple of an EXCEPT component's several indexes, and the
//! exception it ends with past the last component; a recursive section of an inner module, which
//! `ModuleNode.levelCheck` checks again with the applications' levels of the second pass; a
//! theorem with a labeled goal, whose LabelNode keeps the level field TheoremNode.levelCheck reads
//! at constant; and a DEF entry with arguments after an identifier prefix, which `genIdToSelector`
//! ends on with an internal error and its Java stack trace, which the binary declines.
//! Full outputs were recorded with TLC d8fb231 and JDK 21.0.13+9.

mod common;

#[test]
fn checks_a_module_as_sany_does() {
    common::check_recorded(
        "sany-checks",
        10,
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

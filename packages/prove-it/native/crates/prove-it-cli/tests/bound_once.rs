//! A LET definition or an operator's argument its body reads more than once: TLC binds it to a
//! `LazyValue`, computed where the body first reads it and never where it doesn't, and the engine
//! binds it once and keys what reads it by its value. A definition that fails only where a
//! guard lets the body read it, one read through another operator's argument, an argument read
//! for each element of a filter, a definition whose value keys an EXCEPT, and one whose
//! evaluation recurses and is read inside a recursion.
//! Full outputs were recorded with TLC d8fb231 and JDK 21.0.13+9.

mod common;

#[test]
fn reads_a_name_bound_once_where_tlc_computes_it() {
    common::check_recorded(
        "bound-once",
        5,
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

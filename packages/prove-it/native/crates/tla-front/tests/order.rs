//! TLC's orders on a small spec. `scripts/front-differential.ts order` holds the Rust orders to the
//! TypeScript ones on every corpus model.

use tla_front::TlcVersion;
use tla_front::order::TlcOrder;

#[test]
fn leaves_out_what_a_theorem_assume_declares() {
    let source = "---- MODULE Main ----\nCONSTANT N\nField == [NEW |-> 1].NEW\nVARIABLE x\nText == \"NEW\"\nVARIABLE w\nTHEOREM Thm == ASSUME NEW VARIABLE y, CONSTANT c, NEW d PROVE y = y\n====";
    let order = TlcOrder::new(source, &|_| None, TlcVersion::Master).expect("an order");
    let names = |is_variable| -> Vec<String> {
        order
            .get_declaration_order(is_variable)
            .expect("a declaration order")
            .iter()
            .map(|name| name.to_string())
            .collect()
    };
    assert_eq!(names(true), ["w", "x"]);
    assert_eq!(names(false), ["N"]);
}

// A file that instantiates its inner module of the file's name: SANY scopes the inner module's
// context, which the front end keys by name, so it declines rather than read the file's context
// while it builds it.
#[test]
fn declines_a_file_that_instantiates_its_inner_module_of_its_name() {
    let module = |name: &str| {
        (name == "B").then(|| {
            "---- MODULE B ----\n---- MODULE B ----\nQ == 2\n====\nI == INSTANCE B\nR == I!Q\n===="
                .to_owned()
        })
    };
    let order = TlcOrder::new(
        "---- MODULE Main ----\nEXTENDS B\nVARIABLE x\n====",
        &module,
        TlcVersion::Master,
    )
    .expect("an order");
    assert!(matches!(
        order.get_declaration_order(true),
        Err(tla_front::errors::FrontError::NotYet(_))
    ));
}

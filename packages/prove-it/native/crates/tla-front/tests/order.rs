//! TLC's orders on a small spec. `scripts/front-differential.ts order` holds the Rust orders to the
//! TypeScript ones on every corpus model.

use tla_front::TlcVersion;
use tla_front::order::TlcOrder;

#[test]
fn leaves_out_what_a_theorem_assume_declares() {
    let source = "---- MODULE Main ----\nCONSTANT N\nVARIABLE x\nTHEOREM Thm == ASSUME NEW VARIABLE y, CONSTANT c, NEW d PROVE y = y\n====";
    let order = TlcOrder::new(source, &|_| None, TlcVersion::Master).expect("an order");
    let names = |is_variable| -> Vec<String> {
        order
            .get_declaration_order(is_variable)
            .expect("a declaration order")
            .iter()
            .map(|name| name.to_string())
            .collect()
    };
    assert_eq!(names(true), ["x"]);
    assert_eq!(names(false), ["N"]);
}

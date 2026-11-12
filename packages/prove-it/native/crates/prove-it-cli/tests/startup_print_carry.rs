//! Which operands of an expression a startup definition prints may carry a set TLC fails to print
//! into the printed value (`Compiler::carried_children`): each row prints an expression holding
//! `Int \X {}` at one operand, which TLC fails to size where it prints it, and says whether the
//! value printed may hold it, where the native checker declines the definition, or not, where TLC
//! prints the value as the engine does.

use std::process::Command;

const UNSIZED: &str = "(Int \\X {})";
const DECLINED: &str = "a set TLC may fail to print, at startup";

// The expression, with `@` for the unsized set, and whether the printed value may hold it.
const ROWS: &[(&str, bool)] = &[
    // A boolean, a number or a string holds no set.
    ("Cardinality(@)", false),
    ("@ = {}", false),
    ("@ # {}", false),
    ("<<1>> \\in @", false),
    ("<<1>> \\notin @", false),
    ("@ \\subseteq {}", false),
    ("Len(<<@>>)", false),
    ("Cardinality(@) + 1", false),
    ("\\A x \\in {@} : TRUE", false),
    ("\\E x \\in {@} : TRUE", false),
    ("@ = {} /\\ TRUE", false),
    ("PrintT(@) \\/ TRUE", false),
    // The branches of IF and CASE, not their conditions.
    ("IF @ = {} THEN 1 ELSE 2", false),
    ("IF TRUE THEN <<@>> ELSE <<>>", true),
    ("CASE @ = {} -> 1 [] OTHER -> 2", false),
    ("CASE TRUE -> <<@>> [] OTHER -> <<>>", true),
    // DOMAIN holds a constructor's domain, not its range.
    ("DOMAIN [a |-> @]", false),
    ("DOMAIN <<@>>", false),
    ("DOMAIN [x \\in {1} |-> @]", false),
    ("DOMAIN [x \\in {@} |-> 1]", true),
    ("DOMAIN (@ :> 1)", true),
    ("DOMAIN (1 :> @)", false),
    // A field selection holds that field of a record written there.
    ("[a |-> @, b |-> 1].b", false),
    ("[a |-> @, b |-> 1].a", true),
    // An application holds the function's range, not the argument.
    ("[x \\in {@} |-> 1][@]", false),
    ("<<@, 1>>[2]", false),
    ("<<@, 1>>[1 + 1]", true),
    // Constructors, CHOOSE, filters, maps, LET and the sequence and set operators carry it.
    ("<<@>>", true),
    ("{@}", true),
    ("[a |-> @]", true),
    ("[x \\in {1} |-> @]", true),
    ("CHOOSE x \\in {@} : TRUE", true),
    ("{x \\in {@} : TRUE}", true),
    ("{<<x>> : x \\in {@}}", true),
    ("LET P == @ IN <<P>>", true),
    ("LET P == @ IN Cardinality({P})", false),
    ("LET P == (LET P == @ IN <<P>>) IN <<P>>", true),
    ("LET P == (LET Q == @ IN Cardinality({Q})) IN <<P>>", false),
    // A part that is a domain written there is sized.
    ("<<{1} \\X (DOMAIN [a |-> 0])>>", false),
    ("<<{1} \\X (DOMAIN <<1, 2>>)>>", false),
    ("<<{1} \\X (DOMAIN [x \\in {1, 2} |-> x])>>", false),
    ("<<{1} \\X (DOMAIN [x \\in Int |-> x])>>", true),
    ("LET P == {@} IN <<P>>[1]", true),
    ("LET F(Q) == <<Q>> IN F(@)", true),
    ("<<@, 1>>[1]", true),
    ("<<1, @>>[1]", false),
    ("Append(<<>>, @)", true),
    ("<<@>> \\o <<>>", true),
    ("Head(<<@>>)", true),
    ("UNION {{@}}", true),
    ("{@} \\cup {}", true),
];

#[test]
fn counts_a_set_only_where_the_printed_value_may_hold_it() {
    let directory =
        std::env::temp_dir().join(format!("prove-it-startup-carry-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let mut wrong = Vec::new();
    for &(expression, is_carried) in ROWS {
        let expression = expression.replace("@", UNSIZED);
        std::fs::write(
            directory.join("M.tla"),
            format!(
                "---- MODULE M ----\nEXTENDS Integers, Sequences, FiniteSets, TLC\nTest == PrintT({expression})\nASSUME Test\n====\n"
            ),
        )
        .expect("the spec");
        std::fs::write(directory.join("M.cfg"), "").expect("the configuration");
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args(["-workers", "1", "-fp", "0", "-noGenerateSpecTE", "M"])
            .current_dir(&directory)
            .output()
            .expect("the binary runs");
        let is_declined = String::from_utf8_lossy(&output.stderr).contains(DECLINED);
        if is_declined != is_carried {
            wrong.push(format!("{expression}: declined {is_declined}"));
        }
    }
    std::fs::remove_dir_all(&directory).expect("removed");
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

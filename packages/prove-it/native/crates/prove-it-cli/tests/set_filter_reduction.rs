mod common;

use common::{run_spec_with, stderr, stdout};

#[test]
fn reduces_intersections_and_differences_using_the_lazy_operands_membership() {
    let filter = "{v \\in SUBSET {1} : FALSE}";
    let cases = [
        (format!("{filter} \\cap {{1}}"), "{}", false),
        (format!("{{1}} \\cap {filter}"), "{}", false),
        (format!("{{1}} \\ {filter}"), "{}", false),
        (format!("{filter} \\cap {{}}"), "{}", true),
        (format!("{{}} \\cap {filter}"), "{}", true),
        (format!("{{}} \\ {filter}"), "{}", true),
        (format!("{filter} \\ {{1}}"), "{}", true),
        (format!("{filter} \\cap {{{{1}}}}"), "{}", true),
        (format!("{{{{1}}}} \\ {filter}"), "{{1}}", true),
    ];
    for workers in ["1", "4"] {
        for (index, (expression, expected, succeeds)) in cases.iter().enumerate() {
            let source = format!(
                "---- MODULE Stop ----\nEXTENDS Integers\nVARIABLE x\nInit == x = 0\nNext == UNCHANGED x\nASSUME ({expression}) = {expected}\n====\n"
            );
            let (output, directory) = run_spec_with(
                &format!("filter-reduction-{workers}-{index}"),
                &source,
                "INIT Init\nNEXT Next\n",
                &["-workers", workers],
            );
            let text = stdout(&output);
            assert_eq!(
                output.status.code(),
                Some(if *succeeds { 0 } else { 10 }),
                "{text}"
            );
            assert!(stderr(&output).is_empty(), "{}", stderr(&output));
            if !succeeds {
                assert!(text.contains("Attempted to check if the non-enumerable value\n1\nis element of\n{{}, {1}}"), "{text}");
            }
            std::fs::remove_dir_all(directory).expect("removed");
        }
    }
}

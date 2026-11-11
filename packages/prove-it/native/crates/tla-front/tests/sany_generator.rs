//! SANY's semantic graph, as XMLExporter prints it.

use tla_front::sany::generator::{GenerationOptions, generate_sany_specification};
use tla_front::sany::nodes::NodeKind;

// SANY's corpus AssumeProveTest, as XMLExporter prints it: the OpDeclNode of a NEW operator
// begins at its declaration's first token, the `_` of an infix or postfix operator.
#[test]
fn locates_a_new_operator_at_its_declaration() {
    let specification = generate_sany_specification(
        "---- MODULE Main ----\nTHEOREM T == ASSUME NEW STATE _+_, NEW TEMPORAL _^+, ACTION -._, NEW f(_, _) PROVE TRUE\n====\n",
        &|_| None,
        &GenerationOptions::default(),
    )
    .expect("a graph");
    let columns: Vec<(String, u32, u32)> = specification
        .graph
        .nodes
        .iter()
        .filter_map(|node| match &node.kind {
            NodeKind::OpDecl(declaration) if declaration.location.begin_line == 2 => Some((
                declaration.name.to_string(),
                declaration.location.begin_column,
                declaration.location.end_column,
            )),
            _ => None,
        })
        .collect();
    assert_eq!(
        columns,
        [
            ("+".to_owned(), 31, 33),
            ("^+".to_owned(), 49, 51),
            ("-.".to_owned(), 61, 63),
            ("f".to_owned(), 70, 76),
        ]
    );
}

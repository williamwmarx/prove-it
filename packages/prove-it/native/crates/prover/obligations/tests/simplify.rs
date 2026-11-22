//! Proof.Simplify's steps as tlapm's obligations show them.

use prove_obligations::index::{ObligationSource, get_obligations};

fn get_locations(name: &str, source: &str) -> Vec<(usize, String, String)> {
    get_obligations(
        &[ObligationSource {
            file: format!("{name}.tla"),
            source: source.to_owned(),
        }],
        &mut |_| None,
        None,
        &mut |_| {},
    )
    .expect("the module has obligations")
    .into_iter()
    .flat_map(|result| result.obligations)
    .map(|obligation| (obligation.id, obligation.location, obligation.text))
    .collect()
}

// A TAKE over a domain other than the goal's adds the goal's domain's inclusion in it as a fact
// (`simplify_step`'s `Take`), at the bound's name as tlapm's hint locates it, which the fact's
// support obligation reports.
#[test]
fn locates_a_take_domain_inclusion_at_the_bound_name() {
    let source = "---- MODULE Take ----\nCONSTANT P(_), S, T\nTHEOREM \\A x \\in S : P(x)\n<1> TAKE y \\in T\n<1> QED\n  OBVIOUS\n====\n";
    let locations = get_locations("Take", source);
    let inclusion = locations
        .iter()
        .find(|(_, _, text)| text.ends_with("PROVE  S \\subseteq T\n"))
        .expect("the inclusion's obligation");
    assert_eq!((inclusion.0, inclusion.1.as_str()), (4, "4:10:4:11"));
    assert_eq!(
        locations
            .iter()
            .map(|(_, location, _)| location.as_str())
            .collect::<Vec<_>>(),
        ["6:3:6:10", "4:1:4:17", "4:1:4:17", "4:10:4:11"]
    );
}

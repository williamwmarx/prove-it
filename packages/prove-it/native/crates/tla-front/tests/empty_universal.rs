use tla_front::errors::{FrontError, TAUTOLOGY};
use tla_front::model::{LoweredModel, ModelOptions, lower_front};

const SOURCE: &str = "---- MODULE EmptyUniversal ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x=0
Next == x'=x
Spec == Init /\\ [][Next]_x
SpecWarn == Init /\\ [][Next]_<<>>
Constant == TRUE
State == x=0
Empty == \\A n \\in {} : <>(x=n)
EmptyState == \\A n \\in {} : x=n
EmptyTuple == \\A <<n,m>> \\in {} : <>(x=n+m)
ConstantEmpty == \\A n \\in {} : TRUE
Nonempty == \\A n \\in {0} : <>(x=n)
BadLater == \\A n \\in {}, m \\in (1 \\div 0) : <>(x=n+m)
DeadEffect == \\A n \\in {} : IF PrintT(\"body\") THEN <>(x=n) ELSE <>(x=n)
%s
====
";

fn lower(
    label: &str,
    config: &str,
    warnings: bool,
    extra: &str,
) -> Result<LoweredModel, FrontError> {
    let directory = std::env::temp_dir().join(format!(
        "tla-front-empty-universal-{label}-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    let path = directory.join("EmptyUniversal.tla");
    std::fs::write(&path, SOURCE.replace("%s", extra)).expect("a source");
    let options = ModelOptions {
        libraries: &[],
        version: None,
        is_warning_enabled: warnings,
        is_spec_described: false,
        random_seed: 4,
        root_extendees: &[],
    };
    let result = lower_front(&path, config, &options);
    std::fs::remove_dir_all(directory).expect("removed");
    result
}

#[test]
fn rejects_empty_universal_properties_before_evaluating_their_bodies() {
    for property in ["Empty", "EmptyTuple", "DeadEffect"] {
        let error = lower(
            property,
            &format!("SPECIFICATION Spec\nPROPERTY {property}\n"),
            true,
            "",
        )
        .err()
        .expect("TLC rejects an empty universal property");
        assert_eq!(error, FrontError::Evaluation(TAUTOLOGY.to_owned()));
        let coded = error.get_coded(false).expect("a coded error");
        assert_eq!((coded.code, coded.exit_code), (2253, 77));
    }
}

#[test]
fn preserves_warning_order_before_an_empty_universal_property() {
    let error = lower(
        "warnings",
        "SPECIFICATION SpecWarn\nINVARIANT Constant\nPROPERTIES State EmptyState\n",
        true,
        "",
    )
    .err()
    .expect("TLC rejects the property");
    let FrontError::Warned(warnings, error) = error else {
        panic!("warnings before the error")
    };
    assert_eq!(
        warnings
            .iter()
            .map(|warning| warning.code)
            .collect::<Vec<_>>(),
        [2149, 2140, 2255, 2255]
    );
    assert_eq!(*error, FrontError::Evaluation(TAUTOLOGY.to_owned()));
    let error = lower(
        "nowarning",
        "SPECIFICATION SpecWarn\nINVARIANT Constant\nPROPERTIES State EmptyState\n",
        false,
        "",
    )
    .err()
    .expect("TLC rejects the property");
    assert_eq!(error, FrontError::Evaluation(TAUTOLOGY.to_owned()));
}

#[test]
fn evaluates_every_bound_before_testing_whether_the_contexts_are_empty() {
    let error = lower(
        "bad-later",
        "SPECIFICATION Spec\nPROPERTY BadLater\n",
        true,
        "",
    )
    .err()
    .expect("the later bound fails");
    assert_eq!(error.get_coded(false).expect("a coded error").code, 1000);
}

#[test]
fn keeps_nonempty_and_constant_true_properties() {
    for property in ["Nonempty", "ConstantEmpty"] {
        assert!(
            lower(
                property,
                &format!("SPECIFICATION Spec\nPROPERTY {property}\n"),
                true,
                ""
            )
            .is_ok()
        );
    }
}

#[test]
fn retains_the_existing_boundary_for_constant_definition_prints() {
    let error = lower(
        "startup-print",
        "SPECIFICATION Spec\nPROPERTY Empty\n",
        true,
        "Unused == PrintT(\"startup\")",
    )
    .err()
    .expect("the startup print needs replay");
    assert_eq!(
        error,
        FrontError::NotYet("what the spec prints as TLC computes its constants".to_owned())
    );
}

#[test]
fn certifies_empty_comprehensions_without_evaluating_unreachable_effects() {
    for (label, domain) in [
        ("empty-filter", "{m \\in {} : PrintT(\"unreached\")}"),
        ("empty-map", "{Print(\"unreached\", m) : m \\in {}}"),
    ] {
        let error = lower(
            label,
            "SPECIFICATION Spec\nPROPERTY Comprehension\n",
            true,
            &format!("Comprehension == \\A n \\in {domain} : <>(x=n)"),
        )
        .err()
        .expect("TLC rejects an empty comprehension domain");
        assert_eq!(error, FrontError::Evaluation(TAUTOLOGY.to_owned()));
    }
}

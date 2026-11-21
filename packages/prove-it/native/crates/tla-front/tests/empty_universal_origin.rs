use tla_front::errors::{FrontError, TAUTOLOGY};
use tla_front::model::{
    ClassOrigin, JavaProfile, ModelOptions, ModelOrigin, ModelSources,
    lower_front_ranking_with_origin,
};

#[test]
fn certifies_empty_unrolling_only_in_a_closed_operator_context() {
    for label in ["", "L::", "L::K::"] {
        let source = format!(
            "---- MODULE M ----\nVARIABLE x\nMakeEmpty == {{}}\nSpec == x=0 /\\ [][x'=x]_x\nP == {label} \\A i \\in MakeEmpty : <>(x=i)\n====\n"
        );
        let sources = ModelSources {
            source: &source,
            load_module: &|_| None,
            load_class: &|_| None,
        };
        let options = ModelOptions {
            libraries: &[],
            version: None,
            is_warning_enabled: true,
            is_spec_described: false,
            random_seed: 4,
            root_extendees: &[],
        };
        for (profile, name, presence, certified) in [
            (JavaProfile::Default, "M", ClassOrigin::Absent, true),
            (JavaProfile::Default, "M", ClassOrigin::Present, false),
            (JavaProfile::Default, "M", ClassOrigin::Unknown, false),
            (JavaProfile::Opaque, "M", ClassOrigin::Absent, false),
            (
                JavaProfile::Default,
                "tlc2/overrides/TLCOverrides",
                ClassOrigin::Present,
                false,
            ),
        ] {
            let witness = |queried: &str| {
                if queried == name {
                    presence
                } else {
                    ClassOrigin::Absent
                }
            };
            let origin = ModelOrigin::new(profile, &witness);
            let result = lower_front_ranking_with_origin(
                &sources,
                "SPECIFICATION Spec\nPROPERTY P\n",
                &options,
                &|_, _, _| Vec::new(),
                Some(&origin),
            );
            let error = result
                .err()
                .expect("an empty property or an unproved context");
            let error = match error {
                FrontError::Warned(warnings, inner) if warnings.is_empty() => *inner,
                error => error,
            };
            if certified {
                assert_eq!(error, FrontError::Evaluation(TAUTOLOGY.to_owned()));
            } else {
                assert!(matches!(error, FrontError::NotYet(_)), "{error:?}");
            }
        }
    }
}

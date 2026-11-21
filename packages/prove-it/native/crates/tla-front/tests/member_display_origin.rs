use tla_front::TlcVersion;
use tla_front::model::{
    ClassOrigin, JavaProfile, ModelOptions, ModelOrigin, ModelSources, ParentRuntime,
    lower_front_ranking_with_origin,
};

#[test]
fn member_display_needs_the_complete_java_producer_context() {
    let source = "---- MODULE M ----\nEXTENDS N\nVARIABLE x\nF == 1\nInit == LET K == F IN K \\in SUBSET {1, \"a\"} /\\ x=0\nNext == UNCHANGED x\n====\n";
    let imported = "---- MODULE N ----\n====\n";
    let reads = tla_front::source_reads::ModuleSourceReads::default();
    let modules = |name: &str| {
        let text = (name == "N").then(|| imported.to_owned());
        reads.record(name, Ok(text.as_deref()));
        text
    };
    let sources = ModelSources {
        source,
        load_module: &modules,
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
    for (profile, name, presence, supplied, closed) in [
        (JavaProfile::Default, "N", ClassOrigin::Absent, true, true),
        (JavaProfile::Default, "N", ClassOrigin::Present, true, false),
        (JavaProfile::Default, "N", ClassOrigin::Unknown, true, false),
        (JavaProfile::Opaque, "N", ClassOrigin::Absent, true, false),
        (JavaProfile::Default, "N", ClassOrigin::Absent, false, false),
        (
            JavaProfile::Default,
            "tlc2/overrides/TLCOverrides",
            ClassOrigin::Present,
            true,
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
        for version in [TlcVersion::Master, TlcVersion::V1_7_4] {
            let options = ModelOptions {
                version: Some(version),
                ..options
            };
            for parent in [ParentRuntime::Unknown, ParentRuntime::ModeledTlcMasterJdk21] {
                let mut origin = ModelOrigin::new(profile, &witness);
                origin.parent_runtime = parent;
                origin.module_source_reads = Some(&reads);
                let lowered = lower_front_ranking_with_origin(
                    &sources,
                    "INIT Init\nNEXT Next\n",
                    &options,
                    &|_, _, _| Vec::new(),
                    supplied.then_some(&origin),
                )
                .unwrap();
                let ir = tla_ir::decode(&lowered.ir).unwrap();
                let member = ir
                    .builtins
                    .iter()
                    .find(|builtin| ir.texts[builtin.name as usize].as_ref() == "\\in")
                    .unwrap();
                assert_eq!(
                    member.flags & tla_ir::Builtin::CLOSED_JAVA_CONTEXT != 0,
                    closed
                        && parent == ParentRuntime::ModeledTlcMasterJdk21
                        && version == TlcVersion::Master
                );
                assert!(ir.builtins.iter().all(|builtin| {
                    builtin.flags & tla_ir::Builtin::CLOSED_JAVA_CONTEXT == 0
                        || matches!(ir.texts[builtin.name as usize].as_ref(), "\\in" | "\\notin")
                }));
            }
        }
    }
}

#[test]
fn member_display_keeps_uninventoried_instance_contexts_opaque() {
    let provider = "---- MODULE N ----\nK == 0\n====\n";
    let reads = tla_front::source_reads::ModuleSourceReads::default();
    let modules = |name: &str| {
        let text = (name == "N").then(|| provider.to_owned());
        reads.record(name, Ok(text.as_deref()));
        text
    };
    let absent = |_: &str| ClassOrigin::Absent;
    let mut origin = ModelOrigin::new(JavaProfile::Default, &absent);
    origin.parent_runtime = ParentRuntime::ModeledTlcMasterJdk21;
    origin.module_source_reads = Some(&reads);
    let options = ModelOptions {
        libraries: &[],
        version: None,
        is_warning_enabled: true,
        is_spec_described: false,
        random_seed: 4,
        root_extendees: &[],
    };
    for (extra, closed) in [
        ("THEOREM T == TRUE\nPROOF OBVIOUS\n", true),
        (
            "S == \"INSTANCE N\"\nTHEOREM T == TRUE\nPROOF OMITTED\n",
            true,
        ),
        (
            "THEOREM T == TRUE\n<1>1. INSTANCE N\n<1> QED OBVIOUS\n",
            false,
        ),
        (
            "THEOREM T == TRUE\n<1> DEFINE I == INSTANCE N\n<1> QED OBVIOUS\n",
            false,
        ),
        (
            "THEOREM T == TRUE\n<1>1. HAVE LET I == INSTANCE N IN TRUE\n<1> QED OBVIOUS\n",
            false,
        ),
        (
            "THEOREM T == TRUE\n<1>1. TRUE\n<2>1. INSTANCE N\n<2> QED OBVIOUS\n<1> QED OBVIOUS\n",
            false,
        ),
        (
            "THEOREM T == ASSUME NEW k \\in (LET I == INSTANCE N IN {1}) PROVE TRUE\nPROOF OMITTED\n",
            false,
        ),
        ("USE LET I == INSTANCE N IN TRUE\n", false),
    ] {
        let source = format!(
            "---- MODULE M ----\nVARIABLE x\n{extra}Init == 1 \\in SUBSET {{1, \"a\"}} /\\ x=0\nNext == UNCHANGED x\n====\n"
        );
        let sources = ModelSources {
            source: &source,
            load_module: &modules,
            load_class: &|_| None,
        };
        let lowered = lower_front_ranking_with_origin(
            &sources,
            "INIT Init\nNEXT Next\n",
            &options,
            &|_, _, _| Vec::new(),
            Some(&origin),
        )
        .unwrap_or_else(|error| panic!("{extra}: {error:?}"));
        let ir = tla_ir::decode(&lowered.ir).unwrap();
        assert_eq!(
            ir.builtins
                .iter()
                .any(|builtin| builtin.flags & tla_ir::Builtin::CLOSED_JAVA_CONTEXT != 0),
            closed,
            "{extra}"
        );
    }
}

#[test]
fn member_display_needs_actual_pinned_standard_source_reads() {
    use tla_front::report::{ReportOptions, get_sany_text_of};
    use tla_front::source_reads::ModuleSourceReads;

    for (custom, supplied, omit_dependency, expected) in [
        (false, true, false, true),
        (true, true, false, false),
        (false, false, false, false),
        (false, true, true, false),
    ] {
        let reads = ModuleSourceReads::default();
        let source =
            "---- MODULE M ----\nEXTENDS Integers,TLC\nASSUME 1 \\in SUBSET {1, \"a\"}\n====\n";
        let modules = |name: &str| {
            let text = (name == "TLC").then(|| {
                let pinned = tla_front::get_standard_module(name, TlcVersion::Master).unwrap();
                if custom {
                    let end = pinned.rfind("\n====").unwrap();
                    format!(
                        "{}\nFoo == PrintT(\"hidden-tlc\"){}",
                        &pinned[..end],
                        &pinned[end..]
                    )
                } else {
                    pinned.to_owned()
                }
            });
            if !(omit_dependency && name == "Naturals") {
                reads.record(name, Ok(text.as_deref()));
            }
            text
        };
        let report = get_sany_text_of(
            "M",
            source,
            &ReportOptions {
                version: TlcVersion::Master,
                file_name: None,
                load_module: &modules,
                describe_file: &|name, _| Ok(name.to_owned()),
                root_extendees: &[],
                is_xml_export: false,
                lint_codes: Default::default(),
            },
        )
        .unwrap();
        assert!(!report.is_failed);
        let sources = ModelSources {
            source,
            load_module: &modules,
            load_class: &|_| None,
        };
        let absent = |_: &str| ClassOrigin::Absent;
        let mut origin = ModelOrigin::new(JavaProfile::Default, &absent);
        origin.parent_runtime = ParentRuntime::ModeledTlcMasterJdk21;
        origin.module_source_reads = supplied.then_some(&reads);
        let options = ModelOptions {
            libraries: &[],
            version: Some(TlcVersion::Master),
            is_warning_enabled: false,
            is_spec_described: false,
            random_seed: 0,
            root_extendees: &[],
        };
        let lowered = lower_front_ranking_with_origin(
            &sources,
            "",
            &options,
            &|_, _, _| Vec::new(),
            Some(&origin),
        )
        .unwrap();
        let ir = tla_ir::decode(&lowered.ir).unwrap();
        assert_eq!(
            ir.builtins
                .iter()
                .any(|builtin| builtin.flags & tla_ir::Builtin::CLOSED_JAVA_CONTEXT != 0),
            expected,
            "custom={custom}, supplied={supplied}, omit_dependency={omit_dependency}"
        );
    }
}

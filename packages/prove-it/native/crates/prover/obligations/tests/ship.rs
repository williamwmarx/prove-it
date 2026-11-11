//! The encoding tests of `obligation-zenon.test.ts`, `obligation-isabelle.test.ts`, `ptl.test.ts`
//! and `prove.test.ts`, on the same fixtures: each text `encode_for_backend` gives must equal the
//! one tlapm wrote, less comments and line breaks.

use std::path::{Path, PathBuf};

use prove_obligations::errors::ObligationError;
use prove_obligations::index::{ObligationSource, PrintedObligation, get_obligations};
use prove_obligations::ship::encode_for_backend;
use prove_obligations::smt::rewrite::EncodingSession;
use prove_obligations::tlaps_module::TLAPS_MODULE;

fn get_fixtures(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../../tests/fixtures")
        .join(name)
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

fn get_module_obligations(
    name: &str,
    source: String,
    load_module: &mut dyn FnMut(&str) -> Option<ObligationSource>,
) -> Vec<PrintedObligation> {
    get_obligations(
        &[ObligationSource {
            file: format!("{name}.tla"),
            source,
        }],
        load_module,
        None,
        &mut |_| {},
    )
    .expect("the module has obligations")
    .into_iter()
    .flat_map(|result| result.obligations)
    .collect()
}

fn find_obligation(obligations: &[PrintedObligation], id: usize) -> &PrintedObligation {
    obligations
        .iter()
        .find(|obligation| obligation.id == id)
        .unwrap_or_else(|| panic!("no obligation {id}"))
}

fn encode(obligation: &PrintedObligation, prover: &str) -> Result<String, ObligationError> {
    encode_for_backend(obligation, prover, &mut EncodingSession::default())
}

fn collapse_whitespace(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

// Leaves out the lines that start with `;`: tlapm's comments.
fn remove_line_comments(text: &str) -> String {
    text.lines()
        .filter(|line| !line.starts_with(';'))
        .collect::<Vec<_>>()
        .join("\n")
}

// tlapm's theories differ from Prove It's only in comments, line breaks, and the theory's name,
// which tlapm takes from a temporary file.
fn normalize_theory(text: &str) -> String {
    let mut uncommented = String::new();
    let mut rest = text;
    while let Some(start) = rest.find("(*") {
        uncommented.push_str(&rest[..start]);
        match rest[start + 2..].find("*)") {
            Some(end) => rest = &rest[start + 2 + end + 2..],
            None => {
                rest = &rest[start..];
                break;
            }
        }
    }
    uncommented.push_str(rest);
    let is_word = |character: char| character.is_ascii_alphanumeric() || character == '_';
    let mut renamed = String::new();
    let mut rest = uncommented.as_str();
    while let Some(start) = rest.find("tlapm_") {
        let is_word_start = !renamed.chars().last().is_some_and(is_word)
            && !rest[..start].chars().last().is_some_and(is_word);
        let after = &rest[start + "tlapm_".len()..];
        let digits = after
            .find(|character: char| !matches!(character, '0'..='9' | 'a'..='f'))
            .unwrap_or(after.len());
        let is_word_end = !after[digits..].chars().next().is_some_and(is_word);
        renamed.push_str(&rest[..start]);
        if is_word_start && digits > 0 && is_word_end {
            renamed.push_str("tlapm");
            rest = &after[digits..];
        } else {
            renamed.push_str("tlapm_");
            rest = after;
        }
    }
    renamed.push_str(rest);
    collapse_whitespace(&renamed)
}

#[test]
fn zenon_obligations_match_tlapm() {
    let fixtures = get_fixtures("zenon-encoder");
    let obligations =
        get_module_obligations("Encoder", read(&fixtures.join("Encoder.tla")), &mut |_| {
            None
        });
    let mut count = 0;
    for obligation in &obligations {
        let path = fixtures.join(format!("Encoder-{}.znn", obligation.id));
        if !path.exists() {
            continue;
        }
        count += 1;
        let text = encode(obligation, "zenon").expect("the obligation encodes");
        assert_eq!(
            collapse_whitespace(&remove_line_comments(&text)),
            collapse_whitespace(&remove_line_comments(&read(&path))),
            "obligation {}",
            obligation.id
        );
    }
    assert_eq!(count, 11);
}

#[test]
fn zenon_rejects_a_function_with_several_bounds() {
    // tlapm leaves Zenon an empty file for it.
    let fixtures = get_fixtures("zenon-encoder");
    let obligations =
        get_module_obligations("Encoder", read(&fixtures.join("Encoder.tla")), &mut |_| {
            None
        });
    assert!(matches!(
        encode(&obligations[23], "zenon"),
        Err(ObligationError::Prover(_))
    ));
}

fn get_isabelle_obligations(name: &str) -> Vec<PrintedObligation> {
    let fixtures = get_fixtures("isabelle-encoder");
    let source = if name == "TLAPS" {
        TLAPS_MODULE.to_owned()
    } else {
        read(&fixtures.join(format!("{name}.tla")))
    };
    get_module_obligations(name, source, &mut |used| {
        (used == "TLAPS").then(|| ObligationSource {
            file: "TLAPS.tla".to_owned(),
            source: TLAPS_MODULE.to_owned(),
        })
    })
}

#[test]
fn isabelle_theories_match_tlapm() {
    let fixtures = get_fixtures("isabelle-encoder");
    let mut theories: Vec<(String, String, usize)> = std::fs::read_dir(&fixtures)
        .expect("the fixtures exist")
        .filter_map(|entry| {
            let file = entry.ok()?.file_name().into_string().ok()?;
            let (name, id) = file.strip_suffix(".thy")?.rsplit_once('-')?;
            Some((file.clone(), name.to_owned(), id.parse().ok()?))
        })
        .collect();
    theories.sort();
    assert_eq!(theories.len(), 6);
    for (file, name, id) in theories {
        let obligations = get_isabelle_obligations(&name);
        let text = encode(find_obligation(&obligations, id), "isabelle")
            .unwrap_or_else(|error| panic!("{file}: {error}"));
        assert_eq!(
            normalize_theory(&text),
            normalize_theory(&read(&fixtures.join(&file))),
            "{file}"
        );
    }
}

#[test]
fn isabelle_fails_a_goal_with_a_set_of_several_bounds() {
    // tlapm leaves Isabelle part of a theory for it.
    let obligations = get_isabelle_obligations("Level_test");
    assert!(matches!(
        encode(find_obligation(&obligations, 1), "isabelle"),
        Err(ObligationError::Prover(_))
    ));
}

// The LS4 input for the obligation whose last hypothesis cites PTL.
fn get_ptl_input(theorem: &[&str]) -> Result<String, ObligationError> {
    let source = [
        "---- MODULE M ----",
        "EXTENDS Naturals",
        "PTL == TRUE (*{ by (prover: \"ls4\") }*)",
        "ExpandENABLED == TRUE (*{ by (prover: \"expandenabled\") }*)",
        "VARIABLE x",
        "vars == <<x>>",
        "Init == x = 0",
        "Next == x' = x + 1",
        "Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)",
        "Inv == x \\in Nat",
    ]
    .into_iter()
    .chain(theorem.iter().copied())
    .chain(["===="])
    .collect::<Vec<_>>()
    .join("\n");
    let obligations = get_module_obligations("M", source, &mut |_| None);
    let cited = obligations
        .iter()
        .find(|obligation| obligation.text.contains("PTL \nPROVE"))
        .expect("an obligation cites PTL");
    encode(cited, "ls4")
}

#[test]
fn ptl_prints_the_ls4_input_tlapm_sends() {
    let input = get_ptl_input(&[
        "THEOREM Spec => []Inv",
        "<1>1. Init => Inv",
        "  BY DEF Init, Inv",
        "<1>2. Inv /\\ [Next]_vars => Inv'",
        "  BY DEF Inv, Next, vars",
        "<1>. QED  BY <1>1, <1>2, PTL DEF Spec",
    ]);
    assert_eq!(
        input.expect("the obligation encodes"),
        "not (((always (h8828a -> h2f89a)) & (always ((h2f89a & (hfc35e | h18388)) -> (next h2f89a))) & (always (cc | ~ cc)) -> (((h8828a & (always (hfc35e | h18388))) & ((sometime (always hc5714)) -> (always (sometime (hfc35e & (~ h18388)))))) -> (always h2f89a))))"
    );
}

#[test]
fn ptl_fails_a_step_whose_enabled_needs_a_hidden_definition() {
    // As tlapm's soundness check does.
    let input = get_ptl_input(&[
        "THEOREM ASSUME []ENABLED <<Next>>_vars PROVE Spec => []<><<Next>>_vars",
        "  BY ExpandENABLED, PTL DEF Spec",
    ]);
    assert!(matches!(input, Err(ObligationError::Prover(_))));
}

// The LS4 input of each theorem ptl.test.ts decides, as the TypeScript writes it.
#[test]
fn ptl_writes_the_inputs_the_typescript_decides() {
    let cases: [(&[&str], &str); 12] = [
        (
            &[
                "THEOREM Spec => []Inv",
                "<1>2. Inv /\\ [Next]_vars => Inv'",
                "  BY DEF Inv, Next, vars",
                "<1>. QED  BY <1>2, PTL DEF Spec",
            ],
            "not (((always ((h2f89a & (hfc35e | h18388)) -> (next h2f89a))) & (always (cc | ~ cc)) -> (((h8828a & (always (hfc35e | h18388))) & ((sometime (always hc5714)) -> (always (sometime (hfc35e & (~ h18388)))))) -> (always h2f89a))))",
        ),
        (
            &[
                "THEOREM Spec => (x = 0 ~> x = 2)",
                "<1>1. Spec => (x = 0 ~> x = 1)",
                "  OMITTED",
                "<1>2. Spec => (x = 1 ~> x = 2)",
                "  OMITTED",
                "<1>. QED  BY <1>1, <1>2, PTL",
            ],
            "not (((always (h94a4d -> (always (h4ca64 -> (sometime h7fe4a))))) & (always (h94a4d -> (always (h7fe4a -> (sometime hda924))))) & (always (cc | ~ cc)) -> (h94a4d -> (always (h4ca64 -> (sometime hda924))))))",
        ),
        (
            &[
                "THEOREM Spec => (x = 0 ~> x = 2)",
                "<1>1. Spec => (x = 0 ~> x = 1)",
                "  OMITTED",
                "<1>. QED  BY <1>1, PTL",
            ],
            "not (((always (h94a4d -> (always (h4ca64 -> (sometime h7fe4a))))) & (always (cc | ~ cc)) -> (h94a4d -> (always (h4ca64 -> (sometime hda924))))))",
        ),
        (
            &[
                "THEOREM ASSUME []ENABLED <<Next>>_vars PROVE Spec => []<><<Next>>_vars",
                "  BY PTL DEF Spec",
            ],
            "not (((always (always hc5714)) & (always (cc | ~ cc)) -> (((h8828a & (always (hfc35e | h18388))) & ((sometime (always hc5714)) -> (always (sometime (hfc35e & (~ h18388)))))) -> (always (sometime (hfc35e & (~ h18388)))))))",
        ),
        (
            &[
                "THEOREM ASSUME []<>ENABLED <<Next>>_vars PROVE Spec => []<><<Next>>_vars",
                "  BY PTL DEF Spec",
            ],
            "not (((always (always (sometime hc5714))) & (always (cc | ~ cc)) -> (((h8828a & (always (hfc35e | h18388))) & ((sometime (always hc5714)) -> (always (sometime (hfc35e & (~ h18388)))))) -> (always (sometime (hfc35e & (~ h18388)))))))",
        ),
        (
            &[
                "THEOREM ASSUME []<>ENABLED <<Next>>_vars PROVE SF_vars(Next) => []<><<Next>>_vars",
                "  BY PTL",
            ],
            "not (((always (always (sometime hc5714))) & (always (cc | ~ cc)) -> (((always (sometime hc5714)) -> (always (sometime (hfc35e & (~ h18388))))) -> (always (sometime (hfc35e & (~ h18388)))))))",
        ),
        (
            &["THEOREM ASSUME x = 1 PROVE x = 1", "  BY PTL"],
            "not ((h7fe4a & (always (cc | ~ cc)) -> h7fe4a))",
        ),
        (
            &["THEOREM ASSUME x = 1 PROVE 1 = x", "  BY PTL"],
            "not ((h7fe4a & (always (cc | ~ cc)) -> h344d6))",
        ),
        (
            &[
                "THEOREM ASSUME NEW CONSTANT c, c = 1 PROVE [](c = 1)",
                "  BY PTL",
            ],
            "not (((always h38dda) & (always (cc | ~ cc)) -> (always h38dda)))",
        ),
        (
            &["THEOREM ASSUME x = 1 PROVE [](x = 1)", "  BY PTL"],
            "not ((h7fe4a & (always (cc | ~ cc)) -> (always h7fe4a)))",
        ),
        (
            &[
                "THEOREM TRUE",
                "<1>. DEFINE P(T) == T # {}",
                "<1>1. ASSUME NEW T, P(T) PROVE T = T",
                "  <2>1. CASE T = {}",
                "    OMITTED",
                "  <2>2. CASE ~(T = {})",
                "    OMITTED",
                "  <2>. QED  BY <2>1, <2>2, PTL",
                "<1>. QED  OBVIOUS",
            ],
            "not (((hbe322 -> haf23d) & ((~ hbe322) -> haf23d) & (always (cc | ~ cc)) -> haf23d))",
        ),
        (
            &[
                "THEOREM ASSUME NEW T PROVE T = T",
                "<1>1. CASE T = {}",
                "  OMITTED",
                "<1>2. CASE ~(T = {})",
                "  OMITTED",
                "<1>. QED  BY <1>1, <1>2, PTL",
            ],
            "not (((always ((always hbe322) -> haf23d)) & (always ((always (~ hbe322)) -> haf23d)) & (always (cc | ~ cc)) -> haf23d))",
        ),
    ];
    for (theorem, expected) in cases {
        assert_eq!(
            get_ptl_input(theorem).expect("the obligation encodes"),
            expected,
            "{theorem:?}"
        );
    }
}

// tlapm's comments name its version and the obligation, so only the commands are compared.
fn encode_smt_fixture(name: &str, id: usize) -> String {
    let directory = get_fixtures("prove");
    let load = |module: &str| {
        let path = directory.join(format!("{module}.tla"));
        path.exists().then(|| read(&path))
    };
    let source = load(name).unwrap_or_default();
    let obligations = get_module_obligations(name, source, &mut |module| {
        load(module)
            .or_else(|| (module == "TLAPS").then(|| TLAPS_MODULE.to_owned()))
            .map(|source| ObligationSource {
                file: format!("{module}.tla"),
                source,
            })
    });
    let text = encode(find_obligation(&obligations, id), "smt").expect("the obligation encodes");
    collapse_whitespace(&remove_line_comments(&text))
}

#[test]
fn smt_encodes_an_action_with_an_if_and_a_primed_variable() {
    let expected = read(&get_fixtures("prove").join("HourClock_proof-6.smt"));
    assert_eq!(
        encode_smt_fixture("HourClock_proof", 6),
        collapse_whitespace(&remove_line_comments(&expected))
    );
}

#[test]
fn smt_flattens_functions_and_shares_the_ones_with_the_same_body() {
    let expected = read(&get_fixtures("prove").join("Simple_proof-7.smt"));
    assert_eq!(
        encode_smt_fixture("Simple_proof", 7),
        collapse_whitespace(&remove_line_comments(&expected))
    );
}

#[test]
fn an_unknown_prover_has_no_encoder() {
    let obligations = get_isabelle_obligations("Level_test");
    let error = encode(&obligations[0], "spass").expect_err("no spass backend");
    assert_eq!(error.name(), "TlaUnsupportedError");
    assert_eq!(error.message(), "the spass backend");
}

// tlapm's Prep.compute_meth fails a prover it does not know with "Unknown prover", whatever the
// name; the TypeScript looked names up in an object and took `constructor` for a prover.
#[test]
fn a_prover_named_like_an_object_property_is_unknown() {
    let source = [
        "---- MODULE M ----",
        "EXTENDS TLAPS",
        "CONSTANT c",
        "P1 == TRUE (*{ by (prover:\"constructor\") }*)",
        "THEOREM c = c BY P1",
        "====",
    ]
    .join("\n");
    let obligations = get_module_obligations("M", source, &mut |name| {
        (name == "TLAPS").then(|| ObligationSource {
            file: "TLAPS.tla".to_owned(),
            source: TLAPS_MODULE.to_owned(),
        })
    });
    let error = encode(&obligations[0], "smt").expect_err("an unknown prover");
    assert_eq!(error.name(), "TlaProverError");
    assert_eq!(error.message(), "Unknown prover: constructor");
}

// Operators named like an object's properties are ordinary operators, as in tlapm.
#[test]
fn an_operator_named_like_an_object_property_encodes() {
    for (name, smt_name) in [
        ("constructor", "constructor"),
        ("hasOwnProperty", "hasOwnProperty"),
        ("valueOf", "valueOf"),
        ("toString", "toString"),
        ("__proto__", "____proto____"),
    ] {
        let source =
            format!("---- MODULE M ----\nCONSTANT {name}\nTHEOREM {name} = {name} OBVIOUS\n====");
        let obligations = get_module_obligations("M", source, &mut |_| None);
        let text = encode(&obligations[0], "smt").unwrap_or_else(|error| panic!("{name}: {error}"));
        assert!(
            text.contains(&format!("(declare-fun smt__CONSTANT__{smt_name}__ () Idv)")),
            "{name}: {text}"
        );
    }
}

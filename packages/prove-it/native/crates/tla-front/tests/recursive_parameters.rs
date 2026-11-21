//! Recursive operator parameter forwarding, recorded from TLC at d8fb231.

use std::path::Path;

use tla_front::sany::generator::{GenerationOptions, generate_sany_specification};
use tla_front::sany::nodes::format_sany_location;

#[test]
fn recursive_parameter_diagnostics_match_the_pinned_jar() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/recursive-parameters");
    let mut paths: Vec<_> = std::fs::read_dir(&directory)
        .expect("the recorded cases")
        .map(|entry| entry.expect("a case").path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "tla"))
        .collect();
    paths.sort();
    assert_eq!(paths.len(), 24);
    for path in paths {
        let source = std::fs::read_to_string(&path).expect("a source");
        let specification = generate_sany_specification(
            &source,
            &|name| {
                tla_front::standard_modules::MASTER
                    .iter()
                    .find(|(module, _)| *module == name)
                    .map(|(_, source)| (*source).to_owned())
            },
            &GenerationOptions::default(),
        )
        .unwrap_or_else(|error| panic!("{}: {error:?}", path.display()));
        let actual = specification
            .messages
            .iter()
            .map(|message| {
                assert!(!message.is_warning, "{}: {message:?}", path.display());
                format!(
                    "{}\n{}",
                    format_sany_location(&message.location),
                    message.text
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        let expected =
            std::fs::read_to_string(path.with_extension("txt")).expect("the jar recording");
        assert_eq!(actual, expected, "{}", path.display());
    }
}

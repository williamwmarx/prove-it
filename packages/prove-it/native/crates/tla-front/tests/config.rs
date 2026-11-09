//! The configuration parser on cases TLC's `ModelConfig.parse` decides in its own way.
//! `scripts/front-differential.ts config` holds it to `src/config.ts` on every corpus `.cfg`.

use tla_front::TlcVersion;
use tla_front::config::{ConfigValue, parse_config};

fn error(source: &str, version: TlcVersion) -> String {
    parse_config(source, version).expect_err("an error").message
}

#[test]
fn reads_constants_substitutions_and_lists() {
    let config = parse_config(
        "CONSTANTS N = 3 P <- Q S = {a, \"b\", TRUE} F(1) = [M] x\nINIT Init NEXT Next\nINVARIANTS A B\nCHECK_DEADLOCK FALSE",
        TlcVersion::Master,
    )
    .expect("a config");
    assert_eq!(config.constants.len(), 3);
    assert_eq!(config.constants[0].value, ConfigValue::Number(3.0));
    assert_eq!(config.substitutions[0].target, "Q");
    assert_eq!(config.constants[2].module.as_deref(), Some("M"));
    assert_eq!(config.invariants, ["A", "B"]);
    assert!(!config.check_deadlock);
}

#[test]
fn reports_errors_as_tlc_does() {
    assert_eq!(
        error("INIT Init\nINIT Other", TlcVersion::Master),
        "TLC found an error in the configuration file at line 2\nThe keyword INIT appeared twice."
    );
    assert_eq!(
        error("ALIAS A", TlcVersion::V1_7_4),
        "TLC found an error in the configuration file at line 1\nIt was expecting a keyword, but did not find it."
    );
    assert_eq!(
        error("CONSTANT N = \"open", TlcVersion::Master),
        "TLC found an error in the configuration file:\nLexical error at line 2, column 0.  Encountered: <EOF> after : \"\\\"open\\n\""
    );
    assert_eq!(
        error("INIT\n  \u{1F600}", TlcVersion::Master),
        "TLC found an error in the configuration file:\nLexical error at line 2, column 3.  Encountered: \"\\ud83d\" (55357), after : \"\""
    );
}

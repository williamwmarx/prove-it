//! TLC's message codes for the front end's errors, as `src/tlc/messages.ts` finds them.

use tla_front::errors::FrontError;
use tla_front::tlc_messages::CodedError;

fn coded(error: FrontError, is_tool: bool) -> Option<CodedError> {
    error.get_coded(is_tool)
}

#[test]
fn codes_configuration_errors_by_their_text() {
    let error = FrontError::Config(
        "The constant parameter N is not assigned a value by the configuration file.".to_owned(),
    );
    let printed = coded(error, true).expect("a coded error");
    assert_eq!((printed.code, printed.exit_code), (2222, 151));
    let error = FrontError::Config("something TLC never says".to_owned());
    assert_eq!(coded(error, false).map(|coded| coded.code), Some(1000));
}

#[test]
fn nests_the_error_a_message_reports_under_tool() {
    let text = "The configuration file substitutes constant C with non-constant Foo - specifically: In evaluation, the identifier x is either undefined or not an operator.\nline 1";
    let error = FrontError::Config(text.to_owned());
    assert_eq!(
        coded(error.clone(), false)
            .map(|coded| coded.text)
            .as_deref(),
        Some(text)
    );
    assert_eq!(
        coded(error, true).map(|coded| coded.text).as_deref(),
        Some(
            "The configuration file substitutes constant C with non-constant Foo - specifically: @!@!@STARTMSG 2280:0 @!@!@\nIn evaluation, the identifier x is either undefined or not an operator.\nline 1\n@!@!@ENDMSG 2280 @!@!@"
        )
    );
}

#[test]
fn leaves_other_errors_uncoded() {
    let error = FrontError::NotYet("anything".to_owned());
    assert_eq!(coded(error, false), None);
    let error = FrontError::Evaluation("TLC can't handle real numbers: 1.5 at line 1".to_owned());
    assert_eq!(
        coded(error, false).map(|coded| (coded.code, coded.exit_code)),
        Some((1000, 75))
    );
}

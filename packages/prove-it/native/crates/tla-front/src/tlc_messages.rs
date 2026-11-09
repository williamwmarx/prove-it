//! TLC's message codes for the errors the front end raises, as `src/tlc/messages.ts` finds them
//! from a message's text, and how TLC prints such an error with its code.

use crate::errors::FrontError;

/// EXIT_STATUS in `src/exit-codes.ts`.
const SPEC_EVALUATION_FAILURE: i32 = 75;
const CONFIG_PARSE_ERROR: i32 = 151;
const GENERAL_ERROR: i32 = 255;

/// EC.SYSTEM_STACK_OVERFLOW, and STACK_OVERFLOW_MESSAGE in `src/errors.ts`.
const STACK_OVERFLOW: u32 = 1005;
pub const STACK_OVERFLOW_MESSAGE: &str = "This was a Java StackOverflowError. It was probably the result\nof an incorrect recursive function definition that caused TLC to enter\nan infinite loop when trying to compute the function or its application\nto an element in its putative domain.";

/// MESSAGE_CODE.general, the code of a message TLC builds from no template.
pub const GENERAL: u32 = 1000;

// The messages that TLC builds from a message code, from tlc2.output.MP, by their code and
// template, with whether TLC throws them as an EvalException rather than a TLCRuntimeException.
// Generated from CODED_MESSAGES in src/tlc/messages.ts.
#[rustfmt::skip]
const CODED_MESSAGES: &[(u32, &str, bool)] = &[
    (1005, "This was a Java StackOverflowError. It was probably the result\nof an incorrect recursive function definition that caused TLC to enter\nan infinite loop when trying to compute the function or its application\nto an element in its putative domain.", false),
    (2117, "Failed to recover the next state from its fingerprint.", true),
    (2123, "Failed to recover the initial state from its fingerprint.", true),
    (2132, "The first argument of Assert evaluated to FALSE; the second argument was:\n%1%", true),
    (2145, "TLCGet(%1%) was undefined.", true),
    (2154, "Attempted to apply the operator overridden by the Java method\n%1%,\nbut it produced the following error:\n%2%", false),
    (2148, "The action formula A appearing in a WF_v(A) or SF_v(A) operator does not specify the primed value of the variable %1% occurring in the state formula v.\n", false),
    (2155, "Attempted to compare %1% with the value\n%2%", true),
    (2158, "Attempted to check if the value:\n%1%\nis an element of %2%.", true),
    (2157, "Attempted to apply TransitiveClosure to a set containing\nthe following value:\n%1%", true),
    (2165, "Choose can only deal with numbers up to %1%", false),
    (2169, "The %1% argument of %2% should be a %3%, but instead it is:\n%4%", true),
    (2176, "Applying %1% to the following value,\nwhich is not %2%:\n%3%", true),
    (2177, "Attempted to apply BagUnion to the following set, whose\nelement is not a bag:\n%1%", true),
    (2178, "Overflow when computing %1%", false),
    (2179, "The second argument of \\div is 0.", true),
    (2180, "0^0 is undefined.", true),
    (2181, "Attempted to compute cardinality of the value\n%1%", true),
    (2182, "Evaluating an expression of the form %1% when s is not a %2%:\n%3%", true),
    (2183, "The %1% argument of %2% must be in the domain of its %3% argument:\n%4%\n, but instead it is\n%5%", true),
    (2184, "Attempted to apply %1% to the empty sequence.", true),
    (2115, "No next state actions defined to generate successor states from.", false),
    (2146, "The invariant %1% is not a state predicate (one with no primes or temporal operators).%2%", false),
    (2213, "TLC cannot handle the temporal formula %1%", false),
    (2214, "Temporal formulas containing actions must be of forms <>[]A or []<>A.", false),
    (2215, "TLC expected a %1% value, but did not find one. %2%", false),
    (2222, "The constant parameter %1% is not assigned a value by the configuration file.", false),
    (2223, "In the configuration file, the identifier %1% appears\non the right-hand side of a <- after already appearing on the\nleft-hand side of one.", false),
    (2224, "The configuration file substitutes for %1% with the undefined identifier %2%.", false),
    (2225, "The configuration file substitutes for %1% with %2% of different number of arguments.", false),
    (2226, "In the configuration file, the identifier %1% does not appear in the specification.", false),
    (2227, "The configuration file cannot specify both INIT/NEXT and SPECIFICATION fields.", false),
    (2228, "TLC requires %1% not to take any argument.", false),
    (2228, "TLC requires %1% not to take any argument, but one was given: %2%", false),
    (2229, "The %1% %2% specified in the configuration file\nis not defined in the specification.", false),
    (2230, "The %1% of %2% is equal to %3%", false),
    (2231, "The configuration file did not specify the initial state predicate.", false),
    (2231, "The configuration file did not specify the initial state predicate.\nCan also be caused by trying to run TLC on a specification from\na module imported with a parameterized INSTANCE statement.", false),
    (2232, "The configuration file did not specify the next state predicate.", false),
    (2233, "The %1% %2% cannot be a constant.", false),
    (2234, "The operator %1% cannot take any argument.", false),
    (2235, "The operator %1% is not defined in the spec.", false),
    (2237, "The spec is trivially false because %1% is false.", false),
    (2238, "TLC cannot handle subscript %1%", false),
    (2239, "TLC cannot handle this conjunct of the spec:\n%1%", false),
    (2241, "The property %1% is not correctly defined.", false),
    (2242, "The arity of the operator %1% is inconsistent in the configuration file.", false),
    (2244, "TLC can't handle real numbers.\n%1%", false),
    (2247, "In computing %1%, TLC expected a %2% expression,\nbut instead found %3%.\n%4%", false),
    (2248, "In computing %1%, TLC expected a %2% expression,\nbut didn't find one.\n%3%", false),
    (2260, "In computing ENABLED, TLC encountered a temporal formula (%1%).\n%2%", false),
    (2261, "TLC encountered a temporal formula (%1%) when evaluating a predicate or action.\n%2%", false),
    (2265, "TLC can't handle a number this big.\n%1%", false),
    (2266, "The %1% argument of %2% should be an %3%, but instead it is:\n%4%", true),
    (2280, "In evaluation, the identifier %1% is either undefined or not an operator.\n%2%", false),
    (2281, "The configuration file substitutes constant %1% with non-constant %2%%3%", false),
    (2283, "The argument of %1% should be a %2%, but instead it is:\n%3%", true),
    (5003, "TLC found an error in the configuration file at line %1%\nThe keyword %2% was not followed by an identifier.", false),
    (5004, "TLC found an error in the configuration file at line %1%\nThe keyword %2% appeared twice.", false),
    (5005, "TLC found an error in the configuration file at line %1%\nExpected an identifier after %2%.", false),
    (5006, "TLC found an error in the configuration file at line %1%\nIt was expecting %2%, but did not find it.", false),
    (5007, "TLC found an error in the configuration file:\n%1%", false),
    (5002, "TLC found an error in the configuration file at line %1%\n", false),
    (2253, "Temporal formula is a tautology (its negation is unsatisfiable).", false),
    (2301, "TLC does not support temporal existential, nor universal, quantification over state variables.", false),
];

/// The message of a code: the code, and whether TLC throws it as an EvalException.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CodedMessage {
    pub code: u32,
    pub is_eval_exception: bool,
}

/// Whether the text matches the template, whose `%n%` placeholders match any text.
fn matches_template(text: &str, template: &str) -> bool {
    let mut parts: Vec<String> = vec![String::new()];
    let mut rest = template;
    while let Some(start) = rest.find('%') {
        let after = &rest[start + 1..];
        let digits = after.chars().take_while(char::is_ascii_digit).count();
        let is_placeholder = digits > 0 && after[digits..].starts_with('%');
        let literal = &rest[..if is_placeholder { start } else { start + 1 }];
        if let Some(last) = parts.last_mut() {
            last.push_str(literal);
        }
        if is_placeholder {
            parts.push(String::new());
            rest = &after[digits + 1..];
        } else {
            rest = after;
        }
    }
    if let Some(last) = parts.last_mut() {
        last.push_str(rest);
    }
    matches_parts(text, &parts)
}

/// Whether the text is the parts with any text between each two.
fn matches_parts(text: &str, parts: &[String]) -> bool {
    let (Some(first), Some(last)) = (parts.first(), parts.last()) else {
        return text.is_empty();
    };
    if parts.len() == 1 {
        return text == first;
    }
    if !text.starts_with(first.as_str()) || text.len() < first.len() + last.len() {
        return false;
    }
    let end = text.len() - last.len();
    if !text.is_char_boundary(end) || !text[end..].starts_with(last.as_str()) {
        return false;
    }
    let mut at = first.len();
    for part in &parts[1..parts.len() - 1] {
        let Some(found) = text[at..end].find(part.as_str()) else {
            return false;
        };
        at += found + part.len();
    }
    true
}

/// The overflows of SetOfFcnsValue and SetOfTuplesValue, which TLC raises with a plain message
/// that reads like the coded overflow of SetOfRcdsValue and SubsetValue.
fn is_uncoded(text: &str) -> bool {
    let Some(rest) = text.strip_prefix("Overflow when computing the number of elements in") else {
        return false;
    };
    if rest.starts_with(' ') {
        return true;
    }
    let Some(record) = rest.strip_prefix(":\n[") else {
        return false;
    };
    let name = record
        .chars()
        .take_while(|char| char.is_ascii_alphanumeric() || *char == '_')
        .count();
    !(name > 0 && record[name..].starts_with(" : "))
}

/// getCodedMessage: the code of the first template the message's text matches.
pub fn get_coded_message(text: &str) -> Option<CodedMessage> {
    if is_uncoded(text) {
        return None;
    }
    CODED_MESSAGES
        .iter()
        .find(|(_, template, _)| matches_template(text, template))
        .map(|(code, _, is_eval_exception)| CodedMessage {
            code: *code,
            is_eval_exception: *is_eval_exception,
        })
}

/// The messages that end with the message of the error they report, after this text.
fn get_inner_message_prefix(code: u32) -> Option<&'static str> {
    match code {
        // "The exception was a <class>\n: "
        1000 => Some("\n: "),
        2105 => Some("failed.\n"),
        2154 => Some("but it produced the following error:\n"),
        2213 => Some(":\n"),
        2281 => Some(" - specifically: "),
        _ => None,
    }
}

/// formatInnerMessage: the text of a coded message with the message of the error it reports
/// marked in -tool output, as TLC's message holds that error's text as TLC printed it.
pub fn format_inner_message(code: u32, text: &str, is_tool: bool) -> String {
    let prefix = if is_tool {
        get_inner_message_prefix(code)
    } else {
        None
    };
    let Some(index) = prefix.and_then(|prefix| text.find(prefix).map(|index| index + prefix.len()))
    else {
        return text.to_owned();
    };
    format!(
        "{}{}",
        &text[..index],
        format_nested_message(&text[index..], is_tool)
    )
}

/// formatNestedMessage: the text of an error's message as TLC prints it inside another message.
pub fn format_nested_message(text: &str, is_tool: bool) -> String {
    let code = if is_tool {
        get_coded_message(text).map(|coded| coded.code)
    } else {
        None
    };
    match code {
        None => text.to_owned(),
        Some(code) => format!(
            "@!@!@STARTMSG {code}:0 @!@!@\n{}\n@!@!@ENDMSG {code} @!@!@",
            format_inner_message(code, text, is_tool)
        ),
    }
}

/// An error TLC prints with its message code, at level error, and the exit code it ends with.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CodedError {
    pub code: u32,
    pub text: String,
    pub exit_code: i32,
}

impl FrontError {
    /// What `printError` in `src/cli/shared.ts` prints for a configuration or evaluation error:
    /// its message's code, unless TLC throws it as an EvalException, and the message with the
    /// error it reports nested in -tool output, and getErrorExitCode's exit code. None for the
    /// errors TLC doesn't print with a code.
    pub fn get_coded(&self, is_tool: bool) -> Option<CodedError> {
        let (message, exit_code) = match self {
            FrontError::Config(message) => (message, CONFIG_PARSE_ERROR),
            FrontError::Evaluation(message) => (message, SPEC_EVALUATION_FAILURE),
            // TLC reports a stack overflow outside the computation of states on its own.
            FrontError::StackOverflow => {
                return Some(CodedError {
                    code: STACK_OVERFLOW,
                    text: STACK_OVERFLOW_MESSAGE.to_owned(),
                    exit_code: GENERAL_ERROR,
                });
            }
            _ => return None,
        };
        let code = get_coded_message(message)
            .filter(|coded| !coded.is_eval_exception)
            .map_or(GENERAL, |coded| coded.code);
        Some(CodedError {
            code,
            text: format_inner_message(code, message, is_tool),
            exit_code,
        })
    }
}

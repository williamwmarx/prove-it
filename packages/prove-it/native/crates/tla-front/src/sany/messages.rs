//! SANY's semantic messages as its generator and levelCheck report them, for the specs whose
//! messages `environment::get_sany_messages` doesn't derive from linking yet: the port of the
//! TypeScript report's `onModule` over `generator.rs` and `levels.rs`, which print what SANY's
//! `Generator` and `LevelNode.levelCheck` do.

use std::cell::RefCell;

use crate::ast::Name;
use crate::environment::ModuleMessages;
use crate::errors::FrontError;
use crate::errors::SanyError;
use crate::sany::generator::{GenerationOptions, generate_sany_specification};
use crate::sany::levels::{LevelCheck, check_module_levels};
use crate::sany::linter::lint_sany_module;
use crate::sany::nodes::{Graph, NodeId, SanyMessage, format_sany_location};
use crate::sany::{GENERATOR_EXCEPTION, Result, UNLINKABLE, UNLINTED_MODULES, not_yet};

/// The warnings of SANY's linter for the modules it lints, in order, where SANY lints them: SANY
/// lints only a spec without errors.
pub type Lints = Option<Vec<SanyError>>;

/// What SANY's generator reports: each module's messages, or the index in the order of the
/// module `Generator` throws on as it generates it.
pub enum Generated {
    Messages(Vec<ModuleMessages>, Lints),
    /// Messages one of which has a shape no recording shows: the first line of that one.
    Unproven(Vec<ModuleMessages>, Lints, String),
    /// A shape whose messages linking would give otherwise than SANY, and why.
    Declined(String),
    Exception(usize),
}

/// The shapes of the first lines of the messages SANY prints in `tests/conformance/sany-stdout`'s
/// recordings of the real SANY (`grid.json`, `corpus.json`, `report-cases.json` and
/// `sany-cases.json`; `get_message_shape`). A message of the generator whose shape isn't one of
/// these is unproven: only what a recording shows SANY printing is printed. The test below derives
/// the list from the recordings.
const PROVEN_MESSAGES: &[&str] = &[
    "!: should not follow an operand selector.",
    "<*> and <+> cannot be used for a named step.",
    "<> followed by action not of form <<X>>_v.",
    "=> has both temporal formula and action as arguments.",
    "@ used where its meaning is not defined.",
    "X ' already defined or declared.",
    "X ' is a built-in operator, and cannot be redefined.",
    "X 'X' is defined with N parameters, but is applied to N arguments.",
    "X 'X' is not a legal target of a substitution. ",
    "X + already defined or declared.",
    "X -. already defined or declared.",
    "X /= already defined or declared.",
    "X /= is a built-in operator, and cannot be redefined.",
    "X <> already defined or declared.",
    "X <> is a built-in operator, and cannot be redefined.",
    "X N arguments but found N.",
    "X N of recursive operator X is primed",
    "X N of recursive operator foo is primed",
    "X N of recursive operator op is primed",
    "X N of recursive operator r is primed",
    "X N of recursive operator zz is primed",
    "X N operator (not an expression) is expected ",
    "X X",
    "X X  may not appear within a recursive definition section.",
    "X X algorithm in module X has changed since its last translation.",
    "X X already defined or declared.",
    "X X declaration may not appear within a recursive definition section.",
    "X X declared in X statement but not defined.",
    "X X has operator arguments in its X declaration.",
    "X X in a X statement.",
    "X X is a built-in operator, and cannot be redefined.",
    "X X may not appear within a recursive definition section.",
    "X X or X may not appear within a recursive definition section.",
    "X X or X statement.",
    "X X+ translation in module X has changed since its last translation.",
    "X X, X, or X",
    "X X/X clause within the scope of a declaration",
    "X X/X expression has only one operand.",
    "X X/X instead of expression.",
    "X [] already defined or declared.",
    "X [] is a built-in operator, and cannot be redefined.",
    "X `X' should not have argument(s).",
    "X `X' used with wrong number of arguments.",
    "X `X' used without being extended or instantiated.",
    "X a X declaration as an expression or operator.",
    "X arity N but found operator of arity N.",
    "X c declared in X statement but not defined.",
    "X clause entry should describe a defined operator.",
    "X dd already defined or declared.",
    "X declaration may not appear within a recursive definition section.",
    "X declaration of 'X' conflicts with ",
    "X declarations or definitions for symbol +.  ",
    "X declarations or definitions for symbol <N>N.  ",
    "X declarations or definitions for symbol <N>a.  ",
    "X declarations or definitions for symbol <N>abc.  ",
    "X declarations or definitions for symbol X.  ",
    "X declarations or definitions for symbol dd.  ",
    "X declarations or definitions for symbol ee.  ",
    "X declarations or definitions for symbol foo.  ",
    "X declarations or definitions for symbol k.  ",
    "X declarations or definitions for symbol op.  ",
    "X declarations or definitions for symbol p.  ",
    "X declarations or definitions for symbol pc.  ",
    "X declarations or definitions for symbol qq.  ",
    "X declarations or definitions for symbol recDef.  ",
    "X declarations or definitions for symbol vars.  ",
    "X declarations or definitions for symbol x.  ",
    "X dependency among .tla files; dependency cycle is:",
    "X ee already defined or declared.",
    "X error in applying operator $X:",
    "X error in applying operator ':",
    "X error in applying operator =:",
    "X error in applying operator X:",
    "X error in applying operator apply:",
    "X error in applying operator op:",
    "X error in applying operator r:",
    "X error in applying operator zz:",
    "X error in instantiating module 'X':",
    "X error when instantiating module 'X':",
    "X error, probably due to error ",
    "X error:",
    "X error: assumptions must be level N (X), ",
    "X expecting a X.",
    "X expression appears as argument number N (counting from N) to operator 'X', in a position an operator is required.",
    "X expression type `X'.",
    "X expression used where an expression is required.",
    "X expression with arity N used as argument N of operator `X', ",
    "X field name \"X\" in the record constructor is identical to the existing definition or declaration",
    "X field name \"a\" in the record constructor is identical to the existing definition or declaration",
    "X field name \"d\" in the record constructor is identical to the existing definition or declaration",
    "X field name \"e\" in the record constructor is identical to the existing definition or declaration",
    "X find label `X'.",
    "X find source file for module X imported in module X.",
    "X find source file for module X imported in module tcp.",
    "X foo already defined or declared.",
    "X foo declared in X statement but not defined.",
    "X formal parameter x ",
    "X function X defined at wrong X/X level.",
    "X function recDef defined at wrong X/X level.",
    "X has both temporal formula and action as arguments.",
    "X in instantiating module 'X':",
    "X inside X clauses are not yet implemented.",
    "X lab must contain formal parameter `X'.",
    "X label `X'.",
    "X lb declares extra parameter(s)  q  ",
    "X lbl declares extra parameter(s)  x  ",
    "X lbl must contain formal parameter `X'.",
    "X list has both temporal formula and action as arguments.",
    "X missing for symbol X declared at line N, col N to line N, col N of module X ",
    "X missing for symbol c declared at line N, col N to line N, col N of module X ",
    "X missing for symbol q declared at line N, col N to line N, col N of module X ",
    "X missing for symbol v declared at line N, col N to line N, col N of module X ",
    "X missing for symbol w declared at line N, col N to line N, col N of module X ",
    "X missing for symbol y declared at line N, col N to line N, col N of module X ",
    "X name 'X' does not match the name 'X' of the top level module it contains.",
    "X name X is incomplete.",
    "X name `X' already defined or declared.",
    "X name import is incomplete.",
    "X name or step number here, not `X'.",
    "X non-existent subexpression of a X",
    "X not allowed within scope of declaration in nested X/X.",
    "X not find declaration or definition of symbol 'X'.",
    "X not in definition or proof step.",
    "X not parse module X from file X.tla",
    "X number N to operator 'X' ",
    "X number of arguments (N) given to operator 'X', ",
    "X of X has different arity than its X declaration.",
    "X of X must have form !i!j.",
    "X of b has different arity than its X declaration.",
    "X of foo has different arity than its X declaration.",
    "X of op has different arity than its X declaration.",
    "X of qq has different arity than its X declaration.",
    "X only expression allowed as a fact in a X is ",
    "X op already defined or declared.",
    "X op declared in X statement but not defined.",
    "X operand `X' of subexpression with no operands.",
    "X operand specified by `X'.",
    "X operator <N>N requires N arguments.",
    "X operator <N>abc requires N arguments.",
    "X operator X defined at wrong X/X level.",
    "X operator X requires N arguments.",
    "X operator X!+ requires N arguments.",
    "X operator X!X requires N arguments.",
    "X operator foo defined at wrong X/X level.",
    "X operator import requires N arguments.",
    "X operator must be substituted for symbol 'X', and it must have arity N.",
    "X operator op requires N arguments.",
    "X operator recDef defined at wrong X/X level.",
    "X operator: `X'.",
    "X parameter q of label `X'.",
    "X parameter x of label `X'.",
    "X proof step selected instead of expression.",
    "X qq declared in X statement but not defined.",
    "X r declared in X statement but not defined.",
    "X recDef declared in X statement but not defined.",
    "X s declared in X statement but not defined.",
    "X selection failed, probably due to an error in the selected expression.",
    "X selector for X subexpression must specify  one of two operands.",
    "X stack trace follows:",
    "X subexpression of an X not yet implemented.",
    "X subexpression of expression that has none.",
    "X substitutions for symbol 'X' in substitution.",
    "X t declared in X statement but not defined.",
    "X take subexpression of `X'.",
    "X the X algorithm and its X+ translation in module X have changed since the last translation.",
    "X to declare 'X' as a variable.",
    "X token found.",
    "X u declared in X statement but not defined.",
    "X unexpected null node specified by 'X'.",
    "X unexpected problem was encountered attempting to validate the specification for X",
    "X use !X to select subexpression of a X.",
    "X used where only temporal formula or state predicate allowed.",
    "X v declared in X statement but not defined.",
    "X vars already defined or declared.",
    "X w declared in X statement but not defined.",
    "X with N argument(s) used for quantifier with N bound identifier(s).",
    "X with N arguments used for X expression taking N arguments.",
    "X with incorrect arity passed as argument. ",
    "X't resolve infix operator symbol `X'.",
    "X-constant X for temporal goal.",
    "X-constant X, X, or X for temporal goal.",
    "X-constant bound of temporal X.",
    "X-defined module 'X': this definition or declaration conflicts ",
    "X-defined symbol 'X': this definition or declaration conflicts ",
    "X-level bound of quantified temporal formula.",
    "X-unique fields in constructor.",
    "X/X used where an expression is required.",
    "X: the declaration of 'X' conflicts with ",
    "X: the definition of 'X' conflicts with ",
    "[] followed by action not of form [X]_v.",
    "[]X matched by X instead of []X",
    "[]X used within the scope of an ordinary X's assumptions",
    "`X' can be used only after a name and either at the end after an",
];

/// The shape of a message: its first line, with each run of word characters (`[A-Za-z0-9_]`)
/// that starts with a capital letter written X, each number N, each quoted name `X' or 'X' and
/// each operator spelled with a backslash X, as the recordings' shapes are: what a message says of
/// the spec is a parameter of its wording.
fn get_message_shape(text: &str) -> String {
    let line = text.lines().next().unwrap_or_default();
    let mut shape = String::new();
    let mut word = String::new();
    let flush = |word: &mut String, shape: &mut String| {
        if word.starts_with(|first: char| first.is_ascii_uppercase()) {
            shape.push('X');
        } else if !word.is_empty() && word.chars().all(|digit| digit.is_ascii_digit()) {
            shape.push('N');
        } else {
            shape.push_str(word);
        }
        word.clear();
    };
    let characters: Vec<char> = line.chars().collect();
    let mut index = 0;
    while index < characters.len() {
        let character = characters[index];
        // A name SANY quotes, `name' or 'name', is a parameter of the message, written `X' or 'X'.
        let is_quote = character == '`'
            || (character == '\''
                && characters
                    .get(index.wrapping_sub(1))
                    .is_none_or(|before| !before.is_ascii_alphanumeric()));
        let end = is_quote
            .then(|| characters[index + 1..].iter().position(|&end| end == '\''))
            .flatten();
        if let Some(length) = end {
            flush(&mut word, &mut shape);
            shape.push(character);
            shape.push_str("X'");
            index += length + 2;
            continue;
        }
        // An operator SANY spells with a backslash, such as \lnot, is a name too.
        if character == '\\'
            && characters
                .get(index + 1)
                .is_some_and(char::is_ascii_alphabetic)
        {
            flush(&mut word, &mut shape);
            shape.push('X');
            index += 1;
            while characters
                .get(index)
                .is_some_and(char::is_ascii_alphanumeric)
            {
                index += 1;
            }
            continue;
        }
        if character.is_ascii_alphanumeric() || character == '_' {
            word.push(character);
        } else {
            flush(&mut word, &mut shape);
            shape.push(character);
        }
        index += 1;
    }
    flush(&mut word, &mut shape);
    shape
}

fn get_sany_error(message: &SanyMessage) -> SanyError {
    SanyError {
        location: format_sany_location(&message.location),
        message: message.text.clone(),
    }
}

/// The messages of each module of `order`, the order SANY analyzes the modules in, for the root
/// module `root` of the text `source`, to whose EXTENDS TLC adds `root_extendees`: SANY
/// level-checks a module only while no module so far has errors
/// (`SANY.frontEndSemanticAnalysis`).
pub fn get_generator_messages(
    root: &str,
    source: &str,
    load_module: &dyn Fn(&str) -> Option<String>,
    root_extendees: &[&str],
    order: &[Name],
) -> Result<Generated> {
    let ends = RefCell::new(Vec::new());
    let check_levels = |graph: &mut Graph, module: NodeId, messages: &mut Vec<SanyMessage>| {
        if messages.iter().all(|message| message.is_warning) {
            check_module_levels(graph, module, &mut LevelCheck { messages });
        }
        ends.borrow_mut().push(messages.len());
    };
    let generated = generate_sany_specification(
        source,
        load_module,
        &GenerationOptions {
            root_file_name: Some(Name::from(root)),
            root_file_path: None,
            root_extendees: (!root_extendees.is_empty()).then(|| {
                root_extendees
                    .iter()
                    .map(|&name| Name::from(name))
                    .collect()
            }),
            on_module: Some(&check_levels),
        },
    );
    let specification = match generated {
        Err(FrontError::NotYet(reason)) if reason == GENERATOR_EXCEPTION => {
            // The modules before the one that throws are those `on_module` saw.
            return Ok(Generated::Exception(ends.into_inner().len()));
        }
        Err(FrontError::NotYet(reason)) if reason.starts_with(UNLINKABLE) => {
            return Ok(Generated::Declined(reason[UNLINKABLE.len()..].to_owned()));
        }
        generated => generated?,
    };
    let names: Vec<&Name> = specification
        .modules
        .iter()
        .filter_map(|&module| specification.graph.node(module).symbol_name())
        .collect();
    if names.len() != order.len() || names.iter().zip(order).any(|(name, other)| *name != other) {
        return not_yet("SANY's generator analyzing the modules in another order");
    }
    let unproven = specification
        .messages
        .iter()
        .find(|message| !PROVEN_MESSAGES.contains(&get_message_shape(&message.text).as_str()))
        .map(|message| message.text.lines().next().unwrap_or_default().to_owned());
    let ends = ends.into_inner();
    let mut start = 0;
    let messages = ends
        .into_iter()
        .map(|end| {
            let messages = &specification.messages[start..end];
            start = end;
            ModuleMessages {
                warnings: messages
                    .iter()
                    .filter(|message| message.is_warning)
                    .map(get_sany_error)
                    .collect(),
                errors: messages
                    .iter()
                    .filter(|message| !message.is_warning)
                    .map(get_sany_error)
                    .collect(),
            }
        })
        .collect();
    let lints = if specification
        .messages
        .iter()
        .all(|message| message.is_warning)
    {
        let mut lints = Vec::new();
        for &module in &specification.modules {
            let linted = specification
                .graph
                .node(module)
                .symbol_name()
                .is_some_and(|name| !UNLINTED_MODULES.contains(&&**name));
            if linted {
                lints.extend(lint_sany_module(&specification.graph, module)?);
            }
        }
        Some(lints)
    } else {
        None
    };
    Ok(match unproven {
        Some(message) => Generated::Unproven(messages, lints, message),
        None => Generated::Messages(messages, lints),
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{PROVEN_MESSAGES, get_message_shape};

    /// The values of a recording's `"id": "output"` lines, unescaped.
    fn get_outputs(recording: &str) -> Vec<String> {
        recording
            .lines()
            .filter_map(|line| line.split_once("\": \""))
            .map(|(_, value)| {
                let value = value.trim_end_matches(',').trim_end_matches('"');
                let mut output = String::new();
                let mut characters = value.chars();
                while let Some(character) = characters.next() {
                    if character != '\\' {
                        output.push(character);
                        continue;
                    }
                    match characters.next() {
                        Some('n') => output.push('\n'),
                        Some('t') => output.push('\t'),
                        Some('u') => {
                            let code: String = characters.by_ref().take(4).collect();
                            let unit = u32::from_str_radix(&code, 16).expect("a code unit");
                            output.push(char::from_u32(unit).expect("a character"));
                        }
                        Some(other) => output.push(other),
                        None => {}
                    }
                }
                output
            })
            .collect()
    }

    fn is_location(line: &str) -> bool {
        line == "Unknown location"
            || line.starts_with("In module ")
            || (line.starts_with("line ") && line.contains(" of module "))
    }

    #[test]
    fn proves_each_message_by_a_recording_of_sany() {
        let mut shapes = BTreeSet::new();
        for recording in [
            include_str!("../../../../../tests/conformance/sany-stdout/grid.json"),
            include_str!("../../../../../tests/conformance/sany-stdout/corpus.json"),
            include_str!("../../../../../tests/conformance/sany-stdout/report-cases.json"),
            include_str!("../../../../../tests/conformance/sany-stdout/sany-cases.json"),
        ] {
            for output in get_outputs(recording) {
                let lines: Vec<&str> = output.split('\n').collect();
                for window in lines.windows(3) {
                    if is_location(window[0]) && window[1].is_empty() && !window[2].is_empty() {
                        shapes.insert(get_message_shape(window[2]));
                    }
                }
            }
        }
        let proven: BTreeSet<String> = PROVEN_MESSAGES
            .iter()
            .map(|&shape| shape.to_owned())
            .collect();
        assert_eq!(proven, shapes);
    }

    #[test]
    fn writes_capitalized_words_as_x() {
        assert_eq!(
            get_message_shape("Symbol F declared in RECURSIVE statement but not defined.\nmore"),
            "X X declared in X statement but not defined."
        );
        assert_eq!(
            get_message_shape("Unknown operator: `def'."),
            "X operator: `X'."
        );
    }
}

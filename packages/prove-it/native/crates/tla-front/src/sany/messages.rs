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
use crate::sany::nodes::{Graph, NodeId, SanyMessage, format_sany_location};
use crate::sany::{GENERATOR_EXCEPTION, Result, not_yet};

/// What SANY's generator reports: each module's messages, or the index in the order of the
/// module `Generator` throws on as it generates it.
pub enum Generated {
    Messages(Vec<ModuleMessages>),
    Exception(usize),
}

/// The first lines of the messages SANY prints in `tests/conformance/sany-stdout`'s recordings of
/// the real SANY (`grid.json` and `corpus.json`), each word that starts with a capital letter
/// written X (`get_message_shape`). A message of the generator whose shape isn't one of these is
/// `NotYet`: only what a recording shows SANY printing is printed. The test below derives the
/// list from the recordings.
const PROVEN_MESSAGES: &[&str] = &[
    "<*> and <+> cannot be used for a named step.",
    "<> followed by action not of form <<X>>_v.",
    "=> has both temporal formula and action as arguments.",
    "@ used where its meaning is not defined.",
    "X '\\lnot' is not a legal target of a substitution. ",
    "X 'c' is not a legal target of a substitution. ",
    "X 'f' is defined with 1 parameters, but is applied to 2 arguments.",
    "X 'f' is defined with 2 parameters, but is applied to 3 arguments.",
    "X -. already defined or declared.",
    "X 1 of recursive operator X is primed",
    "X 1 of recursive operator op is primed",
    "X 1 operator (not an expression) is expected ",
    "X <> already defined or declared.",
    "X <> is a built-in operator, and cannot be redefined.",
    "X X",
    "X X  may not appear within a recursive definition section.",
    "X X algorithm in module X has changed since its last translation.",
    "X X already defined or declared.",
    "X X declaration may not appear within a recursive definition section.",
    "X X declared in X statement but not defined.",
    "X X has operator arguments in its X declaration.",
    "X X is a built-in operator, and cannot be redefined.",
    "X X may not appear within a recursive definition section.",
    "X X or X may not appear within a recursive definition section.",
    "X X or X statement.",
    "X X+ translation in module X has changed since its last translation.",
    "X X, X, or X",
    "X \\lnot already defined or declared.",
    "X \\lnot is a built-in operator, and cannot be redefined.",
    "X `!(...)' should not have argument(s).",
    "X `X' should not have argument(s).",
    "X `X' used without being extended or instantiated.",
    "X `lbl' used with wrong number of arguments.",
    "X arity 1 but found operator of arity 0.",
    "X arity 1 but found operator of arity 2.",
    "X arity 2 but found operator of arity 0.",
    "X arity 2 but found operator of arity 1.",
    "X arity 2 but found operator of arity 3.",
    "X clause entry should describe a defined operator.",
    "X declaration may not appear within a recursive definition section.",
    "X declaration of '+' conflicts with ",
    "X declarations or definitions for symbol X.  ",
    "X declarations or definitions for symbol op.  ",
    "X declarations or definitions for symbol recDef.  ",
    "X dependency among .tla files; dependency cycle is:",
    "X error in applying operator $X:",
    "X error in applying operator ':",
    "X error in applying operator X:",
    "X error in applying operator apply:",
    "X error in applying operator op:",
    "X error in instantiating module 'X':",
    "X error when instantiating module 'X':",
    "X error:",
    "X error: assumptions must be level 0 (X), ",
    "X expecting a X.",
    "X expression appears as argument number 1 (counting from 1) to operator 'X', in a position an operator is required.",
    "X expression appears as argument number 1 (counting from 1) to operator 'op', in a position an operator is required.",
    "X expression type `X'.",
    "X expression type `['.",
    "X expression used where an expression is required.",
    "X expression with arity 1 used as argument 1 of operator `op', ",
    "X expression with arity 2 used as argument 1 of operator `op', ",
    "X expression with arity 3 used as argument 1 of operator `op', ",
    "X field name \"X\" in the record constructor is identical to the existing definition or declaration",
    "X find source file for module X imported in module X.",
    "X formal parameter x ",
    "X function X defined at wrong X/X level.",
    "X function recDef defined at wrong X/X level.",
    "X in instantiating module 'X':",
    "X inside X clauses are not yet implemented.",
    "X label `lbl'.",
    "X lbl declares extra parameter(s)  x  ",
    "X lbl must contain formal parameter `x'.",
    "X list has both temporal formula and action as arguments.",
    "X missing for symbol X declared at line 2, col 10 to line 2, col 10 of module X ",
    "X missing for symbol c declared at line 5, col 10 to line 5, col 10 of module X ",
    "X name 'X' does not match the name 'X' of the top level module it contains.",
    "X name X is incomplete.",
    "X name `f' already defined or declared.",
    "X name `it' already defined or declared.",
    "X name import is incomplete.",
    "X name or step number here, not `X'.",
    "X not allowed within scope of declaration in nested X/X.",
    "X not find declaration or definition of symbol '+'.",
    "X not find declaration or definition of symbol '@@'.",
    "X not in definition or proof step.",
    "X number 1 to operator 'X' ",
    "X number 1 to operator 'op' ",
    "X number of arguments (0) given to operator 'X', ",
    "X number of arguments (1) given to operator 'X', ",
    "X number of arguments (2) given to operator 'X', ",
    "X of X has different arity than its X declaration.",
    "X of op has different arity than its X declaration.",
    "X only expression allowed as a fact in a X is ",
    "X op already defined or declared.",
    "X op declared in X statement but not defined.",
    "X operand specified by `argument selector 3'.",
    "X operator X defined at wrong X/X level.",
    "X operator X requires 0 arguments.",
    "X operator X requires 1 arguments.",
    "X operator X requires 2 arguments.",
    "X operator \\union requires 2 arguments.",
    "X operator import requires 1 arguments.",
    "X operator must be substituted for symbol 'X', and it must have arity 1.",
    "X operator must be substituted for symbol 'X', and it must have arity 2.",
    "X operator op requires 0 arguments.",
    "X operator op requires 1 arguments.",
    "X operator op requires 2 arguments.",
    "X operator recDef defined at wrong X/X level.",
    "X operator: `@@'.",
    "X operator: `X'.",
    "X operator: `bar'.",
    "X operator: `def'.",
    "X operator: `import!X'.",
    "X operator: `s'.",
    "X operator: `|'.",
    "X parameter x of label `lbl'.",
    "X proof step selected instead of expression.",
    "X recDef declared in X statement but not defined.",
    "X substitutions for symbol 'c' in substitution.",
    "X the X algorithm and its X+ translation in module X have changed since the last translation.",
    "X to declare '@' as a variable.",
    "X token found.",
    "X unexpected problem was encountered attempting to validate the specification for X",
    "X used where only temporal formula or state predicate allowed.",
    "X with incorrect arity passed as argument. ",
    "X't resolve infix operator symbol `+'.",
    "X't resolve infix operator symbol `@@'.",
    "X-constant X for temporal goal.",
    "X-constant X, X, or X for temporal goal.",
    "X-constant bound of temporal X.",
    "X-defined module 'X': this definition or declaration conflicts ",
    "X-defined symbol '-.': this definition or declaration conflicts ",
    "X-defined symbol '@': this definition or declaration conflicts ",
    "X-defined symbol 'X': this definition or declaration conflicts ",
    "X-defined symbol 'def': this definition or declaration conflicts ",
    "X-defined symbol 'x': this definition or declaration conflicts ",
    "X-level bound of quantified temporal formula.",
    "X-unique fields in constructor.",
    "X/X used where an expression is required.",
    "X: the definition of '+' conflicts with ",
    "[] followed by action not of form [X]_v.",
    "[]X matched by X instead of []X",
    "[]X used within the scope of an ordinary X's assumptions",
    "\\equiv has both temporal formula and action as arguments.",
    "\\land has both temporal formula and action as arguments.",
    "\\lor has both temporal formula and action as arguments.",
];

/// The shape of a message: its first line, with each run of word characters (`[A-Za-z0-9_]`)
/// that starts with a capital letter written X, as the recordings' shapes are.
fn get_message_shape(text: &str) -> String {
    let line = text.lines().next().unwrap_or_default();
    let mut shape = String::new();
    let mut word = String::new();
    let flush = |word: &mut String, shape: &mut String| {
        if word.starts_with(|first: char| first.is_ascii_uppercase()) {
            shape.push('X');
        } else {
            shape.push_str(word);
        }
        word.clear();
    };
    for character in line.chars() {
        if character.is_ascii_alphanumeric() || character == '_' {
            word.push(character);
        } else {
            flush(&mut word, &mut shape);
            shape.push(character);
        }
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
    if let Some(message) = specification
        .messages
        .iter()
        .find(|message| !PROVEN_MESSAGES.contains(&get_message_shape(&message.text).as_str()))
    {
        return not_yet(format!(
            "a message of SANY's generator that no recording shows: {}",
            message.text.lines().next().unwrap_or_default()
        ));
    }
    let ends = ends.into_inner();
    let mut start = 0;
    Ok(Generated::Messages(
        ends.into_iter()
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
            .collect(),
    ))
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
            "X operator: `def'."
        );
    }
}

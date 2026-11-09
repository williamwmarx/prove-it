//! The productions of javacc/tla+.jj, with their lookahead specifications and the semantic
//! actions that steer parsing or set the `expecting` message, as `src/sany/parse-error.ts`
//! writes them.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use super::lexer::{Token, get_kind};
use super::{
    Action, Exit, Frame, Grammar, KindSet, Node, Predicate, Production, Repeat, StackElement,
    State, UNBOUNDED_AMOUNT, Unit, create_node, is_looser, reduce_postfix, reduce_stack,
};

/// A token kind in angle brackets, a production's name, or a unit.
enum Part {
    Name(&'static str),
    Unit(usize),
}

impl From<&'static str> for Part {
    fn from(name: &'static str) -> Part {
        Part::Name(name)
    }
}

impl From<usize> for Part {
    fn from(unit: usize) -> Part {
        Part::Unit(unit)
    }
}

macro_rules! parts {
    ($($part:expr),* $(,)?) => { vec![$(Part::from($part)),*] };
}

macro_rules! seq {
    ($builder:expr; $($part:expr),* $(,)?) => {{ let parts = parts![$($part),*]; $builder.sequence(parts) }};
}

macro_rules! choice {
    ($builder:expr; $($part:expr),* $(,)?) => {{ let parts = parts![$($part),*]; $builder.choice(parts) }};
}

macro_rules! zero_or_more {
    ($builder:expr; $($part:expr),* $(,)?) => {{ let parts = parts![$($part),*]; $builder.repeat(Repeat::ZeroOrMore, parts) }};
}

macro_rules! one_or_more {
    ($builder:expr; $($part:expr),* $(,)?) => {{ let parts = parts![$($part),*]; $builder.repeat(Repeat::OneOrMore, parts) }};
}

macro_rules! optional {
    ($builder:expr; $($part:expr),* $(,)?) => {{ let parts = parts![$($part),*]; $builder.repeat(Repeat::Optional, parts) }};
}

/// A LOOKAHEAD whose expansion is the parts given.
macro_rules! lookahead_of {
    ($builder:expr; [$($part:expr),* $(,)?]) => {{ let parts = parts![$($part),*]; $builder.lookahead(None, Some(parts), None) }};
    ($builder:expr; [$($part:expr),* $(,)?], $semantic:expr) => {{ let parts = parts![$($part),*]; $builder.lookahead(None, Some(parts), Some(predicate($semantic))) }};
    ($builder:expr; $amount:expr, [$($part:expr),* $(,)?], $semantic:expr) => {{ let parts = parts![$($part),*]; $builder.lookahead(Some($amount), Some(parts), Some(predicate($semantic))) }};
}

fn predicate(semantic: impl Fn(&mut State) -> bool + 'static) -> Predicate {
    Rc::new(semantic)
}

struct Builder {
    units: Vec<Unit>,
    productions: HashMap<&'static str, Production>,
}

impl Builder {
    fn add(&mut self, unit: Unit) -> usize {
        self.units.push(unit);
        self.units.len() - 1
    }

    fn add_part(&mut self, part: Part) -> usize {
        match part {
            Part::Unit(unit) => unit,
            Part::Name(name) => match name.strip_prefix('<') {
                Some(kind) => self.tokens([get_kind(kind.trim_end_matches('>'))]),
                None => self.add(Unit::Call(name)),
            },
        }
    }

    fn tokens(&mut self, kinds: impl IntoIterator<Item = usize>) -> usize {
        self.add(Unit::Tokens(KindSet::of(kinds)))
    }

    fn sequence(&mut self, parts: Vec<Part>) -> usize {
        let units = parts.into_iter().map(|part| self.add_part(part)).collect();
        self.add(Unit::Sequence(units))
    }

    fn choice(&mut self, parts: Vec<Part>) -> usize {
        let alternatives = parts
            .into_iter()
            .map(|part| match part {
                Part::Unit(unit) if matches!(self.units[unit], Unit::Sequence(_)) => unit,
                part => self.sequence(vec![part]),
            })
            .collect();
        self.add(Unit::Choice(alternatives))
    }

    fn repeat(&mut self, repeat: Repeat, parts: Vec<Part>) -> usize {
        let body = self.sequence(parts);
        self.add(Unit::Repeat(repeat, body))
    }

    fn action(&mut self, run: impl Fn(&mut State) -> Option<String> + 'static) -> usize {
        let run: Action = Rc::new(run);
        self.add(Unit::Action(run))
    }

    fn expect(&mut self, expecting: &'static str) -> usize {
        self.action(move |state| {
            state.expecting = expecting.to_owned();
            None
        })
    }

    fn lookahead(
        &mut self,
        amount: Option<i64>,
        expansion: Option<Vec<Part>>,
        semantic: Option<Predicate>,
    ) -> usize {
        let amount = amount.unwrap_or(if expansion.is_some() {
            UNBOUNDED_AMOUNT
        } else {
            0
        });
        let expansion = expansion.map(|parts| self.sequence(parts));
        self.add(Unit::Lookahead {
            amount,
            expansion,
            semantic,
        })
    }

    fn lookahead_amount(&mut self, amount: i64) -> usize {
        self.lookahead(Some(amount), None, None)
    }

    fn lookahead_semantic(&mut self, semantic: impl Fn(&mut State) -> bool + 'static) -> usize {
        self.lookahead(None, None, Some(predicate(semantic)))
    }

    fn production(
        &mut self,
        name: &'static str,
        message: Option<&'static str>,
        parts: Vec<Part>,
        exit: Option<Exit>,
    ) {
        let body = self.sequence(parts);
        self.productions.insert(
            name,
            Production {
                message,
                body,
                exit,
            },
        );
    }
}

fn get_kind_range(first: &str, last: &str) -> std::ops::RangeInclusive<usize> {
    get_kind(first)..=get_kind(last)
}

/// TLAplusParser.isOp, isInfixOp, isPostfixOp, and isFieldNameToken.
fn is_operator_kind(kind: usize) -> bool {
    get_kind_range("op_57", "op_119").contains(&kind)
}

fn is_infix_kind(kind: usize) -> bool {
    get_kind_range("op_1", "op_119").contains(&kind)
}

fn is_postfix_kind(kind: usize) -> bool {
    get_kind_range("op_57", "op_70").contains(&kind)
}

fn is_field_name_kind(kind: usize) -> bool {
    get_kind_range("ACTION", "EXCEPT").contains(&kind)
        || kind == get_kind("EXTENDS")
        || get_kind_range("IF", "SF").contains(&kind)
        || kind == get_kind("STATE")
        || get_kind_range("THEN", "WITH").contains(&kind)
        || kind == get_kind("US")
        || get_kind_range("op_112", "op_116").contains(&kind)
}

/// The Java code that lets a keyword name a module or a record field.
fn set_field_name(state: &mut State) {
    let token = state.get_token(1);
    if is_field_name_kind(state.kind(token)) {
        state.tokens[token].kind = get_kind("IDENTIFIER");
    }
}

/// TLAplusParser.belchDEF, which inserts a DEFBREAK token before the left-hand side of the next
/// definition. It reverses the links of the tokens it walks over, so that `next` leads back
/// toward the definition's start, and restores them when done.
fn belch_def(state: &mut State) {
    let stops = ["EOF", "THEOREM", "PROPOSITION", "ASSUMPTION", "END_MODULE"].map(get_kind);
    let is_kind = |state: &State, token: usize, names: &[&str]| {
        names.iter().any(|name| state.kind(token) == get_kind(name))
    };
    let next_of = |state: &State, token: usize| state.tokens[token].next;
    let mut previous: Option<usize> = Some(state.token);
    let mut current = state.get_next(state.token);
    state.tokens[state.token].next = None;
    let mut next = state.get_next(current);
    state.tokens[current].next = previous;
    while !stops.contains(&state.kind(next))
        && !is_kind(state, current, &["THEOREM", "PROPOSITION"])
    {
        if is_kind(state, current, &["DEF"]) {
            let mut head = previous;
            if let Some(start) = head {
                if is_kind(state, start, &["RBR", "RSB"]) {
                    let mut at = start;
                    let mut depth = 1;
                    while let Some(back) = next_of(state, at) {
                        at = back;
                        let is_open = is_kind(state, at, &["LBR", "LSB"]);
                        if is_open && depth == 1 {
                            break;
                        }
                        if is_open && depth > 1 {
                            depth -= 1;
                        }
                        if is_kind(state, at, &["RBR", "RSB"]) {
                            depth += 1;
                        }
                    }
                    head = match next_of(state, at) {
                        None => None,
                        Some(back) if state.kind(back) == get_kind("IDENTIFIER") => Some(back),
                        Some(_) => Some(at),
                    };
                } else if state.kind(start) == get_kind("IDENTIFIER") {
                    let operator = next_of(state, start);
                    if let Some(operator) = operator
                        && is_operator_kind(state.kind(operator))
                        && !is_postfix_kind(state.kind(operator))
                        && (!is_infix_kind(state.kind(operator))
                            || next_of(state, operator)
                                .is_some_and(|back| state.kind(back) == get_kind("IDENTIFIER")))
                    {
                        let after = next_of(state, operator);
                        head = if after
                            .is_some_and(|back| state.kind(back) == get_kind("SUBSTITUTE"))
                        {
                            previous
                        } else if is_infix_kind(state.kind(operator)) {
                            after
                        } else {
                            Some(operator)
                        };
                    }
                } else if is_operator_kind(state.kind(start)) {
                    head = next_of(state, start);
                }
            }
            if let Some(head) = head
                && next_of(state, head).is_none_or(|back| state.kind(back) != get_kind("DEFBREAK"))
            {
                let token = &state.tokens[head];
                let inserted = Token {
                    kind: get_kind("DEFBREAK"),
                    image: "Beginning of definition".to_owned(),
                    begin_line: token.begin_line,
                    begin_column: token.begin_column,
                    next: token.next,
                };
                state.tokens.push(inserted);
                let index = state.tokens.len() - 1;
                state.tokens[head].next = Some(index);
            }
            break;
        }
        previous = Some(current);
        current = next;
        next = state.get_next(current);
        state.tokens[current].next = previous;
    }
    while let Some(back) = previous {
        state.tokens[current].next = Some(next);
        next = current;
        current = back;
        previous = state.tokens[current].next;
    }
    state.tokens[current].next = Some(next);
}

/// TLAplusParser.matchFcnConst: whether the next tokens are "<< ... >> \in" or a list of
/// identifiers followed by \in.
fn match_fcn_const(state: &mut State) -> bool {
    let mut token = state.get_token(1);
    if state.kind(token) == get_kind("LAB") {
        let mut depth = 1;
        while depth != 0 {
            token = state.get_next(token);
            if state.kind(token) == get_kind("LAB") {
                depth += 1;
            }
            if state.kind(token) == get_kind("RAB") {
                depth -= 1;
            }
            if state.kind(token) == get_kind("EOF") {
                return false;
            }
        }
        let after = state.get_next(token);
        return state.kind(after) == get_kind("IN");
    }
    if state.kind(token) != get_kind("IDENTIFIER") {
        return false;
    }
    token = state.get_next(token);
    while state.kind(token) == get_kind("COMMA") {
        token = state.get_next(token);
        if state.kind(token) != get_kind("IDENTIFIER") {
            return false;
        }
        token = state.get_next(token);
    }
    state.kind(token) == get_kind("IN")
}

/// The UTF-16 code unit at index of a token's image.
fn get_image_unit(state: &State, token: usize, index: usize) -> Option<u16> {
    state.tokens[token].image.encode_utf16().nth(index)
}

/// TLAplusParser.levelOfProofStepLexeme: -1 for <*> and -2 for <+>, and NaN where parseInt finds
/// no number.
fn get_step_level(state: &State, token: usize) -> f64 {
    match get_image_unit(state, token, 1) {
        Some(0x2a) => -1.0,
        Some(0x2b) => -2.0,
        _ => {
            let digits: String = state.tokens[token]
                .image
                .chars()
                .skip(1)
                .take_while(char::is_ascii_digit)
                .collect();
            digits.parse::<f64>().unwrap_or(f64::NAN)
        }
    }
}

fn begins_proof(state: &mut State) -> bool {
    let token = state.get_token(1);
    if state.tokens[token].image.encode_utf16().count() < 2 {
        return false;
    }
    match get_image_unit(state, token, 1) {
        Some(0x2a) => return state.proof_levels.is_empty(),
        Some(0x2b) => return true,
        _ => {}
    }
    if state.is_next_kind(&[
        "ProofStepLexeme",
        "BareLevelLexeme",
        "UnnumberedStepLexeme",
        "ProofStepDotLexeme",
    ]) {
        if state.proof_levels.is_empty() {
            return true;
        }
        let level = state.get_proof_level();
        return level >= 0.0 && get_step_level(state, token) > level;
    }
    state.is_next_kind(&["BY", "PROOF", "OBVIOUS", "OMITTED"])
}

/// TLAplusParser.correctLevel, which also sets the level of a proof from its first step.
fn is_correct_level(state: &mut State, token: usize) -> bool {
    let level = get_step_level(state, token);
    let Some(depth) = state.proof_levels.len().checked_sub(1) else {
        return level == -1.0;
    };
    let outer_level = depth
        .checked_sub(1)
        .map_or(-1.0, |outer| state.proof_levels[outer]);
    let is_first_step = state.proof_levels[depth] < 0.0;
    if is_first_step {
        state.proof_levels[depth] = if level < 0.0 {
            outer_level + 1.0
        } else {
            level
        };
    }
    if level == -1.0 {
        return true;
    }
    if level == -2.0 {
        return is_first_step;
    }
    if is_first_step {
        level > outer_level
    } else {
        state.proof_levels[depth] == level
    }
}

/// The OpArgs node that a PrimitiveExp's heirs end with, directly or in their last "!"
/// extension.
fn get_arguments(heirs: &[Rc<Node>]) -> Option<Rc<Node>> {
    let last = heirs.last()?;
    let node = if last.kind == "BangExt" {
        last.heirs.last()?.clone()
    } else {
        last.clone()
    };
    (node.kind == "OpArgs").then_some(node)
}

/// TLAplusParser.isLabel: whether a node is an identifier, or an operator applied to
/// identifiers.
fn is_label(node: &Node) -> bool {
    if node.kind == "GeneralId" {
        return true;
    }
    let op_args = if node.kind == "OpApplication" {
        get_arguments(&node.heirs)
    } else {
        None
    };
    op_args.is_some_and(|op_args| {
        op_args
            .heirs
            .iter()
            .enumerate()
            .all(|(index, argument)| index % 2 == 0 || argument.kind == "GeneralId")
    })
}

/// The first node below node, stopping at junction lists, that does not start to the right of
/// the current junction list's bullet: what TLAplusParser.checkIndentation reports.
fn get_misindented_node(state: &mut State, node: &Node) -> Option<Rc<Node>> {
    for child in &node.heirs {
        if child.kind == "Junctions" {
            continue;
        }
        let column = state.tokens[child.first].begin_column;
        if !state.is_above_current(Some(column)) {
            return Some(child.clone());
        }
        if let Some(misindented) = get_misindented_node(state, child) {
            return Some(misindented);
        }
    }
    None
}

/// OperatorStack.pushOnStack for the node of the production just parsed: an operand, or, if
/// is_operator holds of it, an operator, which reduce_stack reduces with what is below it.
fn push_on_stack(builder: &mut Builder, is_operator: fn(&Node) -> bool) -> usize {
    builder.action(move |state| {
        let node = state.get_heir(1)?;
        let operator = if is_operator(&node) {
            Some(state.last_operator.clone())
        } else {
            None
        };
        let stack = state.operator_stacks.last_mut()?;
        match operator {
            None => {
                stack.push(StackElement {
                    node,
                    operator: None,
                });
                None
            }
            Some(operator) => {
                stack.push(StackElement { node, operator });
                if stack.len() == 1 {
                    None
                } else {
                    reduce_stack(state)
                }
            }
        }
    })
}

fn push_operand(builder: &mut Builder) -> usize {
    push_on_stack(builder, |_| false)
}

fn push_operator(builder: &mut Builder) -> usize {
    push_on_stack(builder, |_| true)
}

/// TLAplusParser's lastOp, which the productions of operators set.
fn set_last_operator(builder: &mut Builder) -> usize {
    builder.action(|state| {
        let image = state.tokens[state.token].image.clone();
        state.last_operator = state.get_operator(&image);
        None
    })
}

fn check_step_level(builder: &mut Builder, problem: &'static str) -> usize {
    builder.action(move |state| {
        let token = state.token;
        if is_correct_level(state, token) {
            None
        } else {
            Some(format!(
                "{}: {problem}",
                state.format_location(token, token)
            ))
        }
    })
}

fn set_field_name_expecting(builder: &mut Builder, expecting: &'static str) -> usize {
    builder.action(move |state| {
        state.expecting = expecting.to_owned();
        set_field_name(state);
        None
    })
}

fn set_terminal_proof(builder: &mut Builder, is_terminal_proof: bool) -> usize {
    builder.action(move |state| {
        state.is_terminal_proof = is_terminal_proof;
        None
    })
}

fn kinds(names: &[&str]) -> Vec<usize> {
    names.iter().map(|name| get_kind(name)).collect()
}

const PREFIX_OPERATOR_KINDS: &[&str] = &[
    "op_26", "op_29", "op_58", "CASESEP", "op_61", "op_112", "op_113", "op_114", "op_115", "op_116",
];

fn prefix_operator(builder: &mut Builder) -> usize {
    builder.tokens(kinds(PREFIX_OPERATOR_KINDS))
}

fn nonexp_prefix_operator(builder: &mut Builder) -> usize {
    let mut all = kinds(PREFIX_OPERATOR_KINDS);
    all.push(get_kind("op_76"));
    builder.tokens(all)
}

fn infix_operator(builder: &mut Builder) -> usize {
    builder.tokens(get_kind_range("op_1", "op_119"))
}

fn postfix_operator(builder: &mut Builder) -> usize {
    builder.tokens(get_kind_range("op_57", "op_70"))
}

fn step_start(builder: &mut Builder) -> usize {
    builder.tokens(kinds(&[
        "ProofStepLexeme",
        "ProofImplicitStepLexeme",
        "ProofStepDotLexeme",
        "BareLevelLexeme",
        "UnnumberedStepLexeme",
    ]))
}

fn above_current(state: &mut State) -> bool {
    state.is_above_current(None)
}

/// The prefix operators and the operand that Expression and ExtendableExpr share. Each use is a
/// separate lookahead site, as in the generated parser.
fn get_prefix_operators(b: &mut Builder) -> usize {
    let prefix = prefix_operator(b);
    let operators = choice!(b; prefix, "<op_77>");
    let lookahead = lookahead_of!(b; [operators], above_current);
    let operator = choice!(b; "PrefixOp", "InfixOp");
    let push = push_operator(b);
    zero_or_more!(b; lookahead, operator, push)
}

fn get_operand(b: &mut Builder) -> usize {
    let open = lookahead_of!(b; ["OpenStart"], above_current);
    let push = push_operand(b);
    let open = seq!(b; open, "OpenExpression", push);
    let extendable = b.lookahead_semantic(above_current);
    let extendable = seq!(b; extendable, "ExtendableExpr");
    choice!(b; open, extendable)
}

fn get_use_item(b: &mut Builder) -> usize {
    let expect = b.expect("identifier");
    let module = seq!(b; "<MODULE>", expect, "Identifier");
    choice!(b; module, "Expression")
}

fn get_assume_prove_item(b: &mut Builder) -> usize {
    let lookahead = b.lookahead_semantic(|state| {
        state.is_next_kind(&["ASSUME", "BOXASSUME"]) || {
            let second = state.get_token(2);
            let third = state.get_token(3);
            state.kind(second) == get_kind("COLONCOLON")
                && [get_kind("ASSUME"), get_kind("BOXASSUME")].contains(&state.kind(third))
        }
    });
    let assume_prove = seq!(b; lookahead, "AssumeProve");
    choice!(b; assume_prove, "NewSymb", "Expression")
}

fn get_junction_list(b: &mut Builder) -> Vec<Part> {
    let lookahead = b.lookahead_semantic(State::is_new_bullet);
    let rest = zero_or_more!(b; lookahead, "JuncItem");
    parts!["JuncItem", rest]
}

/// An alternative of OperatorOrFunctionDefinition: a left-hand side, then "==", then a body.
fn definition(b: &mut Builder, expecting: &'static str, mut parts: Vec<Part>) -> usize {
    let body = parts.pop();
    let expect = b.expect("==");
    let belch = b.action(move |state| {
        belch_def(state);
        state.expecting = expecting.to_owned();
        None
    });
    parts.extend(parts![expect, "<DEF>", belch]);
    parts.extend(body);
    b.sequence(parts)
}

fn belch(b: &mut Builder) -> usize {
    b.action(|state| {
        belch_def(state);
        None
    })
}

fn exit(run: impl Fn(&mut Frame, &mut State) -> Option<String> + 'static) -> Option<Exit> {
    Some(Rc::new(run))
}

/// The productions.
pub(super) fn create_grammar() -> Grammar {
    let mut builder = Builder {
        units: Vec::new(),
        productions: HashMap::new(),
    };
    let b = &mut builder;

    let action = belch(b);
    let prelude = optional!(b; "Prelude");
    b.production(
        "CompilationUnit",
        None,
        parts![action, prelude, "Module"],
        None,
    );

    let pragma = choice!(b; "<NUMBER>", "<IDENTIFIER>");
    let pragma = zero_or_more!(b; pragma);
    b.production("Prelude", None, parts!["<BEGIN_PRAGMA>", pragma], None);

    let e1 = b.expect("---- MODULE");
    let e2 = b.expect("EXTENDS clause or module body");
    let e3 = b.expect("Module body");
    let e4 = b.expect("==== or more Module body");
    b.production(
        "Module",
        Some("Module definition"),
        parts![
            e1,
            "BeginModule",
            e2,
            "Extends",
            e3,
            "Body",
            e4,
            "EndModule"
        ],
        None,
    );

    let e1 = b.expect("---- MODULE (beginning of module)");
    let begin = choice!(b; "<_BM0>", "<_BM1>", "<_BM2>");
    let field = set_field_name_expecting(b, "Identifier");
    let name = b.action(|state| {
        if state.module_name.is_none() {
            state.module_name = Some(state.tokens[state.token].image.clone());
        }
        state.expecting = "----".to_owned();
        None
    });
    b.production(
        "BeginModule",
        Some("Begin module"),
        parts![e1, begin, field, "Identifier", name, "<SEPARATOR>"],
        None,
    );

    b.production("EndModule", None, parts!["<END_MODULE>"], None);

    let field = set_field_name_expecting(b, "Identifier");
    let e1 = b.expect("comma or module body");
    let field2 = set_field_name_expecting(b, "Identifier");
    let rest = zero_or_more!(b; "<COMMA>", field2, "Identifier");
    let extends = optional!(b; "<EXTENDS>", field, "Identifier", e1, rest);
    b.production("Extends", Some("Extends"), parts![extends], None);

    let e1 = b.expect(
        "LOCAL, INSTANCE, PROOF, ASSUMPTION, THEOREM, RECURSIVE, declaration, or definition",
    );
    let l1 = b.lookahead_amount(2);
    let definition_unit = seq!(b; l1, "OperatorOrFunctionDefinition");
    let l2 = b.lookahead_amount(2);
    let instance = seq!(b; l2, "Instance");
    let l3 = b.lookahead_amount(2);
    let assumption = seq!(b; l3, "Assumption");
    let l4 = b.lookahead_amount(2);
    let theorem = seq!(b; l4, "Theorem");
    let l5 = b.lookahead_amount(1);
    let belch_after = belch(b);
    let module = seq!(b; l5, "Module", belch_after);
    let l6 = b.lookahead_semantic(|state| {
        (state.is_next_kind(&["USE"]) && {
            let second = state.get_token(2);
            state.kind(second) != get_kind("ONLY")
        }) || state.is_next_kind(&["HIDE"])
    });
    let use_or_hide = seq!(b; l6, "UseOrHideOrBy");
    let units = choice!(b;
        "<SEPARATOR>",
        "VariableDeclaration",
        "ParamDeclaration",
        definition_unit,
        "Recursive",
        instance,
        assumption,
        theorem,
        module,
        use_or_hide,
    );
    let units = zero_or_more!(b; units);
    b.production("Body", Some("Module body"), parts![e1, units], None);

    let e1 = b.expect("Identifier");
    let e2 = b.expect("comma or module body");
    let e3 = b.expect("Identifier");
    let rest = zero_or_more!(b; "<COMMA>", e3, "Identifier");
    b.production(
        "VariableDeclaration",
        Some("variable declaration"),
        parts!["<VARIABLE>", e1, "Identifier", e2, rest],
        None,
    );

    let e1 = b.expect("CONSTANT");
    let e2 = b.expect("Identifier, operator or _");
    let e3 = b.expect(",");
    let e4 = b.expect("Identifier, operator or _");
    let rest = zero_or_more!(b; "<COMMA>", e4, "ConstantDeclarationItems");
    b.production(
        "ParamDeclaration",
        Some("Parameter declaration"),
        parts![e1, "ParamSubDecl", e2, "ConstantDeclarationItems", e3, rest],
        None,
    );

    b.production(
        "ParamSubDecl",
        Some("Parameter declaration item"),
        parts!["<CONSTANT>"],
        None,
    );

    let e1 = b.expect("RECURSIVE");
    let e2 = b.expect("Identifier, operator or _");
    let e3 = b.expect(",");
    let e4 = b.expect("Identifier, operator or _");
    let e5 = b.expect("`,' or `)'");
    let rest = zero_or_more!(b; "<COMMA>", e4, "ConstantDeclarationItems", e5);
    b.production(
        "Recursive",
        Some("Recursive"),
        parts![e1, "<RECURSIVE>", e2, "ConstantDeclarationItems", e3, rest],
        None,
    );

    let e1 = b.expect("Identifier, _ or prefix op");
    let e2 = b.expect("(, comma, or Module Body");
    let l1 = b.lookahead_amount(2);
    let e3 = b.expect("_");
    let e4 = b.expect("comma or )");
    let e5 = b.expect("_");
    let e6 = b.expect("comma or )");
    let more = zero_or_more!(b; "<COMMA>", e5, "<US>", e6);
    let arguments = optional!(b; l1, "<LBR>", e3, "<US>", e4, more, "<RBR>");
    let identifier = seq!(b; "Identifier", e2, arguments);
    let e7 = b.expect("_");
    let prefix = seq!(b; "NonExpPrefixOp", e7, "<US>");
    let e8 = b.expect("prefix or postfix operator");
    let e9 = b.expect("_");
    let infix = seq!(b; "InfixOp", e9, "<US>");
    let after = choice!(b; infix, "PostfixOp");
    let underscore = seq!(b; "<US>", e8, after);
    let items = choice!(b; identifier, prefix, underscore);
    b.production(
        "ConstantDeclarationItems",
        Some("Constant declaration items"),
        parts![e1, items],
        None,
    );

    let e1 = b.expect("LOCAL, Identifier or Operator Symbol");
    let local = optional!(b; "<LOCAL>");
    let e2 = b.expect("LOCAL, Identifier or Operator Symbol");
    let function = {
        let lookahead = lookahead_of!(b; ["<IDENTIFIER>", "<LSB>"]);
        let e1 = b.expect("[");
        let e2 = b.expect("Identifier");
        let e3 = b.expect("COMMA or ]");
        let e4 = b.expect("Identifier");
        let rest = zero_or_more!(b; "<COMMA>", e4, "QuantBound");
        definition(
            b,
            "Expression",
            parts![
                lookahead,
                "Identifier",
                e1,
                "<LSB>",
                e2,
                "QuantBound",
                e3,
                rest,
                "<RSB>",
                "Expression"
            ],
        )
    };
    let postfix = {
        let postfix = postfix_operator(b);
        let lookahead = lookahead_of!(b; ["<IDENTIFIER>", postfix]);
        definition(
            b,
            "Expression",
            parts![lookahead, "PostfixLHS", "Expression"],
        )
    };
    let infix = {
        let infix = infix_operator(b);
        let lookahead = lookahead_of!(b; ["<IDENTIFIER>", infix]);
        definition(b, "Expression", parts![lookahead, "InfixLHS", "Expression"])
    };
    let ident = {
        let after = choice!(b; "<LBR>", "<DEF>");
        let lookahead = lookahead_of!(b; ["<IDENTIFIER>", after]);
        let body = choice!(b; "Expression", "Instantiation");
        definition(
            b,
            "Expression or Instance",
            parts![lookahead, "IdentLHS", body],
        )
    };
    let prefix = definition(b, "Expression", parts!["PrefixLHS", "Expression"]);
    let definitions = choice!(b; function, postfix, infix, ident, prefix);
    b.production(
        "OperatorOrFunctionDefinition",
        Some("Definition"),
        parts![e1, local, "<DEFBREAK>", e2, definitions],
        None,
    );

    let e1 = b.expect("Identifier or >>");
    let e2 = b.expect("COMMA or >>");
    let e3 = b.expect("COMMA or >>");
    let e4 = b.expect("COMMA or >>");
    let rest = zero_or_more!(b; "<COMMA>", e3, "Identifier", e4);
    let items = optional!(b; "Identifier", e2, rest);
    b.production(
        "IdentifierTuple",
        Some("Identifier tuple"),
        parts!["<LAB>", e1, items, "<RAB>"],
        None,
    );

    let e1 = b.expect("( or ==");
    let e2 = b.expect("Identifier Declaration, prefix op, _ or )");
    let declaration = choice!(b; "IdentDecl", "SomeFixDecl");
    let e3 = b.expect("COMMA or )");
    let e4 = b.expect("Identifier Declaration, prefix op or _");
    let declaration2 = choice!(b; "IdentDecl", "SomeFixDecl");
    let e5 = b.expect("COMMA or )");
    let rest = zero_or_more!(b; "<COMMA>", e4, declaration2, e5);
    let arguments = optional!(b; "<LBR>", e2, declaration, e3, rest, "<RBR>");
    b.production(
        "IdentLHS",
        Some("Identifier LHS"),
        parts!["Identifier", e1, arguments],
        None,
    );

    let prefix = nonexp_prefix_operator(b);
    let e1 = b.expect("Identifier");
    b.production(
        "PrefixLHS",
        Some("Prefix LHS"),
        parts![prefix, e1, "Identifier"],
        None,
    );
    let infix = infix_operator(b);
    b.production(
        "InfixLHS",
        Some("Infix LHS"),
        parts!["Identifier", infix, "Identifier"],
        None,
    );
    let postfix = postfix_operator(b);
    b.production(
        "PostfixLHS",
        Some("Postfix LHS"),
        parts!["Identifier", postfix],
        None,
    );

    let e1 = b.expect("( or ...");
    let e2 = b.expect("_");
    let e3 = b.expect("COMMA or )");
    let e4 = b.expect("_");
    let e5 = b.expect("COMMA or )");
    let rest = zero_or_more!(b; "<COMMA>", e4, "<US>", e5);
    let arguments = optional!(b; "<LBR>", e2, "<US>", e3, rest, "<RBR>");
    b.production(
        "IdentDecl",
        Some("Identifier Declation"),
        parts!["Identifier", e1, arguments],
        None,
    );

    let e1 = b.expect("_");
    let prefix = seq!(b; "NonExpPrefixOp", e1, "<US>");
    let e2 = b.expect("infix or postfix operator");
    let e3 = b.expect("_");
    let infix = seq!(b; "InfixOp", e3, "<US>");
    let after = choice!(b; infix, "PostfixOp");
    let underscore = seq!(b; "<US>", e2, after);
    let declaration = choice!(b; prefix, underscore);
    b.production(
        "SomeFixDecl",
        Some("Op. Symbol Declaration"),
        parts![declaration],
        None,
    );

    let e1 = b.expect("LOCAL or instance");
    let local = optional!(b; "<LOCAL>");
    let e2 = b.expect("COMMA or Module Body");
    b.production(
        "Instance",
        Some("Instance"),
        parts![e1, local, "Instantiation", e2],
        None,
    );

    let field = set_field_name_expecting(b, "Module identifier");
    let e1 = b.expect("WITH or another definition.");
    let e2 = b.expect("");
    let e3 = b.expect("");
    let l1 = b.lookahead_amount(3);
    let e4 = b.expect("");
    let e5 = b.expect("");
    let rest = zero_or_more!(b; l1, "<COMMA>", e4, "Substitution", e5);
    let with = optional!(b; "<WITH>", e2, "Substitution", e3, rest);
    b.production(
        "Instantiation",
        Some("NonLocalInstance"),
        parts!["<INSTANCE>", field, "Identifier", e1, with],
        None,
    );

    let target = choice!(b; "Identifier", "NonExpPrefixOp", "InfixOp", "PostfixOp");
    let e1 = b.expect("<-");
    let e2 = b.expect("Expression or Op. Symbol");
    b.production(
        "Substitution",
        Some("Substitution"),
        parts![target, e1, "<SUBSTITUTE>", e2, "OpOrExpr"],
        None,
    );

    let prefix = prefix_operator(b);
    let last = set_last_operator(b);
    b.production("PrefixOp", None, parts![prefix, last], None);
    let prefix = nonexp_prefix_operator(b);
    let last = set_last_operator(b);
    b.production("NonExpPrefixOp", None, parts![prefix, last], None);
    let infix = infix_operator(b);
    let last = set_last_operator(b);
    b.production("InfixOp", Some("Infix Op"), parts![infix, last], None);
    let postfix = postfix_operator(b);
    let last = set_last_operator(b);
    b.production("PostfixOp", None, parts![postfix, last], None);
    b.production("Identifier", None, parts!["<IDENTIFIER>"], None);

    let e1 = b.expect("ASSUM...");
    let keyword = choice!(b; "<ASSUMPTION>", "<ASSUME>");
    let l1 = b.lookahead_amount(2);
    let defbreak = optional!(b; "<DEFBREAK>");
    let e2 = b.expect("==");
    let name = optional!(b; l1, defbreak, "Identifier", e2, "<DEF>");
    let belch_expecting = b.action(|state| {
        belch_def(state);
        state.expecting = "Expression".to_owned();
        None
    });
    b.production(
        "Assumption",
        Some("Assumption"),
        parts![e1, keyword, name, belch_expecting, "Expression"],
        None,
    );

    // A label returns from AssumeProve after the labeled AssumeProve, which a choice expresses.
    let labeled = seq!(b; "Identifier", "<COLONCOLON>", "AssumeProve");
    let assume = choice!(b; "<ASSUME>", "<BOXASSUME>");
    let e1 = b.expect("Expression, Declaration, or AssumeProve");
    let item = get_assume_prove_item(b);
    let e2 = b.expect("PROVE or `,'");
    let e3 = b.expect("Expression, Declaration, or AssumeProve");
    let item2 = get_assume_prove_item(b);
    let e4 = b.expect("PROVE or `,'");
    let rest = zero_or_more!(b; "<COMMA>", e3, item2, e4);
    let prove = choice!(b; "<PROVE>", "<BOXPROVE>");
    let e5 = b.expect("Expression");
    let unlabeled = seq!(b; assume, e1, item, e2, rest, prove, e5, "Expression");
    let assume_prove = choice!(b; labeled, unlabeled);
    b.production(
        "AssumeProve",
        Some("Assume-Prove"),
        parts![assume_prove],
        None,
    );

    let e1 = b.expect("NEW, CONSTANT, VARIABLE, STATE, ACTION, or TEMPORAL");
    let constant = {
        let l1 = b.lookahead_amount(2);
        let l2 = b.lookahead_amount(2);
        let new_constant = seq!(b; l2, "<NEW>", "<CONSTANT>");
        let keyword = choice!(b; new_constant, "<NEW>", "<CONSTANT>");
        let e1 = b.expect("Constant declaration");
        let l3 = b.lookahead_amount(2);
        let check = b.action(|state| {
            let declaration = state.get_heir(2)?;
            (declaration.heirs.len() > 1).then(|| {
                format!(
                    "declared symbol with arguments before \\in at {}",
                    state.format_location(declaration.first, declaration.last)
                )
            })
        });
        let e2 = b.expect("Expression");
        let bound = optional!(b; "<IN>", check, e2, "Expression");
        let declaration = seq!(b; l3, "IdentDecl", bound);
        let declaration = choice!(b; declaration, "SomeFixDecl");
        seq!(b; l1, keyword, e1, declaration)
    };
    let variable = {
        let l1 = b.lookahead_amount(2);
        let new = optional!(b; "<NEW>");
        let e1 = b.expect("Identifier");
        seq!(b; l1, new, "<VARIABLE>", e1, "Identifier")
    };
    let other = {
        let l1 = b.lookahead_amount(2);
        let new = optional!(b; "<NEW>");
        let level = choice!(b; "<STATE>", "<ACTION>", "<TEMPORAL>");
        let e1 = b.expect("Declaration");
        let declaration = choice!(b; "IdentDecl", "SomeFixDecl");
        seq!(b; l1, new, level, e1, declaration)
    };
    let symbol = choice!(b; constant, variable, other);
    b.production(
        "NewSymb",
        Some("NEW symbol declaration"),
        parts![e1, symbol],
        None,
    );

    let e1 = b.expect("Expression");
    let bound = optional!(b; "<IN>", e1, "Expression");
    b.production("MaybeBound", Some("Domain binding"), parts![bound], None);

    let e1 = b.expect("THEOREM, PROPOSITION");
    let keyword = choice!(b; "<THEOREM>", "<PROPOSITION>");
    let e2 = b.expect("Identifier, Assume-Prove or Expression");
    let l1 = b.lookahead_amount(2);
    let e3 = b.expect("==");
    let name = optional!(b; l1, "Identifier", e3, "<DEF>");
    let belch_unit = belch(b);
    let l2 = b.lookahead_amount(3);
    let l3 = b.lookahead_semantic(|state| state.is_next_kind(&["ASSUME", "BOXASSUME"]));
    let assume_prove = seq!(b; l2, l3, "AssumeProve");
    let body = choice!(b; assume_prove, "Expression");
    let l4 = b.lookahead_semantic(begins_proof);
    let proof = optional!(b; l4, "Proof");
    b.production(
        "Theorem",
        Some("Theorem"),
        parts![e1, keyword, e2, name, belch_unit, body, proof],
        None,
    );

    let push_level = b.action(|state| {
        state.proof_levels.push(-1.0);
        None
    });
    let l1 = b.lookahead_semantic(|state| {
        state.is_next_kind(&["BY"]) || {
            let second = state.get_token(2);
            state.kind(second) == get_kind("BY")
        }
    });
    let by = seq!(b; l1, "UseOrHideOrBy");
    let l2 = b.lookahead_amount(2);
    let proof_keyword = optional!(b; "<PROOF>");
    let leaf = choice!(b; "<OBVIOUS>", "<OMITTED>");
    let terminal = seq!(b; l2, proof_keyword, leaf);
    let l3 = b.lookahead_amount(2);
    let proof_keyword = optional!(b; l3, "<PROOF>");
    let l4 = b.lookahead_semantic(|state| {
        let second = state.get_token(2);
        state.kind(second) != get_kind("QED")
    });
    let e1 = b.expect("a proof step");
    let steps = zero_or_more!(b; l4, "Step", e1);
    let structured = seq!(b; proof_keyword, steps, "QEDStep");
    let proof = choice!(b; by, terminal, structured);
    let pop_level = b.action(|state| {
        state.proof_levels.pop();
        None
    });
    b.production(
        "Proof",
        Some("Proof"),
        parts![push_level, proof, pop_level],
        None,
    );

    let proof_keyword = optional!(b; "<PROOF>");
    let terminal = set_terminal_proof(b, true);
    let only = optional!(b; "<ONLY>");
    let by = seq!(b; proof_keyword, "<BY>", terminal, only);
    let not_terminal = set_terminal_proof(b, false);
    let only = optional!(b; "<ONLY>");
    let use_unit = seq!(b; "<USE>", not_terminal, only);
    let not_terminal = set_terminal_proof(b, false);
    let hide = seq!(b; "<HIDE>", not_terminal);
    let keyword = choice!(b; by, use_unit, hide);
    let e1 = b.expect("an expression, `MODULE' or `DEF'");
    let item = get_use_item(b);
    let e2 = b.expect("MODULE or expression");
    let item2 = get_use_item(b);
    let after = b.action(|state| {
        state.expecting = if state.is_terminal_proof {
            "comma, DEF, or [.]"
        } else {
            "comma, DEF, or proof step"
        }
        .to_owned();
        None
    });
    let rest = zero_or_more!(b; "<COMMA>", e2, item2, after);
    let items = optional!(b; item, rest);
    let e3 = b.expect("MODULE or expression");
    let item3 = get_use_item(b);
    let e4 = b.expect("MODULE or expression");
    let item4 = get_use_item(b);
    let after = b.action(|state| {
        state.expecting = if state.is_terminal_proof {
            "comma or [.]"
        } else {
            "comma or proof step"
        }
        .to_owned();
        None
    });
    let rest = zero_or_more!(b; "<COMMA>", e4, item4, after);
    let definitions = optional!(b; "<DF>", e3, item3, rest);
    let end = b.action(|state| {
        if state.is_terminal_proof {
            state.expecting = "[.]".to_owned();
        }
        None
    });
    b.production(
        "UseOrHideOrBy",
        Some("UseOrHideOrBy"),
        parts![keyword, e1, items, definitions, end],
        None,
    );

    let e1 = b.expect("Step number");
    let start = step_start(b);
    let check = check_step_level(b, "QED step's number has bad level.");
    let e2 = b.expect("QED");
    let l1 = b.lookahead_semantic(begins_proof);
    let proof = optional!(b; l1, "Proof");
    b.production(
        "QEDStep",
        Some("QED step"),
        parts![e1, start, check, e2, "<QED>", proof],
        None,
    );

    let e1 = b.expect("Step number");
    let start = step_start(b);
    let check = check_step_level(b, "step's number has bad level.");
    let e2 = b.expect("proof step");
    let l1 = b.lookahead_semantic(|state| state.is_next_kind(&["USE", "HIDE"]));
    let use_unit = seq!(b; l1, "UseOrHideOrBy");
    let l2 = b.lookahead_semantic(|state| state.is_next_kind(&["INSTANCE"]));
    let instance = seq!(b; l2, "Instantiation");
    let l3 = b.lookahead_semantic(|state| state.is_next_kind(&["DEFBREAK", "DEFINE"]));
    let define = seq!(b; l3, "DefStep");
    let step = choice!(b;
        use_unit,
        instance,
        define,
        "HaveStep",
        "TakeStep",
        "WitnessStep",
        "PickStep",
        "CaseStep",
        "AssertStep",
    );
    let l4 = b.lookahead_semantic(begins_proof);
    let check_proof = b.action(|state| {
        let step = state.get_heir(1)?;
        if ["PickStep", "CaseStep", "AssertStep"].contains(&step.kind) {
            None
        } else {
            Some(format!(
                "{}: proof of step that does not take a proof.",
                state.format_location(step.first, step.last)
            ))
        }
    });
    let proof = optional!(b; l4, check_proof, "Proof");
    b.production(
        "Step",
        Some("Step"),
        parts![e1, start, check, e2, step, proof],
        None,
    );

    let define = optional!(b; "<DEFINE>");
    let l1 = b.lookahead_amount(2);
    let definitions = one_or_more!(b; l1, "OperatorOrFunctionDefinition");
    b.production(
        "DefStep",
        Some("DefStep"),
        parts![define, definitions],
        None,
    );

    let e1 = b.expect("expression");
    b.production(
        "HaveStep",
        Some("HaveStep"),
        parts!["<HAVE>", e1, "Expression"],
        None,
    );

    let e1 = b.expect("identifier");
    let more = zero_or_more!(b; "<COMMA>", "<IDENTIFIER>");
    let identifiers = seq!(b; "<IDENTIFIER>", more, "<IN>");
    let start = choice!(b; identifiers, "<LAB>");
    let l1 = lookahead_of!(b; [start]);
    let e2 = b.expect("comma or step");
    let e3 = b.expect("identifier or tuple of identifiers");
    let e4 = b.expect("comma or proof step");
    let rest = zero_or_more!(b; "<COMMA>", e3, "QuantBound", e4);
    let bounds = seq!(b; l1, "QuantBound", e2, rest);
    let e5 = b.expect("comma or proof step");
    let e6 = b.expect("identifier");
    let e7 = b.expect("comma or proof step");
    let rest = zero_or_more!(b; "<COMMA>", e6, "Identifier", e7);
    let identifiers = seq!(b; "Identifier", e5, rest);
    let take = choice!(b; bounds, identifiers);
    b.production(
        "TakeStep",
        Some("TakeStep"),
        parts!["<TAKE>", e1, take],
        None,
    );

    let e1 = b.expect("expression");
    let e2 = b.expect("expression");
    let e3 = b.expect("comma or colon");
    let rest = zero_or_more!(b; "<COMMA>", e2, "Expression", e3);
    b.production(
        "WitnessStep",
        Some("WitnessStep"),
        parts!["<WITNESS>", e1, "Expression", rest],
        None,
    );

    let e1 = b.expect("identifier");
    let more = zero_or_more!(b; "<COMMA>", "<IDENTIFIER>");
    let l1 = lookahead_of!(b; ["<IDENTIFIER>", more, "<COLON>"]);
    let e2 = b.expect("comma, or colon");
    let e3 = b.expect("identifier");
    let e4 = b.expect("comma or colon");
    let rest = zero_or_more!(b; "<COMMA>", e3, "Identifier", e4);
    let identifiers = seq!(b; l1, "Identifier", e2, rest);
    let e5 = b.expect("comma or colon");
    let e6 = b.expect("identifier or tuple of identifiers");
    let e7 = b.expect("comma or colon");
    let rest = zero_or_more!(b; "<COMMA>", e6, "QuantBound", e7);
    let bounds = seq!(b; "QuantBound", e5, rest);
    let pick = choice!(b; identifiers, bounds);
    let e8 = b.expect("expression");
    b.production(
        "PickStep",
        Some("PickStep"),
        parts!["<PICK>", e1, pick, "<COLON>", e8, "Expression"],
        None,
    );

    let e1 = b.expect("expression");
    b.production(
        "CaseStep",
        Some("CaseStep"),
        parts!["<CASE>", e1, "Expression"],
        None,
    );

    let e1 = b.expect("expression or ASSUME/PROVE");
    let suffices = optional!(b; "<SUFFICES>", e1);
    let l1 = b.lookahead_semantic(|state| state.is_next_kind(&["ASSUME", "BOXASSUME"]));
    let assume_prove = seq!(b; l1, "AssumeProve");
    let body = choice!(b; "Expression", assume_prove);
    b.production(
        "AssertStep",
        Some("AssertStep"),
        parts![suffices, body],
        None,
    );

    let expression =
        choice!(b; "ParenExpr", "BraceCases", "SBracketCases", "TupleOrAction", "FairnessExpr");
    b.production("ParenthesesExpression", None, parts![expression], None);

    let expression = choice!(b;
        "SomeQuant",
        "SomeTQuant",
        "IfThenElse",
        "Case",
        "LetIn",
        "UnboundOrBoundChoose",
    );
    b.production("OpenExpression", None, parts![expression], None);

    b.production("String", Some("String"), parts!["<STRING_LITERAL>"], None);

    let l1 = b.lookahead_amount(2);
    let fraction = optional!(b; l1, "<DOT>", "<NUMBER_LITERAL>");
    b.production("Number", None, parts!["<NUMBER_LITERAL>", fraction], None);

    let rest = zero_or_more!(b; "<COMMA>", "OpOrExpr");
    b.production(
        "OpArgs",
        Some("Optional Arguments"),
        parts!["<LBR>", "OpOrExpr", rest, "<RBR>"],
        None,
    );

    let operator = {
        let prefix = nonexp_prefix_operator(b);
        let infix = infix_operator(b);
        let postfix = postfix_operator(b);
        let operators = choice!(b; prefix, infix, postfix);
        let follows = b.tokens(kinds(&[
            "COMMA",
            "RBR",
            "DEFBREAK",
            "LOCAL",
            "INSTANCE",
            "THEOREM",
            "ASSUME",
            "END_MODULE",
            "SEPARATOR",
            "_BM0",
            "ASSUMPTION",
            "CONSTANT",
            "VARIABLE",
            "RECURSIVE",
        ]));
        let lookahead = lookahead_of!(b; 2, [operators, follows], above_current);
        let check = b.action(|state| {
            let token = state.token;
            let image = &state.tokens[token].image;
            (image == "\\X" || image == "\\times").then(|| {
                format!(
                    "{}: \\X may not be used as an infix operator.",
                    state.format_location(token, token)
                )
            })
        });
        let infix = seq!(b; "InfixOp", check);
        let operator = choice!(b; "NonExpPrefixOp", infix, "PostfixOp");
        seq!(b; lookahead, operator)
    };
    let l1 = lookahead_of!(b; ["<LAMBDA>"], above_current);
    let lambda = seq!(b; l1, "Lambda");
    let op_or_expr = choice!(b; operator, lambda, "Expression");
    b.production(
        "OpOrExpr",
        None,
        parts![op_or_expr],
        exit(|frame, _| {
            frame.node = frame.heirs.first().cloned();
            None
        }),
    );

    b.production(
        "ParenExpr",
        None,
        parts!["<LBR>", "Expression", "<RBR>"],
        None,
    );

    let quantifier = choice!(b; "<EXISTS>", "<FORALL>");
    let more = zero_or_more!(b; "<COMMA>", "<IDENTIFIER>");
    let l1 = lookahead_of!(b; ["<IDENTIFIER>", more, "<COLON>"]);
    let rest = zero_or_more!(b; "<COMMA>", "Identifier");
    let identifiers = seq!(b; l1, "Identifier", rest);
    let rest = zero_or_more!(b; "<COMMA>", "QuantBound");
    let bounds = seq!(b; "QuantBound", rest);
    let variables = choice!(b; identifiers, bounds);
    b.production(
        "SomeQuant",
        Some("Quantified form"),
        parts![quantifier, variables, "<COLON>", "Expression"],
        None,
    );

    let quantifier = choice!(b; "<T_EXISTS>", "<T_FORALL>");
    let rest = zero_or_more!(b; "<COMMA>", "Identifier");
    b.production(
        "SomeTQuant",
        Some("Bound Quantified Expression"),
        parts![quantifier, "Identifier", rest, "<COLON>", "Expression"],
        None,
    );

    let e1 = b.expect(", or \\in");
    let rest = zero_or_more!(b; "<COMMA>", "Identifier", e1);
    let identifiers = seq!(b; "Identifier", rest);
    let variables = choice!(b; "IdentifierTuple", identifiers);
    b.production(
        "QuantBound",
        Some("Quant Bound"),
        parts![variables, "<IN>", "Expression"],
        None,
    );

    let constant = {
        let l1 = b.lookahead_semantic(match_fcn_const);
        let variable = choice!(b; "IdentifierTuple", "Identifier");
        let e1 = b.expect("\\in");
        let e2 = b.expect("':', ',' or '}'");
        let colon = seq!(b; "<COLON>", "Expression");
        let commas = one_or_more!(b; "<COMMA>", "Expression");
        let after = choice!(b; colon, commas);
        let after = optional!(b; after);
        seq!(b; l1, variable, e1, "<IN>", "Expression", e2, after)
    };
    let enumeration = {
        let start = choice!(b; "IdentifierTuple", "<IDENTIFIER>");
        let l1 = lookahead_of!(b; [start, "<COMMA>"]);
        let rest = zero_or_more!(b; "<COMMA>", "Expression");
        seq!(b; l1, "Expression", rest)
    };
    let map = {
        let start = choice!(b; "IdentifierTuple", "<IDENTIFIER>");
        let l1 = lookahead_of!(b; [start, "<COLON>"]);
        let rest = zero_or_more!(b; "<COMMA>", "QuantBound");
        seq!(b; l1, "Expression", "<COLON>", "QuantBound", rest)
    };
    let general = {
        let check = b.action(|state| {
            let expression = state.get_heir(2)?;
            (expression.kind == "InfixExpr"
                && expression
                    .heirs
                    .get(1)
                    .is_some_and(|heir| state.tokens[heir.first].image == "\\in"))
            .then(|| {
                format!(
                    "Form {{a \\in b : c \\in d }}, at line {}, is not allowed",
                    state.tokens[state.token].begin_line
                )
            })
        });
        let rest = zero_or_more!(b; "<COMMA>", "QuantBound");
        let colon = seq!(b; "<COLON>", check, "QuantBound", rest);
        let commas = one_or_more!(b; "<COMMA>", "Expression");
        let after = choice!(b; colon, commas);
        let after = optional!(b; after);
        seq!(b; "Expression", after)
    };
    let cases = choice!(b; constant, enumeration, map, general);
    let cases = optional!(b; cases);
    b.production(
        "BraceCases",
        Some("Some { } form"),
        parts!["<LBC>", cases, "<RBC>"],
        None,
    );

    let function = {
        let l1 = b.lookahead_semantic(match_fcn_const);
        let rest = zero_or_more!(b; "<COMMA>", "QuantBound");
        seq!(b; l1, "QuantBound", rest, "<MAPTO>", "Expression", "<RSB>")
    };
    let record = {
        let l1 = lookahead_of!(b; ["<IDENTIFIER>", "<MAPTO>"]);
        let rest = zero_or_more!(b; "<COMMA>", "FieldVal");
        seq!(b; l1, "FieldVal", rest, "<RSB>")
    };
    let keyword_record = {
        let l1 = b.lookahead_semantic(|state| {
            let second = state.get_token(2);
            let first = state.get_token(1);
            state.kind(second) == get_kind("MAPTO") && is_field_name_kind(state.kind(first))
        });
        let rename = b.action(|state| {
            let token = state.get_token(1);
            state.tokens[token].kind = get_kind("IDENTIFIER");
            None
        });
        let rest = zero_or_more!(b; "<COMMA>", "FieldVal");
        seq!(b; l1, rename, "FieldVal", rest, "<RSB>")
    };
    let record_set = {
        let l1 = lookahead_of!(b; ["<IDENTIFIER>", "<COLON>"]);
        let rest = zero_or_more!(b; "<COMMA>", "FieldSet");
        seq!(b; l1, "FieldSet", rest, "<RSB>")
    };
    let expression = {
        let rest = zero_or_more!(b; "<COMMA>", "Expression");
        let application = b.action(|state| {
            let frame = state.frames.last_mut()?;
            frame.node = Some(create_node("FcnAppl", frame.heirs.clone()));
            state.last_operator = Some(state.operators.fcn.clone());
            None
        });
        let application = seq!(b; rest, "<RSB>", application);
        let set = seq!(b; "<ARROW>", "Expression", "<RSB>");
        let rest = zero_or_more!(b; "<COMMA>", "ExceptSpec");
        let except = seq!(b; "<EXCEPT>", "ExceptSpec", rest, "<RSB>");
        let action_unit = seq!(b; "<ARSB>", "ReducedExpression");
        let after = choice!(b; application, set, except, action_unit);
        seq!(b; "Expression", after)
    };
    let cases = choice!(b; function, record, keyword_record, record_set, expression);
    b.production(
        "SBracketCases",
        Some("Some [] Form"),
        parts!["<LSB>", cases],
        None,
    );

    b.production(
        "FieldVal",
        Some("Field Value"),
        parts!["Identifier", "<MAPTO>", "Expression"],
        None,
    );
    b.production(
        "FieldSet",
        Some("Field Set"),
        parts!["Identifier", "<COLON>", "Expression"],
        None,
    );

    let e1 = b.expect("= or ,");
    let components = one_or_more!(b; "ExceptComponent", e1);
    b.production(
        "ExceptSpec",
        Some("Except Spec"),
        parts!["<BANG>", components, "<EQUALS>", "Expression"],
        None,
    );

    let field = b.action(|state| {
        set_field_name(state);
        None
    });
    let dot = seq!(b; "<DOT>", field, "Identifier");
    let rest = zero_or_more!(b; "<COMMA>", "Expression");
    let index = seq!(b; "<LSB>", "Expression", rest, "<RSB>");
    let component = choice!(b; dot, index);
    b.production(
        "ExceptComponent",
        Some("Except Component"),
        parts![component],
        None,
    );

    let rest = zero_or_more!(b; "<COMMA>", "Expression");
    let items = optional!(b; "Expression", rest);
    let action_end = seq!(b; "<ARAB>", "ReducedExpression");
    let end = choice!(b; "<RAB>", action_end);
    b.production(
        "TupleOrAction",
        Some("Some << -- >> or >>_ Form"),
        parts!["<LAB>", items, end],
        None,
    );

    // The innermost NoOpExtension sets FairnessHook to its arguments, which end with ")".
    let l1 = b.lookahead_amount(2);
    let arguments = optional!(b; l1, "OpArgs");
    let bang = seq!(b; "<BANG>", "NoOpExtension");
    let hook = b.action(|state| {
        state.is_fairness_hooked = state.kind(state.token) == get_kind("RBR");
        None
    });
    let after = choice!(b; bang, hook);
    b.production(
        "NoOpExtension",
        None,
        parts!["Identifier", arguments, after],
        None,
    );

    let reduced =
        choice!(b; "NoOpExtension", "ParenExpr", "BraceCases", "SBracketCases", "TupleOrAction");
    b.production(
        "ReducedExpression",
        Some("restricted form of expression"),
        parts![reduced],
        None,
    );

    let start = b.action(|state| {
        state.is_fairness_hooked = false;
        state.is_fairness_parenthesized.push(false);
        None
    });
    let keyword = choice!(b; "<WF>", "<SF>");
    let l1 = b.lookahead_amount(2);
    let parenthesized = b.action(|state| {
        if let Some(last) = state.is_fairness_parenthesized.last_mut() {
            *last = true;
        }
        None
    });
    let argument = optional!(b; l1, "<LBR>", "Expression", "<RBR>", parenthesized);
    b.production(
        "FairnessExpr",
        Some("Fairness Expression"),
        parts![start, keyword, "ReducedExpression", argument],
        exit(|frame, state| {
            let is_parenthesized = state.is_fairness_parenthesized.pop().unwrap_or(false);
            if is_parenthesized || state.is_fairness_hooked {
                return None;
            }
            let first = &state.tokens[frame.heirs.first()?.first];
            Some(format!(
                "Ill-structured fairness expression at line {}, column {}",
                first.begin_line, first.begin_column
            ))
        }),
    );

    b.production(
        "IfThenElse",
        Some("IF THEN ELSE"),
        parts![
            "<IF>",
            "Expression",
            "<THEN>",
            "Expression",
            "<ELSE>",
            "Expression"
        ],
        None,
    );

    let l1 = b.lookahead_semantic(|state| {
        state.is_case_separator() && {
            let second = state.get_token(2);
            state.kind(second) != get_kind("OTHER")
        }
    });
    let arms = zero_or_more!(b; l1, "<CASESEP>", "CaseArm");
    let l2 = b.lookahead_semantic(State::is_case_separator);
    let other = optional!(b; l2, "<CASESEP>", "OtherArm");
    b.production(
        "Case",
        Some("CASE Expression"),
        parts!["<CASE>", "CaseArm", arms, other],
        None,
    );
    b.production(
        "CaseArm",
        Some("Case Arm"),
        parts!["Expression", "<ARROW>", "Expression"],
        None,
    );
    b.production(
        "OtherArm",
        Some("Case Other Arm"),
        parts!["<OTHER>", "<ARROW>", "Expression"],
        None,
    );
    b.production(
        "LetIn",
        Some("Case Other Arm"),
        parts!["<LET>", "LetDefinitions", "<LETIN>", "Expression"],
        None,
    );
    let definitions = choice!(b; "OperatorOrFunctionDefinition", "Recursive");
    let definitions = one_or_more!(b; definitions);
    b.production(
        "LetDefinitions",
        Some("Let Definitions"),
        parts![definitions],
        None,
    );

    let push_junction = b.action(|state| {
        let token = state.get_token(1);
        let junction = (state.kind(token), state.tokens[token].begin_column);
        state.junctions.push(junction);
        None
    });
    let l1 = lookahead_of!(b; ["<OR>"]);
    let mut or_list = parts![l1];
    or_list.extend(get_junction_list(b));
    let or_list = b.sequence(or_list);
    let l2 = lookahead_of!(b; ["<AND>"]);
    let mut and_list = parts![l2];
    and_list.extend(get_junction_list(b));
    let and_list = b.sequence(and_list);
    let list = choice!(b; or_list, and_list);
    let pop_junction = b.action(|state| {
        state.junctions.pop();
        None
    });
    b.production(
        "Junctions",
        Some("AND-OR Junction"),
        parts![push_junction, list, pop_junction],
        None,
    );

    let bullet = choice!(b; "<OR>", "<AND>");
    b.production(
        "JuncItem",
        Some("Junction Item"),
        parts![bullet, "Expression"],
        // TLAplusParser.checkIndentation.
        exit(|frame, state| {
            let item = get_misindented_node(state, frame.heirs.get(1)?)?;
            let bullet = frame.heirs.first()?.first;
            let end = frame.heirs.get(1)?.last;
            Some(format!(
                "Item at {} is not properly indented inside conjunction or  disjunction list item at {}",
                state.format_location(item.first, item.last),
                state.format_location(bullet, end)
            ))
        }),
    );

    let variable = choice!(b; "Identifier", "IdentifierTuple");
    b.production(
        "UnboundOrBoundChoose",
        Some("(Un)Bounded Choose"),
        parts!["<CHOOSE>", variable, "MaybeBound", "<COLON>", "Expression"],
        None,
    );

    let e1 = b.expect("Identifier");
    let e2 = b.expect("`,' or `:'");
    let e3 = b.expect("Identifier");
    let e4 = b.expect("`,' or `:'");
    let rest = zero_or_more!(b; "<COMMA>", e3, "Identifier", e4);
    let e5 = b.expect("Expression");
    b.production(
        "Lambda",
        Some("Lambda"),
        parts![
            "<LAMBDA>",
            e1,
            "Identifier",
            e2,
            rest,
            "<COLON>",
            e5,
            "Expression"
        ],
        None,
    );

    let start = b.action(|state| {
        state.operator_stacks.push(Vec::new());
        None
    });
    let prefix = get_prefix_operators(b);
    let operand = get_operand(b);
    b.production(
        "Expression",
        Some("Expression"),
        parts![start, prefix, operand],
        // OperatorStack.finalReduce, which pushes an operator that binds looser than any other,
        // whose node, null in Java, is never printed.
        exit(|frame, state| {
            let node = frame.heirs.first()?.clone();
            let void = state.operators.void.clone();
            state.operator_stacks.last_mut()?.push(StackElement {
                node,
                operator: Some(void),
            });
            let message = reduce_stack(state);
            frame.node = state
                .operator_stacks
                .last()
                .and_then(|stack| stack.first())
                .map(|element| element.node.clone());
            state.operator_stacks.pop();
            message
        }),
    );

    let junctions = {
        let start = choice!(b; "<AND>", "<OR>");
        // OperatorStack.preInEmptyTop.
        let l1 = lookahead_of!(b; [start], |state: &mut State| {
            state
                .operator_stacks
                .last()
                .and_then(|stack| stack.last())
                .is_none_or(|top| {
                    top.operator
                        .as_ref()
                        .is_some_and(|operator| operator.fix != super::Fix::Postfix)
                })
        });
        seq!(b; l1, "Junctions")
    };
    let head = choice!(b; junctions, "ParenthesesExpression", "PrimitiveExp");
    let push = push_operand(b);
    let postfix = {
        let l1 = lookahead_of!(b; ["PostfixOp"], above_current);
        let push = push_operator(b);
        seq!(b; l1, "PostfixOp", push)
    };
    let record = {
        let l1 = lookahead_of!(b; ["<DOT>"], above_current);
        let field = b.action(|state| {
            set_field_name(state);
            None
        });
        let l2 = b.lookahead_semantic(above_current);
        // OperatorStack.reduceRecord, which first applies a postfix operator on top.
        let reduce = b.action(|state| {
            let field = state.get_heir(1)?;
            let dot = state.get_heir(2)?;
            let mut stack = state.operator_stacks.pop()?;
            if stack.last()?.operator.is_some() {
                let top = stack.len();
                reduce_postfix(state, &mut stack, top);
            }
            let last = stack.len() - 1;
            stack[last] = StackElement {
                node: create_node(
                    "RecordComponent",
                    vec![stack[last].node.clone(), dot, field],
                ),
                operator: None,
            };
            state.operator_stacks.push(stack);
            None
        });
        seq!(b; l1, "<DOT>", field, l2, "Identifier", reduce)
    };
    let application = {
        let l1 = lookahead_of!(b; ["<LSB>"], above_current);
        let e1 = b.expect("function argument");
        // TLAplusParser.isGenOp, which holds of a function application.
        let push = push_on_stack(b, |node| node.kind == "FcnAppl");
        seq!(b; l1, e1, "SBracketCases", push)
    };
    let suffix = choice!(b; postfix, record, application);
    let suffixes = zero_or_more!(b; suffix);
    let infix = {
        let l1 = lookahead_of!(b; ["InfixOp"], above_current);
        let push = push_operator(b);
        let prefix = get_prefix_operators(b);
        let operand = get_operand(b);
        seq!(b; l1, "InfixOp", push, prefix, operand)
    };
    let label = {
        let l1 = lookahead_of!(b; ["<COLONCOLON>"], above_current);
        let check = b.action(|state| {
            let top = state.operator_stacks.last()?.last()?.node.clone();
            if !is_label(&top) {
                let token = state.token;
                return Some(format!(
                    "`::' at {} does not follow a label.",
                    state.format_location(token, token)
                ));
            }
            state.operator_stacks.last_mut()?.pop();
            None
        });
        // TLAplusParser.labelDoesNotChangeParse, given the operator parsed last.
        let labeled = b.action(|state| {
            let labeled = state.get_heir(1)?;
            let operator = state
                .operator_stacks
                .last()
                .and_then(|stack| stack.last())
                .and_then(|top| top.operator.clone());
            if (labeled.kind == "InfixExpr" || labeled.kind == "PostfixExpr")
                && let (Some(operator), Some(last)) = (&operator, &state.last_operator)
                && !is_looser(operator, last)
            {
                let label = state.get_heir(3)?;
                return Some(format!(
                    "Removing label at {} would change expression parsing.",
                    state.format_location(label.first, label.last)
                ));
            }
            let node = create_node(
                "Label",
                vec![state.get_heir(3)?, state.get_heir(2)?, labeled],
            );
            state.operator_stacks.last_mut()?.push(StackElement {
                node,
                operator: None,
            });
            None
        });
        seq!(b; l1, "<COLONCOLON>", check, "Expression", labeled)
    };
    let after = choice!(b; infix, label);
    let after = optional!(b; after);
    b.production(
        "ExtendableExpr",
        Some("ExtendableExpr"),
        parts![head, push, suffixes, after],
        None,
    );

    let string = {
        let l1 = lookahead_of!(b; ["String"], above_current);
        seq!(b; l1, "String")
    };
    let number = {
        let l1 = lookahead_of!(b; ["<NUMBER_LITERAL>"], above_current);
        seq!(b; l1, "Number")
    };
    let general = {
        let step = choice!(b; "<ProofStepLexeme>", "<ProofImplicitStepLexeme>");
        let check = b.action(|state| {
            let token = state.token;
            if state.get_proof_level() < 0.0 && state.proof_levels.len() <= 1 {
                return Some(format!(
                    "{}: Step number used outside proof.",
                    state.format_location(token, token)
                ));
            }
            (get_image_unit(state, token, 1) == Some(0x2b)).then(|| {
                format!(
                    "{}: <+> step number used in an expression.",
                    state.format_location(token, token)
                )
            })
        });
        let step = seq!(b; step, check);
        let l1 = lookahead_of!(b; ["<op_76>"]);
        let negation = seq!(b; l1, "NonExpPrefixOp");
        let head = choice!(b; "Identifier", step, "InfixOp", "PostfixOp", negation);
        let l2 = b.lookahead_amount(2);
        let arguments = optional!(b; l2, "OpArgs");
        let extensions = zero_or_more!(b; "BangExt");
        seq!(b; head, arguments, extensions)
    };
    let primitive = choice!(b; string, number, general);
    b.production(
        "PrimitiveExp",
        Some("Primitive expression"),
        parts![primitive],
        exit(|frame, _| {
            let head = frame.heirs.first()?.clone();
            frame.node = if head.kind == "String" || head.kind == "Number" {
                Some(head)
            } else if get_arguments(&frame.heirs).is_some() {
                Some(create_node("OpApplication", frame.heirs.clone()))
            } else if frame.heirs.len() == 1 {
                Some(create_node("GeneralId", frame.heirs.clone()))
            } else {
                None
            };
            None
        }),
    );

    let l1 = lookahead_of!(b; ["Identifier"], |state: &mut State| {
        let token = state.get_token(1);
        state.tokens[token].image != "@"
    });
    let identifier = seq!(b; l1, "Identifier");
    let name = choice!(b; identifier, "NonExpPrefixOp", "InfixOp", "PostfixOp");
    let l2 = b.lookahead_amount(2);
    let arguments = optional!(b; l2, "OpArgs");
    let named = seq!(b; name, arguments);
    let extension = choice!(b; named, "OpArgs", "StructOp");
    b.production(
        "BangExt",
        Some("Bang Extension"),
        parts!["<BANG>", extension],
        None,
    );

    let e1 = b.expect("`<<' , `>>' , `:' , `@' , or number");
    let l1 = b.lookahead_semantic(|state| {
        let token = state.get_token(1);
        state.tokens[token].image == "@"
    });
    let at = seq!(b; l1, "<IDENTIFIER>");
    let operator = choice!(b; "<LAB>", "<RAB>", "<COLON>", "Number", at);
    b.production(
        "StructOp",
        Some("StructOp"),
        parts![e1, operator],
        exit(|frame, state| {
            let number = frame.heirs.first()?;
            (number.kind == "Number" && number.heirs.len() > 1).then(|| {
                format!(
                    "Illegal structural term at {}",
                    state.format_location(number.first, number.last)
                )
            })
        }),
    );

    let start = choice!(b;
        "<CASE>",
        "<CHOOSE>",
        "<EXISTS>",
        "<FORALL>",
        "<IF>",
        "<LET>",
        "<T_EXISTS>",
        "<T_FORALL>",
    );
    b.production("OpenStart", None, parts![start], None);

    Grammar {
        units: builder.units,
        productions: builder.productions,
        analyses: RefCell::new(HashMap::new()),
    }
}

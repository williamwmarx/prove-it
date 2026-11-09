//! The report SANY's parser, TLAplusParser, gives for a module it fails to parse, as
//! `src/sany/parse-error.ts` emulates it. This interprets the grammar of javacc/tla+.jj the way
//! the code JavaCC generates from it runs: the productions, their lookahead specifications, and
//! the semantic actions that steer parsing or set the `expecting` message.
//! TLAplusParser.msgStackToString prints that message, the token the parser failed at, and the
//! productions it was in, so the interpreter must fail at the same token, in the same
//! productions, and must look as far ahead as JavaCC's jj_rescan_token does.

mod grammar;
mod lexer;

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::TlcVersion;
use crate::config::escape_lexeme;
use crate::tlc_data::SANY_OPERATOR_SYNONYMS;
use lexer::{KIND_COUNT, Lexer, Token, get_kind};

pub use lexer::get_sany_174_lexical_error;

type Predicate = Rc<dyn Fn(&mut State) -> bool>;
type Action = Rc<dyn Fn(&mut State) -> Option<String>>;
type Exit = Rc<dyn Fn(&mut Frame, &mut State) -> Option<String>>;

/// A set of token kinds.
#[derive(Clone, Default)]
struct KindSet([u64; KIND_COUNT.div_ceil(64)]);

impl KindSet {
    fn of(kinds: impl IntoIterator<Item = usize>) -> KindSet {
        let mut set = KindSet::default();
        for kind in kinds {
            set.insert(kind);
        }
        set
    }

    fn insert(&mut self, kind: usize) {
        self.0[kind / 64] |= 1 << (kind % 64);
    }

    fn has(&self, kind: usize) -> bool {
        kind < KIND_COUNT && self.0[kind / 64] & (1 << (kind % 64)) != 0
    }

    fn add_all(&mut self, other: &KindSet) {
        for (word, other) in self.0.iter_mut().zip(other.0) {
            *word |= other;
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Repeat {
    ZeroOrMore,
    OneOrMore,
    Optional,
}

/// A unit of the grammar. A lookahead first in a choice's alternative or in a loop's body decides
/// whether to take that expansion; elsewhere JavaCC checks only its semantic part.
enum Unit {
    Tokens(KindSet),
    Call(&'static str),
    Sequence(Vec<usize>),
    Choice(Vec<usize>),
    Repeat(Repeat, usize),
    /// Java code in a production, which may throw a ParseException with a message.
    Action(Action),
    Lookahead {
        amount: i64,
        expansion: Option<usize>,
        semantic: Option<Predicate>,
    },
}

struct Production {
    /// The name TLAplusParser.bpa pushes on the message stack, if the production calls it.
    message: Option<&'static str>,
    body: usize,
    /// Java code that runs after the production's epa.
    exit: Option<Exit>,
}

#[derive(Clone)]
struct Analysis {
    first: KindSet,
    is_nullable: bool,
    has_semantic_start: bool,
}

struct Grammar {
    units: Vec<Unit>,
    productions: HashMap<&'static str, Production>,
    analyses: RefCell<HashMap<usize, Analysis>>,
}

/// A SyntaxTreeNode: a token, or what a production matched, which spans from its first token to
/// its last.
struct Node {
    kind: &'static str,
    heirs: Vec<Rc<Node>>,
    first: usize,
    last: usize,
}

fn create_node(kind: &'static str, heirs: Vec<Rc<Node>>) -> Rc<Node> {
    let first = heirs.first().map_or(0, |heir| heir.first);
    let last = heirs.last().map_or(0, |heir| heir.last);
    Rc::new(Node {
        kind,
        heirs,
        first,
        last,
    })
}

/// The production being parsed: the nodes of what it has matched, and the node it returns if
/// that is not a node of its own kind over them.
#[derive(Default)]
struct Frame {
    heirs: Vec<Rc<Node>>,
    node: Option<Rc<Node>>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Fix {
    Prefix,
    Postfix,
    Infix,
    Nfix,
}

/// An Operator of Operators.CanonicalOperators. None of them is right-associative.
struct Operator {
    name: String,
    low: i64,
    high: i64,
    is_left_associative: bool,
    fix: Fix,
}

/// An OSelement of OperatorStack: an operand, or an operator with its node.
#[derive(Clone)]
struct StackElement {
    node: Rc<Node>,
    operator: Option<Rc<Operator>>,
}

/// A jj_2 call, which jj_rescan_token scans again if it looked past the current token: JJCalls.
#[derive(Clone, Copy)]
struct LookaheadCall {
    generation: i64,
    first: usize,
    amount: i64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Scan {
    Matched,
    Failed,
    Done,
}

/// JavaCC's amount for a LOOKAHEAD that gives an expansion but no amount.
const UNBOUNDED_AMOUNT: i64 = 2_147_483_647;

struct Operators {
    master: HashMap<String, Rc<Operator>>,
    tlc_174: HashMap<String, Rc<Operator>>,
    fcn: Rc<Operator>,
    void: Rc<Operator>,
}

fn create_operators() -> Operators {
    let mut canonical: Vec<(String, Rc<Operator>)> = Vec::new();
    let mut add = |fix: Fix, low: i64, high: i64, is_left_associative: bool, names: &[&str]| {
        for name in names {
            canonical.push((
                (*name).to_owned(),
                Rc::new(Operator {
                    name: (*name).to_owned(),
                    low,
                    high,
                    is_left_associative,
                    fix,
                }),
            ));
        }
    };
    add(Fix::Postfix, 160, 160, true, &["["]);
    add(Fix::Postfix, 150, 150, false, &["'", "^+", "^*", "^#"]);
    add(Fix::Prefix, 120, 120, false, &["-."]);
    add(Fix::Prefix, 80, 80, false, &["SUBSET", "UNION"]);
    add(Fix::Prefix, 90, 90, false, &["DOMAIN"]);
    add(
        Fix::Prefix,
        40,
        150,
        false,
        &["[]", "<>", "ENABLED", "UNCHANGED"],
    );
    add(Fix::Prefix, 40, 40, true, &["\\lnot"]);
    add(Fix::Nfix, 100, 130, true, &["\\times"]);
    add(Fix::Infix, 140, 140, false, &["^", "^^"]);
    add(
        Fix::Infix,
        130,
        130,
        false,
        &["/", "//", "\\oslash", "\\div"],
    );
    add(
        Fix::Infix,
        130,
        130,
        true,
        &[
            "*",
            "&&",
            "&",
            "**",
            "\\odot",
            "\\otimes",
            "\\star",
            "\\o",
            "\\bigcirc",
            "\\bullet",
        ],
    );
    add(Fix::Infix, 110, 110, true, &["-", "--", "\\ominus"]);
    add(Fix::Infix, 100, 110, true, &["|", "||", "%%"]);
    add(Fix::Infix, 100, 110, false, &["%"]);
    add(Fix::Infix, 100, 100, true, &["+", "++", "\\oplus"]);
    add(Fix::Infix, 90, 140, false, &["\\wr"]);
    add(
        Fix::Infix,
        90,
        130,
        true,
        &["$$", "$", "??", "##", "\\uplus", "\\sqcap", "\\sqcup"],
    );
    add(Fix::Infix, 90, 130, false, &["!!"]);
    add(Fix::Infix, 90, 90, false, &["...", ".."]);
    add(Fix::Infix, 80, 80, true, &["\\intersect", "\\union"]);
    add(Fix::Infix, 80, 80, false, &["\\"]);
    add(Fix::Infix, 70, 70, false, &["<:", ":>"]);
    add(Fix::Infix, 60, 60, true, &["@@"]);
    add(Fix::Infix, 50, 140, true, &["\\cdot"]);
    add(
        Fix::Infix,
        50,
        50,
        false,
        &[
            "=",
            "/=",
            "<",
            ">",
            "\\in",
            "\\notin",
            "\\leq",
            "\\geq",
            "\\subseteq",
            "\\subset",
            "\\supseteq",
            "\\supset",
            "\\sqsubseteq",
            "\\sqsubset",
            "\\sqsupseteq",
            "\\sqsupset",
            "\\prec",
            "\\preceq",
            "\\succ",
            "\\succeq",
            "\\sim",
            "\\simeq",
            "\\approx",
            "\\cong",
            "\\asymp",
            "\\doteq",
            "\\propto",
            "\\ll",
            "\\gg",
            "|-",
            "|=",
            "-|",
            "=|",
            ":=",
            "::=",
        ],
    );
    add(Fix::Infix, 30, 30, true, &["\\land", "\\lor"]);
    add(Fix::Infix, 20, 20, false, &["~>", "\\equiv", "-+->"]);
    add(Fix::Infix, 10, 10, false, &["=>"]);
    // Operators.getOperator, which knows an operator by its name or a synonym.
    let mut master: HashMap<String, Rc<Operator>> = canonical.iter().cloned().collect();
    for synonyms in SANY_OPERATOR_SYNONYMS {
        let Some(operator) = master.get(synonyms[0]).cloned() else {
            continue;
        };
        for synonym in &synonyms[1..] {
            master.insert((*synonym).to_owned(), operator.clone());
        }
    }
    // TLC 1.7.4's SANY read its operators from ConfigConstants, which gave these three 10-13.
    let mut tlc_174 = master.clone();
    for name in ["SUBSET", "UNION", "DOMAIN"] {
        tlc_174.insert(
            name.to_owned(),
            Rc::new(Operator {
                name: name.to_owned(),
                low: 100,
                high: 130,
                is_left_associative: false,
                fix: Fix::Prefix,
            }),
        );
    }
    // OperatorStack's fcnOp, which a function application's "[" pushes, and
    // Operator.VoidOperator, which OperatorStack.finalReduce pushes to reduce the whole stack.
    let fcn = master["["].clone();
    let void = Rc::new(Operator {
        name: "$$_void".to_owned(),
        low: 0,
        high: 0,
        is_left_associative: false,
        fix: Fix::Infix,
    });
    Operators {
        master,
        tlc_174,
        fcn,
        void,
    }
}

struct State {
    tokens: Vec<Token>,
    lexer: Lexer,
    lexical_error: Option<String>,
    operators: Rc<Operators>,
    is_174: bool,
    token: usize,
    /// jj_gen, which counts consumed tokens, and its value at the last failed jj_ntk switch.
    generation: i64,
    failed_switch_generation: i64,
    scan_position: usize,
    last_position: usize,
    remaining: i64,
    is_looking_ahead: bool,
    is_rescanning: bool,
    farthest_rescan: i64,
    /// The jj_2 calls of each lookahead site, in the order the sites first ran.
    calls: Vec<(usize, Vec<LookaheadCall>)>,
    expecting: String,
    messages: Vec<(&'static str, usize)>,
    module_name: Option<String>,
    junctions: Vec<(usize, i64)>,
    frames: Vec<Frame>,
    /// OperatorStack's stack of stacks, one for each Expression being parsed.
    operator_stacks: Vec<Vec<StackElement>>,
    last_operator: Option<Rc<Operator>>,
    proof_levels: Vec<f64>,
    is_terminal_proof: bool,
    /// Whether FairnessHook is set, which it is if the last NoOpExtension ended with arguments.
    is_fairness_hooked: bool,
    is_fairness_parenthesized: Vec<bool>,
    report: Option<String>,
}

impl State {
    fn get_operator(&self, name: &str) -> Option<Rc<Operator>> {
        let operators = if self.is_174 {
            &self.operators.tlc_174
        } else {
            &self.operators.master
        };
        operators.get(name).cloned()
    }

    fn get_next(&mut self, token: usize) -> usize {
        if let Some(next) = self.tokens[token].next {
            return next;
        }
        let read = match self.lexer.next_token() {
            Ok(read) => read,
            Err(error) => {
                self.lexical_error.get_or_insert(error);
                Token {
                    kind: get_kind("EOF"),
                    image: String::new(),
                    begin_line: 0,
                    begin_column: 0,
                    next: None,
                }
            }
        };
        self.tokens.push(read);
        let next = self.tokens.len() - 1;
        self.tokens[token].next = Some(next);
        next
    }

    /// TLAplusParser.getToken, which counts from the scan position while a semantic lookahead
    /// runs during a scan.
    fn get_token(&mut self, index: usize) -> usize {
        let mut token = if self.is_looking_ahead {
            self.scan_position
        } else {
            self.token
        };
        for _ in 0..index {
            token = self.get_next(token);
        }
        token
    }

    fn kind(&self, token: usize) -> usize {
        self.tokens[token].kind
    }

    fn is_next_kind(&mut self, names: &[&str]) -> bool {
        let next = self.get_token(1);
        let kind = self.kind(next);
        names.iter().any(|name| get_kind(name) == kind)
    }

    /// JunctionListContext.isAboveCurrent, for the next token by default.
    fn is_above_current(&mut self, column: Option<i64>) -> bool {
        let column = match column {
            Some(column) => column,
            None => {
                let next = self.get_token(1);
                self.tokens[next].begin_column
            }
        };
        self.junctions
            .last()
            .is_none_or(|junction| junction.1 < column)
    }

    fn is_new_bullet(&mut self) -> bool {
        let next = self.get_token(1);
        let (kind, column) = (self.kind(next), self.tokens[next].begin_column);
        self.junctions
            .last()
            .is_some_and(|junction| junction.1 == column && junction.0 == kind)
    }

    /// TLAplusParser.caseSep.
    fn is_case_separator(&mut self) -> bool {
        self.is_next_kind(&["CASESEP"]) && self.is_above_current(None)
    }

    /// SyntaxTreeNode.getLocation for the tokens first to last, as Location.toString prints it.
    fn format_location(&self, first: usize, last: usize) -> String {
        let (first, last) = (&self.tokens[first], &self.tokens[last]);
        format!(
            "line {}, col {} to line {}, col {} of module {}",
            first.begin_line,
            first.begin_column,
            last.begin_line,
            last.begin_column + last.image.encode_utf16().count() as i64 - 1,
            self.module_name.as_deref().unwrap_or("undefined")
        )
    }

    /// The node offset nodes back among those of what the production being parsed has matched.
    fn get_heir(&self, offset: usize) -> Option<Rc<Node>> {
        let heirs = &self.frames.last()?.heirs;
        heirs
            .len()
            .checked_sub(offset)
            .map(|index| heirs[index].clone())
    }

    fn get_proof_level(&self) -> f64 {
        self.proof_levels.last().copied().unwrap_or(-1.0)
    }
}

/// Operator.succ and Operator.prec: whether left binds tighter than right, or looser.
fn is_tighter(left: &Operator, right: &Operator) -> bool {
    left.low > right.high
}

fn is_looser(left: &Operator, right: &Operator) -> bool {
    left.high < right.low
}

/// Operators.getMixfix, which turns "-" into the prefix "-.".
fn get_mixfix(state: &State, operator: &Rc<Operator>) -> Option<Rc<Operator>> {
    if operator.fix == Fix::Prefix {
        return Some(operator.clone());
    }
    state
        .operators
        .master
        .get(&format!("{}.", operator.name))
        .cloned()
}

/// OperatorStack.reducePostfix: replaces the operand and postfix operator below index top with
/// their expression.
fn reduce_postfix(state: &State, stack: &mut Vec<StackElement>, top: usize) {
    let operand = stack[top - 2].node.clone();
    let postfix = stack[top - 1].clone();
    let is_fcn = postfix
        .operator
        .as_ref()
        .is_some_and(|operator| Rc::ptr_eq(operator, &state.operators.fcn));
    let node = if is_fcn {
        let mut heirs = vec![operand];
        heirs.extend(postfix.node.heirs.iter().cloned());
        create_node("FcnAppl", heirs)
    } else {
        create_node("PostfixExpr", vec![operand, postfix.node])
    };
    stack.splice(
        top - 2..top,
        [StackElement {
            node,
            operator: None,
        }],
    );
}

/// OperatorStack.reducePrefix and reduceInfix: replace the operator below the top of the stack
/// and its operands with their expression.
fn reduce_operator(stack: &mut Vec<StackElement>, operator: &Operator) {
    let top = stack.len() - 1;
    if operator.fix != Fix::Infix && operator.fix != Fix::Nfix {
        let node = create_node(
            "PrefixExpr",
            vec![stack[top - 2].node.clone(), stack[top - 1].node.clone()],
        );
        stack.splice(
            top - 2..top,
            [StackElement {
                node,
                operator: None,
            }],
        );
        return;
    }
    let left = stack[top - 3].node.clone();
    let is_times = operator.fix == Fix::Nfix;
    let mut heirs = if is_times && left.kind == "Times" {
        left.heirs.clone()
    } else {
        vec![left]
    };
    heirs.push(stack[top - 2].node.clone());
    heirs.push(stack[top - 1].node.clone());
    let node = create_node(if is_times { "Times" } else { "InfixExpr" }, heirs);
    stack.splice(
        top - 3..top,
        [StackElement {
            node,
            operator: None,
        }],
    );
}

/// OperatorStack.reduceStack, run when an operator is pushed: it reduces the operators below it
/// that bind tighter, and gives the message it throws where precedence can't order two operators,
/// or two operands follow each other. The grammar pushes an infix or postfix operator only after
/// an operand, except for a "-" that Expression takes for a prefix one, so the checks that reject
/// other orders never fail and are left out.
fn reduce_stack(state: &mut State) -> Option<String> {
    let mut stack = state.operator_stacks.pop()?;
    let message = reduce_stack_of(state, &mut stack);
    state.operator_stacks.push(stack);
    message
}

fn reduce_stack_of(state: &State, stack: &mut Vec<StackElement>) -> Option<String> {
    loop {
        let top = stack.len().checked_sub(1)?;
        let right = stack[top].clone();
        let right_operator = right.operator.clone()?;
        if right_operator.fix == Fix::Prefix {
            return None;
        }
        let middle = stack.get(top.checked_sub(1)?)?.clone();
        let left = top.checked_sub(2).map(|index| stack[index].clone());
        if middle
            .operator
            .as_ref()
            .is_some_and(|operator| operator.fix == Fix::Postfix)
        {
            reduce_postfix(state, stack, top);
            continue;
        }
        if let Some(middle_operator) = &middle.operator {
            let mixfix = get_mixfix(state, &right_operator)?;
            return is_tighter(middle_operator, &mixfix).then(|| {
                format!(
                    "\n  Precedence conflict between ops {} in block {} and {}.",
                    middle_operator.name,
                    state.format_location(middle.node.first, middle.node.last),
                    mixfix.name
                )
            });
        }
        let left = left?;
        let Some(left_operator) = left.operator.clone() else {
            return Some(format!(
                "Expression at location {} and expression at location {} follow each other without any intervening operator.",
                state.format_location(left.node.first, left.node.last),
                state.format_location(middle.node.first, middle.node.last)
            ));
        };
        if right_operator.fix == Fix::Postfix {
            if is_looser(&left_operator, &right_operator) {
                return None;
            }
            if !is_tighter(&left_operator, &right_operator) {
                return Some(format!(
                    "Precedence conflict between ops {} in block {} and {}.",
                    left_operator.name,
                    state.format_location(right.node.first, right.node.last),
                    right_operator.name
                ));
            }
            reduce_operator(stack, &left_operator);
            continue;
        }
        let mixfix = get_mixfix(state, &left_operator);
        let operator = match mixfix {
            Some(mixfix) if top == 2 || stack[top - 3].operator.is_some() => mixfix,
            _ => left_operator.clone(),
        };
        if is_looser(&operator, &right_operator) {
            return None;
        }
        if !is_tighter(&operator, &right_operator)
            && !(Rc::ptr_eq(&operator, &right_operator) && operator.is_left_associative)
        {
            return Some(format!(
                "\n  Precedence conflict between ops {} in block {} and {}.",
                operator.name,
                state.format_location(left.node.first, left.node.last),
                right_operator.name
            ));
        }
        if operator.fix != Fix::Postfix {
            reduce_operator(stack, &operator);
            continue;
        }
        let location = state.format_location(left.node.first, left.node.last);
        let left_line = state.tokens[left.node.first].begin_line;
        let middle_line = state.tokens[middle.node.first].begin_line;
        if left_line < middle_line && right_operator.name == "=" {
            return Some(format!(
                "\n  *** Hint *** You may have mistyped ==\n  Illegal combination of operators {} in block {location} and =.",
                operator.name
            ));
        }
        return Some(if Rc::ptr_eq(&right_operator, &state.operators.void) {
            format!("\n Error following expression at  {location}, missing operator or separator.")
        } else {
            format!(
                "\n  Illegal combination of operators {} in block {location} and {}.",
                operator.name, right_operator.name
            )
        });
    }
}

impl Grammar {
    fn get_production(&self, name: &str) -> &Production {
        &self.productions[name]
    }

    /// What JavaCC's ParseEngine.genFirstSet and Semanticize.emptyExpansionExists compute: the
    /// tokens an expansion can start with, whether it can match nothing, and whether its start
    /// passes a semantic lookahead, which makes JavaCC decide by a jj_2 call instead of a switch.
    fn analyze(&self, unit: usize) -> Analysis {
        if let Some(cached) = self.analyses.borrow().get(&unit) {
            return cached.clone();
        }
        let mut analysis = Analysis {
            first: KindSet::default(),
            is_nullable: true,
            has_semantic_start: false,
        };
        let add = |inner: usize, analysis: &mut Analysis| {
            let inner = self.analyze(inner);
            analysis.first.add_all(&inner.first);
            analysis.has_semantic_start |= inner.has_semantic_start;
            inner.is_nullable
        };
        match &self.units[unit] {
            Unit::Tokens(kinds) => {
                analysis.first = kinds.clone();
                analysis.is_nullable = false;
            }
            Unit::Call(name) => analysis = self.analyze(self.get_production(name).body),
            Unit::Lookahead { semantic, .. } => analysis.has_semantic_start = semantic.is_some(),
            Unit::Sequence(units) => {
                analysis.has_semantic_start = units.first().is_some_and(|head| {
                    matches!(
                        &self.units[*head],
                        Unit::Lookahead {
                            semantic: Some(_),
                            ..
                        }
                    )
                });
                analysis.is_nullable = units.iter().enumerate().all(|(index, inner)| {
                    (index == 0 && matches!(self.units[*inner], Unit::Lookahead { .. }))
                        || add(*inner, &mut analysis)
                });
            }
            Unit::Choice(alternatives) => {
                let mut is_nullable = false;
                for alternative in alternatives {
                    is_nullable |= add(*alternative, &mut analysis);
                }
                analysis.is_nullable = is_nullable;
            }
            Unit::Repeat(repeat, body) => {
                analysis.is_nullable = add(*body, &mut analysis) || *repeat != Repeat::OneOrMore;
            }
            Unit::Action(_) => {}
        }
        self.analyses.borrow_mut().insert(unit, analysis.clone());
        analysis
    }

    fn evaluate_semantic(&self, state: &mut State, semantic: &Predicate) -> bool {
        state.is_looking_ahead = true;
        let is_passed = semantic(state);
        state.is_looking_ahead = false;
        is_passed
    }

    /// jj_scan_token, which also records how far past the current token jj_rescan_token scans,
    /// the length of the longest token sequence the ParseException expects.
    fn scan_token(&self, state: &mut State, kinds: &KindSet) -> Scan {
        if state.scan_position == state.last_position {
            state.remaining -= 1;
            state.last_position = state.get_next(state.scan_position);
        }
        state.scan_position = state.get_next(state.scan_position);
        if state.is_rescanning {
            let mut position = 0;
            let mut token = Some(state.token);
            while let Some(current) = token {
                if current == state.scan_position {
                    break;
                }
                position += 1;
                token = state.tokens[current].next;
            }
            if token.is_some() && position < 100 {
                state.farthest_rescan = state.farthest_rescan.max(position);
            }
        }
        if !kinds.has(state.kind(state.scan_position)) {
            return Scan::Failed;
        }
        if state.remaining == 0 && state.scan_position == state.last_position {
            Scan::Done
        } else {
            Scan::Matched
        }
    }

    /// The jj_3 routines, which match an expansion without running its actions. A loop or option
    /// skips its body's lookahead, but a choice checks the semantic part of each alternative's.
    fn scan(&self, state: &mut State, unit: usize) -> Scan {
        match &self.units[unit] {
            Unit::Tokens(kinds) => self.scan_token(state, kinds),
            Unit::Call(name) => self.scan(state, self.get_production(name).body),
            Unit::Action(_) => Scan::Matched,
            Unit::Lookahead { semantic, .. } => match semantic {
                Some(semantic) if !self.evaluate_semantic(state, semantic) => Scan::Failed,
                _ => Scan::Matched,
            },
            Unit::Sequence(units) => {
                for (index, inner) in units.iter().enumerate() {
                    if index == 0 && matches!(self.units[*inner], Unit::Lookahead { .. }) {
                        continue;
                    }
                    let result = self.scan(state, *inner);
                    if result != Scan::Matched {
                        return result;
                    }
                }
                Scan::Matched
            }
            Unit::Choice(alternatives) => {
                let start = state.scan_position;
                for alternative in alternatives {
                    let head_semantic = match &self.units[*alternative] {
                        Unit::Sequence(units) => {
                            units.first().and_then(|head| match &self.units[*head] {
                                Unit::Lookahead { semantic, .. } => semantic.clone(),
                                _ => None,
                            })
                        }
                        _ => None,
                    };
                    let is_passed = match &head_semantic {
                        None => true,
                        Some(semantic) => self.evaluate_semantic(state, semantic),
                    };
                    let result = if is_passed {
                        self.scan(state, *alternative)
                    } else {
                        Scan::Failed
                    };
                    if result != Scan::Failed {
                        return result;
                    }
                    state.scan_position = start;
                }
                Scan::Failed
            }
            Unit::Repeat(repeat, body) => {
                let start = state.scan_position;
                let first = self.scan(state, *body);
                if first == Scan::Failed {
                    state.scan_position = start;
                    return if *repeat == Repeat::OneOrMore {
                        Scan::Failed
                    } else {
                        Scan::Matched
                    };
                }
                if first == Scan::Done || *repeat == Repeat::Optional {
                    return first;
                }
                loop {
                    let iteration_start = state.scan_position;
                    let result = self.scan(state, *body);
                    if result == Scan::Done {
                        return result;
                    }
                    if result == Scan::Failed {
                        state.scan_position = iteration_start;
                        return Scan::Matched;
                    }
                }
            }
        }
    }

    /// A jj_2 call, which scans expansion with a budget of amount new tokens. It saves the call
    /// for jj_rescan_token as jj_save does, over a call of the same site that can't be rescanned.
    fn scan_ahead(&self, state: &mut State, amount: i64, expansion: usize) -> bool {
        state.remaining = amount;
        state.scan_position = state.token;
        state.last_position = state.token;
        let is_matched = self.scan(state, expansion) != Scan::Failed;
        let call = LookaheadCall {
            generation: state.generation + amount - state.remaining,
            first: state.token,
            amount,
        };
        let generation = state.generation;
        let index = match state.calls.iter().position(|(site, _)| *site == expansion) {
            Some(index) => index,
            None => {
                state.calls.push((expansion, Vec::new()));
                state.calls.len() - 1
            }
        };
        let chain = &mut state.calls[index].1;
        match chain
            .iter()
            .position(|saved| saved.generation <= generation)
        {
            Some(stale) => chain[stale] = call,
            None => chain.push(call),
        }
        is_matched
    }

    /// The index of the alternative that the generated code's lookahead checks choose, or none.
    /// As ParseEngine.buildLookaheadChecker builds them, a check is the semantic lookahead alone
    /// where no tokens are needed, a jj_ntk switch where one token decides, and a jj_2 call
    /// otherwise.
    fn decide(&self, state: &mut State, alternatives: &[usize]) -> Option<usize> {
        alternatives.iter().position(|alternative| {
            let explicit = match &self.units[*alternative] {
                Unit::Sequence(units) => units.first().and_then(|head| match &self.units[*head] {
                    Unit::Lookahead {
                        amount,
                        expansion,
                        semantic,
                    } => Some((*amount, *expansion, semantic.clone())),
                    _ => None,
                }),
                _ => None,
            };
            let (amount, expansion, semantic) = match explicit {
                Some((amount, expansion, semantic)) => {
                    (amount, expansion.unwrap_or(*alternative), semantic)
                }
                None => (1, *alternative, None),
            };
            let analysis = self.analyze(expansion);
            if amount == 0 || analysis.is_nullable {
                return semantic.is_none_or(|semantic| semantic(state));
            }
            if amount == 1 && semantic.is_none() && !analysis.has_semantic_start {
                let next = state.get_token(1);
                if analysis.first.has(state.kind(next)) {
                    return true;
                }
                state.failed_switch_generation = state.generation;
                return false;
            }
            self.scan_ahead(state, amount, expansion)
                && semantic.is_none_or(|semantic| semantic(state))
        })
    }

    /// ParseExceptionExtended.getShortMessage for the ParseException that
    /// generateParseException builds, which shows as many tokens as the longest token sequence it
    /// expects. A rescan that finishes its lookahead ends the rescans of its site.
    fn get_encountered(&self, state: &mut State) -> String {
        state.is_rescanning = true;
        let calls = state.calls.clone();
        for (expansion, chain) in calls {
            let generation = state.generation;
            for call in chain.iter().filter(|saved| saved.generation > generation) {
                state.remaining = call.amount;
                state.scan_position = call.first;
                state.last_position = call.first;
                if self.scan(state, expansion) == Scan::Done {
                    break;
                }
            }
        }
        state.is_rescanning = false;
        let length = i64::from(state.failed_switch_generation == state.generation)
            .max(state.farthest_rescan);
        let mut images: Vec<String> = Vec::new();
        let next = state.get_next(state.token);
        let mut token = next;
        for index in 0..length {
            if state.kind(token) == get_kind("EOF") {
                images.push("<EOF>".to_owned());
                break;
            }
            images.push(state.tokens[token].image.clone());
            // SANY's message follows the tokens the parser has read, without reading another.
            if index < length - 1 {
                token = state.get_next(token);
            }
        }
        format!(
            "Encountered \"{}\" at line {}, column {} and token \"{}\" ",
            images.join(" "),
            state.tokens[next].begin_line,
            state.tokens[next].begin_column,
            escape_lexeme(&state.tokens[state.token].image)
        )
    }

    /// Records TLAplusParser.msgStackToString's report, without its "***Parse Error***" heading.
    fn fail(&self, state: &mut State, message: Option<String>) -> bool {
        let expecting = if state.expecting.is_empty() {
            String::new()
        } else {
            format!("Was expecting \"{}\"\n", state.expecting)
        };
        let message = message.unwrap_or_else(|| self.get_encountered(state));
        let stack: String = state
            .messages
            .iter()
            .rev()
            .take(5)
            .map(|(name, token)| {
                let token = &state.tokens[*token];
                format!(
                    "{name} starting at line {}, column {}.\n",
                    token.begin_line, token.begin_column
                )
            })
            .collect();
        state.report = Some(format!(
            "{expecting}{message}\n\nResidual stack trace follows:\n{stack}"
        ));
        false
    }

    fn consume(&self, state: &mut State, kinds: &KindSet) -> bool {
        let next = state.get_next(state.token);
        if !kinds.has(state.kind(next)) {
            state.failed_switch_generation = state.generation;
            return self.fail(state, None);
        }
        state.token = next;
        state.generation += 1;
        if let Some(frame) = state.frames.last_mut() {
            frame.heirs.push(Rc::new(Node {
                kind: "token",
                heirs: Vec::new(),
                first: next,
                last: next,
            }));
        }
        true
    }

    /// Parses a production, and adds the node it returns to those of the production that called
    /// it.
    fn parse_production(&self, state: &mut State, name: &'static str) -> bool {
        let production = self.get_production(name);
        if let Some(message) = production.message {
            let token = state.get_token(1);
            state.messages.push((message, token));
            state.expecting.clear();
        }
        state.frames.push(Frame::default());
        if !self.parse(state, production.body) {
            return false;
        }
        let mut frame = state.frames.pop().unwrap_or_default();
        if production.message.is_some() {
            state.messages.pop();
            state.expecting.clear();
        }
        if let Some(exit) = &production.exit
            && let Some(message) = exit(&mut frame, state)
        {
            return self.fail(state, Some(message));
        }
        let node = match frame.node {
            Some(node) => Some(node),
            None if frame.heirs.is_empty() => None,
            None => Some(create_node(name, frame.heirs)),
        };
        if let (Some(node), Some(parent)) = (node, state.frames.last_mut()) {
            parent.heirs.push(node);
        }
        true
    }

    /// Runs the parse-mode code JavaCC generates for unit. It returns false once a
    /// ParseException's report is recorded.
    fn parse(&self, state: &mut State, unit: usize) -> bool {
        match &self.units[unit] {
            Unit::Tokens(kinds) => self.consume(state, kinds),
            Unit::Call(name) => self.parse_production(state, name),
            Unit::Action(run) => match run(state) {
                None => true,
                Some(message) => self.fail(state, Some(message)),
            },
            Unit::Lookahead { semantic, .. } => match semantic {
                Some(semantic) if !semantic(state) => self.fail(state, None),
                _ => true,
            },
            Unit::Sequence(units) => units.iter().enumerate().all(|(index, inner)| {
                (index == 0 && matches!(self.units[*inner], Unit::Lookahead { .. }))
                    || self.parse(state, *inner)
            }),
            Unit::Choice(alternatives) => match self.decide(state, alternatives) {
                None => self.fail(state, None),
                Some(index) => self.parse(state, alternatives[index]),
            },
            Unit::Repeat(repeat, body) => {
                if *repeat == Repeat::OneOrMore && !self.parse(state, *body) {
                    return false;
                }
                if *repeat == Repeat::Optional {
                    return self.decide(state, &[*body]).is_none() || self.parse(state, *body);
                }
                while self.decide(state, &[*body]) == Some(0) {
                    if !self.parse(state, *body) {
                        return false;
                    }
                }
                true
            }
        }
    }
}

/// What SANY reports for a module its lexer or parser rejects, or none if it accepts the module.
pub fn get_sany_parse_error(source: &str, version: TlcVersion) -> Option<String> {
    let grammar = grammar::create_grammar();
    let start = Token {
        kind: get_kind("EOF"),
        image: String::new(),
        begin_line: 0,
        begin_column: 0,
        next: None,
    };
    let mut state = State {
        tokens: vec![start],
        lexer: Lexer::new(source),
        lexical_error: None,
        operators: Rc::new(create_operators()),
        is_174: version == TlcVersion::V1_7_4,
        token: 0,
        generation: 0,
        failed_switch_generation: -1,
        scan_position: 0,
        last_position: 0,
        remaining: 0,
        is_looking_ahead: false,
        is_rescanning: false,
        farthest_rescan: 0,
        calls: Vec::new(),
        expecting: "nothing".to_owned(),
        messages: Vec::new(),
        module_name: None,
        junctions: Vec::new(),
        frames: Vec::new(),
        operator_stacks: Vec::new(),
        last_operator: None,
        proof_levels: Vec::new(),
        is_terminal_proof: false,
        is_fairness_hooked: false,
        is_fairness_parenthesized: Vec::new(),
        report: None,
    };
    let is_parsed = grammar.parse_production(&mut state, "CompilationUnit");
    if state.lexical_error.is_some() {
        return state.lexical_error;
    }
    if is_parsed {
        return None;
    }
    state
        .report
        .map(|report| format!("***Parse Error***\n{report}"))
}

//! The SMT-LIB that tlapm's encoder writes (`backend/smtlib.ml`, ported in the obligations crate's
//! `smt` module), which is all the solver decides, read as Z3 4.8.9 reads it under the logic the
//! script sets. Z3 reads more, with errors and warnings after which it reads on, drops what it
//! couldn't read and answers; tlapm never sends that: over the 10,376 smt and z3 inputs of the
//! decider corpus Z3 reports no error. A script outside this subset is declined, never answered,
//! so that the port never answers a script Z3 read otherwise.
//!
//! The subset, read from the encoder, from what Z3's parser (`smt2parser.cpp`, `cmd_context.cpp`,
//! `pattern_validation.cpp`) rejects or drops, and checked against every input of the corpus:
//! - commands, in this order: an optional `(set-option :rlimit <numeral>)` (tlapm's rlimit, which
//!   the decision honours as a step limit: the port's steps are Z3's rlimit units),
//!   `(set-logic <symbol>)`, then `(declare-sort Idv 0)`, `(declare-fun <name> (<sort>*) <sort>)`
//!   and `(assert <term>)` in any order, `(check-sat)`, and an optional `(exit)` last;
//! - a name, declared or bound, starts with `smt__` and is made of letters, digits, `_`, `,` and
//!   `~` (format_name spells every other character Z3 reads in a symbol), so that none is `true`,
//!   `false` or an operator; a function is declared once, before it is used; the sorts are `Bool`,
//!   `Int` and `Idv`;
//! - a term is well sorted, as Z3 checks: `true`, `false`, a numeral without leading zeros, a
//!   bound name or a declared constant (a bound name hides a declared one, as in Z3), an
//!   application of a declared function to its domain, of `=`, `=>`, `distinct`, `<=`, `>=`, `<`,
//!   `>`, `div`, `mod`, `not`, `ite`, `and`, `or`, `+`, `-` or `*` to as many terms of the sorts
//!   the encoder gives them, or a `forall` or `exists` over distinct sorted names around a Bool;
//!   a bound name is never applied, which Z3 rejects;
//! - an assertion may name its Bool term once, `(! <term> :named |<name>|)`, with a quoted name of
//!   printable ASCII that names nothing else: no other assertion and no symbol of the script, which
//!   Z3 would reject or read as the named term;
//! - a quantifier's body may carry patterns, `(! <term> :pattern (<term>+)+)`, each Z3 keeps: its
//!   terms are applications of declared functions to the quantifier's own bound names, declared
//!   constants, numerals and such applications, and together hold every name it binds. The one
//!   exception is the encoder's `:pattern (<declared constant>)`, which Z3 and the port both drop;
//! - `;` comments.
//!
//! The logic, `UFNIA` unless tlapm runs with `--smt-logic`, sets the checks Z3 makes on each
//! declaration and assertion (`cmd_context/check_logic.cpp`, through `cmd_context::insert` and
//! `assert_expr`): a logic its table names allows or refuses uninterpreted functions,
//! integers, quantifiers and nonlinear arithmetic; a logic the table doesn't name gets no check,
//! as one Z3 doesn't support at all, which it answers `unsupported` to and reads on from. A
//! declaration or assertion that fails a check is an error Z3 prints and reads past, so it is
//! dropped, and an assertion that names a dropped function is dropped as the parser's error. Z3
//! decides the survivors with the tactic of the logic (`smt_strategic_solver.cpp`); the port runs
//! UFNIA's, so under another logic it decides only what every tactic answers alike: no assertion
//! (sat), or a quantifier-free script without integers, which congruence closure settles. It
//! declines the rest, an rlimit under such a logic (the steps aren't Z3's), the comparisons a
//! difference logic checks (`check_diff_predicate`) and a numeral where a logic of reals reads it
//! as a real (`smt_logics::logic_has_reals_only`).

use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::ops::Range;

// A token: a parenthesis, a plain symbol, a quoted symbol's text, or a keyword.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Token<'a> {
    Open,
    Close,
    Symbol(&'a str),
    Quoted(&'a str),
}

// A token and the byte it starts at.
struct Lexeme<'a> {
    token: Token<'a>,
    start: usize,
}

enum Node<'a> {
    Atom(Token<'a>),
    List(Vec<usize>),
}

fn is_name_char(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b',' | b'~')
}

fn is_operator_char(byte: u8) -> bool {
    matches!(byte, b'=' | b'>' | b'<' | b'+' | b'-' | b'*' | b'!' | b':')
}

fn tokenize(text: &str) -> Result<Vec<Lexeme<'_>>, String> {
    let bytes = text.as_bytes();
    let mut lexemes = Vec::new();
    let mut position = 0;
    while position < bytes.len() {
        let byte = bytes[position];
        let start = position;
        let token = match byte {
            b';' => {
                position = bytes[position..]
                    .iter()
                    .position(|current| *current == b'\n')
                    .map_or(bytes.len(), |offset| position + offset + 1);
                continue;
            }
            b' ' | b'\n' | b'\t' | b'\r' => {
                position += 1;
                continue;
            }
            b'(' => {
                position += 1;
                Token::Open
            }
            b')' => {
                position += 1;
                Token::Close
            }
            b'|' => {
                let length = bytes[position + 1..]
                    .iter()
                    .position(|current| *current == b'|')
                    .ok_or("an unterminated quoted symbol")?;
                let quoted = &text[position + 1..position + 1 + length];
                if !quoted
                    .bytes()
                    .all(|current| (b' '..=b'~').contains(&current) && current != b'\\')
                {
                    return Err("a quoted symbol outside printable ASCII".into());
                }
                position += length + 2;
                Token::Quoted(quoted)
            }
            _ => {
                while position < bytes.len()
                    && (is_name_char(bytes[position]) || is_operator_char(bytes[position]))
                {
                    position += 1;
                }
                if position == start
                    || position < bytes.len()
                        && !matches!(
                            bytes[position],
                            b' ' | b'\n' | b'\t' | b'\r' | b'(' | b')' | b';'
                        )
                {
                    return Err(format!(
                        "the character {:?}",
                        text[position..].chars().next().unwrap_or(' ')
                    ));
                }
                Token::Symbol(&text[start..position])
            }
        };
        lexemes.push(Lexeme { token, start });
    }
    Ok(lexemes)
}

// The nodes, and each command with the bytes it spans.
type Commands = Vec<(usize, Range<usize>)>;

fn read<'a>(lexemes: &[Lexeme<'a>]) -> Result<(Vec<Node<'a>>, Commands), String> {
    let mut nodes = Vec::new();
    let mut commands = Vec::new();
    let mut stack: Vec<(Vec<usize>, usize)> = Vec::new();
    for lexeme in lexemes {
        let node = match lexeme.token {
            Token::Open => {
                stack.push((Vec::new(), lexeme.start));
                continue;
            }
            Token::Close => {
                let Some((list, start)) = stack.pop() else {
                    return Err("an unbalanced parenthesis".into());
                };
                if stack.is_empty() {
                    commands.push((nodes.len(), start..lexeme.start + 1));
                }
                Node::List(list)
            }
            atom => {
                if stack.is_empty() {
                    return Err("a command that is not a list".into());
                }
                Node::Atom(atom)
            }
        };
        if let Some(top) = stack.last_mut() {
            top.0.push(nodes.len());
        }
        nodes.push(node);
    }
    if !stack.is_empty() {
        return Err("a command the text ends inside".into());
    }
    Ok((nodes, commands))
}

fn is_numeral(text: &str) -> bool {
    text == "0"
        || text.starts_with(|first: char| ('1'..='9').contains(&first))
            && text.bytes().all(|byte| byte.is_ascii_digit())
}

fn is_name(text: &str) -> bool {
    text.starts_with("smt__") && text.bytes().all(is_name_char)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Sort {
    Bool,
    Int,
    Idv,
}

// The checks Z3's check_logic makes under a logic, of the theories the encoder's sorts and
// operators can meet: arrays, bit-vectors, datatypes and the rest of its table never do. Reals
// enter only as the numerals a logic of reals reads.
#[derive(Clone, Copy)]
struct Logic {
    uf: bool,
    ints: bool,
    quantifiers: bool,
    nonlinear: bool,
    // The logic allows only difference arithmetic, which check_diff_predicate checks.
    diff: bool,
    // smt_logics::logic_has_reals_only: Z3 reads a numeral as a real.
    numeral_as_real: bool,
    // Not in check_logic's table: Z3 checks nothing.
    unknown: bool,
}

impl Logic {
    // check_logic::set_logic, Z3 4.8.9: uninterpreted functions, integers, quantifiers, nonlinear
    // arithmetic and difference arithmetic per logic.
    fn of(name: &str) -> Logic {
        let flags = match name {
            "AUFLIA" | "AUFLIRA" => Some((true, true, true, false, false)),
            "AUFNIRA" | "UFNIA" => Some((true, true, true, true, false)),
            "LRA" => Some((false, false, true, false, false)),
            "QF_ABV" | "QF_AX" | "QF_BV" | "QF_LRA" => Some((false, false, false, false, false)),
            "QF_AUFBV" | "QF_UFBV" | "QF_DT" | "QF_UF" | "QF_UFLRA" | "SMTFD" => {
                Some((true, false, false, false, false))
            }
            "QF_AUFLIA" | "QF_UFLIA" | "QF_S" | "QF_SLIA" => {
                Some((true, true, false, false, false))
            }
            "QF_IDL" => Some((false, true, false, false, true)),
            "QF_RDL" => Some((false, false, false, false, true)),
            "QF_LIA" => Some((false, true, false, false, false)),
            "QF_NIA" => Some((false, true, false, true, false)),
            "QF_NRA" => Some((false, false, false, true, false)),
            "QF_UFIDL" => Some((true, true, false, false, true)),
            "QF_UFNRA" => Some((true, false, false, true, false)),
            "UFLRA" | "UFBV" => Some((true, false, true, false, false)),
            "QF_FD" => Some((true, true, false, true, false)),
            _ => None,
        };
        let numeral_as_real = matches!(
            name,
            "QF_RDL"
                | "QF_LRA"
                | "UFLRA"
                | "LRA"
                | "RDL"
                | "NRA"
                | "QF_NRA"
                | "QF_UFNRA"
                | "QF_UFLRA"
        );
        let (uf, ints, quantifiers, nonlinear, diff) = flags.unwrap_or_default();
        Logic {
            uf,
            ints,
            quantifiers,
            nonlinear,
            diff,
            numeral_as_real,
            unknown: flags.is_none(),
        }
    }

    // check_sort: whether a sort passes. A declared sort is of the user_sort family, so its check
    // (`get_family_id() == null_family_id`) never fires: Idv passes under every logic, as a
    // constant of it does (`(declare-fun smt__TLA____IntSet () Idv)` under QF_LIA).
    fn allows(&self, sort: Sort) -> bool {
        self.unknown || sort != Sort::Int || self.ints
    }
}

// Where the port stops reading a command.
enum Fault {
    // Z3 prints an error and reads on: the command is dropped.
    Dropped,
    // Something the port doesn't read: the script is declined.
    Unread(String),
}

impl From<String> for Fault {
    fn from(message: String) -> Fault {
        Fault::Unread(message)
    }
}

impl From<&str> for Fault {
    fn from(message: &str) -> Fault {
        Fault::Unread(message.into())
    }
}

// The names a quantifier binds, within the scope around it.
struct Scope<'a> {
    parent: Option<usize>,
    names: Vec<(&'a str, Sort)>,
}

enum Task {
    // A term in a scope.
    Term(usize, usize),
    // An application, once its arguments are sorted: the list, and how many arguments.
    Apply(usize, usize),
    // A quantifier, once its body is sorted.
    Quantifier,
}

struct Checker<'a> {
    nodes: Vec<Node<'a>>,
    logic: Logic,
    // The domain and range of each declared function.
    funcs: HashMap<&'a str, (Vec<Sort>, Sort)>,
    // The names whose declaration the logic refused.
    dropped: HashSet<&'a str>,
    // Every plain symbol of the script, which a :named name may not be.
    symbols: HashSet<&'a str>,
    // The :named names so far.
    named: HashSet<&'a str>,
    scopes: Vec<Scope<'a>>,
    // Whether the term being read has a quantifier, and a term of sort Int.
    quantified: bool,
    ints: bool,
}

impl<'a> Checker<'a> {
    fn symbol(&self, id: usize) -> Option<&'a str> {
        match self.nodes[id] {
            Node::Atom(Token::Symbol(text)) => Some(text),
            _ => None,
        }
    }

    fn list(&self, id: usize) -> Option<&[usize]> {
        match &self.nodes[id] {
            Node::List(list) => Some(list),
            Node::Atom(_) => None,
        }
    }

    fn sort(&self, id: usize) -> Option<Sort> {
        match self.symbol(id)? {
            "Bool" => Some(Sort::Bool),
            "Int" => Some(Sort::Int),
            "Idv" => Some(Sort::Idv),
            _ => None,
        }
    }

    // The scope and sort of the innermost bound name, if the name is bound.
    fn find_bound(&self, scope: usize, name: &str) -> Option<(usize, Sort)> {
        let mut current = Some(scope);
        while let Some(index) = current {
            let found = self.scopes[index]
                .names
                .iter()
                .rev()
                .find(|bound| bound.0 == name);
            if let Some(bound) = found {
                return Some((index, bound.1));
            }
            current = self.scopes[index].parent;
        }
        None
    }

    // A quantifier's scope, from its sorted names.
    fn bind(&mut self, id: usize, parent: usize) -> Result<usize, String> {
        let declarations = self.list(id).ok_or("malformed bound names")?.to_vec();
        let mut names: Vec<(&'a str, Sort)> = Vec::new();
        for declaration in declarations {
            let (name, sort) = match self.list(declaration) {
                Some([name, sort]) => (self.symbol(*name), self.sort(*sort)),
                _ => (None, None),
            };
            let (Some(name), Some(sort)) = (name.filter(|name| is_name(name)), sort) else {
                return Err("malformed bound names".into());
            };
            if names.iter().any(|bound| bound.0 == name) {
                return Err(format!("{name} bound twice"));
            }
            names.push((name, sort));
        }
        if names.is_empty() {
            return Err("a quantifier that binds nothing".into());
        }
        self.scopes.push(Scope {
            parent: Some(parent),
            names,
        });
        Ok(self.scopes.len() - 1)
    }

    // The sort of an application, from its arguments' sorts.
    fn apply(&self, head: &str, args: &[Sort]) -> Result<Sort, String> {
        let all = |sort: Sort| args.iter().all(|arg| *arg == sort);
        let same = args.windows(2).all(|pair| pair[0] == pair[1]);
        let sort = match head {
            "not" if args.len() == 1 && all(Sort::Bool) => Some(Sort::Bool),
            "and" | "or" if args.len() >= 2 && all(Sort::Bool) => Some(Sort::Bool),
            "=>" if args.len() == 2 && all(Sort::Bool) => Some(Sort::Bool),
            "=" if args.len() == 2 && same => Some(Sort::Bool),
            "distinct" if args.len() >= 2 && same => Some(Sort::Bool),
            "ite" if args.len() == 3 && args[0] == Sort::Bool && args[1] == args[2] => {
                Some(args[1])
            }
            "<=" | ">=" | "<" | ">" if args.len() == 2 && all(Sort::Int) => Some(Sort::Bool),
            "div" | "mod" if args.len() == 2 && all(Sort::Int) => Some(Sort::Int),
            "+" | "*" if args.len() >= 2 && all(Sort::Int) => Some(Sort::Int),
            "-" if (1..=2).contains(&args.len()) && all(Sort::Int) => Some(Sort::Int),
            _ => self
                .funcs
                .get(head)
                .filter(|func| !args.is_empty() && func.0 == args)
                .map(|func| func.1),
        };
        sort.ok_or_else(|| {
            format!(
                "an ill-sorted application of {head} to {} terms",
                args.len()
            )
        })
    }

    // check_logic's is_numeral: a numeral, or the negation of one.
    fn is_numeral(&self, id: usize) -> bool {
        let mut id = id;
        for _ in 0..2 {
            match self.list(id) {
                Some([head, arg]) if self.symbol(*head) == Some("-") => id = *arg,
                Some(_) => return false,
                None => break,
            }
        }
        self.symbol(id).is_some_and(is_numeral)
    }

    // check_sort, on a term of the sort.
    fn check_sort(&mut self, sort: Sort) -> Result<(), Fault> {
        if sort == Sort::Int {
            self.ints = true;
        }
        if self.logic.allows(sort) {
            Ok(())
        } else {
            Err(Fault::Dropped)
        }
    }

    // check_logic on an application, once Z3 has read it: check_sort on its sort, check_mul and
    // check_div on nonlinear arithmetic, and the difference checks, which the port declines.
    fn check_application(
        &mut self,
        id: usize,
        head: &str,
        args: &[Sort],
        sort: Sort,
    ) -> Result<(), Fault> {
        self.check_sort(sort)?;
        if self.logic.unknown {
            return Ok(());
        }
        let terms = self.list(id).map_or(&[][..], |list| &list[1..]);
        match head {
            "*" if !self.logic.nonlinear => {
                let non_numerals = terms.iter().filter(|term| !self.is_numeral(**term)).count();
                if non_numerals > 1 {
                    return Err(Fault::Dropped);
                }
            }
            "div" | "mod" if !self.logic.nonlinear && !self.is_numeral(terms[1]) => {
                return Err(Fault::Dropped);
            }
            "<=" | "<" | ">=" | ">" | "=" if self.logic.diff && args[0] == Sort::Int => {
                return Err("a comparison a difference logic checks".into());
            }
            _ => {}
        }
        Ok(())
    }

    // The sort of a term in a scope, without recursion: the terms may nest thousands deep. In a
    // pattern of the quantifier whose scope is `pattern`, only applications of declared functions,
    // its own bound names, declared constants and numerals may appear, and the bound names found
    // are collected.
    fn get_sort(
        &mut self,
        root: usize,
        scope: usize,
        mut pattern: Option<(usize, &mut HashSet<&'a str>)>,
    ) -> Result<Sort, Fault> {
        let mut tasks = vec![Task::Term(root, scope)];
        let mut sorts: Vec<Sort> = Vec::new();
        while let Some(task) = tasks.pop() {
            let (id, scope) = match task {
                Task::Term(id, scope) => (id, scope),
                Task::Apply(id, count) => {
                    let head = self.list(id).and_then(|list| self.symbol(list[0]));
                    let head = head.ok_or("an application of a list")?;
                    let args = sorts.split_off(sorts.len() - count);
                    let sort = self.apply(head, &args)?;
                    self.check_application(id, head, &args, sort)?;
                    sorts.push(sort);
                    continue;
                }
                Task::Quantifier => {
                    if sorts.pop() != Some(Sort::Bool) {
                        return Err("a quantifier over a term that is not Bool".into());
                    }
                    sorts.push(Sort::Bool);
                    continue;
                }
            };
            let Some(list) = self.list(id).map(<[usize]>::to_vec) else {
                let text = self.symbol(id).ok_or("a quoted symbol in a term")?;
                let sort = if let Some((found, sort)) = self.find_bound(scope, text) {
                    match &mut pattern {
                        Some((own, names)) if *own == found => {
                            names.insert(text);
                        }
                        Some(_) => {
                            return Err(format!("the outer bound name {text} in a pattern").into());
                        }
                        None => {}
                    }
                    sort
                } else if is_numeral(text) {
                    if self.logic.numeral_as_real {
                        return Err("a numeral a logic of reals reads as a real".into());
                    }
                    Sort::Int
                } else if let Some(func) = self.funcs.get(text).filter(|func| func.0.is_empty()) {
                    func.1
                } else if pattern.is_none() && matches!(text, "true" | "false") {
                    Sort::Bool
                } else if self.dropped.contains(text) {
                    // The parser's "unknown function/constant".
                    return Err(Fault::Dropped);
                } else {
                    return Err(format!("the term {text}").into());
                };
                self.check_sort(sort)?;
                sorts.push(sort);
                continue;
            };
            let Some((head, args)) = list.split_first() else {
                return Err("an empty list".into());
            };
            let head = self.symbol(*head).ok_or("an application of a list")?;
            if self.find_bound(scope, head).is_some() {
                return Err(format!("the bound name {head} applied").into());
            }
            match head {
                "forall" | "exists" if pattern.is_none() => {
                    let [declarations, body] = args else {
                        return Err(format!("a malformed {head}").into());
                    };
                    self.quantified = true;
                    if !self.logic.unknown && !self.logic.quantifiers {
                        return Err(Fault::Dropped);
                    }
                    let inner = self.bind(*declarations, scope)?;
                    let term = self.check_patterns(*body, inner)?;
                    tasks.push(Task::Quantifier);
                    tasks.push(Task::Term(term, inner));
                }
                _ if pattern.is_some() && !self.funcs.contains_key(head) => {
                    if self.dropped.contains(head) {
                        return Err(Fault::Dropped);
                    }
                    return Err(format!("{head} in a pattern").into());
                }
                _ if self.dropped.contains(head) => return Err(Fault::Dropped),
                _ => {
                    tasks.push(Task::Apply(id, args.len()));
                    tasks.extend(args.iter().rev().map(|arg| Task::Term(*arg, scope)));
                }
            }
        }
        sorts.pop().ok_or_else(|| "an empty term".into())
    }

    // A quantifier's body without its patterns, once each pattern is checked.
    fn check_patterns(&mut self, body: usize, scope: usize) -> Result<usize, Fault> {
        let Some(list) = self.list(body).map(<[usize]>::to_vec) else {
            return Ok(body);
        };
        if list.first().and_then(|head| self.symbol(*head)) != Some("!") {
            return Ok(body);
        }
        let [_, term, attributes @ ..] = list.as_slice() else {
            return Err("an empty annotation".into());
        };
        if attributes.is_empty() || attributes.len() % 2 != 0 {
            return Err("a malformed annotation".into());
        }
        for pair in attributes.chunks(2) {
            if self.symbol(pair[0]) != Some(":pattern") {
                return Err("an attribute other than :pattern in a quantifier".into());
            }
            let items = self
                .list(pair[1])
                .map(<[usize]>::to_vec)
                .unwrap_or_default();
            let is_constant = |checker: &Self, item: usize| {
                checker.symbol(item).is_some_and(|name| {
                    checker.find_bound(scope, name).is_none()
                        && checker
                            .funcs
                            .get(name)
                            .is_some_and(|func| func.0.is_empty())
                })
            };
            if let [item] = items.as_slice()
                && is_constant(self, *item)
            {
                continue;
            }
            if items.is_empty() || items.iter().any(|item| self.list(*item).is_none()) {
                return Err("a pattern of something other than applications".into());
            }
            let mut names = HashSet::new();
            for item in items {
                self.get_sort(item, scope, Some((scope, &mut names)))?;
            }
            if names.len() != self.scopes[scope].names.len() {
                return Err("a pattern without every name its quantifier binds".into());
            }
        }
        Ok(*term)
    }

    // An assertion's term, without its name, once the name is checked.
    fn check_name(&mut self, term: usize) -> Result<usize, String> {
        let Some(list) = self.list(term).map(<[usize]>::to_vec) else {
            return Ok(term);
        };
        if list.first().and_then(|head| self.symbol(*head)) != Some("!") {
            return Ok(term);
        }
        let [_, inner, keyword, name] = list.as_slice() else {
            return Err("an annotation other than one :named name".into());
        };
        let Node::Atom(Token::Quoted(name)) = self.nodes[*name] else {
            return Err("an annotation other than one :named name".into());
        };
        if self.symbol(*keyword) != Some(":named") {
            return Err("an annotation other than one :named name".into());
        }
        if self.symbols.contains(name) || !self.named.insert(name) {
            return Err(format!(
                "the :named name {name}, which names something else"
            ));
        }
        Ok(*inner)
    }

    // cmd_context::insert's check of a declaration: whether the logic takes it.
    fn declares(&self, domain: &[Sort], range: Sort) -> bool {
        self.logic.unknown
            || (domain.is_empty() || self.logic.uf)
                && domain
                    .iter()
                    .chain([&range])
                    .all(|sort| self.logic.allows(*sort))
    }

    // Whether the assertion survives Z3's reading, or the port stops.
    fn check_assertion(&mut self, term: usize) -> Result<bool, String> {
        self.quantified = false;
        self.ints = false;
        let term = self.check_name(term)?;
        match self.get_sort(term, 0, None) {
            Ok(Sort::Bool) => Ok(true),
            Ok(_) => Err("an assertion that is not Bool".into()),
            Err(Fault::Dropped) => Ok(false),
            Err(Fault::Unread(message)) => Err(message),
        }
    }
}

/// A script in the subset, as Z3 reads it.
pub struct Script<'a> {
    /// The rlimit the script sets, if one.
    pub rlimit: Option<u64>,
    /// The script without the commands Z3 drops: the text itself where it drops none.
    pub text: Cow<'a, str>,
    /// The bytes of each dropped command.
    pub dropped: Vec<Range<usize>>,
}

/// The script as Z3 reads it, or the first thing outside the subset.
pub fn check_script(text: &str) -> Result<Script<'_>, String> {
    let lexemes = tokenize(text)?;
    let symbols = lexemes
        .iter()
        .filter_map(|lexeme| match lexeme.token {
            Token::Symbol(text) => Some(text),
            _ => None,
        })
        .collect();
    let (nodes, commands) = read(&lexemes)?;
    let mut checker = Checker {
        nodes,
        logic: Logic::of("UFNIA"),
        funcs: HashMap::new(),
        dropped: HashSet::new(),
        symbols,
        named: HashSet::new(),
        scopes: vec![Scope {
            parent: None,
            names: Vec::new(),
        }],
        quantified: false,
        ints: false,
    };
    let mut rlimit = None;
    let mut logic = "";
    let mut dropped = Vec::new();
    // Of the assertions Z3 keeps: how many, whether any has a quantifier, and a term of sort Int.
    let mut kept = 0;
    let mut quantified = false;
    let mut ints = false;
    let mut stage = 0;
    for (index, (command, span)) in commands.iter().enumerate() {
        let list = checker
            .list(*command)
            .ok_or("a command that is not a list")?
            .to_vec();
        let name = list
            .first()
            .and_then(|head| checker.symbol(*head))
            .unwrap_or("");
        let args = &list[1.min(list.len())..];
        let arg = |position: usize| args.get(position).and_then(|id| checker.symbol(*id));
        stage = match (name, args.len()) {
            ("set-option", 2) if stage == 0 && arg(0) == Some(":rlimit") => {
                // Z3 reads the option as an unsigned int; 0 sets no limit.
                let steps = arg(1)
                    .filter(|steps| is_numeral(steps))
                    .and_then(|steps| steps.parse::<u32>().ok())
                    .ok_or("an rlimit Z3 doesn't read")?;
                rlimit = (steps > 0).then_some(u64::from(steps));
                1
            }
            ("set-logic", 1) if stage <= 1 => {
                logic = arg(0).ok_or("a logic that is no symbol")?;
                checker.logic = Logic::of(logic);
                2
            }
            ("declare-sort", 2) if stage == 2 && arg(0) == Some("Idv") && arg(1) == Some("0") => 2,
            ("declare-fun", 3) if stage == 2 => {
                let symbol = arg(0).filter(|symbol| is_name(symbol));
                let symbol = symbol.ok_or("a declared name outside the encoder's")?;
                let domain = checker
                    .list(args[1])
                    .ok_or("a malformed declaration")?
                    .iter()
                    .map(|sort| checker.sort(*sort))
                    .collect::<Option<Vec<_>>>();
                let (Some(domain), Some(range)) = (domain, checker.sort(args[2])) else {
                    return Err(format!("a sort of {symbol}"));
                };
                if checker.funcs.contains_key(symbol) {
                    return Err(format!("{symbol} declared twice"));
                }
                if checker.declares(&domain, range) {
                    checker.dropped.remove(symbol);
                    checker.funcs.insert(symbol, (domain, range));
                } else {
                    checker.dropped.insert(symbol);
                    dropped.push(span.clone());
                }
                2
            }
            ("assert", 1) if stage == 2 => {
                if checker.check_assertion(args[0])? {
                    kept += 1;
                    quantified |= checker.quantified;
                    ints |= checker.ints;
                } else {
                    dropped.push(span.clone());
                }
                2
            }
            ("check-sat", 0) if stage == 2 => 3,
            ("exit", 0) if stage == 3 && index + 1 == commands.len() => 4,
            _ => return Err(format!("the command {name}")),
        };
    }
    if stage < 3 {
        return Err("a script without check-sat".into());
    }
    // mk_tactic_for_logic: the port runs UFNIA's tactic; another decides alike only what any
    // tactic does.
    if logic != "UFNIA" {
        if rlimit.is_some() {
            return Err("an rlimit under a logic Z3 runs through another tactic".into());
        }
        if kept > 0 && (quantified || ints) {
            return Err("a logic Z3 runs through another tactic".into());
        }
    }
    let text = if dropped.is_empty() {
        Cow::Borrowed(text)
    } else {
        let mut kept_text = String::with_capacity(text.len());
        let mut position = 0;
        for span in &dropped {
            kept_text.push_str(&text[position..span.start]);
            position = span.end;
        }
        kept_text.push_str(&text[position..]);
        Cow::Owned(kept_text)
    };
    Ok(Script {
        rlimit,
        text,
        dropped,
    })
}

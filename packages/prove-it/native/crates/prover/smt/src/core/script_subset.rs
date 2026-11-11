//! The SMT-LIB that tlapm's encoder writes (`backend/smtlib.ml`, ported in the obligations crate's
//! `smt` module), which is all the solver decides. Z3 reads more, with errors it reports and reads
//! past, but tlapm never sends it: over the 10,376 smt and z3 inputs of the decider corpus Z3
//! reports no error. A script outside this subset is declined, never answered.
//!
//! The subset, read from the encoder and checked against every input of the corpus:
//! - commands, in this order: an optional `(set-option :rlimit <numeral>)` (tlapm's rlimit),
//!   `(set-logic UFNIA)`, then `(declare-sort Idv 0)`, `(declare-fun <name> (<sort>*) <sort>)` and
//!   `(assert <term>)` in any order, `(check-sat)`, and an optional `(exit)` last;
//! - a declared name starts with `smt__` and is declared once; a name, declared or bound, is made of
//!   letters, digits, `_`, `,` and `~` (format_name spells every other character Z3 reads in a
//!   symbol); the sorts are `Bool`, `Int` and `Idv`;
//! - a term is `true`, `false`, a numeral without leading zeros, a bound or declared constant, an
//!   application of a declared function to as many terms as it takes, an application of `=`, `=>`,
//!   `distinct`, `<=`, `>=`, `<`, `>`, `div`, `mod`, `not`, `ite`, `and`, `or`, `+`, `-` or `*` to
//!   as many terms as the encoder gives them, or a `forall` or `exists` over sorted bound names;
//! - an assertion may name its term once, `(! <term> :named |<name>|)`, with a quoted name of
//!   printable ASCII; a quantifier's body may carry patterns, `(! <term> :pattern (<term>+)+)`;
//! - `;` comments.

use std::collections::{HashMap, HashSet};

// A token: a parenthesis, a plain symbol, a quoted symbol's text, or a keyword.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Token<'a> {
    Open,
    Close,
    Symbol(&'a str),
    Quoted(&'a str),
}

enum Node<'a> {
    Atom(Token<'a>),
    List(Vec<usize>),
}

const OPERATORS: [&str; 10] = [
    "=", "=>", "distinct", "<=", ">=", "<", ">", "div", "mod", "not",
];

fn is_name_char(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b',' | b'~')
}

fn is_operator_char(byte: u8) -> bool {
    matches!(byte, b'=' | b'>' | b'<' | b'+' | b'-' | b'*' | b'!' | b':')
}

fn tokenize(text: &str) -> Result<Vec<Token<'_>>, String> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut position = 0;
    while position < bytes.len() {
        let byte = bytes[position];
        match byte {
            b';' => {
                position = bytes[position..]
                    .iter()
                    .position(|current| *current == b'\n')
                    .map_or(bytes.len(), |offset| position + offset + 1);
            }
            b' ' | b'\n' | b'\t' | b'\r' => position += 1,
            b'(' => {
                tokens.push(Token::Open);
                position += 1;
            }
            b')' => {
                tokens.push(Token::Close);
                position += 1;
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
                tokens.push(Token::Quoted(quoted));
                position += length + 2;
            }
            _ => {
                let start = position;
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
                tokens.push(Token::Symbol(&text[start..position]));
            }
        }
    }
    Ok(tokens)
}

fn read<'a>(tokens: &[Token<'a>]) -> Result<(Vec<Node<'a>>, Vec<usize>), String> {
    let mut nodes = Vec::new();
    let mut stack: Vec<Vec<usize>> = vec![Vec::new()];
    for token in tokens {
        let node = match token {
            Token::Open => {
                stack.push(Vec::new());
                continue;
            }
            Token::Close => {
                if stack.len() == 1 {
                    return Err("an unbalanced parenthesis".into());
                }
                Node::List(stack.pop().unwrap_or_default())
            }
            atom => Node::Atom(*atom),
        };
        if let Some(top) = stack.last_mut() {
            top.push(nodes.len());
        }
        nodes.push(node);
    }
    if stack.len() != 1 {
        return Err("a command the text ends inside".into());
    }
    Ok((nodes, stack.pop().unwrap_or_default()))
}

fn is_numeral(text: &str) -> bool {
    text == "0"
        || text.starts_with(|first: char| ('1'..='9').contains(&first))
            && text.bytes().all(|byte| byte.is_ascii_digit())
}

fn is_name(text: &str) -> bool {
    text.starts_with(|first: char| first.is_ascii_alphabetic() || first == '_')
        && text.bytes().all(is_name_char)
}

struct Checker<'a> {
    nodes: Vec<Node<'a>>,
    // The arity of each declared function.
    funcs: HashMap<&'a str, usize>,
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

    fn is_sort(&self, id: usize) -> bool {
        matches!(self.symbol(id), Some("Bool" | "Int" | "Idv"))
    }

    // The bound names of a quantifier, or None if they are malformed.
    fn get_bound(&self, id: usize) -> Option<Vec<&'a str>> {
        let declarations = self.list(id)?;
        if declarations.is_empty() {
            return None;
        }
        declarations
            .iter()
            .map(|declaration| match self.list(*declaration)? {
                [name, sort] if self.is_sort(*sort) => {
                    self.symbol(*name).filter(|name| is_name(name))
                }
                _ => None,
            })
            .collect()
    }

    // Each term, without recursion: the terms may nest thousands deep.
    fn check_term(&self, root: usize, is_named: bool) -> Result<(), String> {
        // A term to check, the names bound around it, and whether it is a quantifier's body.
        let mut todo: Vec<(usize, Vec<&'a str>, bool)> = vec![(root, Vec::new(), false)];
        if is_named {
            todo.clear();
            let list = self.list(root).ok_or("an annotation")?;
            match list {
                [bang, term, keyword, name]
                    if self.symbol(*bang) == Some("!")
                        && self.symbol(*keyword) == Some(":named")
                        && matches!(self.nodes[*name], Node::Atom(Token::Quoted(_))) =>
                {
                    todo.push((*term, Vec::new(), false));
                }
                _ => return Err("an annotation other than one :named name".into()),
            }
        }
        while let Some((id, bound, is_body)) = todo.pop() {
            let Some(list) = self.list(id) else {
                let Some(text) = self.symbol(id) else {
                    return Err("a quoted symbol in a term".into());
                };
                let is_leaf = matches!(text, "true" | "false")
                    || is_numeral(text)
                    || bound.contains(&text)
                    || self.funcs.get(text) == Some(&0);
                if !is_leaf {
                    return Err(format!("the term {text}"));
                }
                continue;
            };
            let Some((head, args)) = list.split_first() else {
                return Err("an empty list".into());
            };
            let head = self.symbol(*head).ok_or("an application of a list")?;
            match head {
                "forall" | "exists" => {
                    let [declarations, body] = args else {
                        return Err(format!("a malformed {head}"));
                    };
                    let mut inner = bound.clone();
                    inner.extend(
                        self.get_bound(*declarations)
                            .ok_or("malformed bound names")?,
                    );
                    todo.push((*body, inner, true));
                }
                "!" => {
                    let [term, attributes @ ..] = args else {
                        return Err("an empty annotation".into());
                    };
                    if !is_body || attributes.is_empty() || attributes.len() % 2 != 0 {
                        return Err("an annotation outside a quantifier's patterns".into());
                    }
                    todo.push((*term, bound.clone(), false));
                    for pair in attributes.chunks(2) {
                        if self.symbol(pair[0]) != Some(":pattern") {
                            return Err("an attribute other than :pattern in a quantifier".into());
                        }
                        let pattern = self.list(pair[1]).filter(|pattern| !pattern.is_empty());
                        let pattern = pattern.ok_or("an empty pattern")?;
                        // A list of terms; or one application; or a declared constant alone,
                        // which the solver drops as a pattern.
                        if self.list(pattern[0]).is_some() {
                            todo.extend(pattern.iter().map(|item| (*item, bound.clone(), false)));
                        } else if !(pattern.len() == 1
                            && self
                                .symbol(pattern[0])
                                .and_then(|name| self.funcs.get(name))
                                == Some(&0))
                        {
                            todo.push((pair[1], bound.clone(), false));
                        }
                    }
                }
                _ => {
                    let arity_ok = match head {
                        "not" => args.len() == 1,
                        "ite" => args.len() == 3,
                        "-" => (1..=2).contains(&args.len()),
                        "and" | "or" | "+" | "*" | "distinct" => args.len() >= 2,
                        _ if OPERATORS.contains(&head) => args.len() == 2,
                        _ => self.funcs.get(head) == Some(&args.len()) && !args.is_empty(),
                    };
                    if !arity_ok {
                        return Err(format!("the application of {head} to {} terms", args.len()));
                    }
                    todo.extend(args.iter().map(|arg| (*arg, bound.clone(), false)));
                }
            }
        }
        Ok(())
    }
}

/// Whether the script is in the subset, or the first thing outside it.
pub fn check_script(text: &str) -> Result<(), String> {
    let tokens = tokenize(text)?;
    let (nodes, commands) = read(&tokens)?;
    let mut checker = Checker {
        nodes,
        funcs: HashMap::new(),
    };
    let mut declared = HashSet::new();
    let mut stage = 0;
    for (index, command) in commands.iter().enumerate() {
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
            ("set-option", 2)
                if stage == 0 && arg(0) == Some(":rlimit") && arg(1).is_some_and(is_numeral) =>
            {
                1
            }
            ("set-logic", 1) if stage <= 1 && arg(0) == Some("UFNIA") => 2,
            ("declare-sort", 2) if stage == 2 && arg(0) == Some("Idv") && arg(1) == Some("0") => 2,
            ("declare-fun", 3) if stage == 2 => {
                let symbol = arg(0).filter(|symbol| symbol.starts_with("smt__") && is_name(symbol));
                let symbol = symbol.ok_or("a declared name outside the encoder's")?;
                let domain = checker
                    .list(args[1])
                    .ok_or("a malformed declaration")?
                    .to_vec();
                if !domain.iter().all(|sort| checker.is_sort(*sort)) || !checker.is_sort(args[2]) {
                    return Err(format!("a sort of {symbol}"));
                }
                if !declared.insert(symbol) {
                    return Err(format!("{symbol} declared twice"));
                }
                checker.funcs.insert(symbol, domain.len());
                2
            }
            ("assert", 1) if stage == 2 => {
                let is_named = checker
                    .list(args[0])
                    .and_then(|term| term.first())
                    .and_then(|head| checker.symbol(*head))
                    == Some("!");
                checker.check_term(args[0], is_named)?;
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
    Ok(())
}

//! Translates the proofs that the TypeScript search found for some fixtures, and compares the
//! lemmas, after `postprocess_tla` and `optimise` too, and the numbering of the formulas with what
//! the TypeScript translation printed. Each `.input` file under `testdata/mltoll` holds a search
//! proof, and the `.expected` file beside it what the TypeScript made of it.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;
use std::rc::Rc;

use super::{TranslateContext, translate_proof};
use crate::eqrel::Relations;
use crate::expr::{Expr, Expressions, Kind, efalse, etrue};
use crate::llproof::{Lemma, LlProof, LlRule, optimise};
use crate::parse::{Definition, Phrase};
use crate::proof::{Proof, ProofKey, Rule, RuleName};
use crate::tla::llproof::postprocess_tla;

#[derive(Debug)]
enum Sexp {
    Atom(String),
    Text(String),
    List(Vec<Sexp>),
}

impl Sexp {
    fn items(&self) -> &[Sexp] {
        match self {
            Sexp::List(items) => items,
            _ => panic!("expected a list, got {self:?}"),
        }
    }

    fn atom(&self) -> &str {
        match self {
            Sexp::Atom(atom) => atom,
            _ => panic!("expected an atom, got {self:?}"),
        }
    }

    fn text(&self) -> &str {
        match self {
            Sexp::Text(text) => text,
            _ => panic!("expected a string, got {self:?}"),
        }
    }
}

fn parse_string(chars: &mut std::iter::Peekable<std::str::Chars>) -> String {
    let mut units: Vec<u16> = Vec::new();
    loop {
        let char = chars.next().expect("an unterminated string");
        match char {
            '"' => return String::from_utf16(&units).expect("valid UTF-16"),
            '\\' => {
                let escaped = chars.next().expect("an unterminated escape");
                let unit = match escaped {
                    'n' => u16::from(b'\n'),
                    'r' => u16::from(b'\r'),
                    't' => u16::from(b'\t'),
                    'b' => 8,
                    'f' => 12,
                    'u' => {
                        let hex: String = (0..4).map(|_| chars.next().expect("hex")).collect();
                        u16::from_str_radix(&hex, 16).expect("a hex escape")
                    }
                    other => u16::try_from(u32::from(other)).expect("an ASCII escape"),
                };
                units.push(unit);
            }
            other => {
                let mut buffer = [0; 2];
                units.extend_from_slice(other.encode_utf16(&mut buffer));
            }
        }
    }
}

fn parse_sexps(text: &str) -> Vec<Sexp> {
    let mut chars = text.chars().peekable();
    let mut stack: Vec<Vec<Sexp>> = vec![Vec::new()];
    while let Some(char) = chars.next() {
        match char {
            '(' => stack.push(Vec::new()),
            ')' => {
                let list = stack.pop().expect("a balanced list");
                stack
                    .last_mut()
                    .expect("an open list")
                    .push(Sexp::List(list));
            }
            '"' => {
                let parsed = parse_string(&mut chars);
                stack
                    .last_mut()
                    .expect("an open list")
                    .push(Sexp::Text(parsed));
            }
            char if char.is_whitespace() => {}
            char => {
                let mut atom = char.to_string();
                while let Some(next) = chars
                    .peek()
                    .filter(|next| !next.is_whitespace() && **next != '(' && **next != ')')
                {
                    atom.push(*next);
                    chars.next();
                }
                stack
                    .last_mut()
                    .expect("an open list")
                    .push(Sexp::Atom(atom));
            }
        }
    }
    stack.pop().expect("the top level")
}

fn json_quote(text: &str) -> String {
    let mut quoted = String::from("\"");
    for char in text.chars() {
        match char {
            '"' => quoted.push_str("\\\""),
            '\\' => quoted.push_str("\\\\"),
            '\n' => quoted.push_str("\\n"),
            '\r' => quoted.push_str("\\r"),
            '\t' => quoted.push_str("\\t"),
            '\u{8}' => quoted.push_str("\\b"),
            '\u{c}' => quoted.push_str("\\f"),
            char if u32::from(char) < 0x20 => {
                quoted.push_str(&format!("\\u{:04x}", u32::from(char)));
            }
            char => quoted.push(char),
        }
    }
    quoted.push('"');
    quoted
}

/// The expressions of a fixture, each built from those numbered before it.
fn build_exprs(exprs: &Expressions, entries: &[Sexp]) -> Vec<Expr> {
    let mut table: Vec<Expr> = Vec::new();
    for entry in entries {
        let get = |sexp: &Sexp| -> Expr {
            let reference = sexp.atom().strip_prefix('#').expect("a reference");
            table[reference.parse::<usize>().expect("a number")].clone()
        };
        let built = match entry {
            Sexp::Atom(atom) if atom == "T" => etrue(),
            Sexp::Atom(atom) if atom == "F" => efalse(),
            Sexp::List(items) => {
                let head = items[0].atom();
                match head {
                    "v" => exprs.evar(items[1].text()),
                    "m" => exprs.emeta(&get(&items[1])),
                    "a" => {
                        let args: Vec<Expr> = items[2..].iter().map(get).collect();
                        exprs.eapp(items[1].text(), &args)
                    }
                    "not" => exprs.enot(&get(&items[1])),
                    "and" | "or" | "imply" | "equiv" => {
                        let kind = match head {
                            "and" => Kind::And,
                            "or" => Kind::Or,
                            "imply" => Kind::Imply,
                            _ => Kind::Equiv,
                        };
                        exprs.binary(kind, &get(&items[1]), &get(&items[2]))
                    }
                    binder => {
                        let kind = match binder {
                            "all" => Kind::All,
                            "ex" => Kind::Ex,
                            "tau" => Kind::Tau,
                            "lam" => Kind::Lam,
                            other => panic!("an unknown expression {other}"),
                        };
                        exprs.binder(kind, &get(&items[2]), items[1].text(), &get(&items[3]))
                    }
                }
            }
            other => panic!("an unknown expression {other:?}"),
        };
        table.push(built);
    }
    table
}

/// Prints expressions as numbers into a table of the expressions, each after its subexpressions.
#[derive(Default)]
struct Printer {
    numbers: HashMap<Expr, usize>,
    entries: Vec<String>,
}

impl Printer {
    fn reference(&mut self, expression: &Expr) -> String {
        if let Some(number) = self.numbers.get(expression) {
            return format!("#{number}");
        }
        let entry = match expression.kind {
            Kind::Var => format!("(v {})", json_quote(&expression.symbol)),
            Kind::Meta => format!("(m {})", self.reference(&expression.args[0])),
            Kind::App => {
                let args: String = expression
                    .args
                    .iter()
                    .map(|arg| format!(" {}", self.reference(arg)))
                    .collect();
                format!("(a {}{args})", json_quote(&expression.symbol))
            }
            Kind::Not => format!("(not {})", self.reference(&expression.args[0])),
            Kind::True => "T".to_owned(),
            Kind::False => "F".to_owned(),
            kind if kind.is_binary() => {
                let left = self.reference(&expression.args[0]);
                let right = self.reference(&expression.args[1]);
                format!("({} {left} {right})", kind.name())
            }
            kind => {
                let variable = self.reference(&expression.args[0]);
                let body = self.reference(&expression.args[1]);
                format!(
                    "({} {} {variable} {body})",
                    kind.name(),
                    json_quote(&expression.symbol)
                )
            }
        };
        self.numbers.insert(expression.clone(), self.entries.len());
        self.entries.push(entry);
        format!("#{}", self.entries.len() - 1)
    }

    fn list(&mut self, expressions: &[Expr]) -> String {
        let references: Vec<String> = expressions
            .iter()
            .map(|expression| self.reference(expression))
            .collect();
        format!("({})", references.join(" "))
    }

    fn rule(&mut self, rule: &LlRule) -> String {
        let mut parts = vec![rule.kind().to_owned()];
        match rule {
            LlRule::False | LlRule::NotTrue => {}
            LlRule::Axiom(formula) | LlRule::Cut(formula) | LlRule::NotNot(formula) => {
                parts.push(self.reference(formula));
            }
            LlRule::NotEq(term) => parts.push(self.reference(term)),
            LlRule::EqSym { left, right } | LlRule::NotEqual { left, right } => {
                parts.push(self.reference(left));
                parts.push(self.reference(right));
            }
            LlRule::Connect {
                connective,
                left,
                right,
            }
            | LlRule::NotConnect {
                connective,
                left,
                right,
            } => {
                parts.push(json_quote(connective.name()));
                parts.push(self.reference(left));
                parts.push(self.reference(right));
            }
            LlRule::Ex { quantified, term }
            | LlRule::All { quantified, term }
            | LlRule::NotEx { quantified, term }
            | LlRule::NotAll { quantified, term } => {
                parts.push(self.reference(term));
                parts.push(self.reference(quantified));
            }
            LlRule::PNotP { positive, negative } => {
                parts.push(self.reference(positive));
                parts.push(self.reference(negative));
            }
            LlRule::CongruenceLr {
                context,
                left,
                right,
            }
            | LlRule::CongruenceRl {
                context,
                left,
                right,
            } => {
                parts.push(self.reference(context));
                parts.push(self.reference(left));
                parts.push(self.reference(right));
            }
            LlRule::Definition {
                name,
                folded,
                unfolded,
            } => {
                parts.push(json_quote(name));
                parts.push(self.reference(folded));
                parts.push(self.reference(unfolded));
            }
            LlRule::Extension {
                name,
                args,
                conclusions,
                branches,
            } => {
                parts.push(json_quote(name));
                parts.push(self.list(args));
                parts.push(self.list(conclusions));
                let branches: Vec<String> =
                    branches.iter().map(|branch| self.list(branch)).collect();
                parts.push(format!("({})", branches.join(" ")));
            }
            LlRule::Lemma { name, args } => {
                parts.push(json_quote(name));
                parts.push(self.list(args));
            }
        }
        parts.join(" ")
    }

    fn tree(&mut self, tree: &LlProof, depth: usize, output: &mut Vec<String>) {
        let rule = self.rule(&tree.rule);
        let conclusions = self.list(&tree.conclusions);
        output.push(format!("{}{rule} {conclusions}", "  ".repeat(depth)));
        for subproof in &tree.subproofs {
            self.tree(subproof, depth + 1, output);
        }
    }

    fn lemmas(&mut self, lemmas: &[Lemma], output: &mut Vec<String>) {
        for lemma in lemmas {
            let params: Vec<String> = lemma
                .params
                .iter()
                .map(|param| format!("({} {})", json_quote(&param.0), self.reference(&param.1)))
                .collect();
            output.push(format!("lemma {} ({})", lemma.name, params.join(" ")));
            self.tree(&lemma.proof, 1, output);
        }
    }
}

fn get_section<'a>(sections: &'a [Sexp], name: &str) -> &'a [Sexp] {
    sections
        .iter()
        .find(|section| section.items()[0].atom() == name)
        .map(|section| &section.items()[1..])
        .unwrap_or_else(|| panic!("no section {name}"))
}

fn get_optional(sexp: &Sexp) -> Option<&Sexp> {
    match sexp {
        Sexp::Atom(atom) if atom == "nil" => None,
        other => Some(other),
    }
}

/// What the translation of a fixture's search proof prints, as the TypeScript printed it.
fn translate_fixture(input: &str) -> String {
    let exprs = Expressions::new();
    let sections = parse_sexps(input);
    let table = build_exprs(&exprs, get_section(&sections, "exprs"));
    let get = |sexp: &Sexp| -> Expr {
        let reference = sexp.atom().strip_prefix('#').expect("a reference");
        table[reference.parse::<usize>().expect("a number")].clone()
    };
    let get_all = |sexp: &Sexp| -> Vec<Expr> { sexp.items().iter().map(get).collect() };
    let mut relations = Relations::new();
    for hypothesis in get_section(&sections, "hyps") {
        relations.analyse(&exprs, &get(hypothesis));
    }
    let phrases: Vec<Phrase> = get_section(&sections, "phrases")
        .iter()
        .map(|formula| Phrase::Hyp {
            name: String::new(),
            formula: get(formula),
            goalness: 0,
        })
        .collect();
    let definitions: Vec<Rc<Definition>> = get_section(&sections, "defs")
        .iter()
        .map(|definition| {
            let items = definition.items();
            Rc::new(match items[0].atom() {
                "real" => Definition::Real {
                    name: items[1].text().to_owned(),
                    symbol: items[2].text().to_owned(),
                    params: get_all(&items[3]),
                    body: get(&items[4]),
                },
                _ => Definition::Pseudo {
                    origin: get(&items[1]),
                    goalness: items[2].atom().parse().expect("a goalness"),
                    symbol: items[3].text().to_owned(),
                    params: get_all(&items[4]),
                    body: get(&items[5]),
                },
            })
        })
        .collect();
    let mut nodes: Vec<Rc<Proof>> = Vec::new();
    let mut shared_proofs = HashSet::new();
    for node in get_section(&sections, "nodes") {
        let items = node.items();
        let name = items[3].text();
        let proof = Rc::new(Proof {
            conclusions: get_all(&items[7]),
            rule: Rule {
                name: RuleName::from_name(name).unwrap_or_else(|| panic!("no rule {name}")),
                relation: get_optional(&items[4]).map(|relation| relation.text().into()),
                definition: get_optional(&items[5]).map(|position| {
                    definitions[position.atom().parse::<usize>().expect("a number")].clone()
                }),
                args: get_all(&items[6]),
            },
            uses: get_all(&items[8]),
            subproofs: items[9]
                .items()
                .iter()
                .map(|id| nodes[id.atom().parse::<usize>().expect("a number")].clone())
                .collect(),
        });
        if items[2].atom() == "1" {
            shared_proofs.insert(ProofKey(proof.clone()));
        }
        nodes.push(proof);
    }
    let root = &nodes[get_section(&sections, "root")[0]
        .atom()
        .parse::<usize>()
        .expect("a number")];
    let next = get_section(&sections, "next")[0].text();
    while *exprs.new_var().symbol != *next {}
    let numbered: RefCell<Vec<Expr>> = RefCell::default();
    let get_number = |expression: &Expr| {
        let mut numbered = numbered.borrow_mut();
        numbered
            .iter()
            .position(|inner| inner == expression)
            .unwrap_or_else(|| {
                numbered.push(expression.clone());
                numbered.len() - 1
            })
    };
    let context = TranslateContext {
        exprs: &exprs,
        get_number: &get_number,
        shared_proofs: &shared_proofs,
        relations: &relations,
    };
    let translated = translate_proof(&context, &phrases, root).expect("a translation");
    let mut printer = Printer::default();
    let mut output = vec!["translated".to_owned()];
    printer.lemmas(&translated, &mut output);
    let postprocessed = postprocess_tla(&exprs, translated).expect("a postprocessing");
    let optimised = optimise(&exprs, &postprocessed).expect("an optimisation");
    output.push("optimised".to_owned());
    printer.lemmas(&optimised, &mut output);
    output.push("numbers".to_owned());
    for expression in numbered.borrow().iter() {
        output.push(printer.reference(expression));
    }
    output.push("exprs".to_owned());
    output.extend(printer.entries);
    output.join("\n") + "\n"
}

#[test]
fn translates_as_the_typescript_does() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("testdata/mltoll");
    let mut inputs: Vec<_> = fs::read_dir(&directory)
        .expect("the fixtures")
        .map(|entry| entry.expect("an entry").path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "input")
        })
        .collect();
    inputs.sort();
    assert!(!inputs.is_empty());
    for input in inputs {
        let expected = fs::read_to_string(input.with_extension("expected")).expect("an output");
        let actual = translate_fixture(&fs::read_to_string(&input).expect("an input"));
        assert!(
            actual == expected,
            "{} differs:\n{}",
            input.display(),
            first_difference(&actual, &expected)
        );
    }
}

fn first_difference(actual: &str, expected: &str) -> String {
    actual
        .lines()
        .zip(expected.lines())
        .enumerate()
        .find(|entry| entry.1.0 != entry.1.1)
        .map_or_else(
            || "the outputs differ in length".to_owned(),
            |entry| {
                format!(
                    "line {}:\n  actual   {}\n  expected {}",
                    entry.0 + 1,
                    entry.1.0,
                    entry.1.1
                )
            },
        )
}

#[test]
fn names_metavariables_after_types() {
    assert_eq!(super::to_identifier("zenon_U"), "zenon_5fU");
    assert_eq!(super::to_identifier("a.b é"), "a_2eb_20_e9");
    assert!(super::is_meta_name("zenon_X3_zenon_5fU"));
    assert!(!super::is_meta_name("zenon_L3_"));
}

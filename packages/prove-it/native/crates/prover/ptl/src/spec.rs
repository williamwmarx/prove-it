//! LS4's reader of the clause set ptl_to_trp prints (`core/Trp2Spec.cc` of LS4): initial clauses,
//! universal clauses, step clauses, whose `next` literals speak of the next moment, and
//! eventuality clauses, each with one `sometime` literal. It stops on text it doesn't read, on an
//! identifier of 32 characters or more, and on a `sometime` or `next` where it doesn't belong,
//! and LS4 then gives no verdict. `True` and `False` are identifiers to it.

use crate::tableau::{Formula, Formulas};

/// An atom's number, and whether the literal is negated.
#[derive(Clone, Copy)]
struct Lit {
    atom: usize,
    is_negated: bool,
}

#[derive(Clone, Copy)]
struct StepLit {
    lit: Lit,
    is_next: bool,
}

#[derive(Default)]
pub struct Spec {
    atoms: Vec<String>,
    initial: Vec<Vec<Lit>>,
    universal: Vec<Vec<Lit>>,
    step: Vec<Vec<StepLit>>,
    eventual: Vec<(Vec<Lit>, Lit)>,
}

#[derive(Clone, PartialEq, Eq)]
enum Token {
    Eof,
    LPar,
    RPar,
    LBr,
    RBr,
    Comma,
    Dot,
    Text(String),
    Error,
}

const IDENT_LIMIT: usize = 32;

struct Reader<'a> {
    bytes: &'a [u8],
    position: usize,
    token: Token,
    spec: Spec,
}

impl Reader<'_> {
    /// `lexNextToken`. None where the identifier is too long.
    fn advance(&mut self) -> Option<()> {
        let mut text = String::new();
        loop {
            let Some(&byte) = self.bytes.get(self.position) else {
                self.token = if text.is_empty() {
                    Token::Eof
                } else {
                    Token::Text(text)
                };
                return Some(());
            };
            if byte.is_ascii_alphanumeric() || byte == b'_' {
                self.position += 1;
                text.push(char::from(byte));
                if text.len() == IDENT_LIMIT {
                    return None;
                }
                continue;
            }
            if !text.is_empty() {
                self.token = Token::Text(text);
                return Some(());
            }
            self.position += 1;
            self.token = match byte {
                b'(' => Token::LPar,
                b')' => Token::RPar,
                b'[' => Token::LBr,
                b']' => Token::RBr,
                b',' => Token::Comma,
                b'.' => Token::Dot,
                b' ' | b'\t' | b'\r' | b'\n' => continue,
                _ => Token::Error,
            };
            return Some(());
        }
    }

    fn is(&self, word: &str) -> bool {
        matches!(&self.token, Token::Text(text) if text == word)
    }

    fn expect(&self, token: Token) -> Option<()> {
        (self.token == token).then_some(())
    }

    fn expect_word(&self, word: &str) -> Option<()> {
        self.is(word).then_some(())
    }

    fn read_id(&mut self) -> Option<usize> {
        let Token::Text(name) = &self.token else {
            return None;
        };
        Some(match self.spec.atoms.iter().position(|atom| atom == name) {
            Some(atom) => atom,
            None => {
                self.spec.atoms.push(name.clone());
                self.spec.atoms.len() - 1
            }
        })
    }

    fn read_literal(&mut self) -> Option<Lit> {
        if !self.is("not") {
            return Some(Lit {
                atom: self.read_id()?,
                is_negated: false,
            });
        }
        self.advance()?;
        let atom = if self.token == Token::LPar {
            self.advance()?;
            let atom = self.read_id()?;
            self.advance()?;
            self.expect(Token::RPar)?;
            atom
        } else {
            self.read_id()?
        };
        Some(Lit {
            atom,
            is_negated: true,
        })
    }

    /// `trp_ReadClauseCore`: the literals, those under `next` marked, and the `sometime` literal.
    fn read_clause(&mut self, is_universal: bool) -> Option<(Vec<StepLit>, Option<Lit>)> {
        let mut literals = Vec::new();
        let mut eventual = None;
        let mut had_next = false;
        self.expect_word("or")?;
        self.advance()?;
        self.expect(Token::LPar)?;
        self.advance()?;
        self.expect(Token::LBr)?;
        loop {
            self.advance()?;
            if self.token == Token::RBr {
                break;
            }
            let Token::Text(_) = self.token else {
                return None;
            };
            if self.is("sometime") || self.is("next") {
                let is_sometime = self.is("sometime");
                if !is_universal || (is_sometime && had_next) || eventual.is_some() {
                    return None;
                }
                had_next |= !is_sometime;
                self.advance()?;
                self.expect(Token::LPar)?;
                self.advance()?;
                let lit = self.read_literal()?;
                self.advance()?;
                self.expect(Token::RPar)?;
                if is_sometime {
                    eventual = Some(lit);
                } else {
                    literals.push(StepLit { lit, is_next: true });
                }
            } else {
                let lit = self.read_literal()?;
                literals.push(StepLit {
                    lit,
                    is_next: false,
                });
            }
            self.advance()?;
            if self.token != Token::Comma {
                break;
            }
        }
        self.expect(Token::RBr)?;
        self.advance()?;
        self.expect(Token::RPar)?;
        Some((literals, eventual))
    }

    /// `trp_LoadSpec`.
    fn read(&mut self) -> Option<()> {
        self.advance()?;
        self.expect_word("and")?;
        self.advance()?;
        self.expect(Token::LPar)?;
        self.advance()?;
        self.expect(Token::LBr)?;
        loop {
            self.advance()?;
            if self.is("always") {
                self.advance()?;
                self.expect(Token::LPar)?;
                self.advance()?;
                let (literals, eventual) = self.read_clause(true)?;
                let plain: Vec<Lit> = literals.iter().map(|literal| literal.lit).collect();
                match eventual {
                    Some(lit) => self.spec.eventual.push((plain, lit)),
                    None if literals.iter().any(|literal| literal.is_next) => {
                        self.spec.step.push(literals);
                    }
                    None => self.spec.universal.push(plain),
                }
                self.advance()?;
                self.expect(Token::RPar)?;
            } else if self.is("or") {
                let (literals, _) = self.read_clause(false)?;
                self.spec
                    .initial
                    .push(literals.iter().map(|literal| literal.lit).collect());
            } else {
                break;
            }
            self.advance()?;
            if self.token != Token::Comma {
                break;
            }
        }
        self.expect(Token::RBr)?;
        self.advance()?;
        self.expect(Token::RPar)?;
        self.advance()?;
        self.expect(Token::Dot)
    }
}

/// The clause set LS4 reads from the text, or None where it stops.
pub fn read_spec(text: &str) -> Option<Spec> {
    let mut reader = Reader {
        bytes: text.as_bytes(),
        position: 0,
        token: Token::Eof,
        spec: Spec::default(),
    };
    reader.read()?;
    Some(reader.spec)
}

struct Builder {
    nodes: Vec<Formula>,
}

impl Builder {
    fn add(&mut self, formula: Formula) -> usize {
        self.nodes.push(formula);
        self.nodes.len() - 1
    }

    fn literal(&mut self, lit: Lit, is_next: bool) -> usize {
        let mut node = self.add(Formula::Atom(lit.atom));
        if lit.is_negated {
            node = self.add(Formula::Not(node));
        }
        if is_next {
            node = self.add(Formula::Next(node));
        }
        node
    }

    fn junction(&mut self, is_and: bool, operands: Vec<usize>) -> usize {
        let Some((&first, rest)) = operands.split_first() else {
            return self.add(Formula::Constant(is_and));
        };
        rest.iter().fold(first, |left, &right| {
            self.add(if is_and {
                Formula::And(left, right)
            } else {
                Formula::Or(left, right)
            })
        })
    }
}

impl Spec {
    /// What the clause set says, as LS4 decides it: the initial clauses now, and the others at
    /// every moment, an eventuality clause holding where its `sometime` literal holds later.
    pub fn to_formulas(&self) -> Formulas {
        let mut builder = Builder { nodes: Vec::new() };
        let mut conjuncts = Vec::new();
        for clause in &self.initial {
            let literals = clause
                .iter()
                .map(|&lit| builder.literal(lit, false))
                .collect();
            conjuncts.push(builder.junction(false, literals));
        }
        let mut always = |builder: &mut Builder, literals: Vec<usize>| {
            let body = builder.junction(false, literals);
            conjuncts.push(builder.add(Formula::Always(body)));
        };
        for clause in &self.universal {
            let literals = clause
                .iter()
                .map(|&lit| builder.literal(lit, false))
                .collect();
            always(&mut builder, literals);
        }
        for clause in &self.step {
            let literals = clause
                .iter()
                .map(|literal| builder.literal(literal.lit, literal.is_next))
                .collect();
            always(&mut builder, literals);
        }
        for (clause, eventual) in &self.eventual {
            let mut literals: Vec<usize> = clause
                .iter()
                .map(|&lit| builder.literal(lit, false))
                .collect();
            let body = builder.literal(*eventual, false);
            literals.push(builder.add(Formula::Eventually(body)));
            always(&mut builder, literals);
        }
        let root = builder.junction(true, conjuncts);
        Formulas {
            nodes: builder.nodes,
            atoms: self.atoms.clone(),
            root,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_each_kind_of_clause() {
        let spec = read_spec(
            "and([\nor([a, not b]),\nalways(or([not NVV1, False])),\nalways(or([not NVV1, next(NVV1)])),\nalways(or([not NVV1, sometime(NVV2)]))]).\n\n",
        )
        .expect("a clause set");
        assert_eq!(spec.atoms, ["a", "b", "NVV1", "False", "NVV2"]);
        assert_eq!(
            (
                spec.initial.len(),
                spec.universal.len(),
                spec.step.len(),
                spec.eventual.len()
            ),
            (1, 1, 1, 1)
        );
        assert!(read_spec("and([\n]).\n\n").is_some());
        assert!(read_spec("and([\nor([])]).\n\n").is_some());
    }

    #[test]
    fn stops_where_ls4_stops() {
        for text in [
            "",
            "Parse error line 1 characters 3-4\n",
            "and([\nor([p(X)])]).\n",
            "and([\nor([sometime(p)])]).\n",
            "and([\nalways(or([next(p), sometime(q)]))]).\n",
            "and([\nor([p])])\n",
            "and([\nor([abcdefghijabcdefghijabcdefghijab])]).\n",
        ] {
            assert!(read_spec(text).is_none(), "{text}");
        }
        assert!(read_spec("and([\nor([abcdefghijabcdefghijabcdefghija])]).").is_some());
    }
}

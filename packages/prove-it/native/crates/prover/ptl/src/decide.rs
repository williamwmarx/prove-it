//! Decides the text tlapm sends LS4, as LS4 does: unsat when the negated obligation has no model,
//! which proves the obligation: `ptl/decide.ts`.

use prove_decide::{DecideError, Decision, Limits, Statistic, Verdict};

use crate::tableau::{Formula, Formulas, get_satisfiability};

/// Where the TypeScript throws a `TlaSyntaxError`, the port declines, so that the TypeScript reads
/// the input again and throws it with its own message.
fn not_ls4() -> DecideError {
    DecideError::Declined("the text isn't LS4 input this port reads".into())
}

/// The tokens of `<->|->|[()~&|]|[\w']+|\S`, on ASCII text.
fn tokenize(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let is_word = |byte: u8| byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'\'';
    let mut tokens = Vec::new();
    let mut start = 0;
    while start < bytes.len() {
        let rest = &text[start..];
        let length = if bytes[start].is_ascii_whitespace() || bytes[start] == 0x0b {
            start += 1;
            continue;
        } else if rest.starts_with("<->") {
            3
        } else if rest.starts_with("->") {
            2
        } else if is_word(bytes[start]) {
            bytes[start..]
                .iter()
                .take_while(|&&byte| is_word(byte))
                .count()
        } else {
            1
        };
        tokens.push(&text[start..start + length]);
        start += length;
    }
    tokens
}

/// LS4's input syntax, as tlapm writes it: every operator is parenthesized except the facts of a
/// sequent, which are joined by & before ->.
struct Parser<'a> {
    tokens: Vec<&'a str>,
    position: usize,
    formulas: Formulas,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<&'a str> {
        self.tokens.get(self.position).copied()
    }

    fn take(&mut self) -> Result<&'a str, DecideError> {
        let token = self.peek().ok_or_else(not_ls4)?;
        self.position += 1;
        Ok(token)
    }

    fn add(&mut self, formula: Formula) -> usize {
        self.formulas.nodes.push(formula);
        self.formulas.nodes.len() - 1
    }

    fn parse_unary(&mut self) -> Result<usize, DecideError> {
        let token = self.take()?;
        match token {
            "(" => {
                let inner = self.parse_equiv()?;
                if self.take()? != ")" {
                    return Err(not_ls4());
                }
                Ok(inner)
            }
            "~" | "not" => {
                let body = self.parse_unary()?;
                Ok(self.add(Formula::Not(body)))
            }
            "always" => {
                let body = self.parse_unary()?;
                Ok(self.add(Formula::Always(body)))
            }
            "sometime" => {
                let body = self.parse_unary()?;
                Ok(self.add(Formula::Eventually(body)))
            }
            "next" => {
                let body = self.parse_unary()?;
                Ok(self.add(Formula::Next(body)))
            }
            _ if token
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'\'') =>
            {
                let atoms = &mut self.formulas.atoms;
                let atom = match atoms.iter().position(|name| name == token) {
                    Some(atom) => atom,
                    None => {
                        atoms.push(token.to_owned());
                        atoms.len() - 1
                    }
                };
                Ok(self.add(Formula::Atom(atom)))
            }
            _ => Err(not_ls4()),
        }
    }

    fn parse_junction(
        &mut self,
        operator: &str,
        parse_operand: fn(&mut Self) -> Result<usize, DecideError>,
        make: fn(usize, usize) -> Formula,
    ) -> Result<usize, DecideError> {
        let mut left = parse_operand(self)?;
        while self.peek() == Some(operator) {
            self.position += 1;
            let right = parse_operand(self)?;
            left = self.add(make(left, right));
        }
        Ok(left)
    }

    fn parse_conjunction(&mut self) -> Result<usize, DecideError> {
        self.parse_junction("&", Self::parse_unary, Formula::And)
    }

    fn parse_implies(&mut self) -> Result<usize, DecideError> {
        let left = self.parse_junction("|", Self::parse_conjunction, Formula::Or)?;
        if self.peek() != Some("->") {
            return Ok(left);
        }
        self.position += 1;
        let right = self.parse_implies()?;
        Ok(self.add(Formula::Implies(left, right)))
    }

    fn parse_equiv(&mut self) -> Result<usize, DecideError> {
        let left = self.parse_implies()?;
        if self.peek() != Some("<->") {
            return Ok(left);
        }
        self.position += 1;
        let right = self.parse_equiv()?;
        Ok(self.add(Formula::Equiv(left, right)))
    }
}

fn parse_ls4(text: &str) -> Result<Formulas, DecideError> {
    if !text.is_ascii() {
        return Err(not_ls4());
    }
    let mut parser = Parser {
        tokens: tokenize(text),
        position: 0,
        formulas: Formulas {
            nodes: Vec::new(),
            atoms: Vec::new(),
            root: 0,
        },
    };
    parser.formulas.root = parser.parse_equiv()?;
    if parser.position < parser.tokens.len() {
        return Err(not_ls4());
    }
    Ok(parser.formulas)
}

/// The verdict, with the steps as its one statistic, each a check of the limits.
pub fn decide(text: &str, limits: &Limits) -> Result<Decision, DecideError> {
    let formulas = parse_ls4(text)?;
    let verdict: Verdict = get_satisfiability(&formulas, &mut || {
        limits.is_step_limit_reached() || limits.is_canceled() || limits.is_past_deadline()
    });
    Ok(Decision {
        verdict,
        statistics: vec![("steps", Statistic::Count(limits.steps()))],
    })
}

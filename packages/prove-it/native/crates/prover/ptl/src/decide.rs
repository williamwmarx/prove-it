//! Decides the text tlapm sends LS4 as `ptl_to_trp -i file | ls4` does: the text is translated to
//! clauses as `translate` does, LS4 reads them as `Trp2Spec.cc` does, and the clauses are
//! satisfiable, which fails the obligation, or not, which proves it. Where the translation writes
//! no clauses, or LS4 can't read what it writes, LS4 reaches no verdict.

use std::collections::HashMap;

use prove_decide::{DecideError, Decision, Limits, Statistic, Verdict};

use crate::tableau::{Formula, Formulas, get_satisfiability};
use crate::translate::{self, Clauses};

/// LS4's identifier buffer (`IDENTBUF_SIZE` in `Trp2Spec.cc`) holds 31 characters; a longer
/// identifier ends it.
const IDENTIFIER_LIMIT: usize = 31;

/// Builds the formula the clauses mean, as LS4 reads them: `or([...])` holds at first,
/// `always(or([...]))` at every time, `next(l)` at the next time and `sometime(l)` at some time.
#[derive(Default)]
struct Builder {
    nodes: Vec<Formula>,
    atoms: Vec<String>,
    numbers: HashMap<String, usize>,
}

impl Builder {
    fn add(&mut self, formula: Formula) -> usize {
        self.nodes.push(formula);
        self.nodes.len() - 1
    }

    /// `trp_ReadId`: an identifier LS4's buffer holds.
    fn atom(&mut self, name: &str) -> Option<usize> {
        if name.len() > IDENTIFIER_LIMIT {
            return None;
        }
        let atom = match self.numbers.get(name) {
            Some(&atom) => atom,
            None => {
                self.atoms.push(name.to_owned());
                self.numbers.insert(name.to_owned(), self.atoms.len() - 1);
                self.atoms.len() - 1
            }
        };
        Some(self.add(Formula::Atom(atom)))
    }

    /// `trp_ReadLiteral`: an identifier or `not` one; an argument list is a syntax error.
    fn literal(&mut self, literal: &translate::Formula) -> Option<usize> {
        use translate::Formula::*;
        match literal {
            Atom(name, args) if args.is_empty() => self.atom(name),
            NotAtom(name, args) if args.is_empty() => {
                let atom = self.atom(name)?;
                Some(self.add(Formula::Not(atom)))
            }
            True => self.atom("True"),
            False => self.atom("False"),
            _ => None,
        }
    }

    /// `trp_ReadClauseCore`: the clause's disjunction, or none where LS4 rejects the clause.
    fn clause(&mut self, clause: &[translate::Formula], is_universal: bool) -> Option<usize> {
        use translate::Formula::*;
        let mut disjunction = None;
        let mut has_next = false;
        let mut has_eventuality = false;
        for literal in clause {
            let node = match literal {
                Sometime(inner) => {
                    if !is_universal || has_next || has_eventuality {
                        return None;
                    }
                    has_eventuality = true;
                    let inner = self.literal(inner)?;
                    self.add(Formula::Eventually(inner))
                }
                Next(inner) => {
                    if !is_universal || has_eventuality {
                        return None;
                    }
                    has_next = true;
                    let inner = self.literal(inner)?;
                    self.add(Formula::Next(inner))
                }
                _ => self.literal(literal)?,
            };
            disjunction = Some(match disjunction {
                Some(left) => self.add(Formula::Or(left, node)),
                None => node,
            });
        }
        Some(disjunction.unwrap_or_else(|| self.add(Formula::Constant(false))))
    }

    fn spec(mut self, clauses: &Clauses) -> Option<Formulas> {
        let mut conjunction = None;
        let lists = [
            (&clauses.initial, false),
            (&clauses.universal, true),
            (&clauses.step, true),
            (&clauses.eventuality, true),
        ];
        for (list, is_universal) in lists {
            for clause in list {
                let mut node = self.clause(clause, is_universal)?;
                if is_universal {
                    node = self.add(Formula::Always(node));
                }
                conjunction = Some(match conjunction {
                    Some(left) => self.add(Formula::And(left, node)),
                    None => node,
                });
            }
        }
        let root = conjunction.unwrap_or_else(|| self.add(Formula::Constant(true)));
        Some(Formulas {
            nodes: self.nodes,
            atoms: self.atoms,
            root,
        })
    }
}

/// The verdict, with the steps as its one statistic, each a check of the limits.
pub fn decide(text: &str, limits: &Limits) -> Result<Decision, DecideError> {
    let formulas = translate::translate(text)
        .ok()
        .and_then(|clauses| Builder::default().spec(&clauses));
    let verdict = match formulas {
        Some(formulas) => get_satisfiability(&formulas, &mut || {
            limits.is_step_limit_reached() || limits.is_canceled() || limits.is_past_deadline()
        }),
        None => Verdict::Unknown,
    };
    Ok(Decision {
        verdict,
        statistics: vec![("steps", Statistic::Count(limits.steps()))],
    })
}

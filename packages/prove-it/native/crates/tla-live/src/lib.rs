//! Prove It's liveness checker (native/DESIGN.md 5.1, stage 3): TLC's check of the temporal
//! properties on the graph of a complete search, as `liveness-checker.ts` makes it. It builds the
//! tableau of the negated properties and fairness, a behavior graph per solution with each state's
//! successors in TLC's order, searches each graph's strongly connected components and chooses the
//! counterexample TLC prints. The predicates it asks about are the engine's answers, one table per
//! atom (`tla-engine`'s `live`); where the engine left one to the interpreter, it declines, and the
//! interpreter's checker checks the properties as before.

mod checker;
mod tableau;

use tableau::{TermId, Terms};

/// A term of the formula, in prefix order: each junction is followed by its operands and each
/// unary term by its body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Term {
    Boolean(bool),
    /// A state predicate, by the position of its atom, whose table has an answer per state.
    State(u32),
    /// ENABLED, by the position of its atom, whose table has an answer per state.
    Enabled(u32),
    /// An action predicate, whose table has an answer per step and then per state for its
    /// stuttering step, with the atom of its fairness's ENABLED.
    Action {
        atom: u32,
        enabled: Option<u32>,
    },
    Not,
    Always,
    Eventually,
    Next,
    And(u32),
    Or(u32),
}

/// A complete search: each state's parent, -1 for an initial state, its steps, those from state
/// i in `edges[edge_offsets[i]..edge_offsets[i + 1]]` in the order generated, and TLC's
/// fingerprint of each state. Under SYMMETRY or a VIEW, `edge_offsets` goes on past the states
/// stored with the steps from the states past them that `reals` names, as many as the engine
/// expanded.
pub struct Graph<'g> {
    pub parents: &'g [i32],
    pub edge_offsets: &'g [u32],
    pub edges: &'g [u32],
    pub fingerprints: &'g [u64],
    /// Under SYMMETRY or a VIEW, the state each step reached, which TLC checks: the state stored for
    /// it, by its index, or a state past them that the search told apart from it by its key. The
    /// tables of state predicates have an answer for each.
    pub reals: Option<&'g [u32]>,
    /// Where an atom reads TLCGet("diameter"), what TLC's diameter is as it adds each state.
    pub diameters: Option<Diameters<'g>>,
}

/// TLC's diameter, the deepest level its search has found so far, as it adds each state to the
/// behavior graphs, after the search expanded it, and once the search is done; and the atoms that
/// read it, whose tables hold the answers for each diameter from 1 to the last, one after another.
pub struct Diameters<'g> {
    pub states: &'g [u32],
    pub last: u32,
    pub atoms: &'g [bool],
}

impl Graph<'_> {
    fn count(&self) -> usize {
        self.parents.len()
    }

    /// How many of the states the search stored it expanded, which have their steps: all of them
    /// once it is complete, and the first few for a check part way through it. Under SYMMETRY or a
    /// VIEW the steps of the states it reached but didn't store follow theirs.
    fn expanded(&self) -> usize {
        self.edge_offsets.len().saturating_sub(1).min(self.count())
    }
}

/// Where the checker asks an atom: of a state, of the step at a position of the graph's edges, from
/// its state, or of a state's stuttering step.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Slot {
    State(u32),
    Step { state: u32, edge: u32 },
    Stutter(u32),
}

/// The engine's answers to the atoms, each asked as TLC evaluates it, with TLC's diameter then.
pub trait Answers {
    /// The atom's answer, or why the engine doesn't answer it.
    fn answer(&self, atom: u32, slot: Slot, diameter: u32) -> Result<bool, Declined>;

    /// Where the answer is among the atom's, as the evaluations logged and an unanswered atom
    /// name it.
    fn position(&self, atom: u32, slot: Slot, diameter: u32) -> usize;

    /// Whether the ENABLED atom of an action's fairness is known false of the state, where the
    /// checker asks about no step from it.
    fn is_disabled(&self, _enabled: u32, _state: u32) -> bool {
        false
    }
}

/// What the checker reads as it adds a state: the search's graph so far, and the atoms' answers.
#[derive(Clone, Copy)]
pub struct Source<'s> {
    pub graph: &'s Graph<'s>,
    pub answers: &'s dyn Answers,
}

/// The answers of a search that is over, one table per atom (`None` for an atom the engine doesn't
/// answer): a state predicate's or ENABLED's answer per state, an action's per step and then per
/// state for its stuttering step, 0 or 1, and for an atom that reads TLCGet("diameter") the
/// answers for each diameter one after another.
struct Tables<'t> {
    tables: &'t [Option<&'t [u8]>],
    graph: &'t Graph<'t>,
}

impl Answers for Tables<'_> {
    fn answer(&self, atom: u32, slot: Slot, diameter: u32) -> Result<bool, Declined> {
        let position = self.position(atom, slot, diameter);
        let answer = self
            .tables
            .get(atom as usize)
            .copied()
            .map(|table| table.map(|answers| answers.get(position).copied()));
        match answer {
            Some(Some(Some(0))) => Ok(false),
            Some(Some(Some(1))) => Ok(true),
            Some(Some(_)) => Err(Declined::from(
                "a predicate the engine leaves to the interpreter",
            )),
            _ => Err(Declined::from("an atom the engine doesn't answer")),
        }
    }

    fn position(&self, atom: u32, slot: Slot, diameter: u32) -> usize {
        let position = match slot {
            Slot::State(state) => state as usize,
            Slot::Step { edge, .. } => edge as usize,
            Slot::Stutter(state) => self.graph.edges.len() + state as usize,
        };
        match &self.graph.diameters {
            Some(diameters) if diameters.atoms.get(atom as usize) == Some(&true) => {
                let length = self.tables[atom as usize].map_or(0, <[u8]>::len);
                length / diameters.last as usize * (diameter as usize - 1) + position
            }
            _ => position,
        }
    }

    fn is_disabled(&self, enabled: u32, state: u32) -> bool {
        matches!(
            self.tables.get(enabled as usize),
            Some(Some(table)) if table.get(state as usize) == Some(&0)
        )
    }
}

/// What the check found, and how many solutions of the formula TLC checks, which it calls branches,
/// unless it declined before it knew, with the evaluations of the atoms where they have effects.
#[derive(Debug, PartialEq, Eq)]
pub struct Liveness {
    pub branches: Option<usize>,
    pub verdict: Verdict,
    pub events: Vec<Event>,
    /// Where the checker declined at an atom the engine didn't answer as it added a state the
    /// search expanded, that atom: TLC evaluates it there, and may fail.
    pub unanswered: Option<Unanswered>,
}

/// An atom the engine didn't answer, at the position `slot` in its table, which TLC evaluates as
/// it adds `state` to the behavior graphs: as an initial state, `is_initial`, or once the search
/// expanded it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unanswered {
    pub state: u32,
    pub atom: u32,
    pub slot: u32,
    pub is_initial: bool,
}

/// Where the atoms' evaluations have effects, such as what Print prints, TLC has them each time it
/// evaluates an atom while it builds the behavior graphs: the evaluations in its order, after the
/// state each starts to add.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Event {
    /// TLC adds an initial state.
    Initial(u32),
    /// TLC adds a state it expanded, with its successors.
    Expanded(u32),
    /// TLC runs Next from the state for a node of it it finds late.
    Late(u32),
    /// TLC evaluates an atom: on the state at the position in its table, or on the step.
    Atom { atom: u32, slot: usize },
    /// TLC has a lasso, and evaluates each property on it to find those it violates
    /// (`Liveness.findViolatedProperties`): the evaluations follow.
    Lasso,
}

/// Adds the states the search expanded to the behavior graphs, as TLC does as it searches even
/// under `-lncheck final`: the first whose tableau node accepts every behavior, which stops TLC's
/// search there, as a `Verdict::Accepted`.
pub fn find_accepted(
    formula: &[Term],
    properties: &[&[Term]],
    graph: &Graph<'_>,
    tables: &[Option<&[u8]>],
) -> Result<Option<Verdict>, Declined> {
    let mut terms = Terms::default();
    let root = read_formula(&mut terms, formula)?;
    let properties = properties
        .iter()
        .map(|property| read_formula(&mut terms, property))
        .collect::<Result<Vec<_>, _>>()?;
    let mut checker = checker::Checker::new(terms, root)?;
    let answers = Tables { tables, graph };
    let source = Source {
        graph,
        answers: &answers,
    };
    checker::find_accepted(&mut checker, &source)?
        .map(|(state, path)| checker::accepted(&checker, &source, &properties, state, path))
        .transpose()
}

/// The first atom the engine didn't answer that TLC evaluates as it adds the states the search
/// expanded to the behavior graphs, where it may fail, unless TLC stops first at a node that
/// accepts every behavior.
pub fn find_unanswered(
    formula: &[Term],
    graph: &Graph<'_>,
    tables: &[Option<&[u8]>],
) -> Option<Unanswered> {
    let mut terms = Terms::default();
    let root = read_formula(&mut terms, formula).ok()?;
    let mut checker = checker::Checker::new(terms, root).ok()?;
    let answers = Tables { tables, graph };
    checker::find_unanswered(
        &mut checker,
        &Source {
            graph,
            answers: &answers,
        },
    )
}

/// What the check found.
#[derive(Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The properties hold.
    Holds,
    /// A counterexample: the states of the lasso, the cycle from `loop_start` on, whether the
    /// solution it violates constrains the cycle, so TLC warns of a stuttering one, and the
    /// positions of the properties it violates, which TLC names.
    Lasso {
        path: Vec<u32>,
        loop_start: usize,
        is_cycle_constrained: bool,
        violated: Vec<usize>,
    },
    /// A tableau node that accepts every behavior, which TLC reports as it adds `state` to the
    /// graph, with the path of states to it and the positions of the properties it violates.
    Accepted {
        state: u32,
        path: Vec<u32>,
        violated: Vec<usize>,
    },
    /// The checker needs the steps from the states past the stored ones that `reals` names and the
    /// graph doesn't expand yet: the engine expands them and checks again.
    Unexpanded,
    /// The interpreter checks the properties: why.
    Declined(Declined),
}

/// Why the checker declines where it needs steps the engine doesn't take.
pub const UNEXPANDED: &str = "a late node of a state the engine didn't expand";

/// Why the native checker leaves the properties to the interpreter.
#[derive(Debug, PartialEq, Eq)]
pub struct Declined(pub String);

impl From<&str> for Declined {
    fn from(reason: &str) -> Self {
        Self(reason.to_owned())
    }
}

fn read_term(terms: &mut Terms, formula: &[Term], at: &mut usize) -> Result<TermId, Declined> {
    let term = *formula
        .get(*at)
        .ok_or_else(|| Declined::from("a formula cut short"))?;
    *at += 1;
    let (kind, count) = match term {
        Term::Boolean(value) => (tableau::Kind::Boolean(value), 0),
        Term::State(atom) => (tableau::Kind::State(atom), 0),
        Term::Enabled(atom) => (tableau::Kind::Enabled(atom), 0),
        Term::Action { atom, enabled } => (tableau::Kind::Action { atom, enabled }, 0),
        Term::Not => (tableau::Kind::Not, 1),
        Term::Always => (tableau::Kind::Always, 1),
        Term::Eventually => (tableau::Kind::Eventually, 1),
        Term::Next => (tableau::Kind::Next, 1),
        Term::And(count) => (tableau::Kind::And, count),
        Term::Or(count) => (tableau::Kind::Or, count),
    };
    let children = (0..count)
        .map(|_| read_term(terms, formula, at))
        .collect::<Result<_, _>>()?;
    Ok(terms.create(kind, children))
}

fn read_formula(terms: &mut Terms, formula: &[Term]) -> Result<TermId, Declined> {
    let mut at = 0;
    let root = read_term(terms, formula, &mut at)?;
    if at != formula.len() {
        return Err(Declined::from("a formula with terms past its end"));
    }
    Ok(root)
}

/// The positions of the properties a lasso of `length` states, whose cycle starts at
/// `loop_start`, violates (`Liveness.findViolatedProperties`, `evaluateOnLasso`): each property
/// evaluated from its first state, an atom by `answer` of its atom term, the position of the state
/// and that of the next, which for the last state is the cycle's first.
pub fn violated_on_lasso(
    properties: &[&[Term]],
    length: usize,
    loop_start: usize,
    answer: &mut dyn FnMut(Term, usize, usize) -> Result<bool, Declined>,
) -> Result<Vec<usize>, Declined> {
    let mut lasso = Lasso {
        length,
        loop_start,
        answer,
    };
    let mut violated = Vec::new();
    for (position, terms) in properties.iter().enumerate() {
        if !lasso.evaluate(terms, 0, 0)? {
            violated.push(position);
        }
    }
    Ok(violated)
}

struct Lasso<'a> {
    length: usize,
    loop_start: usize,
    answer: &'a mut dyn FnMut(Term, usize, usize) -> Result<bool, Declined>,
}

impl Lasso<'_> {
    fn next(&self, position: usize) -> usize {
        if position + 1 < self.length {
            position + 1
        } else {
            self.loop_start
        }
    }

    /// The term at `at` and those of its operands: where the next term starts.
    fn skip(terms: &[Term], at: usize) -> usize {
        let mut at = at;
        let mut pending = 1usize;
        while pending > 0 {
            pending -= 1;
            pending += match terms[at] {
                Term::Not | Term::Always | Term::Eventually | Term::Next => 1,
                Term::And(count) | Term::Or(count) => count as usize,
                _ => 0,
            };
            at += 1;
        }
        at
    }

    fn evaluate(&mut self, terms: &[Term], at: usize, position: usize) -> Result<bool, Declined> {
        let Some(&term) = terms.get(at) else {
            return Err(Declined::from("a formula that ends early"));
        };
        // The states from the earlier of this one and the cycle's first, which the lasso
        // repeats from then on.
        let future = position.min(self.loop_start)..self.length;
        match term {
            Term::Boolean(value) => Ok(value),
            Term::State(_) | Term::Enabled(_) | Term::Action { .. } => {
                let next = self.next(position);
                (self.answer)(term, position, next)
            }
            Term::Not => Ok(!self.evaluate(terms, at + 1, position)?),
            Term::Next => {
                let next = self.next(position);
                self.evaluate(terms, at + 1, next)
            }
            Term::Always | Term::Eventually => {
                let is_always = term == Term::Always;
                for future in future {
                    if self.evaluate(terms, at + 1, future)? != is_always {
                        return Ok(!is_always);
                    }
                }
                Ok(is_always)
            }
            Term::And(count) | Term::Or(count) => {
                let is_and = matches!(term, Term::And(_));
                let mut operand = at + 1;
                for _ in 0..count {
                    if self.evaluate(terms, operand, position)? != is_and {
                        return Ok(!is_and);
                    }
                    operand = Self::skip(terms, operand);
                }
                Ok(is_and)
            }
        }
    }
}

/// The atoms of a formula, in the order TLC's liveness checker asks about them (`atoms` of
/// `createLivenessChecker`): the state and ENABLED atoms of each solution's checks and then of its
/// tableau's nodes, as `collectAtoms` meets them, then the rest the checks ask of, as
/// `collectQuestions` does. An atom is its position in `formula`'s terms, each term standing for
/// itself; a tautology, which has no solutions, declines.
pub fn atom_order(formula: &[Term]) -> Result<Vec<u32>, Declined> {
    let mut terms = Terms::default();
    let root = read_formula(&mut terms, formula)?;
    let solutions = terms.solutions(root)?;
    let mut order = Vec::new();
    let mut add = |atom: u32| {
        if !order.contains(&atom) {
            order.push(atom);
        }
    };
    let collect = |term: TermId, is_question: bool, add: &mut dyn FnMut(u32)| {
        let mut pending = vec![term];
        while let Some(term) = pending.pop() {
            match terms.kind(term) {
                tableau::Kind::State(atom) | tableau::Kind::Enabled(atom) => add(atom),
                tableau::Kind::Action { atom, .. } if is_question => add(atom),
                tableau::Kind::Action {
                    enabled: Some(enabled),
                    ..
                } => add(enabled),
                tableau::Kind::Next if !is_question => {}
                tableau::Kind::Action { .. } | tableau::Kind::Boolean(_) => {}
                _ => pending.extend(terms.children(term).iter().rev()),
            }
        }
    };
    for solution in &solutions {
        for &predicate in solution.state_checks.iter().chain(&solution.action_checks) {
            collect(predicate, false, &mut add);
        }
        for node in solution.tableau.iter().flat_map(|tableau| &tableau.nodes) {
            for &predicate in &node.state_predicates {
                collect(predicate, false, &mut add);
            }
        }
    }
    for solution in &solutions {
        for &predicate in solution.state_checks.iter().chain(&solution.action_checks) {
            collect(predicate, true, &mut add);
        }
    }
    Ok(order)
}

/// Checks the formula, the fairness and the negated properties as `createLivenessChecker` joins
/// them, on a search's graph, from the engine's answers to each atom (`None` for an atom
/// it doesn't answer), and finds which of the properties a counterexample violates. Where the
/// atoms' evaluations have effects, it logs each evaluation of an atom TLC makes.
pub fn check(
    formula: &[Term],
    properties: &[&[Term]],
    graph: &Graph<'_>,
    tables: &[Option<&[u8]>],
    is_effectful: bool,
) -> Liveness {
    let mut branches = None;
    let mut events = Vec::new();
    let mut unanswered = None;
    let mut run = || {
        if graph.edge_offsets.is_empty() {
            return Err(Declined::from("a graph without its steps"));
        }
        let mut terms = Terms::default();
        let root = read_formula(&mut terms, formula)?;
        let properties = properties
            .iter()
            .map(|property| read_formula(&mut terms, property))
            .collect::<Result<Vec<_>, _>>()?;
        let mut checker = checker::Checker::new(terms, root)?;
        branches = Some(checker.branches());
        if is_effectful {
            checker.log_effects();
        }
        let answers = Tables { tables, graph };
        let source = Source {
            graph,
            answers: &answers,
        };
        let verdict = checker::check(&mut checker, &source, &properties, &mut events);
        unanswered = verdict.is_err().then(|| checker.unanswered.get()).flatten();
        verdict
    };
    let verdict = run().unwrap_or_else(|declined| {
        if declined.0 == UNEXPANDED {
            Verdict::Unexpanded
        } else {
            Verdict::Declined(declined)
        }
    });
    Liveness {
        branches,
        verdict,
        events,
        unanswered,
    }
}

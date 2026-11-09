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
}

/// What the check found, and how many solutions of the formula TLC checks, which it calls branches,
/// unless it declined before it knew, with the evaluations of the atoms where they have effects.
#[derive(Debug, PartialEq, Eq)]
pub struct Liveness {
    pub branches: Option<usize>,
    pub verdict: Verdict,
    pub events: Vec<Event>,
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
    /// graph, with the path of states to it.
    Accepted { state: u32, path: Vec<u32> },
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

/// Checks the formula, the fairness and the negated properties as `createLivenessChecker` joins
/// them, on a complete search's graph, from the engine's answers to each atom (`None` for an atom
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
    let mut run = || {
        if graph.edge_offsets.len() <= graph.count() {
            return Err(Declined::from("a search that didn't expand every state"));
        }
        let mut terms = Terms::default();
        let root = read_formula(&mut terms, formula)?;
        let properties = properties
            .iter()
            .map(|property| read_formula(&mut terms, property))
            .collect::<Result<Vec<_>, _>>()?;
        let mut checker = checker::Checker::new(terms, root, graph, tables)?;
        branches = Some(checker.branches());
        if is_effectful {
            checker.log_effects();
        }
        checker::check(&mut checker, &properties, &mut events)
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
    }
}

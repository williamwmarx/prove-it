//! tlapm's proof IR (P_t). A port of `src/obligations/proof.ts`.

use std::cell::Cell;

use crate::expression::{Bound, Defn, Expr, Locus, Sequent};
use crate::pragma::OldMethod;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StepNumber {
    /// `level` is an OCaml int, as tlapm's lexer reads it (alexer.mll:93).
    Named {
        level: i64,
        label: String,
        is_anonymous: bool,
    },
    Unnamed {
        level: i64,
        id: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UseDefCore {
    Dvar { name: String },
    Dx { index: isize },
}

#[derive(Clone, Debug)]
pub struct UseDef {
    pub core: UseDefCore,
    pub location: Option<Locus>,
}

#[derive(Clone, Debug, Default)]
pub struct Usable {
    pub facts: Vec<Expr>,
    pub defs: Vec<UseDef>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Omission {
    Implicit,
    Explicit,
    Elsewhere,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ObligationKind {
    Main,
    Support,
    Error(String),
    Omitted(Omission),
}

/// `method` is the one an old-style pragma names, which keeps find_meth from choosing.
#[derive(Clone, Debug)]
pub struct Obligation {
    pub sequent: Sequent,
    pub location: Option<Locus>,
    pub kind: ObligationKind,
    pub method: Option<OldMethod>,
}

/// `ProofProps`. `use_location` is where a USE step comes from, so find_meth can tell apart the
/// facts of each BY.
#[derive(Clone, Debug, Default)]
pub struct ProofProps {
    pub location: Option<Locus>,
    pub step: Option<StepNumber>,
    pub obligations: Option<Vec<Obligation>>,
    pub method: Option<OldMethod>,
    pub use_location: Option<Locus>,
}

#[derive(Clone, Debug)]
pub struct Proof {
    pub core: ProofCore,
    pub props: ProofProps,
}

#[derive(Clone, Debug)]
pub enum ProofCore {
    Obvious,
    Omitted(Omission),
    By { usable: Usable, is_only: bool },
    Steps { steps: Vec<Step>, qed: Box<QedStep> },
    Error(String),
}

#[derive(Clone, Debug)]
pub struct QedStep {
    pub proof: Proof,
    pub props: ProofProps,
}

#[derive(Clone, Debug)]
pub struct Step {
    pub core: StepCore,
    pub props: ProofProps,
}

#[derive(Clone, Debug)]
pub enum StepCore {
    Hide {
        usable: Usable,
    },
    Define {
        definitions: Vec<Defn>,
    },
    Assert {
        sequent: Sequent,
        proof: Proof,
    },
    Suffices {
        sequent: Sequent,
        proof: Proof,
    },
    Pcase {
        expression: Expr,
        proof: Proof,
    },
    Pick {
        bounds: Vec<Bound>,
        expression: Expr,
        proof: Proof,
    },
    Use {
        usable: Usable,
        is_only: bool,
    },
    Have {
        expression: Expr,
    },
    Take {
        bounds: Vec<Bound>,
    },
    Witness {
        expressions: Vec<Expr>,
    },
    Forget {
        count: usize,
    },
}

pub fn get_step_name(step: &StepNumber) -> String {
    match step {
        StepNumber::Named { level, label, .. } => format!("<{level}>{label}"),
        StepNumber::Unnamed { level, .. } => format!("<{level}>"),
    }
}

/// Std.unique: one counter for the whole run, shared by the parser, anonymization, and
/// simplification, so anonymous step names match tlapm's.
#[derive(Debug, Default)]
pub struct Counter {
    pub value: Cell<usize>,
}

pub fn get_unique(counter: &Counter) -> usize {
    let next = counter.value.get() + 1;
    counter.value.set(next);
    next
}

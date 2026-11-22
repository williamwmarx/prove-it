//! tlapm's proof IR (P_t). A port of `src/obligations/proof.ts`.

use std::cell::Cell;

use crate::expression::{Bound, Defn, Expr, Locus, Sequent};
use crate::pragma::OldMethod;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StepNumber {
    Named {
        level: usize,
        label: String,
        is_anonymous: bool,
    },
    Unnamed {
        level: usize,
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
    /// Module.Elab's `enabledaxioms` property, from the leaf proof: see ProofProps.
    pub is_enabled_axioms_sound: Option<bool>,
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
    /// Props.supp: a suppression pragma precedes the step or proof, whose obligations are kept but
    /// not emitted (Proof.Gen.collect's obgetter).
    pub is_suppressed: bool,
    /// Module.Elab's `enabledaxioms` property, which its ENABLEDaxioms check assigns to each leaf
    /// proof of a theorem that cites the directive: whether the assumptions the leaf depends on
    /// are all of level at most 1, which the directive's rule is sound for. None where the
    /// theorem never cites it.
    pub is_enabled_axioms_sound: Option<bool>,
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

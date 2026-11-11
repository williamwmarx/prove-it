//! Ported from Z3 (src/smt/smt_enode.h, src/smt/smt_eq_justification.h,
//! src/smt/smt_justification.h), MIT license, see z3-license.txt, through `enode.ts`. E-graph nodes
//! and the justifications for their equalities.
//!
//! The nodes live in an `Enodes` arena and the justifications in a `Justifications` arena, both
//! owned by the context, and refer to each other by handle (design/smt-core.md §2). A handle is
//! never reused, so a handle never aliases a newer object.

use super::literal::Literal;
use crate::core::ast::{Decl, Expr};
use crate::util::error::SmtError;

/// A node: its index in `Enodes`.
pub type EnodeId = u32;
/// A justification: its index in `Justifications`.
pub type JustificationId = u32;

/// What a justification marks to explain itself, implemented by the conflict resolution. It also
/// reads, for the justifications, what they read through their nodes in the TypeScript.
pub trait Antecedents {
    fn mark_literal(&mut self, literal: Literal);
    fn mark_eq(&mut self, first: EnodeId, second: EnodeId);
    fn mark_justification(&mut self, justification: JustificationId);
    fn mark_justified_eq(
        &mut self,
        first: EnodeId,
        second: EnodeId,
        justification: EqJustification,
    );
    /// `node.root`.
    fn get_root(&self, node: EnodeId) -> EnodeId;
    /// The `getLiteral` of an `MpIffJustification`, which the context always makes
    /// `(node) => this.enodeToLiteral(node)`.
    fn enode_to_literal(&self, node: EnodeId) -> Result<Literal, SmtError>;
}

/// The subclasses of `Justification`, whose `isMarked` is kept by `Justifications`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Justification {
    /// eq_propagation_justification: the equality atom is true because its sides are in one class.
    EqPropagation { first: EnodeId, second: EnodeId },
    /// eq_root_propagation_justification: a Boolean node merged with true or false.
    EqRootPropagation { node: EnodeId },
    /// eq_conflict_justification: two interpreted roots, such as two numerals, were merged.
    EqConflict {
        first: EnodeId,
        second: EnodeId,
        justification: EqJustification,
    },
    /// mp_iff_justification: a Boolean node takes the value of an equal node. Its `getLiteral` is
    /// `Antecedents::enode_to_literal`.
    MpIff { first: EnodeId, second: EnodeId },
    /// unit_resolution_justification: a clause simplified with literals that were false.
    UnitResolution {
        justification: Option<JustificationId>,
        literals: Vec<Literal>,
    },
    /// ext_theory_propagation_justification: theory reasoning from literals and equalities, the
    /// equalities as pairs of nodes. The arithmetic theory makes it with the literals of its core
    /// and no equalities; a theory that needs data of its own for its explanation adds a variant
    /// here carrying it, explained by its own arm of `get_antecedents`.
    Theory {
        literals: Vec<Literal>,
        eqs: Vec<EnodeId>,
    },
}

impl Justification {
    pub fn get_antecedents(&self, antecedents: &mut impl Antecedents) -> Result<(), SmtError> {
        match self {
            Justification::EqPropagation { first, second } => antecedents.mark_eq(*first, *second),
            Justification::EqRootPropagation { node } => {
                let root = antecedents.get_root(*node);
                antecedents.mark_eq(*node, root);
            }
            Justification::EqConflict {
                first,
                second,
                justification,
            } => {
                let first_root = antecedents.get_root(*first);
                antecedents.mark_eq(*first, first_root);
                let second_root = antecedents.get_root(*second);
                antecedents.mark_eq(*second, second_root);
                antecedents.mark_justified_eq(*first, *second, *justification);
            }
            Justification::MpIff { first, second } => {
                antecedents.mark_eq(*first, *second);
                let literal = antecedents.enode_to_literal(*first)?;
                antecedents.mark_literal(literal);
            }
            Justification::UnitResolution {
                justification,
                literals,
            } => {
                if let Some(justification) = justification {
                    antecedents.mark_justification(*justification);
                }
                for literal in literals {
                    antecedents.mark_literal(*literal);
                }
            }
            Justification::Theory { literals, eqs } => {
                for literal in literals {
                    antecedents.mark_literal(*literal);
                }
                for pair in eqs.as_chunks::<2>().0 {
                    antecedents.mark_eq(pair[0], pair[1]);
                }
            }
        }
        Ok(())
    }
}

/// The justifications of a context, each with its `isMarked`.
#[derive(Clone, Debug, Default)]
pub struct Justifications {
    entries: Vec<Justification>,
    marks: Vec<bool>,
}

impl Justifications {
    pub fn new() -> Self {
        Self::default()
    }

    /// `new …Justification(…)`.
    pub fn mk(&mut self, justification: Justification) -> JustificationId {
        let id = self.entries.len() as JustificationId;
        self.entries.push(justification);
        self.marks.push(false);
        id
    }

    pub fn get(&self, id: JustificationId) -> &Justification {
        &self.entries[id as usize]
    }

    pub fn is_marked(&self, id: JustificationId) -> bool {
        self.marks[id as usize]
    }

    pub fn set_marked(&mut self, id: JustificationId, value: bool) {
        self.marks[id as usize] = value;
    }

    /// The justifications to read and their marks to write at once, as the conflict resolution
    /// does while it explains one justification and marks those it leads to.
    pub fn split_marks(&mut self) -> (&[Justification], &mut [bool]) {
        (&self.entries, &mut self.marks)
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// eq_justification: why two nodes on a transitivity branch are equal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EqJustification {
    Axiom,
    Congruence { is_commutative: bool },
    Equation { literal: Literal },
    Justification { justification: JustificationId },
}

pub const AXIOM_EQ_JUSTIFICATION: EqJustification = EqJustification::Axiom;

/// The congruence justifications, which carry no data of their own and so are shared.
pub const CONGRUENCE_JUSTIFICATIONS: [EqJustification; 2] = [
    EqJustification::Congruence {
        is_commutative: false,
    },
    EqJustification::Congruence {
        is_commutative: true,
    },
];

const IS_EQ: u32 = 1;
const IS_BOOL: u32 = 2;
const IS_MERGE_TF: u32 = 4;
const IS_CGC_ENABLED: u32 = 8;
const IS_MARKED: u32 = 16;
const IS_MARKED2: u32 = 32;
const IS_INTERPRETED: u32 = 64;
/// The number of arguments, in the bits of flags above the Boolean fields.
const NUM_ARGS_SHIFT: u32 = 7;

#[derive(Clone, Debug)]
pub struct Enode {
    pub owner: Expr,
    pub decl: Decl,
    pub root: EnodeId,
    pub next: EnodeId,
    pub cg: EnodeId,
    pub class_size: u32,
    /// The parents, empty for a node without any.
    pub parents: Vec<EnodeId>,
    /// m_trans: the next node on the transitivity branch toward the root of the proof tree, and why
    /// the two are equal.
    pub trans_target: Option<EnodeId>,
    pub trans_justification: EqJustification,
    pub th_var: i32,
    /// The approximate label sets of the class, 64 bits in two words: the low 32 bits, then the
    /// high.
    pub lbls: u32,
    pub lbls_high: u32,
    pub plbls: u32,
    pub plbls_high: u32,
    pub lbl_hash: i32,
    pub generation: u32,
    pub iscope_level: u32,
    /// The Boolean fields, one bit each, so a node takes 48 bytes less, and the number of
    /// arguments.
    flags: u32,
    /// m_args: the first two arguments inline, like Z3's arguments after the node, and the rest in
    /// an array. A missing argument is the node itself.
    arg0: EnodeId,
    arg1: EnodeId,
    more_args: Vec<EnodeId>,
}

impl Enode {
    fn set_flag(&mut self, flag: u32, value: bool) {
        self.flags = if value {
            self.flags | flag
        } else {
            self.flags & !flag
        };
    }

    pub fn num_args(&self) -> u32 {
        self.flags >> NUM_ARGS_SHIFT
    }

    pub fn get_arg(&self, index: u32) -> EnodeId {
        match index {
            0 => self.arg0,
            1 => self.arg1,
            _ => self.more_args[index as usize - 2],
        }
    }

    pub fn is_eq(&self) -> bool {
        self.flags & IS_EQ != 0
    }

    pub fn is_bool(&self) -> bool {
        self.flags & IS_BOOL != 0
    }

    pub fn is_cgc_enabled(&self) -> bool {
        self.flags & IS_CGC_ENABLED != 0
    }

    pub fn is_merge_tf(&self) -> bool {
        self.flags & IS_MERGE_TF != 0
    }

    pub fn set_is_merge_tf(&mut self, value: bool) {
        self.set_flag(IS_MERGE_TF, value);
    }

    pub fn is_marked(&self) -> bool {
        self.flags & IS_MARKED != 0
    }

    pub fn set_is_marked(&mut self, value: bool) {
        self.set_flag(IS_MARKED, value);
    }

    pub fn is_marked2(&self) -> bool {
        self.flags & IS_MARKED2 != 0
    }

    pub fn set_is_marked2(&mut self, value: bool) {
        self.set_flag(IS_MARKED2, value);
    }

    pub fn is_interpreted(&self) -> bool {
        self.flags & IS_INTERPRETED != 0
    }

    pub fn set_is_interpreted(&mut self, value: bool) {
        self.set_flag(IS_INTERPRETED, value);
    }

    pub fn add_parent(&mut self, parent: EnodeId) {
        self.parents.push(parent);
    }
}

/// The nodes of a context. A node's methods that read other nodes are methods here.
#[derive(Clone, Debug, Default)]
pub struct Enodes {
    nodes: Vec<Enode>,
}

impl Enodes {
    pub fn new() -> Self {
        Self::default()
    }

    /// `new Enode(…)`. `more_args` are the arguments past the second, and `arg0` and `arg1` are
    /// `None` when there are fewer.
    #[expect(
        clippy::too_many_arguments,
        reason = "the parameters of the TypeScript constructor"
    )]
    pub fn mk(
        &mut self,
        owner: Expr,
        decl: Decl,
        num_args: u32,
        arg0: Option<EnodeId>,
        arg1: Option<EnodeId>,
        more_args: Vec<EnodeId>,
        generation: u32,
        is_eq: bool,
        is_bool: bool,
        is_merge_tf: bool,
        is_cgc_enabled: bool,
        iscope_level: u32,
    ) -> EnodeId {
        let id = self.nodes.len() as EnodeId;
        self.nodes.push(Enode {
            owner,
            decl,
            root: id,
            next: id,
            cg: id,
            class_size: 1,
            parents: Vec::new(),
            trans_target: None,
            trans_justification: AXIOM_EQ_JUSTIFICATION,
            th_var: -1,
            lbls: 0,
            lbls_high: 0,
            plbls: 0,
            plbls_high: 0,
            lbl_hash: -1,
            generation,
            iscope_level,
            flags: (num_args << NUM_ARGS_SHIFT)
                | if is_eq { IS_EQ } else { 0 }
                | if is_bool { IS_BOOL } else { 0 }
                | if is_merge_tf { IS_MERGE_TF } else { 0 }
                | if is_cgc_enabled { IS_CGC_ENABLED } else { 0 },
            arg0: arg0.unwrap_or(id),
            arg1: arg1.unwrap_or(id),
            more_args,
        });
        id
    }

    pub fn get(&self, id: EnodeId) -> &Enode {
        &self.nodes[id as usize]
    }

    pub fn get_mut(&mut self, id: EnodeId) -> &mut Enode {
        &mut self.nodes[id as usize]
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// `node.getArg(index).root`.
    pub fn get_arg_root(&self, node: EnodeId, index: u32) -> EnodeId {
        self.get(self.get(node).get_arg(index)).root
    }

    pub fn is_cgr(&self, node: EnodeId) -> bool {
        self.get(node).cg == node
    }

    pub fn is_true_eq(&self, node: EnodeId) -> bool {
        self.get(node).is_eq() && self.get_arg_root(node, 0) == self.get_arg_root(node, 1)
    }

    pub fn uses_cg_table(&self, node: EnodeId) -> bool {
        let enode = self.get(node);
        enode.num_args() > 0 && enode.is_cgc_enabled() && !self.is_true_eq(node)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk_leaf(enodes: &mut Enodes, owner: Expr) -> EnodeId {
        enodes.mk(
            owner,
            owner,
            0,
            None,
            None,
            Vec::new(),
            0,
            false,
            false,
            false,
            true,
            0,
        )
    }

    #[test]
    fn makes_a_node_its_own_class() {
        let mut enodes = Enodes::new();
        let leaf = mk_leaf(&mut enodes, 7);
        let node = enodes.get(leaf);
        assert_eq!(
            (node.root, node.next, node.cg, node.class_size),
            (leaf, leaf, leaf, 1)
        );
        assert_eq!((node.get_arg(0), node.get_arg(1)), (leaf, leaf));
        assert_eq!(node.trans_target, None);
        assert_eq!(node.th_var, -1);
        assert_eq!(node.lbl_hash, -1);
        assert!(enodes.is_cgr(leaf));
        assert!(!enodes.uses_cg_table(leaf));
    }

    #[test]
    fn packs_the_flags_and_the_number_of_arguments() {
        let mut enodes = Enodes::new();
        let args: Vec<EnodeId> = (0..4).map(|owner| mk_leaf(&mut enodes, owner)).collect();
        let node = enodes.mk(
            10,
            20,
            4,
            Some(args[0]),
            Some(args[1]),
            vec![args[2], args[3]],
            3,
            false,
            true,
            false,
            true,
            2,
        );
        let enode = enodes.get_mut(node);
        assert_eq!(enode.num_args(), 4);
        assert_eq!(
            (0..4).map(|index| enode.get_arg(index)).collect::<Vec<_>>(),
            args
        );
        assert!(enode.is_bool() && enode.is_cgc_enabled());
        assert!(!enode.is_eq() && !enode.is_merge_tf());
        enode.set_is_marked(true);
        enode.set_is_interpreted(true);
        enode.set_is_merge_tf(true);
        enode.set_is_marked(false);
        assert!(!enode.is_marked() && !enode.is_marked2());
        assert!(enode.is_interpreted() && enode.is_merge_tf());
        assert_eq!(enode.num_args(), 4);
        assert!(enodes.uses_cg_table(node));
    }

    #[test]
    fn an_equality_of_one_class_is_true() {
        let mut enodes = Enodes::new();
        let first = mk_leaf(&mut enodes, 0);
        let second = mk_leaf(&mut enodes, 1);
        let eq = enodes.mk(
            2,
            3,
            2,
            Some(first),
            Some(second),
            Vec::new(),
            0,
            true,
            true,
            false,
            true,
            0,
        );
        assert!(!enodes.is_true_eq(eq));
        assert!(enodes.uses_cg_table(eq));
        enodes.get_mut(second).root = first;
        assert!(enodes.is_true_eq(eq));
        assert!(!enodes.uses_cg_table(eq));
    }

    #[derive(Default)]
    struct Recorder {
        literals: Vec<Literal>,
        eqs: Vec<(EnodeId, EnodeId)>,
        justifications: Vec<JustificationId>,
    }

    impl Antecedents for Recorder {
        fn mark_literal(&mut self, literal: Literal) {
            self.literals.push(literal);
        }
        fn mark_eq(&mut self, first: EnodeId, second: EnodeId) {
            self.eqs.push((first, second));
        }
        fn mark_justification(&mut self, justification: JustificationId) {
            self.justifications.push(justification);
        }
        fn mark_justified_eq(&mut self, first: EnodeId, second: EnodeId, _: EqJustification) {
            self.eqs.push((first, second));
        }
        fn get_root(&self, node: EnodeId) -> EnodeId {
            node + 100
        }
        fn enode_to_literal(&self, node: EnodeId) -> Result<Literal, SmtError> {
            Ok(node * 2)
        }
    }

    #[test]
    fn justifications_mark_their_antecedents() {
        let mut justifications = Justifications::new();
        let theory = justifications.mk(Justification::Theory {
            literals: vec![4, 7],
            eqs: vec![1, 2, 3, 4],
        });
        let unit = justifications.mk(Justification::UnitResolution {
            justification: Some(theory),
            literals: vec![9],
        });
        let mp_iff = justifications.mk(Justification::MpIff {
            first: 5,
            second: 6,
        });
        let conflict = justifications.mk(Justification::EqConflict {
            first: 1,
            second: 2,
            justification: AXIOM_EQ_JUSTIFICATION,
        });
        let mut recorder = Recorder::default();
        for id in [theory, unit, mp_iff, conflict] {
            assert_eq!(
                justifications.get(id).get_antecedents(&mut recorder),
                Ok(())
            );
        }
        assert_eq!(recorder.literals, [4, 7, 9, 10]);
        assert_eq!(recorder.justifications, [theory]);
        assert_eq!(
            recorder.eqs,
            [(1, 2), (3, 4), (5, 6), (1, 101), (2, 102), (1, 2)]
        );
        assert!(!justifications.is_marked(unit));
        justifications.set_marked(unit, true);
        assert!(justifications.is_marked(unit) && !justifications.is_marked(theory));
    }
}

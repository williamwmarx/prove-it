//! The pieces of the next-state relation an action is made of, so that a step's answer to the
//! action is whether the walk that took it passed through one of them (perf.md, "Plan (ii)").
//!
//! An action matches pieces P of Next's walk where it is the disjunction of the pieces each taken
//! in its full context in Next: so the two are read side by side only through what adds no
//! context, a conjunction of one item, an `\E` over the same constant set (whose bound names then
//! stand for each other), a disjunction of which the action takes some disjuncts, and a global
//! definition with no arguments. A disjunct matches only where it is the same expression, up to
//! those bound names. Anything else matches nothing, and the action is evaluated.

use tla_ir::{Bound, NodeId, NodeKind, Pattern, Resolution, TextId};

use super::Compiler;

// The bound names of the action's quantifiers and the ones of Next's they stand for.
type Renaming = Vec<(TextId, TextId)>;

impl Compiler<'_> {
    /// The nodes of Next's walk the action is the disjunction of, each taken in its full context,
    /// or `None` where it isn't so made.
    pub(crate) fn match_pieces(&self, action: NodeId, next: NodeId) -> Option<Vec<NodeId>> {
        let mut pieces = Vec::new();
        self.match_into(action, next, &mut Vec::new(), &mut pieces)
            .then_some(pieces)
            .filter(|pieces| !pieces.is_empty())
    }

    fn match_into(
        &self,
        action: NodeId,
        next: NodeId,
        renaming: &mut Renaming,
        pieces: &mut Vec<NodeId>,
    ) -> bool {
        let (action_kind, next_kind) = (self.node(action).1, self.node(next).1);
        if self.is_same(action, next, renaming) {
            pieces.push(next);
            return true;
        }
        match (action_kind, next_kind) {
            (_, NodeKind::And(items)) if items.len() == 1 => {
                self.match_into(action, items[0], renaming, pieces)
            }
            (NodeKind::And(items), _) if items.len() == 1 => {
                self.match_into(items[0], next, renaming, pieces)
            }
            (_, NodeKind::Identifier(name)) if self.definition_body(name).is_some() => {
                let body = self.definition_body(name).expect("a body");
                self.match_into(action, body, renaming, pieces)
            }
            (NodeKind::Identifier(name), _) if self.definition_body(name).is_some() => {
                let body = self.definition_body(name).expect("a body");
                self.match_into(body, next, renaming, pieces)
            }
            (
                NodeKind::Exists {
                    bounds: action_bounds,
                    body: action_body,
                },
                NodeKind::Exists {
                    bounds: next_bounds,
                    body: next_body,
                },
            ) => {
                let Some(names) = self.same_bounds(action_bounds, next_bounds) else {
                    return false;
                };
                let depth = renaming.len();
                renaming.extend(names);
                let is_matched = self.match_into(*action_body, *next_body, renaming, pieces);
                renaming.truncate(depth);
                is_matched
            }
            (NodeKind::Or(disjuncts), NodeKind::Or(next_disjuncts)) => {
                disjuncts.iter().all(|&disjunct| {
                    next_disjuncts.iter().any(|&next_disjunct| {
                        let is_same = self.is_same(disjunct, next_disjunct, renaming);
                        if is_same && !pieces.contains(&next_disjunct) {
                            pieces.push(next_disjunct);
                        }
                        is_same
                    })
                })
            }
            (_, NodeKind::Or(next_disjuncts)) => next_disjuncts.iter().any(|&next_disjunct| {
                let is_same = self.is_same(action, next_disjunct, renaming);
                if is_same {
                    pieces.push(next_disjunct);
                }
                is_same
            }),
            _ => false,
        }
    }

    // The body of a global definition with no arguments that a name applies.
    fn definition_body(&self, name: &tla_ir::Name) -> Option<NodeId> {
        let Resolution::Definition(index) = name.resolution else {
            return None;
        };
        if name.is_local {
            return None;
        }
        let definition = self.definition(self.ir.definitions[index as usize]);
        matches!(&definition.form, tla_ir::DefinitionForm::Operator(params) if params.is_empty())
            .then_some(definition.body)
    }

    // The bound names of two lists of bounds, each one name over the same constant set.
    fn same_bounds(&self, action: &[Bound], next: &[Bound]) -> Option<Renaming> {
        if action.len() != next.len() {
            return None;
        }
        action
            .iter()
            .zip(next)
            .map(|(action, next)| match (&action.pattern, &next.pattern) {
                (Pattern::Name(action_name), Pattern::Name(next_name))
                    if self.is_same_constant(action.set, next.set) =>
                {
                    Some((*action_name, *next_name))
                }
                _ => None,
            })
            .collect()
    }

    // Whether two expressions name the same constant: a declared constant, or a constant
    // definition TLC computes as it starts.
    fn is_same_constant(&self, action: NodeId, next: NodeId) -> bool {
        match (self.node(action).1, self.node(next).1) {
            (NodeKind::Identifier(action), NodeKind::Identifier(next)) => {
                !action.is_local
                    && !next.is_local
                    && action.resolution == next.resolution
                    && match action.resolution {
                        Resolution::Constant(_) => true,
                        Resolution::Definition(index) => {
                            self.definition(self.ir.definitions[index as usize]).flags
                                & tla_ir::Definition::NORMALIZED
                                != 0
                        }
                        _ => false,
                    }
            }
            _ => false,
        }
    }

    // Whether two expressions are the same, up to the bound names the renaming pairs: the same
    // node outside any of them, the same number or string, or the same global operator, builtin
    // or variable applied to arguments that are the same.
    fn is_same(&self, action: NodeId, next: NodeId, renaming: &Renaming) -> bool {
        let (action_id, action_kind) = self.node(action);
        let (next_id, next_kind) = self.node(next);
        if action_id == next_id {
            return renaming.is_empty();
        }
        let is_same_name = |action: &tla_ir::Name, next: &tla_ir::Name| {
            if action.is_local || next.is_local {
                return action.is_local
                    && next.is_local
                    && renaming
                        .iter()
                        .rev()
                        .find(|(name, _)| *name == action.text)
                        .is_some_and(|&(_, renamed)| renamed == next.text);
            }
            action.resolution == next.resolution
                && matches!(
                    action.resolution,
                    Resolution::Definition(_)
                        | Resolution::Builtin(_)
                        | Resolution::Constant(_)
                        | Resolution::Variable(_)
                )
        };
        match (action_kind, next_kind) {
            (NodeKind::Number(action), NodeKind::Number(next)) => action == next,
            (NodeKind::String(action), NodeKind::String(next)) => action == next,
            (NodeKind::Identifier(action), NodeKind::Identifier(next)) => {
                is_same_name(action, next)
            }
            (
                NodeKind::Apply {
                    name: action_name,
                    args: action_args,
                },
                NodeKind::Apply {
                    name: next_name,
                    args: next_args,
                },
            ) => {
                !action_name.is_local
                    && is_same_name(action_name, next_name)
                    && action_args.len() == next_args.len()
                    && action_args
                        .iter()
                        .zip(next_args)
                        .all(|(&action, &next)| self.is_same(action, next, renaming))
            }
            _ => false,
        }
    }
}

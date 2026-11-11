//! The pieces of the next-state relation an action is made of, so that a step's answer to the
//! action is whether the walk that took it passed through one of them (perf.md, "Plan (ii)").
//!
//! An action matches pieces P of Next's walk where it is the disjunction of the pieces each taken
//! in its full context in Next: so the two are read side by side only through what adds no
//! context, a conjunction of one item, an `\E` over the same constant set (whose bound names then
//! stand for each other), a disjunction of which the action takes some disjuncts, a global
//! definition with no arguments, and on Next's side alone, a global operator whose arguments are
//! names, and an `\E` that the action fixes to one value of its own scope, as the liveness checker
//! binds `self` of `\A self \in S : WF_v(p(self))` (perf.md, "Plan (ii) under one value"). A
//! disjunct matches only where it is the same expression, up to those bound names. Anything else
//! matches nothing, and the action is evaluated.

use tla_ir::{Bound, DefinitionForm, NodeId, NodeKind, Param, Pattern, Resolution, TextId, Value};
use tla_values::Id;

use super::Compiler;

/// A node of Next's walk an action atom is made of, with the position of the bit a walk through
/// it sets on the step it takes, and the bounds of the `\E`s around it the action fixes.
pub(crate) struct Piece {
    pub(crate) node: NodeId,
    pub(crate) bit: u32,
    pub(crate) pins: Vec<Pin>,
    /// Whether the compiled walk of Next goes through the node inside each of those `\E`s.
    pub(crate) is_walked: bool,
}

/// A bound of an `\E` of Next, by the `\E`'s node and the bound's position, fixed to one value.
#[derive(Clone, Copy)]
pub(crate) struct Pin {
    pub(crate) exists: NodeId,
    pub(crate) bound: usize,
    pub(crate) value: Id,
}

// A bound name of Next's, as the match reads it.
#[derive(Clone)]
enum Binder {
    /// One of the action's `\E` stands for it, over the same constant set.
    Paired,
    /// The action fixes it to a value of its scope, once it reads it as the name of that value.
    Pinned {
        exists: NodeId,
        bound: usize,
        set: NodeId,
        value: Option<u32>,
    },
}

// What a name of the action's stands for: a binder, or a value its scope binds it to.
#[derive(Clone, Copy)]
enum Named {
    Binder(usize),
    Value(u32),
}

// A value TLC tells apart from others by kind and content alone.
#[derive(PartialEq)]
enum Scalar {
    Int(i64),
    String(Vec<u16>),
    Model(Vec<u16>),
}

struct Matching {
    binders: Vec<Binder>,
    // The names each side reads where the match is, innermost last.
    action: Vec<(TextId, Named)>,
    next: Vec<(TextId, usize)>,
    // The pinned binders of the `\E`s of Next around where the match is.
    pinned: Vec<usize>,
    pieces: Vec<(NodeId, Vec<usize>)>,
}

impl Matching {
    fn add_piece(&mut self, node: NodeId) {
        let piece = (node, self.pinned.clone());
        if !self.pieces.contains(&piece) {
            self.pieces.push(piece);
        }
    }
}

impl Compiler<'_> {
    /// Adds the nodes of Next's walk the action is the disjunction of, each taken in its full
    /// context, with the bit at `bit`, or adds none and is false where it isn't so made. `values`
    /// are what the action's scope binds its names to, innermost first.
    pub(crate) fn add_pieces(
        &mut self,
        action: NodeId,
        next: NodeId,
        values: &[(TextId, u32)],
        bit: u32,
    ) -> bool {
        let mut matching = Matching {
            binders: Vec::new(),
            action: values
                .iter()
                .rev()
                .map(|&(name, value)| (name, Named::Value(value)))
                .collect(),
            next: Vec::new(),
            pinned: Vec::new(),
            pieces: Vec::new(),
        };
        if !self.match_into(action, next, &mut matching) || matching.pieces.is_empty() {
            return false;
        }
        let mut pieces = Vec::with_capacity(matching.pieces.len());
        for (node, pinned) in matching.pieces {
            let mut pins = Vec::with_capacity(pinned.len());
            for binder in pinned {
                // A piece under an `\E` the action never read the name of would hold under
                // every value of it.
                let Binder::Pinned {
                    exists,
                    bound,
                    value: Some(value),
                    ..
                } = matching.binders[binder]
                else {
                    return false;
                };
                let Ok(value) = self.intern_value(value) else {
                    return false;
                };
                pins.push(Pin {
                    exists,
                    bound,
                    value,
                });
            }
            pieces.push(Piece {
                node,
                bit,
                pins,
                is_walked: false,
            });
        }
        self.pieces.extend(pieces);
        true
    }

    /// Whether the compiled walk went through every piece of the atom with the bit at `bit`
    /// inside the `\E`s it fixes, so that every step it takes through them has the bit.
    pub(crate) fn is_piece_walked(&self, bit: u32) -> bool {
        self.pieces
            .iter()
            .filter(|piece| piece.bit == bit)
            .all(|piece| piece.is_walked)
    }

    fn match_into(&self, action: NodeId, next: NodeId, matching: &mut Matching) -> bool {
        let (action_kind, next_kind) = (self.node(action).1, self.node(next).1);
        if self.try_same(action, next, matching) {
            matching.add_piece(next);
            return true;
        }
        match (action_kind, next_kind) {
            (_, NodeKind::And(items)) if items.len() == 1 => {
                self.match_into(action, items[0], matching)
            }
            (NodeKind::And(items), _) if items.len() == 1 => {
                self.match_into(items[0], next, matching)
            }
            // A disjunct of Next the action is as it stands, before either is unwrapped.
            (_, NodeKind::Or(next_disjuncts))
                if let Some(&next_disjunct) = next_disjuncts
                    .iter()
                    .find(|&&next_disjunct| self.try_same(action, next_disjunct, matching)) =>
            {
                matching.add_piece(next_disjunct);
                true
            }
            // A global definition's body reads none of the names around it.
            (_, NodeKind::Identifier(name)) if let Some(body) = self.definition_body(name) => {
                let outer = std::mem::take(&mut matching.next);
                let is_matched = self.match_into(action, body, matching);
                matching.next = outer;
                is_matched
            }
            (NodeKind::Identifier(name), _) if let Some(body) = self.definition_body(name) => {
                let outer = std::mem::take(&mut matching.action);
                let is_matched = self.match_into(body, next, matching);
                matching.action = outer;
                is_matched
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
            ) if let Some(names) = self.same_bounds(action_bounds, next_bounds) => {
                let (action_depth, next_depth) = (matching.action.len(), matching.next.len());
                for (action_name, next_name) in names {
                    let binder = matching.binders.len();
                    matching.binders.push(Binder::Paired);
                    matching.action.push((action_name, Named::Binder(binder)));
                    matching.next.push((next_name, binder));
                }
                let is_matched = self.match_into(*action_body, *next_body, matching);
                matching.action.truncate(action_depth);
                matching.next.truncate(next_depth);
                is_matched
            }
            // Each disjunct of the action is the disjunction of pieces of its own.
            (NodeKind::Or(disjuncts), _) => disjuncts
                .iter()
                .all(|&disjunct| self.match_into(disjunct, next, matching)),
            // The walk goes into the operator's body with each parameter standing for its
            // argument; a parameter whose argument is a name the action fixes stands for that
            // name, and any other matches nothing.
            (_, NodeKind::Apply { name, args })
                if let Some((params, body)) = self.operator_body(name)
                    && params.len() == args.len() =>
            {
                let names = params
                    .iter()
                    .zip(args)
                    .filter_map(|(param, &argument)| {
                        let NodeKind::Identifier(argument) = self.node(argument).1 else {
                            return None;
                        };
                        let &(_, binder) = matching
                            .next
                            .iter()
                            .rev()
                            .find(|(name, _)| argument.is_local && *name == argument.text)?;
                        matches!(matching.binders[binder], Binder::Pinned { .. })
                            .then_some((param.name, binder))
                    })
                    .collect();
                let outer = std::mem::replace(&mut matching.next, names);
                let is_matched = self.match_into(action, body, matching);
                matching.next = outer;
                is_matched
            }
            (_, NodeKind::Exists { bounds, body }) => {
                let exists = self.node(next).0;
                let (next_depth, pinned_depth) = (matching.next.len(), matching.pinned.len());
                let is_named = bounds.iter().enumerate().all(|(position, bound)| {
                    let Pattern::Name(name) = bound.pattern else {
                        return false;
                    };
                    let binder = matching.binders.len();
                    matching.binders.push(Binder::Pinned {
                        exists,
                        bound: position,
                        set: bound.set,
                        value: None,
                    });
                    matching.next.push((name, binder));
                    matching.pinned.push(binder);
                    true
                });
                let is_matched = is_named && self.match_into(action, *body, matching);
                matching.next.truncate(next_depth);
                matching.pinned.truncate(pinned_depth);
                is_matched
            }
            // The action is made of pieces of one disjunct of Next.
            (_, NodeKind::Or(next_disjuncts)) => next_disjuncts
                .iter()
                .any(|&next_disjunct| self.try_match(action, next_disjunct, matching)),
            _ => false,
        }
    }

    // Whether the action is made of pieces of Next's node, as `match_into` reads it, undoing what
    // it fixed and found where it isn't.
    fn try_match(&self, action: NodeId, next: NodeId, matching: &mut Matching) -> bool {
        let (binders, pieces) = (matching.binders.clone(), matching.pieces.len());
        let is_matched = self.match_into(action, next, matching);
        if !is_matched {
            matching.binders = binders;
            matching.pieces.truncate(pieces);
        }
        is_matched
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
        matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty())
            .then_some(definition.body)
    }

    // The parameters and body of a global operator with parameters that isn't recursive.
    fn operator_body(&self, name: &tla_ir::Name) -> Option<(&[Param], NodeId)> {
        let Resolution::Definition(index) = name.resolution else {
            return None;
        };
        if name.is_local {
            return None;
        }
        let definition = self.definition(self.ir.definitions[index as usize]);
        match &definition.form {
            DefinitionForm::Operator(params)
                if !params.is_empty() && definition.flags & tla_ir::Definition::RECURSIVE == 0 =>
            {
                Some((params, definition.body))
            }
            _ => None,
        }
    }

    // The bound names of two lists of bounds, each one name over the same constant set.
    fn same_bounds(&self, action: &[Bound], next: &[Bound]) -> Option<Vec<(TextId, TextId)>> {
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

    // Whether two expressions are the same, as `is_same` reads them, undoing what it fixed where
    // they aren't.
    fn try_same(&self, action: NodeId, next: NodeId, matching: &mut Matching) -> bool {
        let binders = matching.binders.clone();
        let is_same = self.is_same(action, next, matching);
        if !is_same {
            matching.binders = binders;
        }
        is_same
    }

    // Whether two expressions are the same, up to the names the match pairs or fixes: the same
    // node outside any of them, the same number or string, or the same global operator, builtin
    // or variable applied to arguments that are the same. A name of Next's the action reads as a
    // value of its scope is fixed to that value from then on.
    fn is_same(&self, action: NodeId, next: NodeId, matching: &mut Matching) -> bool {
        let (action_id, action_kind) = self.node(action);
        let (next_id, next_kind) = self.node(next);
        if action_id == next_id && matching.action.is_empty() && matching.next.is_empty() {
            return true;
        }
        match (action_kind, next_kind) {
            (NodeKind::Number(action), NodeKind::Number(next)) => action == next,
            (NodeKind::String(action), NodeKind::String(next)) => action == next,
            (NodeKind::Identifier(action), NodeKind::Identifier(next)) => {
                self.is_same_name(action, next, matching)
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
                    && self.is_same_name(action_name, next_name, matching)
                    && action_args.len() == next_args.len()
                    && action_args
                        .iter()
                        .zip(next_args)
                        .all(|(&action, &next)| self.is_same(action, next, matching))
            }
            _ => false,
        }
    }

    fn is_same_name(
        &self,
        action: &tla_ir::Name,
        next: &tla_ir::Name,
        matching: &mut Matching,
    ) -> bool {
        if !action.is_local && !next.is_local {
            return action.resolution == next.resolution
                && matches!(
                    action.resolution,
                    Resolution::Definition(_)
                        | Resolution::Builtin(_)
                        | Resolution::Constant(_)
                        | Resolution::Variable(_)
                );
        }
        if !action.is_local || !next.is_local {
            return false;
        }
        let Some(&(_, binder)) = matching
            .next
            .iter()
            .rev()
            .find(|(name, _)| *name == next.text)
        else {
            return false;
        };
        let Some(&(_, named)) = matching
            .action
            .iter()
            .rev()
            .find(|(name, _)| *name == action.text)
        else {
            return false;
        };
        let value = match (named, &matching.binders[binder]) {
            (Named::Binder(paired), Binder::Paired) => return paired == binder,
            (Named::Value(value), Binder::Pinned { .. }) => value,
            _ => return false,
        };
        let Some(scalar) = self.scalar(&self.ir.values.list[value as usize]) else {
            return false;
        };
        let Binder::Pinned {
            set, value: fixed, ..
        } = &mut matching.binders[binder]
        else {
            return false;
        };
        match *fixed {
            Some(fixed) => self.scalar(&self.ir.values.list[fixed as usize]) == Some(scalar),
            // The walk takes the value only where it is in the `\E`'s set.
            None if self.holds_scalar(*set, &scalar) == Some(true) => {
                *fixed = Some(value);
                true
            }
            None => false,
        }
    }

    // A value that is an integer, string or model value.
    fn scalar(&self, value: &Value) -> Option<Scalar> {
        Some(match value {
            Value::Int(value) => Scalar::Int(i64::from(*value)),
            Value::String(index) => Scalar::String(
                self.ir
                    .get_text_units(self.ir.values.strings[*index as usize]),
            ),
            Value::ModelValue(index) => Scalar::Model(
                self.ir
                    .get_text_units(self.ir.values.strings[*index as usize]),
            ),
            _ => return None,
        })
    }

    // The scalar a constant expression is, where it is a number, a string, a constant or a
    // definition of one.
    fn constant_scalar(&self, node: NodeId) -> Option<Scalar> {
        match self.node(node).1 {
            NodeKind::Number(value) => Some(Scalar::Int(i64::from(*value))),
            NodeKind::String(text) => Some(Scalar::String(self.ir.get_text_units(*text))),
            NodeKind::Identifier(name) if !name.is_local => match name.resolution {
                Resolution::Constant(index) => {
                    let value = self.ir.constants[index as usize].value?;
                    self.scalar(&self.ir.values.list[value as usize])
                }
                _ => self.constant_scalar(self.constant_body(name)?),
            },
            _ => None,
        }
    }

    // Whether a constant set holds a scalar, where the set is a constant, an interval, a set
    // enumeration, a union of those, or a definition of one; none where it is anything else.
    fn holds_scalar(&self, set: NodeId, value: &Scalar) -> Option<bool> {
        match self.node(set).1 {
            NodeKind::Identifier(name) if !name.is_local => match name.resolution {
                Resolution::Constant(index) => {
                    let constant = self.ir.constants[index as usize].value?;
                    let Value::Set(elements) = &self.ir.values.list[constant as usize] else {
                        return None;
                    };
                    let mut is_member = false;
                    for element in elements {
                        is_member |= self.scalar(element)? == *value;
                    }
                    Some(is_member)
                }
                _ => self.holds_scalar(self.constant_body(name)?, value),
            },
            NodeKind::SetEnumeration(elements) => {
                let mut is_member = false;
                for &element in elements {
                    is_member |= self.constant_scalar(element)? == *value;
                }
                Some(is_member)
            }
            NodeKind::Apply { name, args } if !name.is_local && args.len() == 2 => {
                let Resolution::Builtin(index) = name.resolution else {
                    return None;
                };
                match self.text(self.ir.builtins[index as usize].name) {
                    ".." => {
                        let (Some(Scalar::Int(low)), Some(Scalar::Int(high))) =
                            (self.constant_scalar(args[0]), self.constant_scalar(args[1]))
                        else {
                            return None;
                        };
                        Some(matches!(value, Scalar::Int(value) if (low..=high).contains(value)))
                    }
                    "\\cup" | "\\union" => match (
                        self.holds_scalar(args[0], value),
                        self.holds_scalar(args[1], value),
                    ) {
                        (Some(true), _) | (_, Some(true)) => Some(true),
                        (Some(false), Some(false)) => Some(false),
                        _ => None,
                    },
                    _ => None,
                }
            }
            _ => None,
        }
    }

    // The body of a global definition with no arguments that TLC computes without effects.
    fn constant_body(&self, name: &tla_ir::Name) -> Option<NodeId> {
        let Resolution::Definition(index) = name.resolution else {
            return None;
        };
        let definition = self.definition(self.ir.definitions[index as usize]);
        (!self.ir.model.startup.definitions.contains(&index)
            && definition.flags & tla_ir::Definition::RECURSIVE == 0)
            .then(|| self.definition_body(name))
            .flatten()
    }
}

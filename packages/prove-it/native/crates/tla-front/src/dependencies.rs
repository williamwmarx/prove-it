//! What TLC's evaluation needs to know about each definition of a spec, as `src/dependencies.ts`
//! computes it: whether it is constant-level, which effects evaluating it has, which variables it
//! reads, and its liveness level. Each fact is reachability over the definitions it calls, so one
//! pass over the spec's call graph computes them all. A row of words holds a definition's facts:
//! the first word holds the flags below, and the rest a bitset of the variables it reads.

use std::rc::Rc;

use crate::ast::*;
use crate::environment::Environment;
use crate::hash::FastMap;

/// The definition reads a variable, a state-level builtin, or an action or temporal operator.
const NONCONSTANT: u32 = 1;
/// Evaluating the definition again can print, assert, read the clock or choose at random.
const IMPURE: u32 = 2;
/// Like `IMPURE`, but an Assert that held holds again, so repeating it looks the same.
const REPEATED_EFFECT: u32 = 4;
/// The definition builds a set with UNION or `\cup`, which streams until TLC caches it.
const STREAMED: u32 = 8;
/// The variables the definition reads don't decide its value: it has an effect, or it is an
/// action.
const READS_IMPURE: u32 = 16;
/// The liveness level of the definition, as thresholds so that reachability is a bitwise or.
/// A formula's level, `CONSTANT_LEVEL` to `TEMPORAL_LEVEL` in `liveness.ts`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Level {
    Constant,
    Variable,
    Action,
    Temporal,
}

const VARIABLE_LEVEL_FLAGS: u32 = 32;
const ACTION_LEVEL_FLAGS: u32 = VARIABLE_LEVEL_FLAGS | 64;
const TEMPORAL_LEVEL_FLAGS: u32 = ACTION_LEVEL_FLAGS | 128;

const PURITY_MASK: u32 = IMPURE | REPEATED_EFFECT | STREAMED;
const READ_MASK: u32 = NONCONSTANT | READS_IMPURE;

const BUILTIN_STATE_LEVEL: u32 = 1;
const BUILTIN_LEVEL_CONSTANT: u32 = 2;

const IMPURE_BUILTINS: [&str; 10] = [
    "Print",
    "PrintT",
    "Assert",
    "AssertEq",
    "JavaTime",
    "RandomElement",
    "TLCGet",
    "TLCGetOrDefault",
    "TLCGetAndSet",
    "TLCSet",
];

/// UNION and `\cup` build sets that stream the sets they combine until TLC caches them.
const STREAMED_BUILTINS: [&str; 2] = ["UNION", "\\cup"];

const TEMPORAL_OPERATORS: [&str; 2] = ["~>", "-+->"];

/// The facts of every definition of the environment, by the definition's address.
pub struct DefinitionFacts {
    ids: FastMap<usize, usize>,
    rows: Vec<u32>,
    words: usize,
}

struct Edge {
    callee: Rc<Definition>,
    /// The configuration replaces the name by a constant value, which TLC's level and variable
    /// analyses take for a constant and its effect analysis evaluates.
    is_overridden: bool,
    /// Whether the reference is outside every action and temporal operator, where the level of
    /// the callee counts.
    is_level_counted: bool,
}

fn is_action_kind(kind: &ExpressionKind) -> bool {
    matches!(
        kind,
        ExpressionKind::Prime(_) | ExpressionKind::Unchanged(_) | ExpressionKind::Action { .. }
    )
}

fn is_temporal_kind(kind: &ExpressionKind) -> bool {
    matches!(
        kind,
        ExpressionKind::Always(_) | ExpressionKind::Eventually(_) | ExpressionKind::Fairness { .. }
    )
}

fn is_temporal_quantifier(kind: &ExpressionKind) -> bool {
    matches!(
        kind,
        ExpressionKind::UnboundedQuantifier {
            is_temporal: true,
            ..
        }
    )
}

/// The operator an `Apply` applies, as written.
fn applied(expression: &Expression) -> Option<Name> {
    match expression.kind {
        ExpressionKind::Apply { .. } => expression.reference(),
        _ => None,
    }
}

fn builtin_flags(environment: &Environment, name: &str) -> u32 {
    environment
        .builtins
        .get(name)
        .map_or(0, |builtin| builtin.flags)
}

fn is_impure_builtin(name: &str, environment: &Environment) -> bool {
    IMPURE_BUILTINS.contains(&name) || builtin_flags(environment, name) & BUILTIN_STATE_LEVEL != 0
}

/// The level flags of a node, or none for a node whose level the nodes it holds decide.
fn get_own_level_flags(node: &Expression) -> Option<u32> {
    let operator = applied(node);
    if is_action_kind(&node.kind) || operator.as_deref() == Some("\\cdot") {
        return Some(ACTION_LEVEL_FLAGS);
    }
    if matches!(node.kind, ExpressionKind::Enabled(_)) {
        return Some(VARIABLE_LEVEL_FLAGS);
    }
    if is_temporal_kind(&node.kind)
        || is_temporal_quantifier(&node.kind)
        || operator.is_some_and(|operator| TEMPORAL_OPERATORS.contains(&&*operator))
    {
        return Some(TEMPORAL_LEVEL_FLAGS);
    }
    None
}

/// The facts an expression's own nodes establish, with the definitions it refers to.
fn collect_local_facts(
    expressions: &[Expr],
    environment: &Environment,
    words: usize,
) -> (Vec<u32>, Vec<Edge>) {
    let mut row = vec![0; words];
    let mut edges = Vec::new();
    let mut pending: Vec<(Expr, bool)> = expressions
        .iter()
        .rev()
        .map(|expression| (expression.clone(), true))
        .collect();
    while let Some((node, is_level_counted)) = pending.pop() {
        let kind = &node.kind;
        let operator = applied(&node);
        let is_nonconstant_kind = is_action_kind(kind)
            || is_temporal_kind(kind)
            || matches!(kind, ExpressionKind::Enabled(_));
        if is_nonconstant_kind
            || is_temporal_quantifier(kind)
            || operator.as_deref().is_some_and(|operator| {
                TEMPORAL_OPERATORS.contains(&operator) || operator == "\\cdot"
            })
        {
            row[0] |= NONCONSTANT;
        }
        if is_nonconstant_kind {
            row[0] |= READS_IMPURE;
        }
        let own_level_flags = get_own_level_flags(&node);
        if is_level_counted && let Some(flags) = own_level_flags {
            row[0] |= flags;
        }
        let is_inner_level_counted = is_level_counted && own_level_flags.is_none();
        if let Some(name) = node.reference()
            && !node.is_locally_resolved()
        {
            let target = environment
                .substitutions
                .get(&name)
                .cloned()
                .unwrap_or_else(|| name.clone());
            let definition = environment.definitions.get(&target).cloned();
            let is_overridden = environment.constants.contains_key(&name);
            let variable_index = environment.variable_index.get(&name).copied();
            if variable_index.is_some()
                || builtin_flags(environment, &name) & BUILTIN_STATE_LEVEL != 0
            {
                row[0] |= NONCONSTANT;
            }
            if let Some(index) = variable_index {
                if is_inner_level_counted {
                    row[0] |= VARIABLE_LEVEL_FLAGS;
                }
                if !is_overridden {
                    row[1 + (index >> 5)] |= 1 << (index & 31);
                }
            }
            match definition {
                Some(callee) => edges.push(Edge {
                    callee,
                    is_overridden,
                    is_level_counted: is_inner_level_counted,
                }),
                None => {
                    if is_impure_builtin(&name, environment) {
                        row[0] |= IMPURE
                            | if &*name == "Assert" {
                                0
                            } else {
                                REPEATED_EFFECT
                            };
                    }
                    if STREAMED_BUILTINS.contains(&&*name) {
                        row[0] |= STREAMED;
                    }
                    if !is_overridden && is_impure_builtin(&target, environment) {
                        row[0] |= READS_IMPURE;
                    }
                    let flags = builtin_flags(environment, &target);
                    if is_inner_level_counted
                        && !is_overridden
                        && variable_index.is_none()
                        && flags & BUILTIN_STATE_LEVEL != 0
                        && flags & BUILTIN_LEVEL_CONSTANT == 0
                    {
                        row[0] |= VARIABLE_LEVEL_FLAGS;
                    }
                }
            }
        }
        pending.extend(
            node.children()
                .into_iter()
                .rev()
                .map(|child| (child, is_inner_level_counted)),
        );
    }
    (row, edges)
}

fn get_definition_expressions(definition: &Definition) -> Vec<Expr> {
    let mut expressions: Vec<Expr> = match &definition.kind {
        DefinitionKind::Function { bounds } => {
            bounds.iter().map(|bound| bound.set.clone()).collect()
        }
        DefinitionKind::Operator { .. } => Vec::new(),
    };
    expressions.push(definition.body.clone());
    expressions
}

/// Closes each row under bitwise or along the edges: a definition's facts are its own and those
/// of every definition it reaches. Tarjan's algorithm lists the strongly connected components
/// with the callees first, so each component ors in components that are already final.
fn close_rows(local: &[u32], words: usize, edges: &[Vec<usize>], mask: u32) -> Vec<u32> {
    let count = edges.len();
    let mut closed = local.to_vec();
    let mut index = vec![usize::MAX; count];
    let mut low_link = vec![0; count];
    let mut component = vec![usize::MAX; count];
    let mut stack: Vec<usize> = Vec::new();
    // The frames of a depth-first visit: the node and the edge it resumes at.
    let mut frames: Vec<(usize, usize)> = Vec::new();
    let mut next_index = 0;
    let mut component_count = 0;
    let or_row = |closed: &mut [u32], into: usize, from: usize| {
        for word in 0..words {
            let bits = closed[from * words + word];
            closed[into * words + word] |= if word == 0 { bits & mask } else { bits };
        }
    };
    for root in 0..count {
        if index[root] != usize::MAX {
            continue;
        }
        frames.push((root, 0));
        index[root] = next_index;
        low_link[root] = next_index;
        next_index += 1;
        stack.push(root);
        while let Some(&(node, position)) = frames.last() {
            if position < edges[node].len() {
                frames.last_mut().expect("a frame").1 = position + 1;
                let callee = edges[node][position];
                if index[callee] == usize::MAX {
                    frames.push((callee, 0));
                    index[callee] = next_index;
                    low_link[callee] = next_index;
                    next_index += 1;
                    stack.push(callee);
                } else if component[callee] == usize::MAX {
                    // A visited node without a component is still on the stack.
                    low_link[node] = low_link[node].min(index[callee]);
                }
                continue;
            }
            frames.pop();
            if let Some(&(caller, _)) = frames.last() {
                low_link[caller] = low_link[caller].min(low_link[node]);
            }
            if low_link[node] != index[node] {
                continue;
            }
            // The component is complete: its members share one row, which ors in their callees'
            // rows.
            let mut members = Vec::new();
            loop {
                let member = stack.pop().unwrap_or(node);
                component[member] = component_count;
                members.push(member);
                if member == node {
                    break;
                }
            }
            component_count += 1;
            let first = members[0];
            for &member in &members {
                if member != first {
                    or_row(&mut closed, first, member);
                }
                for &callee in &edges[member] {
                    if component[callee] != component[first] {
                        or_row(&mut closed, first, callee);
                    }
                }
            }
            for &member in &members {
                if member != first {
                    or_row(&mut closed, member, first);
                }
            }
        }
    }
    closed
}

/// TLC evaluates a constant definition without parameters once, so only other definitions pass on
/// the side effects and random choices of the builtins they call.
fn is_evaluated_once(definition: &Definition, flags: u32) -> bool {
    matches!(&definition.kind, DefinitionKind::Operator { params, .. } if params.is_empty())
        && flags & NONCONSTANT == 0
}

fn address(definition: &Rc<Definition>) -> usize {
    Rc::as_ptr(definition) as usize
}

/// `createDefinitionFacts`.
pub fn create_definition_facts(environment: &Environment) -> DefinitionFacts {
    let mut ids: FastMap<usize, usize> = FastMap::default();
    let mut definitions: Vec<Rc<Definition>> = Vec::new();
    for definition in environment.definitions.values() {
        if let std::collections::hash_map::Entry::Vacant(entry) = ids.entry(address(definition)) {
            entry.insert(definitions.len());
            definitions.push(definition.clone());
        }
    }
    let words = 1 + environment.variables.len().div_ceil(32);
    let mut local = vec![0; definitions.len() * words];
    let mut local_impurity = vec![0; definitions.len() * words];
    let edges: Vec<Vec<Edge>> = definitions
        .iter()
        .enumerate()
        .map(|(id, definition)| {
            let (row, edges) =
                collect_local_facts(&get_definition_expressions(definition), environment, words);
            local_impurity[id * words] = row[0] & PURITY_MASK;
            local[id * words..(id + 1) * words].copy_from_slice(&row);
            edges
        })
        .collect();
    let get_id = |edge: &Edge| ids.get(&address(&edge.callee)).copied();
    let read_edges: Vec<Vec<usize>> = edges
        .iter()
        .map(|own| {
            own.iter()
                .filter(|edge| !edge.is_overridden)
                .filter_map(get_id)
                .collect()
        })
        .collect();
    let reads = close_rows(&local, words, &read_edges, READ_MASK);
    let level_edges: Vec<Vec<usize>> = edges
        .iter()
        .map(|own| {
            own.iter()
                .filter(|edge| !edge.is_overridden && edge.is_level_counted)
                .filter_map(get_id)
                .collect()
        })
        .collect();
    let levels = close_rows(&local, words, &level_edges, TEMPORAL_LEVEL_FLAGS);
    let purity_edges: Vec<Vec<usize>> = edges
        .iter()
        .map(|own| {
            own.iter()
                .filter_map(get_id)
                .filter(|callee| !is_evaluated_once(&definitions[*callee], reads[callee * words]))
                .collect()
        })
        .collect();
    let purity = close_rows(&local_impurity, words, &purity_edges, PURITY_MASK);
    let rows = reads
        .iter()
        .enumerate()
        .map(|(position, word)| {
            if position % words == 0 {
                (word & READ_MASK)
                    | (levels[position] & TEMPORAL_LEVEL_FLAGS)
                    | (purity[position] & PURITY_MASK)
            } else {
                *word
            }
        })
        .collect();
    DefinitionFacts { ids, rows, words }
}

impl DefinitionFacts {
    /// The rows of the definitions, in the order of their ids: the environment's order of
    /// definitions, each once.
    pub fn rows(&self) -> &[u32] {
        &self.rows
    }

    pub fn words(&self) -> usize {
        self.words
    }

    /// The facts of a definition: from the table, or for a LET definition from its own body and
    /// the table's rows of the definitions it calls.
    fn get_row(&self, definition: &Rc<Definition>, environment: &Environment) -> Vec<u32> {
        match self.ids.get(&address(definition)) {
            Some(id) => self.rows[id * self.words..(id + 1) * self.words].to_vec(),
            None => self.get_expressions_row(&get_definition_expressions(definition), environment),
        }
    }

    /// The facts of expressions: their own, with the rows of the definitions they call ored in.
    fn get_expressions_row(&self, expressions: &[Expr], environment: &Environment) -> Vec<u32> {
        let (mut row, edges) = collect_local_facts(expressions, environment, self.words);
        for edge in &edges {
            let callee = self.get_row(&edge.callee, environment);
            if !edge.is_overridden {
                row[0] |= callee[0] & READ_MASK;
                if edge.is_level_counted {
                    row[0] |= callee[0] & TEMPORAL_LEVEL_FLAGS;
                }
                for word in 1..self.words {
                    row[word] |= callee[word];
                }
            }
            if !is_evaluated_once(&edge.callee, callee[0]) {
                row[0] |= callee[0] & PURITY_MASK;
            }
        }
        row
    }

    /// `isImpureDefinition(definition, environment, "repeated")`: evaluating the definition
    /// again can show, such as by printing twice.
    pub fn has_repeated_definition_effect(
        &self,
        definition: &Rc<Definition>,
        environment: &Environment,
    ) -> bool {
        self.get_row(definition, environment)[0] & REPEATED_EFFECT != 0
    }

    /// `isImpureDefinition`: evaluating the definition can print, assert, read the clock or
    /// choose at random.
    pub fn is_impure_definition(
        &self,
        definition: &Rc<Definition>,
        environment: &Environment,
    ) -> bool {
        self.get_row(definition, environment)[0] & IMPURE != 0
    }

    /// `isConstantLevel`.
    pub fn is_constant_level(
        &self,
        definition: &Rc<Definition>,
        environment: &Environment,
    ) -> bool {
        self.get_row(definition, environment)[0] & NONCONSTANT == 0
    }

    /// `getDefinitionLevel`: constant, state, action or temporal, as `CONSTANT_LEVEL` and the rest
    /// number them.
    pub fn get_definition_level(
        &self,
        definition: &Rc<Definition>,
        environment: &Environment,
    ) -> Level {
        match self.get_row(definition, environment)[0] & TEMPORAL_LEVEL_FLAGS {
            TEMPORAL_LEVEL_FLAGS => Level::Temporal,
            ACTION_LEVEL_FLAGS => Level::Action,
            VARIABLE_LEVEL_FLAGS => Level::Variable,
            _ => Level::Constant,
        }
    }

    /// `hasRepeatedEffect`.
    pub fn has_repeated_effect(&self, expression: &Expr, environment: &Environment) -> bool {
        self.get_expressions_row(std::slice::from_ref(expression), environment)[0] & REPEATED_EFFECT
            != 0
    }
}

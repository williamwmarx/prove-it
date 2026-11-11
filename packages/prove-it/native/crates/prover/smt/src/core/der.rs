//! Ported from Z3 (src/ast/rewriter/der.cpp), MIT license, through `der.ts`. Destructive equality
//! resolution: a quantified variable that a literal of the body defines is replaced by its
//! definition.
//!
//! der_sort_vars visits the definitions by recursion, which stops past `MAX_RECURSION_DEPTH`
//! (design/smt-core.md, recursion).

use std::collections::HashSet;

use crate::core::ast::{
    AstManager, Expr, KIND_QUANTIFIER, KIND_VAR, OP_EQ, QuantifierData, SORT_BOOL,
};
use crate::core::ast_util::{flatten_and_vector, flatten_or_vector};
use crate::core::ref_vector::RefVector;
use crate::core::rewriter_tpl::MAX_RECURSION_DEPTH;
use crate::core::var_subst::{VarSubst, collect_used_vars, elim_unused_vars};
use crate::util::error::SmtError;

#[derive(Clone, Copy, Debug)]
struct VarDefinition {
    index: usize,
    definition: Expr,
}

// der::is_var_diseq for a universal quantifier and der::is_var_eq for an existential one.
fn get_var_definition(
    m: &mut AstManager,
    literal: Expr,
    count: usize,
    is_forall: bool,
) -> Result<Option<VarDefinition>, SmtError> {
    let is_bound_var = |m: &AstManager, term: Expr| {
        m.kinds[term as usize] == KIND_VAR && (m.values[term as usize] as usize) < count
    };
    let is_negated_var =
        |m: &AstManager, term: Expr| m.is_not(term) && is_bound_var(m, m.get_arg(term, 0));
    let from_eq = |m: &mut AstManager, eq: Expr, is_negated: bool| {
        let is_swapped = !is_bound_var(m, m.get_arg(eq, 0));
        let lhs = if is_swapped {
            m.get_arg(eq, 1)
        } else {
            m.get_arg(eq, 0)
        };
        let rhs = if is_swapped {
            m.get_arg(eq, 0)
        } else {
            m.get_arg(eq, 1)
        };
        if !is_bound_var(m, lhs) {
            return Ok(None);
        }
        let definition = if is_negated { m.mk_not(rhs)? } else { rhs };
        Ok::<_, SmtError>(Some(VarDefinition {
            index: m.values[lhs as usize] as usize,
            definition,
        }))
    };
    if is_forall {
        if m.is_not(literal) && m.get_op(m.get_arg(literal, 0)) == OP_EQ {
            return from_eq(m, m.get_arg(literal, 0), false);
        }
        if m.get_op(literal) == OP_EQ && m.sorts[m.get_arg(literal, 0) as usize] == SORT_BOOL {
            let found = from_eq(m, literal, true)?;
            if found.is_some() {
                return Ok(found);
            }
            let is_swapped = !is_negated_var(m, m.get_arg(literal, 0));
            let lhs = if is_swapped {
                m.get_arg(literal, 1)
            } else {
                m.get_arg(literal, 0)
            };
            let rhs = if is_swapped {
                m.get_arg(literal, 0)
            } else {
                m.get_arg(literal, 1)
            };
            return Ok(is_negated_var(m, lhs).then(|| VarDefinition {
                index: m.values[m.get_arg(lhs, 0) as usize] as usize,
                definition: rhs,
            }));
        }
        if is_bound_var(m, literal) {
            return Ok(Some(VarDefinition {
                index: m.values[literal as usize] as usize,
                definition: m.false_expr,
            }));
        }
        if is_negated_var(m, literal) {
            return Ok(Some(VarDefinition {
                index: m.values[m.get_arg(literal, 0) as usize] as usize,
                definition: m.true_expr,
            }));
        }
        return Ok(None);
    }
    if m.get_op(literal) == OP_EQ {
        return from_eq(m, literal, false);
    }
    if is_bound_var(m, literal) {
        return Ok(Some(VarDefinition {
            index: m.values[literal as usize] as usize,
            definition: m.true_expr,
        }));
    }
    if is_negated_var(m, literal) {
        return Ok(Some(VarDefinition {
            index: m.values[m.get_arg(literal, 0) as usize] as usize,
            definition: m.false_expr,
        }));
    }
    Ok(None)
}

pub fn is_occurring(m: &AstManager, index: usize, expr: Expr) -> Result<bool, SmtError> {
    Ok(collect_used_vars(m, expr, index + 1)?[index])
}

// The state of der_sort_vars' visit.
struct EliminationOrder<'a> {
    definitions: &'a mut [Option<Expr>],
    order: Vec<usize>,
    visiting: HashSet<Expr>,
    done: HashSet<Expr>,
}

impl EliminationOrder<'_> {
    fn visit(&mut self, m: &AstManager, expr: Expr, depth: usize) -> Result<(), SmtError> {
        if self.done.contains(&expr) {
            return Ok(());
        }
        if depth >= MAX_RECURSION_DEPTH {
            return Err(SmtError::Unsupported(
                "der's definitions nest too deeply".into(),
            ));
        }
        if m.kinds[expr as usize] == KIND_VAR {
            let index = m.values[expr as usize] as usize;
            let definition = self.definitions.get(index).copied().flatten();
            if let Some(definition) = definition {
                if self.visiting.contains(&expr) {
                    self.visiting.remove(&expr);
                    self.definitions[index] = None;
                } else {
                    self.visiting.insert(expr);
                    self.visit(m, definition, depth + 1)?;
                    if self.definitions[index].is_some() {
                        self.visiting.remove(&expr);
                        self.order.push(index);
                    }
                }
            }
            self.done.insert(expr);
            return Ok(());
        }
        for index in 0..m.get_num_args(expr) {
            let arg = m.get_arg(expr, index);
            self.visit(m, arg, depth + 1)?;
        }
        self.done.insert(expr);
        Ok(())
    }
}

// der_sort_vars: the definitions in an order where each only uses the ones before it, dropping
// the definitions on a cycle.
fn get_elimination_order(
    m: &mut AstManager,
    definitions: &mut [Option<Expr>],
) -> Result<Vec<usize>, SmtError> {
    for (index, slot) in definitions.iter_mut().enumerate() {
        if let Some(definition) = *slot
            && (m.has_quantifier_flags[definition as usize] != 0
                || is_occurring(m, index, definition)?)
        {
            *slot = None;
        }
    }
    let mut state = EliminationOrder {
        definitions,
        order: Vec::new(),
        visiting: HashSet::new(),
        done: HashSet::new(),
    };
    for index in 0..state.definitions.len() {
        if let Some(definition) = state.definitions[index] {
            let variable = m.mk_var(index as i32, m.sorts[definition as usize]);
            state.visit(m, variable, 0)?;
        }
    }
    Ok(state.order)
}

/// der: destructive equality resolution. Its var_subst keeps the cache of its last substitution,
/// and m_map, m_subst_map and m_new_args keep their expressions, until der next fills them.
#[derive(Clone, Debug)]
pub struct Der {
    subst: VarSubst,
    map: RefVector,
    subst_map: RefVector,
    new_args: RefVector,
}

impl Der {
    pub fn new(m: &AstManager) -> Der {
        Der {
            subst: VarSubst::new(m, true),
            map: RefVector::new(),
            subst_map: RefVector::new(),
            new_args: RefVector::new(),
        }
    }

    /// der::operator(): reduces until nothing changes, then drops the eliminated variables. The
    /// result is a temporary.
    pub fn apply(&mut self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        let mut current = expr;
        loop {
            let next = self.reduce(m, current)?;
            if next == current {
                break;
            }
            current = next;
            if m.kinds[current as usize] != KIND_QUANTIFIER {
                return Ok(current);
            }
        }
        if current == expr {
            Ok(expr)
        } else {
            elim_unused_vars(m, current)
        }
    }

    /// ~der.
    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.new_args.reset(m)?;
        self.subst_map.reset(m)?;
        self.map.reset(m)?;
        self.subst.release(m)
    }

    // der::reduce1.
    fn reduce(&mut self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        let data = m.get_quantifier(expr)?.clone();
        let count = data.sorts.len();
        let single = get_var_definition(m, data.body, count, data.is_forall)?;
        if let Some(single) = single
            && m.has_quantifier_flags[single.definition as usize] == 0
            && !is_occurring(m, single.index, single.definition)?
        {
            return Ok(if data.is_forall {
                m.false_expr
            } else {
                m.true_expr
            });
        }
        // The literals vector holds its expressions until reduce1 returns, and releases them in
        // order.
        let mut vector = RefVector::new();
        m.without_temporaries(|m| {
            vector.push(m, data.body);
            if data.is_forall {
                flatten_or_vector(m, &mut vector)
            } else {
                flatten_and_vector(m, &mut vector)
            }
        })?;
        let result = self.reduce_literals(m, expr, &data, &vector.items)?;
        vector.reset(m)?;
        Ok(result)
    }

    // The rest of der::reduce1, on the flattened literals of the body.
    fn reduce_literals(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        data: &QuantifierData,
        literals: &[Expr],
    ) -> Result<Expr, SmtError> {
        let count = data.sorts.len();
        self.map.reset(m)?;
        let mut positions: Vec<Option<usize>> = Vec::new();
        for literal in literals {
            let found = get_var_definition(m, *literal, count, data.is_forall)?;
            let Some(found) = found.filter(|found| {
                self.map
                    .items
                    .get(found.index)
                    .is_none_or(|definition| *definition == -1)
            }) else {
                positions.push(None);
                continue;
            };
            if self.map.len() <= found.index {
                self.map.resize(m, found.index + 1)?;
            }
            self.map.set(m, found.index, found.definition)?;
            positions.push(Some(found.index));
        }
        if positions.iter().all(Option::is_none) {
            return Ok(expr);
        }
        // der_sort_vars drops the definitions on a cycle from m_map.
        let mut definitions: Vec<Option<Expr>> = self
            .map
            .items
            .iter()
            .map(|definition| (*definition != -1).then_some(*definition))
            .collect();
        let order = get_elimination_order(m, &mut definitions)?;
        for (index, definition) in definitions.iter().enumerate() {
            if definition.is_none() && self.map.items[index] != -1 {
                self.map.set(m, index, -1)?;
            }
        }
        if order.is_empty() {
            return Ok(expr);
        }
        // create_substitution: (:var i) becomes the entry at size - i - 1, with the definitions
        // before it in the order substituted.
        let size = self.map.len();
        self.subst_map.reset(m)?;
        self.subst_map.resize(m, size)?;
        for index in order {
            let applied = self
                .subst
                .apply(m, self.map.items[index], &self.subst_map.items)?;
            self.subst_map.set_owned(m, size - index - 1, applied)?;
        }
        // apply_substitution: m_new_args holds the kept literals, and the junction of them is held
        // until it returns.
        self.new_args.reset(m)?;
        for (position, literal) in literals.iter().enumerate() {
            let is_kept = positions[position].is_none_or(|index| self.map.items[index] == -1);
            if is_kept {
                self.new_args.push(m, *literal);
            }
        }
        let kept = self.new_args.items.clone();
        let empty = if data.is_forall {
            m.false_expr
        } else {
            m.true_expr
        };
        let combined = m.without_temporaries(|m| match kept.len() {
            0 => Ok(empty),
            1 => Ok(kept[0]),
            _ if data.is_forall => m.mk_or(&kept),
            _ => m.mk_and(&kept),
        })?;
        m.inc_ref(combined);
        let body = self.subst.apply(m, combined, &self.subst_map.items)?;
        let mut patterns = Vec::new();
        for pattern in &data.patterns {
            patterns.push(self.subst.apply(m, *pattern, &self.subst_map.items)?);
        }
        let result = m.mk_quantifier(QuantifierData {
            body,
            patterns: patterns.clone(),
            ..data.clone()
        })?;
        for pattern in patterns {
            m.release_later(pattern)?;
        }
        m.release_later(body)?;
        m.dec_ref(combined)?;
        Ok(result)
    }
}

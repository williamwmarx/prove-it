//! Ported from Z3 (src/ast/pattern/pattern_inference.cpp), MIT license, through
//! `pattern-inference.ts`. Infers E-matching patterns for quantifiers that have none, with Z3's
//! default parameters: pi.max_multi_patterns=0, pi.block_loop_patterns=true,
//! pi.decompose_patterns=true, pi.arith=1 (conservative), pi.avoid_skolems=true.
//!
//! The TypeScript's `collect` recurses on the body; here it counts its depth, and stops past
//! `MAX_RECURSION_DEPTH` (design/smt-core.md, recursion).

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::core::ast::{
    AstManager, Expr, FAMILY_ARITH, FAMILY_BASIC, KIND_APP, KIND_QUANTIFIER, KIND_VAR, OP_FALSE,
    OP_IDIV, OP_MOD, OP_MUL, OP_TRUE,
};
use crate::core::ref_vector::RefVector;
use crate::core::rewriter_tpl::{InvVarShifter, MAX_RECURSION_DEPTH};
use crate::util::error::SmtError;
use crate::util::ordered_map::OrderedSet;

#[derive(Clone, Debug)]
struct CandidateInfo {
    free_vars: OrderedSet<i32>,
    bound_vars: OrderedSet<i32>,
    size: usize,
}

#[derive(Clone, Debug)]
struct PrePattern {
    exprs: Vec<Expr>,
    free_vars: OrderedSet<i32>,
    index: usize,
}

const PI_ARITH_WEIGHT: i32 = 5;
const PI_NON_NESTED_ARITH_WEIGHT: i32 = 10;
const MAX_SPLITS: usize = 32;

fn is_same_set(left: &OrderedSet<i32>, right: &OrderedSet<i32>) -> bool {
    left.len() == right.len() && left.iter().all(|element| right.contains(element))
}

fn is_subset(left: &OrderedSet<i32>, right: &OrderedSet<i32>) -> bool {
    left.iter().all(|element| right.contains(element))
}

/// The patterns inferred for a quantifier, and its weight.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InferredPatterns {
    pub patterns: Vec<Expr>,
    pub weight: i32,
}

/// pattern_inference_cfg, which asserted_formulas keeps as long as it lives. m_candidates holds
/// its candidates until the end of mk_patterns.
#[derive(Clone, Debug)]
pub struct PatternInference {
    candidates: RefVector,
    candidate_infos: HashMap<Expr, Rc<CandidateInfo>>,
    num_bindings: usize,
    is_arith_forbidden: bool,
    is_nested_arith_only: bool,
    is_blocking_loop_patterns: bool,
}

impl Default for PatternInference {
    fn default() -> PatternInference {
        PatternInference::new()
    }
}

impl PatternInference {
    pub fn new() -> PatternInference {
        PatternInference {
            candidates: RefVector::new(),
            candidate_infos: HashMap::new(),
            num_bindings: 0,
            is_arith_forbidden: true,
            is_nested_arith_only: true,
            is_blocking_loop_patterns: true,
        }
    }

    fn is_forbidden(&self, m: &AstManager, expr: Expr) -> bool {
        if m.is_ground(expr) {
            return false;
        }
        let decl = &m.func_decls[m.decls[expr as usize] as usize];
        if decl.is_skolem {
            return true;
        }
        if decl.family == FAMILY_BASIC {
            return decl.op != OP_TRUE && decl.op != OP_FALSE;
        }
        decl.family == FAMILY_ARITH && self.is_arith_forbidden
    }

    fn collect(&mut self, m: &mut AstManager, body: Expr) -> Result<(), SmtError> {
        let mut cache = HashMap::new();
        self.visit(m, &mut cache, body, 0, 0)?;
        Ok(())
    }

    fn visit(
        &mut self,
        m: &mut AstManager,
        cache: &mut HashMap<(Expr, i32), Option<Rc<CandidateInfo>>>,
        expr: Expr,
        delta: i32,
        depth: usize,
    ) -> Result<Option<Rc<CandidateInfo>>, SmtError> {
        if let Some(info) = cache.get(&(expr, delta)) {
            return Ok(info.clone());
        }
        if depth >= MAX_RECURSION_DEPTH {
            return Err(SmtError::Unsupported(
                "pattern inference nests too deeply".into(),
            ));
        }
        let mut info = None;
        let kind = m.kinds[expr as usize];
        if kind == KIND_VAR {
            let index = m.values[expr as usize];
            let mut free_vars = OrderedSet::new();
            let mut bound_vars = OrderedSet::new();
            if delta <= index && i64::from(index) < self.num_bindings as i64 + i64::from(delta) {
                free_vars.insert(index - delta);
            } else if index < delta {
                bound_vars.insert(index);
            }
            info = Some(Rc::new(CandidateInfo {
                free_vars,
                bound_vars,
                size: 1,
            }));
        } else if kind == KIND_APP {
            let mut child_infos = Vec::with_capacity(m.get_num_args(expr));
            for index in 0..m.get_num_args(expr) {
                let arg = m.get_arg(expr, index);
                child_infos.push(self.visit(m, cache, arg, delta, depth + 1)?);
            }
            if self.is_forbidden(m, expr) {
                info = None;
            } else if m.get_num_args(expr) == 0 {
                info = Some(Rc::new(CandidateInfo {
                    free_vars: OrderedSet::new(),
                    bound_vars: OrderedSet::new(),
                    size: 1,
                }));
            } else if child_infos.iter().all(Option::is_some) {
                let mut free_vars = OrderedSet::new();
                let mut bound_vars = OrderedSet::new();
                let mut size = 1;
                for child_info in child_infos.iter().flatten() {
                    for element in child_info.free_vars.iter() {
                        free_vars.insert(*element);
                    }
                    for element in child_info.bound_vars.iter() {
                        bound_vars.insert(*element);
                    }
                    size += child_info.size;
                }
                let is_candidate_shape = !free_vars.is_empty() && bound_vars.is_empty();
                let new_info = Rc::new(CandidateInfo {
                    free_vars,
                    bound_vars,
                    size,
                });
                info = Some(new_info.clone());
                let decl = &m.func_decls[m.decls[expr as usize] as usize];
                let is_arith_candidate = !self.is_nested_arith_only
                    && (decl.op == OP_IDIV || decl.op == OP_MOD || decl.op == OP_MUL);
                if is_candidate_shape && (decl.family != FAMILY_ARITH || is_arith_candidate) {
                    let mut shifter = InvVarShifter::new(m);
                    let candidate = m.without_temporaries(|m| shifter.shift(m, expr, delta))?;
                    self.add_candidate(m, candidate, new_info.free_vars.clone(), size);
                    m.dec_ref(candidate)?;
                    shifter.release(m)?;
                }
            }
        } else if kind == KIND_QUANTIFIER {
            let data = m.get_quantifier(expr)?;
            let count = data.sorts.len() as i32;
            let body = data.body;
            if let Some(body_info) = self.visit(m, cache, body, delta + count, depth + 1)? {
                let mut bound_vars = OrderedSet::new();
                for element in body_info.bound_vars.iter() {
                    if *element >= count {
                        bound_vars.insert(*element - count);
                    }
                }
                info = Some(Rc::new(CandidateInfo {
                    free_vars: body_info.free_vars.clone(),
                    bound_vars,
                    size: body_info.size + 1,
                }));
            }
        }
        cache.insert((expr, delta), info.clone());
        Ok(info)
    }

    fn add_candidate(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        free_vars: OrderedSet<i32>,
        size: usize,
    ) {
        if self.candidate_infos.contains_key(&expr) {
            return;
        }
        self.candidate_infos.insert(
            expr,
            Rc::new(CandidateInfo {
                free_vars,
                bound_vars: OrderedSet::new(),
                size,
            }),
        );
        self.candidates.push(m, expr);
    }

    // smaller_pattern: whether second is an instance of first.
    fn is_smaller(&self, m: &AstManager, first: Expr, second: Expr) -> bool {
        let mut bindings: Vec<Expr> = vec![-1; self.num_bindings];
        let mut todo = vec![(first, second)];
        while let Some((left, right)) = todo.pop() {
            let kind = m.kinds[left as usize];
            if kind == KIND_APP {
                if m.kinds[right as usize] != KIND_APP
                    || m.decls[left as usize] != m.decls[right as usize]
                    || m.get_num_args(left) != m.get_num_args(right)
                    || m.values[left as usize] != m.values[right as usize]
                {
                    return false;
                }
                for index in 0..m.get_num_args(left) {
                    todo.push((m.get_arg(left, index), m.get_arg(right, index)));
                }
            } else if kind == KIND_VAR
                && let Ok(index) = usize::try_from(m.values[left as usize])
                && index < self.num_bindings
            {
                if bindings[index] == -1 {
                    bindings[index] = right;
                } else if bindings[index] != right {
                    return false;
                }
            } else if left != right {
                return false;
            }
        }
        true
    }

    fn filter_looping_patterns(&mut self, m: &AstManager) -> Vec<Expr> {
        let mut result = Vec::new();
        let candidates = self.candidates.items.clone();
        for first in &candidates {
            let Some(first_info) = self.candidate_infos.get(first).cloned() else {
                continue;
            };
            let is_looping = self.is_blocking_loop_patterns
                && candidates.iter().any(|second| {
                    if second == first {
                        return false;
                    }
                    self.candidate_infos.get(second).is_some_and(|second_info| {
                        is_same_set(&first_info.free_vars, &second_info.free_vars)
                            && self.is_smaller(m, *first, *second)
                            && !self.is_smaller(m, *second, *first)
                    })
                });
            if is_looping {
                self.candidate_infos.remove(first);
            } else {
                result.push(*first);
            }
        }
        result
    }

    fn contains_subpattern(&self, m: &AstManager, expr: Expr) -> bool {
        let Some(info) = self.candidate_infos.get(&expr) else {
            return false;
        };
        let mut visited = HashSet::from([expr]);
        let mut todo = vec![expr];
        while let Some(current) = todo.pop() {
            if m.kinds[current as usize] != KIND_APP {
                continue;
            }
            if current != expr
                && let Some(current_info) = self.candidate_infos.get(&current)
                && is_same_set(&current_info.free_vars, &info.free_vars)
            {
                return true;
            }
            for index in 0..m.get_num_args(current) {
                let arg = m.get_arg(current, index);
                if visited.insert(arg) {
                    todo.push(arg);
                }
            }
        }
        false
    }

    fn mk_pattern(&self, m: &mut AstManager, candidate: Expr) -> Result<Expr, SmtError> {
        let has_var_arg = |m: &AstManager, expr: Expr| {
            m.kinds[expr as usize] == KIND_APP && m.some_arg(expr, |arg, _| m.is_var(arg))
        };
        if has_var_arg(m, candidate) {
            return m.mk_pattern(&[candidate]);
        }
        let mut args = Vec::with_capacity(m.get_num_args(candidate));
        for index in 0..m.get_num_args(candidate) {
            let arg = m.get_arg(candidate, index);
            if m.kinds[arg as usize] != KIND_APP {
                return m.mk_pattern(&[candidate]);
            }
            args.push(arg);
        }
        // An argument without a variable argument is replaced by the last one, which is visited in
        // its place, and its own arguments go last.
        let mut index = 0;
        while index < args.len() {
            let arg = args[index];
            if has_var_arg(m, arg) {
                index += 1;
                continue;
            }
            let last = args[args.len() - 1];
            args[index] = last;
            args.pop();
            if m.is_ground(arg) {
                continue;
            }
            for arg_index in 0..m.get_num_args(arg) {
                let inner_arg = m.get_arg(arg, arg_index);
                if m.kinds[inner_arg as usize] != KIND_APP {
                    return m.mk_pattern(&[candidate]);
                }
                args.push(inner_arg);
            }
        }
        m.mk_pattern(&args)
    }

    fn candidates_to_multi_patterns(
        &self,
        m: &mut AstManager,
        max_patterns: usize,
        candidates: &[Expr],
        result: &mut Vec<Expr>,
    ) -> Result<(), SmtError> {
        let mut pre_patterns: Vec<Option<PrePattern>> = vec![Some(PrePattern {
            exprs: Vec::new(),
            free_vars: OrderedSet::new(),
            index: 0,
        })];
        let mut num_splits = 0;
        let mut index = 0;
        while index < pre_patterns.len() {
            let Some(mut current) = pre_patterns[index].take() else {
                index += 1;
                continue;
            };
            if current.free_vars.len() == self.num_bindings {
                result.push(m.mk_pattern(&current.exprs)?);
                if result.len() >= max_patterns {
                    return Ok(());
                }
            } else if current.index < candidates.len() {
                let candidate = candidates[current.index];
                let candidate_free_vars = self
                    .candidate_infos
                    .get(&candidate)
                    .map(|info| info.free_vars.clone())
                    .unwrap_or_default();
                if !is_subset(&candidate_free_vars, &current.free_vars) {
                    let mut exprs = current.exprs.clone();
                    exprs.push(candidate);
                    let mut free_vars = current.free_vars.clone();
                    for element in candidate_free_vars.iter() {
                        free_vars.insert(*element);
                    }
                    pre_patterns.push(Some(PrePattern {
                        exprs,
                        free_vars,
                        index: current.index + 1,
                    }));
                    if num_splits < MAX_SPLITS {
                        current.index += 1;
                        pre_patterns.push(Some(current));
                        num_splits += 1;
                    }
                } else {
                    current.index += 1;
                    pre_patterns.push(Some(current));
                }
            }
            index += 1;
        }
        Ok(())
    }

    fn mk_patterns(
        &mut self,
        m: &mut AstManager,
        num_bindings: usize,
        body: Expr,
    ) -> Result<Vec<Expr>, SmtError> {
        self.num_bindings = num_bindings;
        self.collect(m, body)?;
        let mut result = Vec::new();
        if !self.candidates.is_empty() {
            let loose_candidates: Vec<Expr> = self
                .filter_looping_patterns(m)
                .into_iter()
                .filter(|candidate| !self.contains_subpattern(m, *candidate))
                .collect();
            // m_tmp1: the candidates that do not cover every variable, which may form a
            // multi-pattern.
            let mut partial_candidates = Vec::new();
            for candidate in loose_candidates {
                let is_total = self
                    .candidate_infos
                    .get(&candidate)
                    .is_some_and(|info| info.free_vars.len() == num_bindings);
                if is_total {
                    result.push(self.mk_pattern(m, candidate)?);
                } else {
                    partial_candidates.push(candidate);
                }
            }
            let num_extra_multi_patterns = usize::from(result.is_empty());
            if num_extra_multi_patterns > 0 && !partial_candidates.is_empty() {
                // std::stable_sort with m_pattern_weight_lt.
                let mut sorted: Vec<(Expr, usize)> = partial_candidates
                    .iter()
                    .enumerate()
                    .map(|(index, candidate)| (*candidate, index))
                    .collect();
                sorted.sort_by(|left, right| {
                    let left_info = self.candidate_infos.get(&left.0);
                    let right_info = self.candidate_infos.get(&right.0);
                    let (Some(left_info), Some(right_info)) = (left_info, right_info) else {
                        return left.1.cmp(&right.1);
                    };
                    if left_info.free_vars.len() != right_info.free_vars.len() {
                        return right_info.free_vars.len().cmp(&left_info.free_vars.len());
                    }
                    if left_info.size != right_info.size {
                        return left_info.size.cmp(&right_info.size);
                    }
                    left.1.cmp(&right.1)
                });
                let sorted: Vec<Expr> = sorted.into_iter().map(|entry| entry.0).collect();
                self.candidates_to_multi_patterns(
                    m,
                    num_extra_multi_patterns,
                    &sorted,
                    &mut result,
                )?;
            }
        }
        self.candidate_infos = HashMap::new();
        self.candidates.reset(m)?;
        Ok(result)
    }

    /// reduce_quantifier for a quantifier without patterns: arithmetic, then looping and
    /// non-nested arithmetic patterns, are allowed when no pattern is found without them.
    pub fn infer(
        &mut self,
        m: &mut AstManager,
        num_bindings: usize,
        body: Expr,
        weight: i32,
    ) -> Result<InferredPatterns, SmtError> {
        self.is_arith_forbidden = true;
        self.is_nested_arith_only = true;
        self.is_blocking_loop_patterns = true;
        let patterns = self.mk_patterns(m, num_bindings, body)?;
        if !patterns.is_empty() {
            return Ok(InferredPatterns { patterns, weight });
        }
        self.is_arith_forbidden = false;
        self.is_blocking_loop_patterns = false;
        let arith_patterns = self.mk_patterns(m, num_bindings, body)?;
        if !arith_patterns.is_empty() {
            return Ok(InferredPatterns {
                patterns: arith_patterns,
                weight: weight.max(PI_ARITH_WEIGHT),
            });
        }
        self.is_nested_arith_only = false;
        let non_nested_patterns = self.mk_patterns(m, num_bindings, body)?;
        let weight = if non_nested_patterns.is_empty() {
            weight
        } else {
            weight.max(PI_NON_NESTED_ARITH_WEIGHT)
        };
        Ok(InferredPatterns {
            patterns: non_nested_patterns,
            weight,
        })
    }

    /// The patterns of a quantifier that pull_quant changed, found once with the settings that
    /// infer restores: arithmetic is allowed, but only nested, and looping patterns are blocked.
    pub fn infer_pulled(
        &mut self,
        m: &mut AstManager,
        num_bindings: usize,
        body: Expr,
    ) -> Result<Vec<Expr>, SmtError> {
        self.is_arith_forbidden = false;
        self.is_nested_arith_only = true;
        self.is_blocking_loop_patterns = true;
        self.mk_patterns(m, num_bindings, body)
    }
}

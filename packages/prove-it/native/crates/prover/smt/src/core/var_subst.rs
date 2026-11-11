//! Ported from Z3 (src/ast/rewriter/var_subst.cpp), MIT license, through `var-subst.ts`.
//! Substitution and shifting of de Bruijn variables.
//!
//! `var_subst` and `expr_safe_replace` apply each other under quantifiers; the depth of that
//! recursion, the nesting of quantifiers, stops past `MAX_RECURSION_DEPTH`.

use std::collections::{HashMap, HashSet};

use crate::core::ast::{
    AstManager, Expr, KIND_APP, KIND_QUANTIFIER, KIND_VAR, QuantifierData, Sort,
};
use crate::core::expr_safe_replace::ExprSafeReplace;
use crate::core::rewriter_tpl::{BetaReducer, MAX_RECURSION_DEPTH};
use crate::util::error::SmtError;

/// var_subst: substitutes args for the free variables, args[n - 1 - i] for (:var i) in standard
/// order and args[i] otherwise, where -1 keeps the variable. Each result comes with a reference,
/// which the caller releases.
#[derive(Clone, Debug)]
pub struct VarSubst {
    reducer: BetaReducer,
    is_std_order: bool,
    // The nesting of the expr_safe_replace and var_subst that apply this one.
    depth: usize,
}

impl VarSubst {
    pub fn new(m: &AstManager, is_std_order: bool) -> VarSubst {
        VarSubst::with_depth(m, is_std_order, 0)
    }

    pub(crate) fn with_depth(m: &AstManager, is_std_order: bool, depth: usize) -> VarSubst {
        VarSubst {
            reducer: BetaReducer::new(m),
            is_std_order,
            depth,
        }
    }

    pub fn apply(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        args: &[Expr],
    ) -> Result<Expr, SmtError> {
        let count = args.len();
        if m.is_ground_app(expr) || count == 0 {
            m.inc_ref(expr);
            return Ok(expr);
        }
        if m.has_quantifier_flags[expr as usize] != 0 {
            if self.depth >= MAX_RECURSION_DEPTH {
                return Err(SmtError::Unsupported(
                    "the substitution nests too deeply".into(),
                ));
            }
            let mut replace = ExprSafeReplace::with_depth(self.depth + 1);
            for (index, arg) in args.iter().enumerate() {
                if *arg != -1 {
                    let variable = m.mk_var(
                        if self.is_std_order {
                            (count - index - 1) as i32
                        } else {
                            index as i32
                        },
                        m.sorts[*arg as usize],
                    );
                    replace.insert(m, variable, *arg);
                }
            }
            let result = replace.apply(m, expr)?;
            replace.release(m)?;
            return Ok(result);
        }
        if m.kinds[expr as usize] == KIND_APP
            && m.every_arg(expr, |arg, _| {
                m.is_ground_app(arg) || m.kinds[arg as usize] == KIND_VAR
            })
        {
            let new_args = m.map_args(expr, |arg, _| {
                if m.is_ground_app(arg) {
                    return arg;
                }
                let index = m.values[arg as usize] as usize;
                let replaced = if index < count {
                    if self.is_std_order {
                        args[count - index - 1]
                    } else {
                        args[index]
                    }
                } else {
                    -1
                };
                if replaced == -1 { arg } else { replaced }
            });
            let result = m.mk_app(m.decls[expr as usize], &new_args, m.sorts[expr as usize])?;
            m.inc_ref(result);
            return Ok(result);
        }
        self.reducer.reset(m)?;
        if self.is_std_order {
            self.reducer.set_inv_bindings(args);
        } else {
            self.reducer.set_bindings(args);
        }
        self.reducer.rewrite(m, expr)
    }

    /// ~var_subst.
    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.reducer.release(m)
    }
}

// A term whose children replace_free_vars is rebuilding: where its children's results start on the
// result stack, and the next child to visit.
struct ReplaceFrame {
    expr: Expr,
    shift: i32,
    start: usize,
    next: usize,
}

// The key of an expression under shift binders in the caches of replace_free_vars and
// get_free_var_sorts, as the TypeScript computes it.
fn get_shift_key(expr: Expr, shift: i32) -> i64 {
    i64::from(expr) * 64 + i64::from(shift)
}

/// Rebuilds expr with each free variable replaced. replace gets the variable, its de Bruijn index
/// relative to expr, and the number of binders above it. Like Z3's rewriter_tpl, it keeps its own
/// stack, so deep terms do not exhaust the call stack.
pub fn replace_free_vars(
    m: &mut AstManager,
    expr: Expr,
    mut replace: impl FnMut(&mut AstManager, Expr, i32, i32) -> Result<Expr, SmtError>,
) -> Result<Expr, SmtError> {
    let mut cache: HashMap<i64, Expr> = HashMap::new();
    let mut frames: Vec<ReplaceFrame> = Vec::new();
    let mut results: Vec<Expr> = Vec::new();
    let mut visit = |m: &mut AstManager,
                     frames: &mut Vec<ReplaceFrame>,
                     results: &mut Vec<Expr>,
                     cache: &mut HashMap<i64, Expr>,
                     current: Expr,
                     shift: i32|
     -> Result<(), SmtError> {
        if m.free_var_bounds[current as usize] <= shift {
            results.push(current);
            return Ok(());
        }
        let key = get_shift_key(current, shift);
        if let Some(cached) = cache.get(&key) {
            results.push(*cached);
        } else if m.kinds[current as usize] != KIND_VAR {
            frames.push(ReplaceFrame {
                expr: current,
                shift,
                start: results.len(),
                next: 0,
            });
        } else {
            let result = replace(m, current, m.values[current as usize] - shift, shift)?;
            cache.insert(key, result);
            results.push(result);
        }
        Ok(())
    };
    visit(m, &mut frames, &mut results, &mut cache, expr, 0)?;
    while let Some(frame) = frames.last_mut() {
        let current = frame.expr;
        let shift = frame.shift;
        let start = frame.start;
        let is_quantifier = m.kinds[current as usize] == KIND_QUANTIFIER;
        // A quantifier's children are its body and its patterns, under its binders.
        let (num_children, num_decls) = if is_quantifier {
            let data = m.get_quantifier(current)?;
            (1 + data.patterns.len(), data.sorts.len() as i32)
        } else {
            (m.get_num_args(current), 0)
        };
        if frame.next < num_children {
            let index = frame.next;
            frame.next += 1;
            if is_quantifier {
                let data = m.get_quantifier(current)?;
                let child = if index == 0 {
                    data.body
                } else {
                    data.patterns[index - 1]
                };
                visit(
                    m,
                    &mut frames,
                    &mut results,
                    &mut cache,
                    child,
                    shift + num_decls,
                )?;
            } else {
                let arg = m.get_arg(current, index);
                visit(m, &mut frames, &mut results, &mut cache, arg, shift)?;
            }
            continue;
        }
        let children = results.split_off(start);
        let result = if is_quantifier {
            let data = m.get_quantifier(current)?;
            let data = QuantifierData {
                body: children[0],
                patterns: children[1..].to_vec(),
                ..data.clone()
            };
            m.mk_quantifier(data)?
        } else {
            m.mk_app(
                m.decls[current as usize],
                &children,
                m.sorts[current as usize],
            )?
        };
        frames.pop();
        cache.insert(get_shift_key(current, shift), result);
        results.push(result);
    }
    results
        .first()
        .copied()
        .ok_or_else(|| SmtError::Invariant("replace_free_vars has no result".into()))
}

/// used_vars::process: the sort of each free variable of expr below count, indexed by de Bruijn
/// index, None for a variable that does not occur. Like Z3, it walks the term without rebuilding
/// it, and visits a shared term once for each number of binders above it.
pub fn get_free_var_sorts(
    m: &AstManager,
    expr: Expr,
    count: usize,
) -> Result<Vec<Option<Sort>>, SmtError> {
    let mut sorts: Vec<Option<Sort>> = vec![None; count];
    let mut exprs = vec![expr];
    let mut deltas = vec![0];
    let mut visited: HashSet<i64> = HashSet::new();
    while let Some(current) = exprs.pop() {
        let delta = deltas.pop().unwrap_or(0);
        if m.free_var_bounds[current as usize] <= delta {
            continue;
        }
        if m.get_ref_count(current) > 1 && !visited.insert(get_shift_key(current, delta)) {
            continue;
        }
        let kind = m.kinds[current as usize];
        if kind == KIND_VAR {
            let index = m.values[current as usize] - delta;
            if let Ok(index) = usize::try_from(index)
                && index < count
                && sorts[index].is_none()
            {
                sorts[index] = Some(m.sorts[current as usize]);
            }
        } else if kind == KIND_APP {
            for index in 0..m.get_num_args(current) {
                exprs.push(m.get_arg(current, index));
                deltas.push(delta);
            }
        } else {
            let data = m.get_quantifier(current)?;
            for child in std::iter::once(data.body).chain(data.patterns.iter().copied()) {
                exprs.push(child);
                deltas.push(delta + data.sorts.len() as i32);
            }
        }
    }
    Ok(sorts)
}

/// Which variables of a quantifier body occur, indexed by de Bruijn index.
pub fn collect_used_vars(m: &AstManager, expr: Expr, count: usize) -> Result<Vec<bool>, SmtError> {
    Ok(get_free_var_sorts(m, expr, count)?
        .iter()
        .map(|sort| sort.is_some())
        .collect())
}

/// unused_vars_eliminator: drops the variables that neither the body nor a pattern uses. Its
/// var_subst keeps the cache of its last substitution until the next one.
#[derive(Clone, Debug)]
pub struct UnusedVarsEliminator {
    subst: VarSubst,
}

impl UnusedVarsEliminator {
    pub fn new(m: &AstManager) -> UnusedVarsEliminator {
        UnusedVarsEliminator {
            subst: VarSubst::new(m, true),
        }
    }

    /// The result comes with a reference, which the caller releases.
    pub fn apply(&mut self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        m.without_temporaries(|m| self.apply_core(m, expr))
    }

    fn apply_core(&mut self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        let data = if m.kinds[expr as usize] == KIND_QUANTIFIER {
            m.get_quantifier(expr)?.clone()
        } else {
            m.inc_ref(expr);
            return Ok(expr);
        };
        // ignore_patterns_on_ground_qbody: a ground body drops the patterns with the variables.
        if m.is_ground(data.body) {
            m.inc_ref(data.body);
            return Ok(data.body);
        }
        // used_vars: the sort of each free variable of the body and the patterns.
        let mut used_sorts: Vec<Option<Sort>> = Vec::new();
        for term in std::iter::once(data.body).chain(data.patterns.iter().copied()) {
            let bound = usize::try_from(m.free_var_bounds[term as usize]).unwrap_or(0);
            for (index, sort) in get_free_var_sorts(m, term, bound)?.into_iter().enumerate() {
                if let Some(sort) = sort {
                    if index >= used_sorts.len() {
                        used_sorts.resize(index + 1, None);
                    }
                    used_sorts[index] = Some(sort);
                }
            }
        }
        let num_decls = data.sorts.len();
        let get_used = |index: usize| used_sorts.get(index).copied().flatten();
        if (0..num_decls)
            .filter(|index| get_used(*index).is_some())
            .count()
            == num_decls
        {
            m.inc_ref(expr);
            return Ok(expr);
        }
        let mut kept_sorts = Vec::new();
        let mut kept_names = Vec::new();
        for (index, sort) in data.sorts.iter().enumerate() {
            if get_used(num_decls - index - 1).is_none() {
                continue;
            }
            kept_sorts.push(*sort);
            kept_names.push(data.names[index].clone());
        }
        // var_mapping: (:var i) becomes the variable it moves to, and an unused variable stays.
        let mut mapping: Vec<Expr> = Vec::new();
        let mut num_removed = 0;
        for index in 0..num_decls.max(used_sorts.len()) {
            let Some(sort) = get_used(index) else {
                if index < num_decls {
                    num_removed += 1;
                }
                mapping.push(-1);
                continue;
            };
            let variable = m.mk_var((index - num_removed) as i32, sort);
            m.inc_ref(variable);
            mapping.push(variable);
        }
        mapping.reverse();
        let body = self.subst.apply(m, data.body, &mapping)?;
        let mut patterns = Vec::new();
        if num_removed != num_decls {
            for pattern in &data.patterns {
                patterns.push(self.subst.apply(m, *pattern, &mapping)?);
            }
        }
        let result = if num_removed == num_decls {
            body
        } else {
            m.mk_quantifier(QuantifierData {
                sorts: kept_sorts,
                names: kept_names,
                body,
                patterns: patterns.clone(),
                ..data
            })?
        };
        if result != body {
            m.inc_ref(result);
            for pattern in &patterns {
                m.dec_ref(*pattern)?;
            }
            m.dec_ref(body)?;
        }
        for variable in &mapping {
            if *variable != -1 {
                m.dec_ref(*variable)?;
            }
        }
        Ok(result)
    }

    /// ~unused_vars_eliminator.
    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.subst.release(m)
    }
}

/// elim_unused_vars: unused_vars_eliminator with a var_subst of its own. The result is a
/// temporary.
pub fn elim_unused_vars(m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
    let mut eliminator = UnusedVarsEliminator::new(m);
    let result = eliminator.apply(m, expr)?;
    eliminator.release(m)?;
    m.release_later(result)?;
    Ok(result)
}

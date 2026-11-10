//! Ported from Z3 (src/ast/rewriter/expr_safe_replace.cpp), MIT license, through
//! `expr-safe-replace.ts`. Replaces subterms by terms, under quantifiers too, without rewriting.
//! Like Z3, it visits the arguments of an application from the last one, and holds the expressions
//! it creates.
//!
//! Under a quantifier it applies another replacer, so the nesting of quantifiers is a recursion,
//! which stops past `MAX_RECURSION_DEPTH`.

use std::collections::HashMap;

use crate::core::ast::{AstManager, Expr, KIND_APP, KIND_VAR, QuantifierData};
use crate::core::ref_vector::RefVector;
use crate::core::rewriter_tpl::{MAX_RECURSION_DEPTH, VarShifter};
use crate::core::var_subst::VarSubst;
use crate::util::error::SmtError;

#[derive(Clone, Debug, Default)]
pub struct ExprSafeReplace {
    pub sources: RefVector,
    pub targets: RefVector,
    refs: RefVector,
    cache: HashMap<Expr, Expr>,
    // The nesting of the expr_safe_replace and var_subst that apply this one.
    depth: usize,
}

impl ExprSafeReplace {
    pub fn new() -> ExprSafeReplace {
        ExprSafeReplace::default()
    }

    pub(crate) fn with_depth(depth: usize) -> ExprSafeReplace {
        ExprSafeReplace {
            depth,
            ..ExprSafeReplace::default()
        }
    }

    pub fn insert(&mut self, m: &mut AstManager, source: Expr, target: Expr) {
        self.sources.push(m, source);
        self.targets.push(m, target);
        self.cache.clear();
    }

    /// operator(): the result comes with a reference, which the caller releases.
    pub fn apply(&mut self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        if self.sources.is_empty() {
            m.inc_ref(expr);
            return Ok(expr);
        }
        if self.cache.is_empty() {
            for (index, source) in self.sources.items.iter().enumerate() {
                self.cache
                    .entry(*source)
                    .or_insert(self.targets.items[index]);
            }
        }
        let mut todo = vec![expr];
        self.refs.push(m, expr);
        while let Some(current) = todo.last().copied() {
            if self.cache.contains_key(&current) {
                todo.pop();
            } else if m.kinds[current as usize] == KIND_VAR {
                self.cache.insert(current, current);
                todo.pop();
            } else if m.kinds[current as usize] == KIND_APP {
                let mut args = Vec::new();
                let mut is_different = false;
                let mut has_all_args = true;
                for index in 0..m.get_num_args(current) {
                    let arg = m.get_arg(current, index);
                    let replaced = if has_all_args {
                        self.cache.get(&arg).copied()
                    } else {
                        None
                    };
                    if let Some(replaced) = replaced {
                        args.push(replaced);
                        is_different |= arg != replaced;
                        continue;
                    }
                    todo.push(arg);
                    has_all_args = false;
                }
                if has_all_args {
                    let result = if is_different {
                        m.mk_app(m.decls[current as usize], &args, m.sorts[current as usize])?
                    } else {
                        current
                    };
                    if is_different {
                        self.refs.push(m, result);
                    }
                    self.cache.insert(current, result);
                    todo.pop();
                }
            } else {
                self.apply_quantifier(m, current, &mut todo)?;
            }
        }
        let Some(result) = self.cache.get(&expr).copied() else {
            return Err(SmtError::Invariant(
                "the replaced expression has no result".into(),
            ));
        };
        m.inc_ref(result);
        if self.refs.len() > 1 << 20 {
            self.cache.clear();
            self.refs.reset(m)?;
        }
        Ok(result)
    }

    // Replaces the quantifier, or pushes the children it still needs.
    fn apply_quantifier(
        &mut self,
        m: &mut AstManager,
        quantifier: Expr,
        todo: &mut Vec<Expr>,
    ) -> Result<(), SmtError> {
        let data = m.get_quantifier(quantifier)?.clone();
        let mut patterns = RefVector::new();
        let mut body = -1;
        let is_all_ground = self
            .sources
            .items
            .iter()
            .all(|source| m.is_ground_app(*source))
            && self
                .targets
                .items
                .iter()
                .all(|target| m.is_ground_app(*target));
        if is_all_ground {
            let mut has_all_data = true;
            match self.cache.get(&data.body).copied() {
                None => {
                    todo.push(data.body);
                    has_all_data = false;
                }
                Some(cached_body) => {
                    body = cached_body;
                    m.inc_ref(body);
                }
            }
            for pattern in &data.patterns {
                let replaced = if has_all_data {
                    self.cache.get(pattern).copied()
                } else {
                    None
                };
                if let Some(replaced) = replaced {
                    patterns.push(m, replaced);
                    continue;
                }
                todo.push(*pattern);
                has_all_data = false;
            }
            if !has_all_data {
                patterns.reset(m)?;
                if body != -1 {
                    m.dec_ref(body)?;
                }
                return Ok(());
            }
        } else {
            if self.depth >= MAX_RECURSION_DEPTH {
                return Err(SmtError::Unsupported(
                    "the replacement nests too deeply".into(),
                ));
            }
            let mut replace = ExprSafeReplace::with_depth(self.depth + 1);
            let mut shifter = VarShifter::new(m);
            let num_decls = data.sorts.len() as i32;
            let mut source = -1;
            let mut target = -1;
            let mut pattern = -1;
            for index in 0..self.sources.len() {
                let original = self.sources.items[index];
                let shifted_source = shifter.shift(m, original, 0, num_decls, 0)?;
                if source != -1 {
                    m.dec_ref(source)?;
                }
                source = shifted_source;
                let shifted_target =
                    shifter.shift(m, self.targets.items[index], 0, num_decls, 0)?;
                if target != -1 {
                    m.dec_ref(target)?;
                }
                target = shifted_target;
                replace.insert(m, source, target);
            }
            for original in &data.patterns {
                let replaced = replace.apply(m, *original)?;
                if pattern != -1 {
                    m.dec_ref(pattern)?;
                }
                pattern = replaced;
                patterns.push(m, pattern);
            }
            let is_all_vars = replace
                .sources
                .items
                .iter()
                .all(|replaced| m.kinds[*replaced as usize] == KIND_VAR);
            if is_all_vars {
                let max_index = replace
                    .sources
                    .items
                    .iter()
                    .map(|replaced| m.values[*replaced as usize])
                    .fold(0, i32::max);
                let mut args = vec![-1; max_index as usize + 1];
                for (index, replaced) in replace.sources.items.iter().enumerate() {
                    args[m.values[*replaced as usize] as usize] = replace.targets.items[index];
                }
                let mut subst = VarSubst::with_depth(m, false, self.depth + 1);
                body = subst.apply(m, data.body, &args)?;
                subst.release(m)?;
            } else {
                body = replace.apply(m, data.body)?;
            }
            for expr in [pattern, target, source] {
                if expr != -1 {
                    m.dec_ref(expr)?;
                }
            }
            shifter.release(m)?;
            replace.release(m)?;
        }
        let result = m.mk_quantifier(QuantifierData {
            body,
            patterns: patterns.items.clone(),
            ..data
        })?;
        self.refs.push(m, result);
        self.cache.insert(quantifier, result);
        todo.pop();
        patterns.reset(m)?;
        m.dec_ref(body)
    }

    /// ~expr_safe_replace.
    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.cache.clear();
        self.refs.reset(m)?;
        self.targets.reset(m)?;
        self.sources.reset(m)
    }
}

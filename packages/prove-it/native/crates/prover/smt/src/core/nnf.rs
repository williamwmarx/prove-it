//! Ported from Z3 (src/ast/normal_forms/nnf.cpp, name_exprs.cpp, defined_names.cpp), MIT license,
//! through `nnf.ts`. Negation normal form in Z3's default NNF_SKOLEM mode: only subformulas that
//! contain quantifiers are normalized, and existential quantifiers in positive positions become
//! Skolem functions of the enclosing universal variables. A quantifier inside an atom gets a name, a
//! fresh predicate over its free variables, with a definition that is normalized too. Like Z3, the
//! frames, the result stack and the caches hold their expressions, so that expressions are created
//! and deleted in Z3's order.
//!
//! The TypeScript's `Nnf` and `QuantifierNamer` keep the `DefinedNames` they were made with; here
//! the owner keeps it, and passes it to [`Nnf::apply`].

use std::collections::HashMap;

use crate::core::act_cache::ActCache;
use crate::core::ast::{
    AstManager, Expr, KIND_APP, KIND_QUANTIFIER, KIND_VAR, OP_AND, OP_EQ, OP_IMPLIES, OP_ITE,
    OP_NOT, OP_OR, OP_XOR, QuantifierData, SORT_BOOL, SmtSymbol, Sort,
};
use crate::core::ast_util::mk_not;
use crate::core::ref_vector::RefVector;
use crate::core::rewriter_tpl::{RewriterConfig, RewriterTpl};
use crate::core::var_subst::{VarSubst, elim_unused_vars, get_free_var_sorts};
use crate::util::error::SmtError;

// The number of free variables of expr, the bound get_free_var_sorts takes.
fn get_free_var_bound(m: &AstManager, expr: Expr) -> usize {
    usize::try_from(m.free_var_bounds[expr as usize]).unwrap_or(0)
}

/// defined_names: the name of each named expression. It holds the expressions and their names.
#[derive(Clone, Debug, Default)]
pub struct DefinedNames {
    names: HashMap<Expr, Expr>,
    exprs: RefVector,
    name_refs: RefVector,
    lims: Vec<usize>,
}

impl DefinedNames {
    pub fn new() -> DefinedNames {
        DefinedNames::default()
    }

    pub fn push(&mut self) {
        self.lims.push(self.exprs.len());
    }

    /// pop_scope: forgets the names since the matching push, the last first.
    pub fn pop(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        let Some(size) = self.lims.pop() else {
            return Ok(());
        };
        while self.exprs.len() > size {
            self.names.remove(&self.exprs.items[self.exprs.len() - 1]);
            self.exprs.shrink(m, self.exprs.len() - 1)?;
            self.name_refs.shrink(m, self.name_refs.len() - 1)?;
        }
        Ok(())
    }

    /// mk_name: (n x1 ... xk) for the free variables x1 ... xk of the quantifier, with n => q and q
    /// => n as the definition, under a universal quantifier whose pattern is the name. Returns the
    /// name and the definition, which comes with a reference, and is -1 when the quantifier already
    /// has a name.
    pub fn mk_name(
        &mut self,
        m: &mut AstManager,
        quantifier: Expr,
    ) -> Result<(Expr, Expr), SmtError> {
        if let Some(existing) = self.names.get(&quantifier) {
            return Ok((*existing, -1));
        }
        // gen_name: a variable that does not occur still takes a position, filled with true.
        let free_var_sorts = get_free_var_sorts(m, quantifier, get_free_var_bound(m, quantifier))?;
        let var_sorts: Vec<Sort> = free_var_sorts
            .iter()
            .map(|sort| sort.unwrap_or(SORT_BOOL))
            .collect();
        let decl = m.mk_fresh_func_decl(
            Some(&SmtSymbol::Name("z3name".into())),
            &var_sorts,
            SORT_BOOL,
            true,
        );
        let mut args = Vec::with_capacity(free_var_sorts.len());
        for (index, sort) in free_var_sorts.iter().enumerate() {
            args.push(match sort {
                None => m.true_expr,
                Some(sort) => m.mk_var(index as i32, *sort),
            });
        }
        let name = m.mk_app(decl, &args, SORT_BOOL)?;
        self.names.insert(quantifier, name);
        self.exprs.push(m, quantifier);
        self.name_refs.push(m, name);
        // bound_vars: the variables are in reverse order in the quantifier.
        let definition = m.with_temporaries(|m| {
            let bound_vars = |m: &mut AstManager, conjunct: Expr| -> Result<Expr, SmtError> {
                if var_sorts.is_empty() {
                    return Ok(conjunct);
                }
                let count = var_sorts.len();
                let pattern = m.mk_pattern(&[name])?;
                let quantifier = m.mk_quantifier(QuantifierData {
                    is_forall: true,
                    sorts: var_sorts.iter().rev().copied().collect(),
                    names: (0..count)
                        .map(|index| SmtSymbol::Number((count - 1 - index) as u64))
                        .collect(),
                    body: conjunct,
                    patterns: vec![pattern],
                    weight: 1,
                    qid: String::new(),
                })?;
                elim_unused_vars(m, quantifier)
            };
            let not_name = m.mk_not(name)?;
            let first_or = m.mk_or(&[not_name, quantifier])?;
            let first = bound_vars(m, first_or)?;
            let not_quantifier = m.mk_not(quantifier)?;
            let second_or = m.mk_or(&[name, not_quantifier])?;
            let second = bound_vars(m, second_or)?;
            m.mk_and(&[first, second])
        })?;
        Ok((name, definition))
    }
}

/// name_quantifier_labels' configuration: replaces each quantifier by its name, and collects the
/// definitions of the new names. It holds the names and the definitions only while
/// [`QuantifierNamer::name`] runs.
#[derive(Clone, Debug, Default)]
struct QuantifierNamerConfig {
    names: DefinedNames,
    definitions: RefVector,
}

impl RewriterConfig for QuantifierNamerConfig {
    const IS_SUBSTITUTING: bool = true;

    fn get_subst(&mut self, m: &mut AstManager, expr: Expr) -> Result<Option<Expr>, SmtError> {
        if m.kinds[expr as usize] != KIND_QUANTIFIER {
            return Ok(None);
        }
        let (name, definition) = self.names.mk_name(m, expr)?;
        if definition != -1 {
            self.definitions.push(m, definition);
            m.dec_ref(definition)?;
        }
        Ok(Some(name))
    }
}

/// name_quantifier_labels: a rewriter that replaces each quantifier by its name, and collects the
/// definitions of the new names.
#[derive(Clone, Debug)]
struct QuantifierNamer {
    rewriter: RewriterTpl<QuantifierNamerConfig>,
}

impl QuantifierNamer {
    fn new(m: &AstManager) -> QuantifierNamer {
        QuantifierNamer {
            rewriter: RewriterTpl::new(m, QuantifierNamerConfig::default()),
        }
    }

    /// The result comes with a reference, which the caller releases.
    fn name(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        names: &mut DefinedNames,
        definitions: &mut RefVector,
    ) -> Result<Expr, SmtError> {
        std::mem::swap(&mut self.rewriter.cfg.names, names);
        std::mem::swap(&mut self.rewriter.cfg.definitions, definitions);
        let result = self.rewriter.rewrite(m, expr);
        std::mem::swap(&mut self.rewriter.cfg.names, names);
        std::mem::swap(&mut self.rewriter.cfg.definitions, definitions);
        result
    }

    fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.rewriter.release(m)
    }
}

/// skolemizer: the Skolem functions take the free variables of the quantifier. The function of the
/// last variable comes first, and takes the variable's name.
#[derive(Clone, Debug)]
struct Skolemizer {
    cache: ActCache,
    subst: VarSubst,
}

impl Skolemizer {
    fn new(m: &AstManager) -> Skolemizer {
        Skolemizer {
            cache: ActCache::new(m.get_num_asts()),
            subst: VarSubst::new(m, true),
        }
    }

    /// The result comes with a reference, which the caller releases.
    fn skolemize(&mut self, m: &mut AstManager, quantifier: Expr) -> Result<Expr, SmtError> {
        if let Some(cached) = self.cache.find(m, quantifier, 0) {
            m.inc_ref(cached);
            return Ok(cached);
        }
        let data = m.get_quantifier(quantifier)?.clone();
        let count = data.sorts.len();
        let free_var_sorts: Vec<Option<Sort>> =
            get_free_var_sorts(m, data.body, get_free_var_bound(m, data.body))?
                .into_iter()
                .skip(count)
                .collect();
        let mut args = RefVector::new();
        let mut arg_sorts = Vec::new();
        for (index, sort) in free_var_sorts.iter().enumerate() {
            let Some(sort) = sort else {
                continue;
            };
            let variable = m.mk_var(index as i32, *sort);
            args.push(m, variable);
            arg_sorts.push(*sort);
        }
        let mut substitution = RefVector::new();
        for index in (0..count).rev() {
            let sort = data.sorts[index];
            let decl = m.mk_fresh_func_decl(Some(&data.names[index]), &arg_sorts, sort, true);
            let app = m.mk_app(decl, &args.items, sort)?;
            substitution.push(m, app);
        }
        for (index, sort) in free_var_sorts.iter().enumerate() {
            let variable = match sort {
                None => -1,
                Some(sort) => m.mk_var(index as i32, *sort),
            };
            substitution.push(m, variable);
        }
        substitution.items.reverse();
        let result = self.subst.apply(m, data.body, &substitution.items)?;
        substitution.reset(m)?;
        args.reset(m)?;
        self.cache.insert(m, quantifier, 0, result)?;
        Ok(result)
    }

    /// ~skolemizer: the cache goes first, then the substitution.
    fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.cache.reset(m)?;
        self.subst.release(m)
    }
}

// A normalization still to finish: its expression, the next child, its polarity, whether it is
// nested in a quantifier, whether to cache its result, and where its children's results start.
#[derive(Clone, Copy, Debug)]
struct Frame {
    curr: Expr,
    index: usize,
    is_positive: bool,
    is_in_quantifier: bool,
    is_caching: bool,
    spos: usize,
}

/// nnf: one object normalizes the formulas of a reduction, and keeps its caches until it is
/// released.
#[derive(Clone, Debug)]
pub struct Nnf {
    frames: Vec<Frame>,
    results: RefVector,
    // One cache per polarity and nesting in a quantifier, in Z3's order of get_cache_idx.
    caches: Vec<ActCache>,
    todo_defs: RefVector,
    skolemizer: Skolemizer,
    namer: QuantifierNamer,
}

impl Nnf {
    pub fn new(m: &AstManager) -> Nnf {
        Nnf {
            frames: Vec::new(),
            results: RefVector::new(),
            caches: (0..4).map(|_| ActCache::new(m.get_num_asts())).collect(),
            todo_defs: RefVector::new(),
            skolemizer: Skolemizer::new(m),
            namer: QuantifierNamer::new(m),
        }
    }

    /// operator(): pushes the normal forms of the definitions of the names it introduced, the last
    /// first, then returns the normal form of expr with a reference, which the caller releases.
    pub fn apply(
        &mut self,
        m: &mut AstManager,
        names: &mut DefinedNames,
        expr: Expr,
        definitions: &mut RefVector,
    ) -> Result<Expr, SmtError> {
        m.without_temporaries(|m| {
            self.reset(m)?;
            let result = self.process(m, names, expr)?;
            let start = definitions.len();
            let mut index = 0;
            while index < self.todo_defs.len() {
                let definition = self.process(m, names, self.todo_defs.items[index])?;
                definitions.push_owned(definition);
                index += 1;
            }
            let mut added = definitions.items.split_off(start);
            added.reverse();
            definitions.items.extend(added);
            Ok(result)
        })
    }

    /// ~nnf: the namer, then the skolemizer, the definitions and the caches, the last first.
    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        m.without_temporaries(|m| {
            self.namer.release(m)?;
            self.skolemizer.release(m)?;
            self.todo_defs.reset(m)?;
            for cache in self.caches.iter_mut().rev() {
                cache.reset(m)?;
            }
            self.results.reset(m)?;
            self.pop_frames(m, 0)
        })
    }

    fn reset(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.pop_frames(m, 0)?;
        self.results.reset(m)?;
        self.todo_defs.reset(m)
    }

    fn pop_frames(&mut self, m: &mut AstManager, size: usize) -> Result<(), SmtError> {
        if size >= self.frames.len() {
            return Ok(());
        }
        for frame in self.frames.split_off(size) {
            m.dec_ref(frame.curr)?;
        }
        Ok(())
    }

    fn get_cache(&mut self, is_positive: bool, is_in_quantifier: bool) -> &mut ActCache {
        &mut self.caches[usize::from(is_in_quantifier) * 2 + usize::from(is_positive)]
    }

    fn push_frame(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        is_positive: bool,
        is_in_quantifier: bool,
        is_caching: bool,
    ) {
        m.inc_ref(expr);
        self.frames.push(Frame {
            curr: expr,
            index: 0,
            is_positive,
            is_in_quantifier,
            is_caching,
            spos: self.results.len(),
        });
    }

    fn skip(&mut self, m: &mut AstManager, expr: Expr, is_positive: bool) -> Result<(), SmtError> {
        let result = if is_positive { expr } else { mk_not(m, expr)? };
        self.results.push(m, result);
        Ok(())
    }

    // visit: whether the result of expr is on the result stack. Otherwise it pushes a frame for
    // expr.
    fn visit(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        is_positive: bool,
        is_in_quantifier: bool,
    ) -> Result<bool, SmtError> {
        if m.has_quantifier_flags[expr as usize] == 0 {
            self.skip(m, expr, is_positive)?;
            return Ok(true);
        }
        let is_caching = m.get_ref_count(expr) > 1;
        if is_caching
            && let Some(cached) = self
                .get_cache(is_positive, is_in_quantifier)
                .find(m, expr, 0)
        {
            self.results.push(m, cached);
            return Ok(true);
        }
        let kind = m.kinds[expr as usize];
        if kind == KIND_VAR || (kind == KIND_APP && m.get_num_args(expr) == 0) {
            self.skip(m, expr, is_positive)?;
            return Ok(true);
        }
        self.push_frame(m, expr, is_positive, is_in_quantifier, is_caching);
        Ok(false)
    }

    // process: the normal form of expr, with a reference.
    fn process(
        &mut self,
        m: &mut AstManager,
        names: &mut DefinedNames,
        expr: Expr,
    ) -> Result<Expr, SmtError> {
        if !self.visit(m, expr, true, false)? {
            while let Some(frame) = self.frames.last().copied() {
                m.limit.checkpoint()?;
                let top = self.frames.len() - 1;
                let curr = frame.curr;
                if frame.index == 0 && m.get_ref_count(curr) > 1 {
                    let cached = self
                        .get_cache(frame.is_positive, frame.is_in_quantifier)
                        .find(m, curr, 0);
                    if let Some(cached) = cached {
                        self.results.push(m, cached);
                        self.pop_frames(m, top)?;
                        continue;
                    }
                }
                let is_done = if m.kinds[curr as usize] == KIND_QUANTIFIER {
                    self.process_quantifier(m, curr, top)?
                } else {
                    self.process_app(m, names, curr, top)?
                };
                if !is_done {
                    continue;
                }
                if frame.is_caching {
                    let last = self.get_last_result()?;
                    self.get_cache(frame.is_positive, frame.is_in_quantifier)
                        .insert(m, curr, 0, last)?;
                }
                self.pop_frames(m, self.frames.len() - 1)?;
            }
        }
        self.results
            .items
            .pop()
            .ok_or_else(|| SmtError::Invariant("nnf has no result".into()))
    }

    fn get_last_result(&self) -> Result<Expr, SmtError> {
        self.results
            .items
            .last()
            .copied()
            .ok_or_else(|| SmtError::Invariant("nnf has no result".into()))
    }

    // Visits the children from the frame's index on, each with its polarity, and whether all are
    // done.
    fn visit_children(
        &mut self,
        m: &mut AstManager,
        top: usize,
        children: &[(Expr, bool)],
    ) -> Result<bool, SmtError> {
        while self.frames[top].index < children.len() {
            let child = children[self.frames[top].index];
            self.frames[top].index += 1;
            let is_in_quantifier = self.frames[top].is_in_quantifier;
            if !self.visit(m, child.0, child.1, is_in_quantifier)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    // Replaces the results from spos on with result.
    fn set_result(
        &mut self,
        m: &mut AstManager,
        spos: usize,
        result: Expr,
    ) -> Result<(), SmtError> {
        m.inc_ref(result);
        self.results.shrink(m, spos)?;
        self.results.push_owned(result);
        Ok(())
    }

    fn process_app(
        &mut self,
        m: &mut AstManager,
        names: &mut DefinedNames,
        expr: Expr,
        top: usize,
    ) -> Result<bool, SmtError> {
        let is_positive = self.frames[top].is_positive;
        let spos = self.frames[top].spos;
        let op = m.get_op(expr);
        let key = if op == OP_EQ && !m.is_bool(m.get_arg(expr, 0)) {
            -1
        } else {
            op
        };
        match key {
            OP_AND | OP_OR => {
                let children = m.map_args(expr, |arg, _| (arg, is_positive));
                if !self.visit_children(m, top, &children)? {
                    return Ok(false);
                }
                let results = self.results.items[spos..].to_vec();
                let decl = if (op == OP_AND) == is_positive {
                    OP_AND
                } else {
                    OP_OR
                };
                let result = m.mk_app(decl, &results, SORT_BOOL)?;
                self.set_result(m, spos, result)?;
                Ok(true)
            }
            OP_NOT => {
                let children = [(m.get_arg(expr, 0), !is_positive)];
                self.visit_children(m, top, &children)
            }
            OP_IMPLIES => {
                let children = [
                    (m.get_arg(expr, 0), !is_positive),
                    (m.get_arg(expr, 1), is_positive),
                ];
                if !self.visit_children(m, top, &children)? {
                    return Ok(false);
                }
                let results = self.results.items[spos..].to_vec();
                let decl = if is_positive { OP_OR } else { OP_AND };
                let result = m.mk_app(decl, &results, SORT_BOOL)?;
                self.set_result(m, spos, result)?;
                Ok(true)
            }
            OP_ITE => {
                let children = [
                    (m.get_arg(expr, 0), true),
                    (m.get_arg(expr, 0), false),
                    (m.get_arg(expr, 1), is_positive),
                    (m.get_arg(expr, 2), is_positive),
                ];
                if !self.visit_children(m, top, &children)? {
                    return Ok(false);
                }
                let results = self.results.items[spos..].to_vec();
                let first = m.mk_app(OP_OR, &[results[1], results[2]], SORT_BOOL)?;
                let second = m.mk_app(OP_OR, &[results[0], results[3]], SORT_BOOL)?;
                let result = m.mk_app(OP_AND, &[first, second], SORT_BOOL)?;
                self.set_result(m, spos, result)?;
                Ok(true)
            }
            OP_EQ | OP_XOR => {
                let children = [
                    (m.get_arg(expr, 0), true),
                    (m.get_arg(expr, 0), false),
                    (m.get_arg(expr, 1), true),
                    (m.get_arg(expr, 1), false),
                ];
                if !self.visit_children(m, top, &children)? {
                    return Ok(false);
                }
                let results = self.results.items[spos..].to_vec();
                let is_equivalence = (op == OP_EQ) == is_positive;
                let first_args = if is_equivalence {
                    [results[1], results[2]]
                } else {
                    [results[0], results[2]]
                };
                let first = m.mk_app(OP_OR, &first_args, SORT_BOOL)?;
                let second_args = if is_equivalence {
                    [results[0], results[3]]
                } else {
                    [results[1], results[3]]
                };
                let second = m.mk_app(OP_OR, &second_args, SORT_BOOL)?;
                let result = m.mk_app(OP_AND, &[first, second], SORT_BOOL)?;
                self.set_result(m, spos, result)?;
                Ok(true)
            }
            _ => {
                // process_default: the quantifiers of an atom get names.
                let named = self.namer.name(m, expr, names, &mut self.todo_defs)?;
                if is_positive {
                    self.results.push_owned(named);
                } else {
                    let negated = mk_not(m, named)?;
                    self.results.push(m, negated);
                    m.dec_ref(named)?;
                }
                Ok(true)
            }
        }
    }

    fn process_quantifier(
        &mut self,
        m: &mut AstManager,
        quantifier: Expr,
        top: usize,
    ) -> Result<bool, SmtError> {
        let data = m.get_quantifier(quantifier)?.clone();
        let frame = self.frames[top];
        let is_universal = data.is_forall == frame.is_positive;
        if frame.index == 0 {
            self.frames[top].index = 1;
            if is_universal {
                if !self.visit(m, data.body, frame.is_positive, true)? {
                    return Ok(false);
                }
            } else {
                let skolemized = self.skolemizer.skolemize(m, quantifier)?;
                let is_done = self.visit(m, skolemized, !data.is_forall, frame.is_in_quantifier)?;
                m.dec_ref(skolemized)?;
                if !is_done {
                    return Ok(false);
                }
            }
        }
        // A skolemized quantifier's result is already on the stack.
        if !is_universal {
            return Ok(true);
        }
        let body = self.get_last_result()?;
        let result = m.mk_quantifier(QuantifierData {
            is_forall: true,
            body,
            ..data
        })?;
        self.set_result(m, self.results.len() - 1, result)?;
        Ok(true)
    }
}

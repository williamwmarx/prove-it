//! Ported from Z3 (src/model/model_macro_solver.cpp, src/ast/macros/macro_util.cpp,
//! src/ast/func_decl_dependencies.cpp), MIT license, through `model-macro-solver.ts`. Collects the
//! conditional macros of a quantifier, f(x) = def when cond, and satisfies quantifiers by taking
//! such a def as the else case of the interpretation of f.
//!
//! The TypeScript's `getInfo` callback is the model finder's quantifier infos, passed as the map
//! that holds them; every quantifier the solvers see has one (the finder registers each first).
//! The recursive walks over terms carry a depth counter (design/smt-core.md, "Recursion").

use std::collections::{HashMap, HashSet};

use prove_num::Rational;

use crate::core::ast::{
    AstManager, Decl, Expr, FAMILY_BASIC, FAMILY_USER, KIND_APP, KIND_QUANTIFIER, KIND_VAR, OP_ADD,
    OP_AND, OP_EQ, OP_GE, OP_ITE, OP_LE, OP_NOT, OP_OR, QuantifierData, SORT_BOOL, Sort,
};
use crate::core::proto_model::{FuncInterp, ProtoModelRef};
use crate::core::quantifier_analyzer::QuantifierInfo;
use crate::core::rewriter::Rewriter;
use crate::core::rewriter_tpl::MAX_RECURSION_DEPTH;
use crate::core::var_subst::replace_free_vars;
use crate::util::error::SmtError;
use crate::util::ordered_map::{OrderedMap, OrderedSet};

/// cond_macro: f(x_0, ..., x_n) = def whenever cond holds. A hint has no condition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CondMacro {
    pub decl: Decl,
    pub def: Expr,
    pub cond: Option<Expr>,
    pub is_ineq: bool,
    pub is_satisfy_atom: bool,
    pub is_hint: bool,
    pub weight: i32,
}

/// The quantifier infos, by quantifier: the TypeScript's `getInfo`.
pub type Infos = HashMap<Expr, QuantifierInfo>;

fn get_info(infos: &Infos, quantifier: Expr) -> Result<&QuantifierInfo, SmtError> {
    infos
        .get(&quantifier)
        .ok_or_else(|| SmtError::Invariant("the quantifier has no info".into()))
}

fn get_info_mut(infos: &mut Infos, quantifier: Expr) -> Result<&mut QuantifierInfo, SmtError> {
    infos
        .get_mut(&quantifier)
        .ok_or_else(|| SmtError::Invariant("the quantifier has no info".into()))
}

fn too_deep() -> SmtError {
    SmtError::Unsupported("the macro solver nests too deeply".into())
}

fn is_user_app(m: &AstManager, expr: Expr) -> bool {
    m.kinds[expr as usize] == KIND_APP
        && m.func_decls[m.decls[expr as usize] as usize].family == FAMILY_USER
}

fn is_atom(m: &AstManager, expr: Expr) -> bool {
    if m.kinds[expr as usize] == KIND_QUANTIFIER || m.sorts[expr as usize] != SORT_BOOL {
        return false;
    }
    if m.kinds[expr as usize] == KIND_VAR
        || m.func_decls[m.decls[expr as usize] as usize].family != FAMILY_BASIC
    {
        return true;
    }
    (m.get_op(expr) == OP_EQ && !m.is_bool(m.get_arg(expr, 0)))
        || m.is_true(expr)
        || m.is_false(expr)
}

fn is_literal(m: &AstManager, expr: Expr) -> bool {
    is_atom(m, expr) || (m.is_not(expr) && is_atom(m, m.get_arg(expr, 0)))
}

fn get_poly_args(m: &AstManager, expr: Expr) -> Vec<Expr> {
    if m.get_op(expr) == OP_ADD {
        m.get_args(expr)
    } else {
        vec![expr]
    }
}

fn is_macro_head(m: &AstManager, expr: Expr, num_decls: usize) -> bool {
    if !is_user_app(m, expr) || m.get_num_args(expr) != num_decls {
        return false;
    }
    // Only looked up, never iterated.
    let mut seen = HashSet::new();
    for arg_index in 0..m.get_num_args(expr) {
        let arg = m.get_arg(expr, arg_index);
        if m.kinds[arg as usize] != KIND_VAR {
            return false;
        }
        let index = m.values[arg as usize];
        if index as usize >= num_decls || !seen.insert(index) {
            return false;
        }
    }
    true
}

fn is_quasi_macro_head(m: &AstManager, expr: Expr, num_decls: usize) -> bool {
    if !is_user_app(m, expr) || m.get_num_args(expr) < num_decls {
        return false;
    }
    // Only looked up and counted, never iterated.
    let mut found = HashSet::new();
    for arg_index in 0..m.get_num_args(expr) {
        let arg = m.get_arg(expr, arg_index);
        if m.kinds[arg as usize] == KIND_VAR {
            let index = m.values[arg as usize];
            if index as usize >= num_decls {
                return false;
            }
            found.insert(index);
        } else if m.is_occurring(m.decls[expr as usize], arg) {
            return false;
        }
    }
    found.len() == num_decls
}

fn get_hint_head_vars(m: &AstManager, expr: Expr) -> Vec<Expr> {
    let mut vars = Vec::new();
    if !is_user_app(m, expr) {
        return vars;
    }
    for index in 0..m.get_num_args(expr) {
        let arg = m.get_arg(expr, index);
        if m.kinds[arg as usize] == KIND_VAR {
            vars.push(arg);
        }
    }
    vars
}

fn is_vars_of_subset(m: &AstManager, expr: Expr, vars: &[Expr]) -> Result<bool, SmtError> {
    // Only looked up, never iterated.
    let mut visited = HashSet::new();
    visit_vars_of_subset(m, expr, vars, &mut visited, 0)
}

fn visit_vars_of_subset(
    m: &AstManager,
    current: Expr,
    vars: &[Expr],
    visited: &mut HashSet<Expr>,
    depth: usize,
) -> Result<bool, SmtError> {
    if m.is_ground(current) || visited.contains(&current) {
        return Ok(true);
    }
    if depth >= MAX_RECURSION_DEPTH {
        return Err(too_deep());
    }
    visited.insert(current);
    let kind = m.kinds[current as usize];
    if kind == KIND_VAR {
        return Ok(vars.contains(&current));
    }
    if kind == KIND_QUANTIFIER {
        return Ok(false);
    }
    for index in 0..m.get_num_args(current) {
        if !visit_vars_of_subset(m, m.get_arg(current, index), vars, visited, depth + 1)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn is_hint_atom(m: &AstManager, lhs: Expr, rhs: Expr) -> Result<bool, SmtError> {
    let vars = get_hint_head_vars(m, lhs);
    Ok(!vars.is_empty()
        && !m.is_occurring(m.decls[lhs as usize], rhs)
        && is_vars_of_subset(m, rhs, &vars)?)
}

fn is_poly_hint(
    m: &AstManager,
    poly: Expr,
    head: Expr,
    exception: Option<Expr>,
) -> Result<bool, SmtError> {
    let vars = get_hint_head_vars(m, head);
    if vars.is_empty() {
        return Ok(false);
    }
    let decl = m.decls[head as usize];
    for arg in get_poly_args(m, poly) {
        if Some(arg) == exception {
            continue;
        }
        if m.is_occurring(decl, arg) || !is_vars_of_subset(m, arg, &vars)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// quantifier_macro_info::collect_macro_candidates, with an empty forbidden set. Each candidate
/// holds a reference to its definition and condition, which `release_cond_macros` releases. Like
/// macro_util, the expressions of each step live until the step returns. The rewriter does
/// macro_util's Boolean and arithmetic rewriting, which keeps nothing between calls.
pub fn collect_macro_candidates(
    m: &mut AstManager,
    rewriter: &mut Rewriter,
    quantifier: Expr,
) -> Result<Vec<CondMacro>, SmtError> {
    let data = m.get_quantifier(quantifier)?.clone();
    // qa: an existential quantifier becomes a universal one of the negated body until the
    // candidates are collected.
    let qa = if data.is_forall {
        quantifier
    } else {
        m.with_temporaries(|m| {
            let body = m.mk_not(data.body)?;
            m.mk_quantifier(QuantifierData {
                is_forall: true,
                body,
                ..data.clone()
            })
        })?
    };
    let qa_body = m.get_quantifier(qa)?.body;
    let candidates = if m.has_quantifier_flags[qa_body as usize] != 0 {
        Vec::new()
    } else {
        collect_candidates(m, rewriter, qa)?
    };
    if qa != quantifier {
        m.dec_ref(qa)?;
    }
    Ok(candidates)
}

/// ~cond_macro, for each candidate in order.
pub fn release_cond_macros(m: &mut AstManager, candidates: &[CondMacro]) -> Result<(), SmtError> {
    for candidate in candidates {
        if let Some(cond) = candidate.cond {
            m.dec_ref(cond)?;
        }
        m.dec_ref(candidate.def)?;
    }
    Ok(())
}

/// The state of macro_util::collect_macro_candidates on one quantifier.
struct Collector<'a> {
    rewriter: &'a mut Rewriter,
    clause: Option<Vec<Expr>>,
    candidates: Vec<CondMacro>,
    weight: i32,
}

// macro_util::collect_macro_candidates.
fn collect_candidates(
    m: &mut AstManager,
    rewriter: &mut Rewriter,
    quantifier: Expr,
) -> Result<Vec<CondMacro>, SmtError> {
    let data = m.get_quantifier(quantifier)?;
    let body = data.body;
    let weight = data.weight;
    let num_decls = data.sorts.len();
    let is_clause = is_literal(m, body)
        || (m.get_op(body) == OP_OR && m.every_arg(body, |arg, _| is_literal(m, arg)));
    let clause = if is_clause {
        Some(if m.get_op(body) == OP_OR {
            m.get_args(body)
        } else {
            vec![body]
        })
    } else {
        None
    };
    let mut collector = Collector {
        rewriter,
        clause: clause.clone(),
        candidates: Vec::new(),
        weight,
    };
    for literal in clause.unwrap_or_else(|| vec![body]) {
        collector.scope(m, |collector, m| {
            collector.collect_core(m, literal, num_decls)
        })?;
    }
    Ok(collector.candidates)
}

impl Collector<'_> {
    // The expressions of a step without a reference live until the step returns.
    fn scope(
        &mut self,
        m: &mut AstManager,
        step: impl FnOnce(&mut Self, &mut AstManager) -> Result<(), SmtError>,
    ) -> Result<(), SmtError> {
        m.with_temporaries_keeping(|m| step(self, m), |_| Vec::new())
    }

    fn mk_not(&mut self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        self.rewriter.mk_app_core(m, OP_NOT, &[expr], SORT_BOOL)
    }

    fn mk_and(&mut self, m: &mut AstManager, args: &[Expr]) -> Result<Expr, SmtError> {
        match args {
            [] => Ok(m.true_expr),
            [arg] => Ok(*arg),
            _ => self.rewriter.mk_app_core(m, OP_AND, args, SORT_BOOL),
        }
    }

    fn mk_sub(&mut self, m: &mut AstManager, first: Expr, second: Expr) -> Result<Expr, SmtError> {
        self.rewriter.mk_sub(m, first, second)
    }

    fn mk_add(m: &mut AstManager, args: &[Expr], sort: Sort) -> Result<Expr, SmtError> {
        match args {
            [] => Ok(m.mk_numeral_of_sort(&Rational::zero(), sort)),
            [arg] => Ok(*arg),
            _ => m.mk_app(OP_ADD, args, sort),
        }
    }

    fn is_rest_containing_decl(&self, m: &AstManager, decl: Decl, except_literal: Expr) -> bool {
        self.clause.as_ref().is_some_and(|clause| {
            clause
                .iter()
                .any(|literal| *literal != except_literal && m.is_occurring(decl, *literal))
        })
    }

    // get_rest_clause_as_cond: the condition comes with a reference, which the caller releases.
    fn get_rest_clause_as_cond(
        &mut self,
        m: &mut AstManager,
        except_literal: Expr,
    ) -> Result<Option<Expr>, SmtError> {
        let Some(clause) = self.clause.clone() else {
            return Ok(None);
        };
        m.with_temporaries_keeping(
            |m| {
                let mut negated = Vec::new();
                for literal in clause {
                    if literal != except_literal {
                        negated.push(self.mk_not(m, literal)?);
                    }
                }
                if negated.is_empty() {
                    Ok(None)
                } else {
                    self.mk_and(m, &negated).map(Some)
                }
            },
            |cond| cond.iter().copied().collect(),
        )
    }

    // A step with the rest of the clause as its condition, which it holds until it returns.
    fn with_rest_clause_as_cond(
        &mut self,
        m: &mut AstManager,
        except_literal: Expr,
        step: impl FnOnce(&mut Self, &mut AstManager, Option<Expr>) -> Result<(), SmtError>,
    ) -> Result<(), SmtError> {
        let cond = self.get_rest_clause_as_cond(m, except_literal)?;
        step(self, m, cond)?;
        if let Some(cond) = cond {
            m.dec_ref(cond)?;
        }
        Ok(())
    }

    // normalize_expr: the variables of the head become (:var 0) ... (:var n-1) in order.
    fn normalize(m: &mut AstManager, head: Expr, expr: Expr) -> Result<Expr, SmtError> {
        let mut mapping: OrderedMap<i32, i32> = OrderedMap::new();
        for index in 0..m.get_num_args(head) {
            mapping.insert(m.values[m.get_arg(head, index) as usize], index as i32);
        }
        if mapping.iter().all(|(from, to)| from == to) {
            return Ok(expr);
        }
        replace_free_vars(m, expr, |m, variable, index, shift| {
            Ok(match mapping.get(&index) {
                None => variable,
                Some(target) => m.mk_var(target + shift, m.sorts[variable as usize]),
            })
        })
    }

    // insert_macro: the candidate holds references to the normalized definition and condition.
    fn insert_macro(
        &mut self,
        m: &mut AstManager,
        head: Expr,
        def: Expr,
        cond: Option<Expr>,
        is_ineq: bool,
        is_hint: bool,
    ) -> Result<(), SmtError> {
        self.scope(m, |collector, m| {
            let norm_def = Collector::normalize(m, head, def)?;
            let norm_cond = match cond {
                Some(cond) => Some(Collector::normalize(m, head, cond)?),
                None if is_hint => None,
                None => Some(m.true_expr),
            };
            m.inc_ref(norm_def);
            if let Some(norm_cond) = norm_cond {
                m.inc_ref(norm_cond);
            }
            collector.candidates.push(CondMacro {
                decl: m.decls[head as usize],
                def: norm_def,
                cond: norm_cond,
                is_ineq,
                is_satisfy_atom: true,
                is_hint,
                weight: collector.weight,
            });
            Ok(())
        })
    }

    // insert_quasi_macro: a head whose arguments are not distinct variables gets fresh
    // variables, and for a macro the equalities between them and the arguments join the
    // condition. new_head, extra_cond and new_cond hold references until it returns, and are
    // released in the reverse order of their declarations.
    #[allow(clippy::too_many_arguments)]
    fn insert_quasi_macro(
        &mut self,
        m: &mut AstManager,
        head: Expr,
        num_decls: usize,
        def: Expr,
        cond: Option<Expr>,
        is_ineq: bool,
        is_hint: bool,
    ) -> Result<(), SmtError> {
        if is_macro_head(m, head, m.get_num_args(head)) {
            return self.insert_macro(m, head, def, cond, is_ineq, is_hint);
        }
        // quasi_macro_head_to_macro_head and hint_to_macro_head: the condition comes before the
        // head.
        let (extra_cond, new_head) = m.with_temporaries_keeping(
            |m| {
                // Only looked up, never iterated.
                let mut seen = HashSet::new();
                let mut new_args = Vec::new();
                let mut new_conds = Vec::new();
                let mut next_var_index = num_decls as i32;
                for index in 0..m.get_num_args(head) {
                    let arg = m.get_arg(head, index);
                    if m.kinds[arg as usize] == KIND_VAR && !seen.contains(&m.values[arg as usize])
                    {
                        seen.insert(m.values[arg as usize]);
                        new_args.push(arg);
                        continue;
                    }
                    let new_var = m.mk_var(next_var_index, m.sorts[arg as usize]);
                    next_var_index += 1;
                    new_args.push(new_var);
                    if !is_hint {
                        new_conds.push(m.mk_eq(new_var, arg)?);
                    }
                }
                let extra_cond = if is_hint {
                    None
                } else {
                    Some(self.mk_and(m, &new_conds)?)
                };
                let new_head =
                    m.mk_app(m.decls[head as usize], &new_args, m.sorts[head as usize])?;
                Ok((extra_cond, new_head))
            },
            |result| match result.0 {
                None => vec![result.1],
                Some(extra_cond) => vec![extra_cond, result.1],
            },
        )?;
        let new_cond = match (extra_cond, cond) {
            (None, _) => None,
            (Some(extra_cond), None) => Some(extra_cond),
            (Some(extra_cond), Some(cond)) => {
                Some(m.with_temporaries(|m| self.mk_and(m, &[cond, extra_cond]))?)
            }
        };
        if let Some(extra_cond) = extra_cond
            && new_cond == Some(extra_cond)
        {
            m.inc_ref(extra_cond);
        }
        self.insert_macro(m, new_head, def, new_cond, is_ineq, is_hint)?;
        if let Some(new_cond) = new_cond {
            m.dec_ref(new_cond)?;
        }
        if let Some(extra_cond) = extra_cond {
            m.dec_ref(extra_cond)?;
        }
        m.dec_ref(new_head)
    }

    fn collect_arith(
        &mut self,
        m: &mut AstManager,
        lhs: Expr,
        rhs: Expr,
        atom: Expr,
        num_decls: usize,
        is_ineq: bool,
    ) -> Result<(), SmtError> {
        if m.get_op(lhs) != OP_ADD && m.get_op(atom) == OP_EQ {
            return Ok(());
        }
        let lhs_args = get_poly_args(m, lhs);
        let arith = Arith {
            lhs,
            rhs,
            atom,
            lhs_args: &lhs_args,
            num_decls,
            is_ineq,
        };
        for arg in &lhs_args {
            if m.kinds[*arg as usize] != KIND_APP {
                continue;
            }
            if self.try_head(m, &arith, *arg, *arg, false)? {
                continue;
            }
            if let Some(negated) = m.get_times_minus_one_arg(*arg)
                && m.kinds[negated as usize] == KIND_APP
            {
                self.try_head(m, &arith, negated, *arg, true)?;
            }
        }
        Ok(())
    }

    fn try_head(
        &mut self,
        m: &mut AstManager,
        arith: &Arith,
        head: Expr,
        monomial: Expr,
        is_negated: bool,
    ) -> Result<bool, SmtError> {
        let decl = m.decls[head as usize];
        let is_arith_macro = is_quasi_macro_head(m, head, arith.num_decls)
            && !arith
                .lhs_args
                .iter()
                .any(|arg| *arg != monomial && m.is_occurring(decl, *arg))
            && !m.is_occurring(decl, arith.rhs)
            && !self.is_rest_containing_decl(m, decl, arith.atom);
        let is_hint = !is_arith_macro && is_poly_hint(m, arith.lhs, head, Some(monomial))?;
        if !is_arith_macro && !is_hint {
            return Ok(false);
        }
        self.scope(m, |collector, m| {
            let rest_args: Vec<Expr> = arith
                .lhs_args
                .iter()
                .copied()
                .filter(|arg| *arg != monomial)
                .collect();
            let rest = Collector::mk_add(m, &rest_args, m.sorts[arith.lhs as usize])?;
            let def = if is_negated {
                collector.mk_sub(m, rest, arith.rhs)?
            } else {
                collector.mk_sub(m, arith.rhs, rest)?
            };
            // A hint's right-hand side may contain variables that are not arguments of the head.
            if is_hint && !is_poly_hint(m, def, head, None)? {
                return Ok(());
            }
            // add_arith_macro_candidate.
            if is_hint {
                return collector.insert_quasi_macro(
                    m,
                    head,
                    arith.num_decls,
                    def,
                    None,
                    arith.is_ineq,
                    true,
                );
            }
            collector.with_rest_clause_as_cond(m, arith.atom, |collector, m, cond| {
                collector.insert_quasi_macro(
                    m,
                    head,
                    arith.num_decls,
                    def,
                    cond,
                    arith.is_ineq,
                    false,
                )
            })
        })?;
        Ok(true)
    }

    fn insert_quasi(
        &mut self,
        m: &mut AstManager,
        atom: Expr,
        num_decls: usize,
        lhs: Expr,
        rhs: Expr,
    ) -> Result<bool, SmtError> {
        if !is_quasi_macro_head(m, lhs, num_decls)
            || m.is_occurring(m.decls[lhs as usize], rhs)
            || self.is_rest_containing_decl(m, m.decls[lhs as usize], atom)
        {
            return Ok(false);
        }
        self.with_rest_clause_as_cond(m, atom, |collector, m, cond| {
            collector.insert_quasi_macro(m, lhs, num_decls, rhs, cond, false, false)
        })?;
        Ok(true)
    }

    fn insert_hint(
        &mut self,
        m: &mut AstManager,
        num_decls: usize,
        lhs: Expr,
        rhs: Expr,
    ) -> Result<(), SmtError> {
        if is_hint_atom(m, lhs, rhs)? {
            self.insert_quasi_macro(m, lhs, num_decls, rhs, None, false, true)?;
        }
        Ok(())
    }

    fn collect_core(
        &mut self,
        m: &mut AstManager,
        atom: Expr,
        num_decls: usize,
    ) -> Result<(), SmtError> {
        let op = m.get_op(atom);
        if op == OP_EQ {
            let lhs = m.get_arg(atom, 0);
            let rhs = m.get_arg(atom, 1);
            if !self.insert_quasi(m, atom, num_decls, lhs, rhs)? {
                self.insert_hint(m, num_decls, lhs, rhs)?;
            }
            if !self.insert_quasi(m, atom, num_decls, rhs, lhs)? {
                self.insert_hint(m, num_decls, rhs, lhs)?;
            }
        }
        if op == OP_NOT {
            let inner = m.get_arg(atom, 0);
            if m.get_op(inner) == OP_EQ && m.is_bool(m.get_arg(inner, 0)) {
                self.scope(m, |collector, m| {
                    let lhs = m.get_arg(inner, 0);
                    let rhs = m.get_arg(inner, 1);
                    let negated_lhs = m.mk_not(lhs)?;
                    let negated_rhs = m.mk_not(rhs)?;
                    if !collector.insert_quasi(m, atom, num_decls, lhs, negated_rhs)? {
                        collector.insert_hint(m, num_decls, lhs, negated_rhs)?;
                    }
                    if !collector.insert_quasi(m, atom, num_decls, rhs, negated_lhs)? {
                        collector.insert_hint(m, num_decls, rhs, negated_lhs)?;
                    }
                    Ok(())
                })?;
            }
        }
        if op == OP_EQ || op == OP_LE || op == OP_GE {
            let lhs = m.get_arg(atom, 0);
            let rhs = m.get_arg(atom, 1);
            self.collect_arith(m, lhs, rhs, atom, num_decls, op != OP_EQ)?;
            self.collect_arith(m, rhs, lhs, atom, num_decls, op != OP_EQ)?;
        }
        Ok(())
    }
}

/// What collect_arith's tryHead closes over.
struct Arith<'a> {
    lhs: Expr,
    rhs: Expr,
    atom: Expr,
    lhs_args: &'a [Expr],
    num_decls: usize,
    is_ineq: bool,
}

fn set_else_interp(
    m: &mut AstManager,
    model: &ProtoModelRef,
    decl: Decl,
    else_expr: Expr,
) -> Result<(), SmtError> {
    let mut model = model.borrow_mut();
    if model.get_func_interp(m, decl).is_none() {
        let arity = m.func_decls[decl as usize].domain.len();
        model.register_func(m, decl, FuncInterp::new(arity))?;
    }
    match model.get_func_interp_mut(m, decl) {
        Some(interp) => interp.set_else(m, else_expr),
        None => Ok(()),
    }
}

/// The three solvers that base_macro_solver::operator() runs.
#[derive(Clone, Copy)]
enum MacroSolver {
    Simple,
    Hint,
    NonAuf,
}

/// What the solvers share: the TypeScript closures' captures.
struct Solve<'a> {
    model: &'a ProtoModelRef,
    infos: &'a mut Infos,
    // func_decl_dependencies of the non-AUF solver, kept across its rounds.
    dependencies: HashMap<Decl, OrderedSet<Decl>>,
    force_template: i32,
}

// base_macro_solver::operator(): runs the solver until it removes no more quantifiers, and leaves
// in qs the quantifiers of its last round.
fn run_macro_solver(
    m: &mut AstManager,
    solve: &mut Solve,
    solver: MacroSolver,
    qs: Vec<Expr>,
    residue: &mut Vec<Expr>,
) -> Result<Vec<Expr>, SmtError> {
    let mut current = qs;
    let mut next = Vec::new();
    loop {
        let is_removed = match solver {
            MacroSolver::Simple => simple_macro_solver(m, solve, &current, &mut next)?,
            MacroSolver::Hint => hint_macro_solver(m, solve, &current, &mut next)?,
            MacroSolver::NonAuf => non_auf_macro_solver(m, solve, &current, &mut next, residue)?,
        };
        if !is_removed {
            return Ok(next);
        }
        current = std::mem::take(&mut next);
    }
}

// simple_macro_solver: a macro for f satisfies its quantifier when no other quantifier uses f.
fn simple_macro_solver(
    m: &mut AstManager,
    solve: &mut Solve,
    qs: &[Expr],
    new_qs: &mut Vec<Expr>,
) -> Result<bool, SmtError> {
    let mut is_removed = false;
    for quantifier in qs {
        let info = get_info(solve.infos, *quantifier)?;
        let mut found = None;
        for candidate in &info.cond_macros {
            if !candidate.is_satisfy_atom {
                continue;
            }
            let mut is_used = false;
            for other in qs {
                if other != quantifier
                    && get_info(solve.infos, *other)?
                        .ng_decls
                        .contains(&candidate.decl)
                {
                    is_used = true;
                    break;
                }
            }
            if !is_used {
                found = Some(*candidate);
                break;
            }
        }
        let Some(found) = found else {
            new_qs.push(*quantifier);
            continue;
        };
        // The conditions of the macro can be ignored: the partial interpretation of f satisfies
        // the ground part, and MBQI adds instances when it does not satisfy the quantifier.
        get_info_mut(solve.infos, *quantifier)?.the_one = Some(found.decl);
        set_else_interp(m, solve.model, found.decl, found.def)?;
        is_removed = true;
    }
    Ok(is_removed)
}

const GREEDY_MAX_DEPTH: usize = 10;

/// The state of hint_macro_solver's greedy search.
struct HintSearch<'a> {
    infos: &'a mut Infos,
    // Only looked up, never iterated.
    forbidden: HashSet<Decl>,
    q_f: OrderedMap<Decl, OrderedSet<Expr>>,
    q_f_def: OrderedMap<Decl, OrderedMap<Expr, OrderedSet<Expr>>>,
    satisfied: OrderedSet<Expr>,
    residue: OrderedSet<Expr>,
    fs: OrderedMap<Decl, Expr>,
}

impl HintSearch<'_> {
    fn is_cyclic(&self, m: &AstManager) -> Result<bool, SmtError> {
        // Only looked up and counted, never iterated.
        let mut acyclic = HashSet::new();
        loop {
            let size = acyclic.len();
            if size == self.fs.len() {
                return Ok(false);
            }
            for (decl, def) in self.fs.iter() {
                if !acyclic.contains(decl) && self.is_acyclic(m, &acyclic, *def)? {
                    acyclic.insert(*decl);
                }
            }
            if size == acyclic.len() {
                return Ok(true);
            }
        }
    }

    fn is_acyclic(
        &self,
        m: &AstManager,
        acyclic: &HashSet<Decl>,
        def: Expr,
    ) -> Result<bool, SmtError> {
        // Only looked up, never iterated.
        let mut visited = HashSet::new();
        self.visit_acyclic(m, acyclic, &mut visited, def, 0)
    }

    fn visit_acyclic(
        &self,
        m: &AstManager,
        acyclic: &HashSet<Decl>,
        visited: &mut HashSet<Expr>,
        current: Expr,
        depth: usize,
    ) -> Result<bool, SmtError> {
        if !visited.insert(current) {
            return Ok(true);
        }
        if depth >= MAX_RECURSION_DEPTH {
            return Err(too_deep());
        }
        let kind = m.kinds[current as usize];
        if kind == KIND_VAR {
            return Ok(true);
        }
        if kind == KIND_QUANTIFIER {
            let body = m.get_quantifier(current)?.body;
            return self.visit_acyclic(m, acyclic, visited, body, depth + 1);
        }
        let decl = m.decls[current as usize];
        if self.fs.contains_key(&decl) && !acyclic.contains(&decl) {
            return Ok(false);
        }
        for index in 0..m.get_num_args(current) {
            if !self.visit_acyclic(m, acyclic, visited, m.get_arg(current, index), depth + 1)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn greedy(&mut self, m: &AstManager, depth: usize) -> Result<bool, SmtError> {
        if self.residue.is_empty() {
            return Ok(!self.is_cyclic(m)?);
        }
        let mut candidates = OrderedSet::new();
        for quantifier in self.residue.iter() {
            for macro_ in &get_info(self.infos, *quantifier)?.cond_macros {
                if macro_.is_satisfy_atom
                    && !self.forbidden.contains(&macro_.decl)
                    && !self.fs.contains_key(&macro_.decl)
                {
                    candidates.insert(macro_.decl);
                }
            }
        }
        for decl in candidates.iter() {
            if self.greedy_on(m, *decl, depth)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn greedy_on(&mut self, m: &AstManager, decl: Decl, depth: usize) -> Result<bool, SmtError> {
        if depth >= GREEDY_MAX_DEPTH {
            return Ok(false);
        }
        let defs: Vec<(Expr, Vec<Expr>)> = self.q_f_def.get(&decl).map_or_else(Vec::new, |defs| {
            defs.iter()
                .map(|(def, qs)| (*def, qs.iter().copied().collect()))
                .collect()
        });
        for (def, qs) in defs {
            let saved_satisfied: Vec<Expr> = self.satisfied.iter().copied().collect();
            let saved_residue: Vec<Expr> = self.residue.iter().copied().collect();
            self.fs.insert(decl, def);
            // update_satisfied_residue.
            let mut is_useful = false;
            for quantifier in qs {
                if self.satisfied.contains(&quantifier) {
                    continue;
                }
                is_useful = true;
                self.residue.remove(&quantifier);
                self.satisfied.insert(quantifier);
                get_info_mut(self.infos, quantifier)?.the_one = Some(decl);
            }
            if is_useful {
                let users: Vec<Expr> = self
                    .q_f
                    .get(&decl)
                    .map_or_else(Vec::new, |qs| qs.iter().copied().collect());
                for quantifier in users {
                    if !self.satisfied.contains(&quantifier) {
                        self.residue.insert(quantifier);
                    }
                }
                if self.greedy(m, depth + 1)? {
                    return Ok(true);
                }
            }
            let satisfied: Vec<Expr> = self.satisfied.iter().copied().collect();
            for quantifier in satisfied {
                if !saved_satisfied.contains(&quantifier) {
                    get_info_mut(self.infos, quantifier)?.the_one = None;
                }
            }
            self.satisfied.clear();
            for quantifier in saved_satisfied {
                self.satisfied.insert(quantifier);
            }
            self.residue.clear();
            for quantifier in saved_residue {
                self.residue.insert(quantifier);
            }
            self.fs.remove(&decl);
        }
        Ok(false)
    }
}

// hint_macro_solver: searches greedily for a set of hints and macros, one per function symbol,
// that satisfies a set of quantifiers without cyclic definitions.
fn hint_macro_solver(
    m: &mut AstManager,
    solve: &mut Solve,
    qs: &[Expr],
    new_qs: &mut Vec<Expr>,
) -> Result<bool, SmtError> {
    let mut forbidden: HashSet<Decl> = HashSet::new();
    let mut current = qs.to_vec();
    let mut qcandidates: Vec<Expr> = Vec::new();
    loop {
        for quantifier in &current {
            let info = get_info(solve.infos, *quantifier)?;
            let is_candidate = info
                .cond_macros
                .iter()
                .any(|macro_| macro_.is_satisfy_atom && !forbidden.contains(&macro_.decl));
            if is_candidate {
                qcandidates.push(*quantifier);
            } else {
                for decl in info.ng_decls.iter() {
                    forbidden.insert(*decl);
                }
                new_qs.push(*quantifier);
            }
        }
        if current.len() == qcandidates.len() {
            break;
        }
        current = std::mem::take(&mut qcandidates);
    }
    if qcandidates.is_empty() {
        return Ok(false);
    }
    let mut q_f: OrderedMap<Decl, OrderedSet<Expr>> = OrderedMap::new();
    let mut q_f_def: OrderedMap<Decl, OrderedMap<Expr, OrderedSet<Expr>>> = OrderedMap::new();
    let mut candidate_decls = OrderedSet::new();
    for quantifier in &qcandidates {
        let info = get_info(solve.infos, *quantifier)?;
        for decl in info.ng_decls.iter() {
            if forbidden.contains(decl) {
                continue;
            }
            q_f.get_or_insert_with(*decl, OrderedSet::new)
                .insert(*quantifier);
        }
        for macro_ in &info.cond_macros {
            if !macro_.is_satisfy_atom || forbidden.contains(&macro_.decl) {
                continue;
            }
            q_f_def
                .get_or_insert_with(macro_.decl, OrderedMap::new)
                .get_or_insert_with(macro_.def, OrderedSet::new)
                .insert(*quantifier);
            candidate_decls.insert(macro_.decl);
        }
    }
    let mut search = HintSearch {
        infos: solve.infos,
        forbidden,
        q_f,
        q_f_def,
        satisfied: OrderedSet::new(),
        residue: OrderedSet::new(),
        fs: OrderedMap::new(),
    };
    for decl in candidate_decls.iter() {
        if !search.greedy_on(m, *decl, 0)? {
            continue;
        }
        let fs: Vec<(Decl, Expr)> = search.fs.iter().map(|(decl, def)| (*decl, *def)).collect();
        for (decl, def) in fs {
            set_else_interp(m, solve.model, decl, def)?;
        }
        for quantifier in &qcandidates {
            if !search.satisfied.contains(quantifier) {
                new_qs.push(*quantifier);
            }
        }
        return Ok(true);
    }
    new_qs.extend(qcandidates);
    Ok(false)
}

// collect_func_decls with ng_only: the uninterpreted functions applied in non-ground terms.
fn collect_ng_func_decls(m: &AstManager, expr: Expr) -> Result<OrderedSet<Decl>, SmtError> {
    let mut decls = OrderedSet::new();
    // Only looked up, never iterated.
    let mut visited = HashSet::new();
    visit_ng_func_decls(m, expr, &mut decls, &mut visited, 0)?;
    Ok(decls)
}

fn visit_ng_func_decls(
    m: &AstManager,
    current: Expr,
    decls: &mut OrderedSet<Decl>,
    visited: &mut HashSet<Expr>,
    depth: usize,
) -> Result<(), SmtError> {
    if !visited.insert(current) {
        return Ok(());
    }
    if depth >= MAX_RECURSION_DEPTH {
        return Err(too_deep());
    }
    let kind = m.kinds[current as usize];
    if kind == KIND_VAR || kind == KIND_QUANTIFIER {
        return Ok(());
    }
    for index in 0..m.get_num_args(current) {
        visit_ng_func_decls(m, m.get_arg(current, index), decls, visited, depth + 1)?;
    }
    if m.get_num_args(current) > 0 && !m.is_ground(current) && is_user_app(m, current) {
        decls.insert(m.decls[current as usize]);
    }
    Ok(())
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Color {
    Progress,
    Closed,
}

fn is_cycle(
    dependencies: &HashMap<Decl, OrderedSet<Decl>>,
    colors: &mut HashMap<Decl, Color>,
    current: Decl,
    depth: usize,
) -> Result<bool, SmtError> {
    match colors.get(&current) {
        Some(Color::Closed) => return Ok(false),
        Some(Color::Progress) => return Ok(true),
        None => {}
    }
    if depth >= MAX_RECURSION_DEPTH {
        return Err(too_deep());
    }
    colors.insert(current, Color::Progress);
    if let Some(children) = dependencies.get(&current) {
        for child in children.iter() {
            if is_cycle(dependencies, colors, *child, depth + 1)? {
                return Ok(true);
            }
        }
    }
    colors.insert(current, Color::Closed);
    Ok(false)
}

// func_decl_dependencies::insert: fails when f has a definition or the new one is cyclic.
fn add_macro(
    m: &mut AstManager,
    solve: &mut Solve,
    decl: Decl,
    else_expr: Expr,
) -> Result<bool, SmtError> {
    if solve.dependencies.contains_key(&decl) {
        return Ok(false);
    }
    let decls = collect_ng_func_decls(m, else_expr)?;
    solve.dependencies.insert(decl, decls);
    // Only looked up, never iterated.
    let mut colors = HashMap::new();
    if is_cycle(&solve.dependencies, &mut colors, decl, 0)? {
        solve.dependencies.remove(&decl);
        return Ok(false);
    }
    set_else_interp(m, solve.model, decl, else_expr)?;
    Ok(true)
}

fn is_better_macro(m: &AstManager, first: &CondMacro, second: Option<&CondMacro>) -> bool {
    let Some(second) = second else {
        return true;
    };
    if !first.is_hint {
        return true;
    }
    if !second.is_hint {
        return false;
    }
    m.is_ground(first.def) && !m.is_ground(second.def)
}

fn get_macro_for(
    m: &AstManager,
    infos: &Infos,
    decl: Decl,
    quantifier: Expr,
) -> Result<Option<CondMacro>, SmtError> {
    let mut result: Option<CondMacro> = None;
    for macro_ in &get_info(infos, quantifier)?.cond_macros {
        if macro_.decl == decl && !macro_.is_hint && is_better_macro(m, macro_, result.as_ref()) {
            result = Some(*macro_);
        }
    }
    Ok(result)
}

fn is_unconditional(m: &AstManager, macro_: &CondMacro) -> bool {
    macro_.cond.is_none_or(|cond| m.is_true(cond))
}

// non_auf_macro_solver: satisfies quantifiers outside the AUF fragment with their macros, even
// when other quantifiers use the defined symbol.
fn non_auf_macro_solver(
    m: &mut AstManager,
    solve: &mut Solve,
    qs: &[Expr],
    new_qs: &mut Vec<Expr>,
    residue: &mut Vec<Expr>,
) -> Result<bool, SmtError> {
    let mut full_macros: OrderedMap<Decl, (CondMacro, Expr)> = OrderedMap::new();
    let mut cond_macros: OrderedSet<Decl> = OrderedSet::new();
    for quantifier in qs {
        let info = get_info(solve.infos, *quantifier)?;
        for macro_ in &info.cond_macros {
            if macro_.is_hint {
                continue;
            }
            if is_unconditional(m, macro_)
                && (!info.is_auf || macro_.weight >= solve.force_template)
            {
                full_macros.insert(macro_.decl, (*macro_, *quantifier));
                cond_macros.remove(&macro_.decl);
            } else if !full_macros.contains_key(&macro_.decl) && !info.is_auf {
                cond_macros.insert(macro_.decl);
            }
        }
    }
    // Only looked up and counted, never iterated.
    let mut removed = HashSet::new();
    let full: Vec<(Decl, CondMacro, Expr)> = full_macros
        .iter()
        .map(|(decl, (macro_, quantifier))| (*decl, *macro_, *quantifier))
        .collect();
    for (decl, macro_, quantifier) in full {
        if add_macro(m, solve, decl, macro_.def)? {
            get_info_mut(solve.infos, quantifier)?.the_one = Some(decl);
            removed.insert(quantifier);
        }
    }
    let conditional: Vec<Decl> = cond_macros.iter().copied().collect();
    for decl in conditional {
        let mut else_expr: Option<Expr> = None;
        let mut to_remove = Vec::new();
        let mut is_full_macro = false;
        for quantifier in qs {
            if removed.contains(quantifier) {
                continue;
            }
            let Some(macro_) = get_macro_for(m, solve.infos, decl, *quantifier)? else {
                continue;
            };
            if is_unconditional(m, &macro_) {
                is_full_macro = true;
                break;
            }
            to_remove.push(*quantifier);
            else_expr = Some(match else_expr {
                None => macro_.def,
                Some(else_expr) => {
                    let sort = m.sorts[else_expr as usize];
                    m.mk_app(
                        OP_ITE,
                        &[macro_.cond.unwrap_or(m.true_expr), macro_.def, else_expr],
                        sort,
                    )?
                }
            });
        }
        let Some(else_expr) = else_expr else {
            continue;
        };
        if is_full_macro || !add_macro(m, solve, decl, else_expr)? {
            continue;
        }
        for quantifier in to_remove {
            get_info_mut(solve.infos, quantifier)?.the_one = Some(decl);
            removed.insert(quantifier);
        }
    }
    for quantifier in qs {
        if removed.contains(quantifier) {
            continue;
        }
        new_qs.push(*quantifier);
        residue.push(*quantifier);
    }
    Ok(!removed.is_empty())
}

/// The macro part of model_finder::fix_model: returns the quantifiers left for the AUF solver.
pub fn solve_macros(
    m: &mut AstManager,
    model: &ProtoModelRef,
    qs: Vec<Expr>,
    infos: &mut Infos,
    force_template: i32,
) -> Result<Vec<Expr>, SmtError> {
    let mut residue = Vec::new();
    let mut solve = Solve {
        model,
        infos,
        dependencies: HashMap::new(),
        force_template,
    };
    let after_simple = run_macro_solver(m, &mut solve, MacroSolver::Simple, qs, &mut residue)?;
    let after_hint =
        run_macro_solver(m, &mut solve, MacroSolver::Hint, after_simple, &mut residue)?;
    let mut result =
        run_macro_solver(m, &mut solve, MacroSolver::NonAuf, after_hint, &mut residue)?;
    result.extend(residue);
    Ok(result)
}

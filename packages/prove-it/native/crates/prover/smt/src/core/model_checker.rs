//! Ported from Z3 (src/smt/smt_model_checker.cpp), MIT license, through `model-checker.ts`.
//! Checks whether the candidate model satisfies each relevant quantifier: the negated body, with
//! the model's interpretations in place of the uninterpreted symbols, goes to an auxiliary context.
//! A model of it is a counterexample that becomes an instance of the quantifier.
//!
//! # Design
//!
//! - `ModelChecker` keeps the context, its model finder and its quantifier manager, so
//!   (design/smt-core.md, "The context") its state is a struct held by the quantifier manager with
//!   the finder. The `impl Context` methods `model_checker_<method>` move both out of the context
//!   while they run, as `model_finder.rs` does, and pass the context and the finder in.
//! - The auxiliary context shares the main context's `AstManager` in the TypeScript, so the ids,
//!   reference counts, fresh names and steps of both interleave in one manager. In Rust a
//!   `Context` owns its manager (`m`), so the auxiliary context owns a placeholder manager, made
//!   once with it and never used, and each of its operations swaps the main manager in for the
//!   operation and back out after (`AuxContext::with_manager`, `std::mem::swap` of the two
//!   `AstManager` values, which moves no expression). Every operation of the auxiliary context
//!   therefore runs on the one manager at the same point as in the TypeScript, which keeps its
//!   ids and steps. The models that the auxiliary context returns hold no manager, so the checker
//!   reads them with the main manager.
//! - The `root2value` that `check` gets is passed down to where the TypeScript reads its field.

use std::collections::HashMap;
use std::mem;

use prove_decide::Limits;

use crate::core::asserted_formulas::AssertedFormulas;
use crate::core::ast::{AstManager, Expr, KIND_APP, OP_NOT, OP_OR, SORT_BOOL, SmtSymbol};
use crate::core::context::{Context, SmtParams};
use crate::core::enode::EnodeId;
use crate::core::model_finder::ModelFinder;
use crate::core::proto_model::ProtoModelRef;
use crate::core::ref_vector::RefVector;
use crate::core::rewriter_tpl::MAX_RECURSION_DEPTH;
use crate::core::var_subst::VarSubst;
use crate::util::error::SmtError;
use crate::util::lbool::LBool;
use crate::util::ordered_map::OrderedMap;
use crate::util::rlimit::ResourceLimit;

// qi_params' mbqi_max_cexs and mbqi_max_iterations.
const MBQI_MAX_CEXS: u32 = 1;
const MBQI_MAX_ITERATIONS: u32 = 1000;

/// An instance whose bindings start at offset in m_pinned_exprs.
#[derive(Clone, Copy, Debug)]
struct Instance {
    quantifier: Expr,
    offset: usize,
    generation: u32,
}

/// What a check of the auxiliary context found: a model of the assertions, or that they are
/// unsatisfiable or undecided.
enum AuxResult {
    Sat(ProtoModelRef),
    Unsat,
    Unknown,
}

/// The auxiliary context: Z3 keeps one context for every check and pushes a scope per check, so
/// the restricted checks continue from the complete check, with its phases and activities. It runs
/// without MBQI and with relevancy level 0, and preprocesses the assertions of a check together.
/// Its manager is a placeholder between its operations (module header).
pub struct AuxContext {
    context: Context,
    asserted: AssertedFormulas,
    // theory_polymorphism's m_qhead: the number of formulas when it last added an assumption. Its
    // trail restores it when the scope is popped, and no formula is asserted outside the scopes.
    poly_qhead: usize,
    // theory_polymorphism's m_assumption, which holds its last assumption.
    poly_assumption: Expr,
}

impl AuxContext {
    /// The context makes its asserted formulas first. Its theories hold only constants that exist
    /// by now, so setup_context can run at once. init_aux_context copies the kernel's smt_params,
    /// so the context has a model finder too, though it never sees a quantifier.
    fn new(m: &mut AstManager) -> Result<AuxContext, SmtError> {
        let asserted = AssertedFormulas::new(m);
        let placeholder =
            AstManager::new(ResourceLimit::new(&Limits::new(f64::INFINITY, None, None)));
        // The context takes the manager while it is made; a failure here ends the decision.
        let manager = mem::replace(m, placeholder);
        let context = Context::new(
            manager,
            SmtParams {
                is_mbqi: true,
                relevancy_level: 0,
            },
        )?;
        let mut aux = AuxContext {
            context,
            asserted,
            poly_qhead: 0,
            poly_assumption: -1,
        };
        mem::swap(m, &mut aux.context.m);
        aux.with_manager(m, |aux| aux.context.setup_context())?;
        Ok(aux)
    }

    /// Runs body with the main manager in the auxiliary context, and takes it back after.
    fn with_manager<T>(
        &mut self,
        m: &mut AstManager,
        body: impl FnOnce(&mut AuxContext) -> Result<T, SmtError>,
    ) -> Result<T, SmtError> {
        mem::swap(m, &mut self.context.m);
        let result = body(self);
        mem::swap(m, &mut self.context.m);
        result
    }

    fn push(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.with_manager(m, |aux| {
            aux.context.push()?;
            aux.asserted.push();
            Ok(())
        })
    }

    fn pop(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.with_manager(m, |aux| {
            aux.context.pop(1)?;
            aux.asserted.pop(&mut aux.context.m)?;
            aux.poly_qhead = 0;
            Ok(())
        })
    }

    /// assert_expr_core: outside the search, the scopes of the last search are popped first.
    fn assert(&mut self, m: &mut AstManager, formula: Expr) -> Result<(), SmtError> {
        self.with_manager(m, |aux| {
            aux.context.pop_to_base_level()?;
            aux.asserted.assert_expr(&mut aux.context.m, formula)
        })
    }

    /// A model of the assertions, or whether they are unsatisfiable or undecided. Z3 registers
    /// theory_polymorphism, which assumes a fresh constant whenever formulas were asserted since
    /// its last assumption.
    fn check(&mut self, m: &mut AstManager) -> Result<AuxResult, SmtError> {
        self.with_manager(m, |aux| {
            let context = &mut aux.context;
            context.pop_to_base_level()?;
            context.internalize_assertions(&mut aux.asserted)?;
            let num_formulas = aux.asserted.get_num_formulas();
            let is_assuming = num_formulas != aux.poly_qhead;
            aux.poly_qhead = num_formulas;
            if is_assuming {
                let assumption = context
                    .m
                    .mk_fresh_const(Some(&SmtSymbol::Name("poly".into())), SORT_BOOL)?;
                context.m.inc_ref(assumption);
                if aux.poly_assumption != -1 {
                    context.m.dec_ref(aux.poly_assumption)?;
                }
                aux.poly_assumption = assumption;
            }
            let assumptions = if is_assuming {
                vec![aux.poly_assumption]
            } else {
                Vec::new()
            };
            context.init_assumptions(&assumptions)?;
            Ok(match context.search()? {
                LBool::True => AuxResult::Sat(context.get_model()?),
                LBool::False => AuxResult::Unsat,
                LBool::Undef => AuxResult::Unknown,
            })
        })
    }
}

#[derive(Default)]
pub struct ModelChecker {
    max_cexs: u32,
    iteration_index: u32,
    new_instances: Vec<Instance>,
    // m_pinned_exprs: the bindings and quantifier of each new instance, held until they are
    // asserted.
    pinned_exprs: RefVector,
    // Only looked up, never iterated.
    value2expr: Option<HashMap<Expr, Expr>>,
    fresh_exprs: Vec<Expr>,
    aux: Option<Box<AuxContext>>,
}

impl ModelChecker {
    /// `new ModelChecker(context, finder, qmanager)`.
    pub fn new(_m: &mut AstManager) -> ModelChecker {
        ModelChecker {
            max_cexs: MBQI_MAX_CEXS,
            ..ModelChecker::default()
        }
    }

    pub fn init_search_eh(&mut self) {
        self.max_cexs = MBQI_MAX_CEXS;
        self.iteration_index = 0;
    }

    pub fn has_new_instances(&self) -> bool {
        !self.new_instances.is_empty()
    }

    fn get_value2expr(
        &mut self,
        context: &Context,
        root2value: &OrderedMap<EnodeId, Expr>,
    ) -> &HashMap<Expr, Expr> {
        self.value2expr.get_or_insert_with(|| {
            let mut value2expr = HashMap::new();
            for (root, value) in root2value.iter() {
                let node = ModelChecker::get_eq_enode_with_min_gen(context, *root);
                let owner = context.node(node).owner;
                if !context.m.is_unique_value(owner) {
                    value2expr.insert(*value, owner);
                }
            }
            value2expr
        })
    }

    // enode::get_eq_enode_with_min_gen: the first node of the class with generation 0, or else
    // the first with the least generation.
    fn get_eq_enode_with_min_gen(context: &Context, root: EnodeId) -> EnodeId {
        let mut result = root;
        let mut result_generation = context.get_generation(root);
        let mut current = root;
        loop {
            let generation = context.get_generation(current);
            if generation == 0 {
                return current;
            }
            if generation < result_generation {
                result = current;
                result_generation = generation;
            }
            current = context.node(current).next;
            if current == root {
                return result;
            }
        }
    }

    // get_type_compatible_term: a term of the context that stands for a value, which may be a
    // fresh constant.
    fn get_type_compatible_term(
        &mut self,
        context: &mut Context,
        root2value: &OrderedMap<EnodeId, Expr>,
        value: Expr,
        depth: usize,
    ) -> Result<Expr, SmtError> {
        if depth >= MAX_RECURSION_DEPTH {
            return Err(SmtError::Unsupported(
                "the model checker's value nests too deeply".into(),
            ));
        }
        let fresh_term = if context.m.kinds[value as usize] == KIND_APP
            && context.m.get_num_args(value) > 0
        {
            let mut args = Vec::with_capacity(context.m.get_num_args(value));
            for index in 0..context.m.get_num_args(value) {
                let arg = context.m.get_arg(value, index);
                args.push(self.get_type_compatible_term(context, root2value, arg, depth + 1)?);
            }
            let decl = context.m.decls[value as usize];
            let sort = context.m.sorts[value as usize];
            context.m.mk_app(decl, &args, sort)?
        } else {
            if let Some(term) = self.get_value2expr(context, root2value).get(&value) {
                return Ok(*term);
            }
            let sort = context.m.sorts[value as usize];
            if let Some(existing) = self
                .fresh_exprs
                .iter()
                .find(|fresh| context.m.sorts[**fresh as usize] == sort)
            {
                return Ok(*existing);
            }
            context
                .m
                .mk_fresh_const(Some(&SmtSymbol::Name("sk".into())), sort)?
        };
        self.fresh_exprs.push(fresh_term);
        if !context.is_e_internalized(fresh_term) {
            context.internalize(fresh_term, false)?;
        }
        Ok(fresh_term)
    }

    // assert_neg_q_m: asserts the negated body under the model, with fresh constants for the
    // variables, which sks holds.
    fn assert_neg_q_m(
        m: &mut AstManager,
        aux: &mut AuxContext,
        quantifier: Expr,
        model: &ProtoModelRef,
        sks: &mut RefVector,
    ) -> Result<(), SmtError> {
        let data = m.get_quantifier(quantifier)?.clone();
        let body = model.borrow_mut().eval(m, data.body, true)?;
        let num_decls = data.sorts.len();
        sks.resize(m, num_decls)?;
        for index in 0..num_decls {
            let sort = data.sorts[num_decls - index - 1];
            let sk = m.mk_fresh_const(None, sort)?;
            sks.set(m, num_decls - index - 1, sk)?;
            if model.borrow().is_finite(m, sort) {
                // restrict_to_universe: ast_manager::mk_or, which keeps a single disjunct in an
                // or.
                let universe_values = model.borrow().get_known_universe(sort);
                let mut universe = Vec::with_capacity(universe_values.len());
                for value in universe_values {
                    universe.push(m.mk_eq(sk, value)?);
                }
                let constraint = m.mk_app(OP_OR, &universe, SORT_BOOL)?;
                m.inc_ref(constraint);
                aux.assert(m, constraint)?;
                m.dec_ref(constraint)?;
            }
        }
        let mut subst = VarSubst::new(m, true);
        let sk_body = subst.apply(m, body, &sks.items)?;
        // m.mk_not, which makes (not true) of a true body too.
        let negated = m.mk_app(OP_NOT, &[sk_body], SORT_BOOL)?;
        m.inc_ref(negated);
        aux.assert(m, negated)?;
        m.dec_ref(negated)?;
        m.dec_ref(sk_body)?;
        subst.release(m)?;
        m.dec_ref(body)
    }

    #[allow(clippy::too_many_arguments)]
    fn add_instance(
        &mut self,
        context: &mut Context,
        finder: &mut ModelFinder,
        root2value: &OrderedMap<EnodeId, Expr>,
        quantifier: Expr,
        cex: &ProtoModelRef,
        sks: &[Expr],
        is_using_inv: bool,
    ) -> Result<bool, SmtError> {
        if sks.is_empty() {
            return Ok(false);
        }
        let num_decls = context.m.get_quantifier(quantifier)?.sorts.len();
        let mut bindings = vec![-1; num_decls];
        let mut max_generation = 0;
        for index in 0..num_decls {
            let sk = sks[num_decls - index - 1];
            let decl = context.m.decls[sk as usize];
            let mut sk_value = cex.borrow_mut().get_some_const_interp(&mut context.m, decl);
            if is_using_inv {
                let Some((term, generation)) =
                    finder.get_inv(context, quantifier, index as u32, sk_value, cex)?
                else {
                    return Ok(false);
                };
                max_generation = max_generation.max(generation);
                sk_value = term;
            } else if let Some(term) = self.get_value2expr(context, root2value).get(&sk_value) {
                sk_value = *term;
            }
            if context.m.contains_model_value(sk_value) {
                sk_value = self.get_type_compatible_term(context, root2value, sk_value, 0)?;
            }
            bindings[num_decls - index - 1] = sk_value;
        }
        let offset = self.pinned_exprs.len();
        for binding in bindings {
            self.pinned_exprs.push(&mut context.m, binding);
        }
        self.pinned_exprs.push(&mut context.m, quantifier);
        self.new_instances.push(Instance {
            quantifier,
            offset,
            generation: context
                .qmanager
                .get_generation(quantifier)
                .max(max_generation),
        });
        Ok(true)
    }

    // check(q): whether the model satisfies the quantifier. A counterexample becomes an instance.
    fn check_quantifier(
        &mut self,
        context: &mut Context,
        finder: &mut ModelFinder,
        root2value: &OrderedMap<EnodeId, Expr>,
        quantifier: Expr,
        model: &ProtoModelRef,
    ) -> Result<bool, SmtError> {
        let mut aux = match self.aux.take() {
            Some(aux) => aux,
            None => Box::new(AuxContext::new(&mut context.m)?),
        };
        aux.push(&mut context.m)?;
        // sks: the fresh constants of the variables, which are released before the scope is
        // popped.
        let mut sks = RefVector::new();
        let result = self.check_in_scope(
            context, finder, root2value, &mut aux, quantifier, model, &mut sks,
        );
        let result = result.and_then(|is_satisfied| {
            sks.reset(&mut context.m)?;
            aux.pop(&mut context.m)?;
            Ok(is_satisfied)
        });
        self.aux = Some(aux);
        result
    }

    #[allow(clippy::too_many_arguments)]
    fn check_in_scope(
        &mut self,
        context: &mut Context,
        finder: &mut ModelFinder,
        root2value: &OrderedMap<EnodeId, Expr>,
        aux: &mut AuxContext,
        quantifier: Expr,
        model: &ProtoModelRef,
        sk_refs: &mut RefVector,
    ) -> Result<bool, SmtError> {
        let flat_q = finder.get_flat_quantifier(&mut context.m, quantifier)?;
        ModelChecker::assert_neg_q_m(&mut context.m, aux, flat_q, model, sk_refs)?;
        let sks = sk_refs.items.clone();
        let complete_cex = match aux.check(&mut context.m)? {
            AuxResult::Unsat => return Ok(true),
            AuxResult::Unknown => return Ok(false),
            AuxResult::Sat(model) => model,
        };
        // complete_cex and cex hold their models.
        complete_cex.borrow_mut().inc_ref();
        // Try to find instances from the instantiation sets first.
        finder.restrict_sks_to_inst_set(context, quantifier, &sks, &mut |m, expr| {
            aux.assert(m, expr)
        })?;
        let mut num_new_instances = 0;
        while let AuxResult::Sat(cex) = aux.check(&mut context.m)? {
            cex.borrow_mut().inc_ref();
            let is_added =
                self.add_instance(context, finder, root2value, quantifier, &cex, &sks, true)?;
            if is_added {
                num_new_instances += 1;
            }
            if is_added && num_new_instances < self.max_cexs {
                ModelChecker::add_blocking_clause(&mut context.m, aux, &cex, &sks)?;
            }
            cex.borrow_mut().dec_ref(&mut context.m)?;
            if !is_added || num_new_instances >= self.max_cexs {
                break;
            }
        }
        if num_new_instances == 0 {
            self.add_instance(
                context,
                finder,
                root2value,
                quantifier,
                &complete_cex,
                &sks,
                false,
            )?;
        }
        complete_cex.borrow_mut().dec_ref(&mut context.m)?;
        Ok(false)
    }

    // add_blocking_clause: diseqs and blocking_clause hold their terms until it is asserted.
    fn add_blocking_clause(
        m: &mut AstManager,
        aux: &mut AuxContext,
        cex: &ProtoModelRef,
        sks: &[Expr],
    ) -> Result<(), SmtError> {
        let mut diseqs = RefVector::new();
        for sk in sks {
            let decl = m.decls[*sk as usize];
            let value = cex.borrow_mut().get_some_const_interp(m, decl);
            let eq = m.mk_eq(*sk, value)?;
            let diseq = m.mk_not(eq)?;
            diseqs.push(m, diseq);
        }
        let blocking_clause = m.mk_app(OP_OR, &diseqs.items, SORT_BOOL)?;
        m.inc_ref(blocking_clause);
        aux.assert(m, blocking_clause)?;
        m.dec_ref(blocking_clause)?;
        diseqs.reset(m)
    }

    // Whether a relevant quantifier was found, and the number of failures.
    fn check_quantifiers(
        &mut self,
        context: &mut Context,
        finder: &mut ModelFinder,
        root2value: &OrderedMap<EnodeId, Expr>,
        model: &ProtoModelRef,
    ) -> Result<(bool, u32), SmtError> {
        let mut is_found_relevant = false;
        let mut num_failures = 0;
        let quantifiers = context.qmanager.quantifiers.clone();
        for quantifier in quantifiers {
            // Z3's resource limit cancels the checks, and the search gives up.
            if context.check_canceled() {
                return Ok((is_found_relevant, num_failures + 1));
            }
            if !context.is_relevant(quantifier)
                || context.get_assignment(context.get_literal(quantifier)?) != LBool::True
            {
                continue;
            }
            is_found_relevant = true;
            if !self.check_quantifier(context, finder, root2value, quantifier, model)? {
                num_failures += 1;
            }
        }
        Ok((is_found_relevant, num_failures))
    }

    /// check(md, root2value): whether the model satisfies every relevant quantifier.
    pub fn check(
        &mut self,
        context: &mut Context,
        finder: &mut ModelFinder,
        model: &ProtoModelRef,
        root2value: &OrderedMap<EnodeId, Expr>,
    ) -> Result<bool, SmtError> {
        if context.qmanager.quantifiers.is_empty() {
            return Ok(true);
        }
        if self.iteration_index >= MBQI_MAX_ITERATIONS {
            return Ok(false);
        }
        self.value2expr = None;
        model.borrow_mut().compress(&mut context.m)?;
        let (is_found_relevant, first_failures) =
            self.check_quantifiers(context, finder, root2value, model)?;
        if is_found_relevant {
            self.iteration_index += 1;
        }
        self.max_cexs += MBQI_MAX_CEXS;
        let mut num_failures = first_failures;
        if num_failures == 0 && !context.validate_model(model)? {
            num_failures = 1 + self
                .check_quantifiers(context, finder, root2value, model)?
                .1;
        }
        if num_failures == 0 {
            model.borrow_mut().cleanup(&mut context.m)?;
        }
        Ok(num_failures == 0)
    }

    /// restart_eh: assert_new_instances.
    pub fn restart_eh(&mut self, context: &mut Context) -> Result<(), SmtError> {
        for instance in mem::take(&mut self.new_instances) {
            if !context.is_b_internalized(instance.quantifier) {
                continue;
            }
            let num_decls = context.m.get_quantifier(instance.quantifier)?.sorts.len();
            let bindings =
                self.pinned_exprs.items[instance.offset..instance.offset + num_decls].to_vec();
            let mut nodes = Vec::with_capacity(num_decls);
            for binding in bindings {
                if !context.is_e_internalized(binding) {
                    context.internalize_with_generation(binding, false, instance.generation)?;
                }
                let node = context.get_enode(binding).ok_or_else(|| {
                    SmtError::Invariant("the binding was not internalized".into())
                })?;
                nodes.push(node);
            }
            context.qmanager_add_instance(instance.quantifier, &nodes, instance.generation)?;
        }
        // reset_new_instances.
        self.pinned_exprs.reset(&mut context.m)
    }
}

impl Context {
    /// check(md, root2value): whether the model satisfies every relevant quantifier.
    pub fn model_checker_check(
        &mut self,
        model: &ProtoModelRef,
        root2value: &OrderedMap<EnodeId, Expr>,
    ) -> Result<bool, SmtError> {
        let Some(mut mbqi) = self.qmanager.mbqi.take() else {
            return Ok(true);
        };
        let result = mbqi
            .checker
            .check(self, &mut mbqi.finder, model, root2value);
        self.qmanager.mbqi = Some(mbqi);
        result
    }

    /// restart_eh: assert_new_instances.
    pub fn model_checker_restart_eh(&mut self) -> Result<(), SmtError> {
        let Some(mut mbqi) = self.qmanager.mbqi.take() else {
            return Ok(());
        };
        let result = mbqi.checker.restart_eh(self);
        self.qmanager.mbqi = Some(mbqi);
        result
    }
}

#[cfg(test)]
mod tests {
    //! Quantified EUF problems without patterns, which only model-based instantiation decides,
    //! against the table `scripts/smt-mbqi-reference.ts` prints for the TypeScript kernel with
    //! MBQI on the same expressions, made in the same order (`tests/tables/mbqi.txt`): the result,
    //! the conflicts, the steps, the instances and the number of ASTs, and the model of a
    //! satisfiable problem, with the arithmetic theory of every context, the model checker's
    //! auxiliary contexts included.

    use prove_decide::Limits;

    use crate::core::ast::{AstManager, Decl, Expr, QuantifierData, SORT_BOOL, SmtSymbol, Sort};
    use crate::core::context::{Context, SmtParams};
    use crate::core::proto_model::tests::print_model;
    use crate::util::lbool::LBool;
    use crate::util::rlimit::ResourceLimit;

    const TABLE: &str = include_str!("../../tests/tables/mbqi.txt");

    fn get_section(name: &str) -> Vec<&'static str> {
        let header = format!("== {name} ==");
        TABLE
            .lines()
            .skip_while(|line| *line != header)
            .skip(1)
            .take_while(|line| !line.starts_with("== "))
            .collect()
    }

    struct Problem {
        context: Context,
        u: Sort,
    }

    impl Problem {
        fn new() -> Problem {
            let limits = Limits::new(f64::INFINITY, None, None);
            let m = AstManager::new(ResourceLimit::new(&limits));
            let mut context = Context::new(
                m,
                SmtParams {
                    is_mbqi: true,
                    relevancy_level: 2,
                },
            )
            .unwrap();
            context.setup_context().unwrap();
            let u = context.m.mk_sort("U");
            Problem { context, u }
        }

        fn func(&mut self, name: &str, domain: &[Sort], range: Sort) -> Decl {
            self.context
                .m
                .mk_func_decl(SmtSymbol::Name(name.into()), domain, range, false)
        }

        fn app(&mut self, decl: Decl, args: &[Expr], sort: Sort) -> Expr {
            self.context.m.mk_app(decl, args, sort).unwrap()
        }

        fn constant(&mut self, name: &str) -> Expr {
            let decl = self.func(name, &[], self.u);
            self.app(decl, &[], self.u)
        }

        fn var(&mut self, index: i32) -> Expr {
            self.context.m.mk_var(index, self.u)
        }

        fn not(&mut self, expr: Expr) -> Expr {
            self.context.m.mk_not(expr).unwrap()
        }

        fn or(&mut self, args: &[Expr]) -> Expr {
            self.context.m.mk_or(args).unwrap()
        }

        fn eq(&mut self, lhs: Expr, rhs: Expr) -> Expr {
            self.context.m.mk_eq(lhs, rhs).unwrap()
        }

        fn neq(&mut self, lhs: Expr, rhs: Expr) -> Expr {
            let eq = self.eq(lhs, rhs);
            self.not(eq)
        }

        fn forall(&mut self, num_vars: usize, body: Expr) -> Expr {
            self.context
                .m
                .mk_quantifier(QuantifierData {
                    is_forall: true,
                    sorts: vec![self.u; num_vars],
                    names: (0..num_vars)
                        .map(|index| SmtSymbol::Name(format!("x{index}")))
                        .collect(),
                    body,
                    patterns: Vec::new(),
                    weight: 0,
                    qid: String::new(),
                })
                .unwrap()
        }

        fn assert(&mut self, expr: Expr) {
            self.context.internalize_assertion(expr, 0).unwrap();
        }

        // report.
        fn report(mut self, name: &str) {
            let mut out = Vec::new();
            let result = self.context.search().unwrap();
            let m = &self.context.m;
            out.push(format!(
                "result={} conflicts={} steps={} instances={} asts={}",
                result as i32,
                self.context.get_num_conflicts(),
                m.limit.count(),
                self.context.qmanager.get_num_instances(),
                m.get_num_asts()
            ));
            if result == LBool::True {
                let model = self.context.get_model().unwrap();
                let m = &self.context.m;
                print_model(&mut out, m, &model.borrow(), &[self.u]);
                out.push(format!(
                    "modeled: steps={} asts={}",
                    m.limit.count(),
                    m.get_num_asts()
                ));
            }
            let expected = get_section(name);
            assert!(!expected.is_empty(), "no section {name}");
            for (index, (actual, expected)) in out.iter().zip(&expected).enumerate() {
                assert_eq!(actual, expected, "{name}, line {}", index + 1);
            }
            assert_eq!(out.len(), expected.len(), "{name}: the number of lines");
        }
    }

    #[test]
    fn finds_a_model_of_a_disequality() {
        // ∀x. f(x) ≠ a, f(b) = c, b ≠ c.
        let mut problem = Problem::new();
        let u = problem.u;
        let f = problem.func("f", &[u], u);
        let x = problem.var(0);
        let a = problem.constant("a");
        let b = problem.constant("b");
        let c = problem.constant("c");
        let fx = problem.app(f, &[x], u);
        let body = problem.neq(fx, a);
        let q = problem.forall(1, body);
        problem.assert(q);
        let fb = problem.app(f, &[b], u);
        let eq = problem.eq(fb, c);
        problem.assert(eq);
        let neq = problem.neq(b, c);
        problem.assert(neq);
        problem.report("diseq-sat");
    }

    fn mk_or_problem(is_sat: bool) -> Problem {
        // ∀x. p(x) ∨ q(x), ¬p(a), and ¬q(b) or ¬q(a).
        let mut problem = Problem::new();
        let u = problem.u;
        let p = problem.func("p", &[u], SORT_BOOL);
        let qd = problem.func("q", &[u], SORT_BOOL);
        let x = problem.var(0);
        let a = problem.constant("a");
        let b = if is_sat { problem.constant("b") } else { a };
        let px = problem.app(p, &[x], SORT_BOOL);
        let qx = problem.app(qd, &[x], SORT_BOOL);
        let body = problem.or(&[px, qx]);
        let q = problem.forall(1, body);
        problem.assert(q);
        let pa = problem.app(p, &[a], SORT_BOOL);
        let not = problem.not(pa);
        problem.assert(not);
        let qb = problem.app(qd, &[b], SORT_BOOL);
        let not = problem.not(qb);
        problem.assert(not);
        problem
    }

    #[test]
    fn completes_a_disjunction_with_projections() {
        mk_or_problem(true).report("or-sat");
    }

    #[test]
    fn refutes_a_disjunction_with_a_model_based_instance() {
        mk_or_problem(false).report("or-unsat");
    }

    #[test]
    fn refutes_a_macro() {
        // ∀x. f(x) = a, f(b) ≠ a.
        let mut problem = Problem::new();
        let u = problem.u;
        let f = problem.func("f", &[u], u);
        let x = problem.var(0);
        let a = problem.constant("a");
        let b = problem.constant("b");
        let fx = problem.app(f, &[x], u);
        let body = problem.eq(fx, a);
        let q = problem.forall(1, body);
        problem.assert(q);
        let fb = problem.app(f, &[b], u);
        let neq = problem.neq(fb, a);
        problem.assert(neq);
        problem.report("macro-unsat");
    }

    #[test]
    fn interprets_a_function_by_a_macro() {
        // ∀x. f(x) = h(x), f(a) = b, h(c) = d, a ≠ c.
        let mut problem = Problem::new();
        let u = problem.u;
        let f = problem.func("f", &[u], u);
        let h = problem.func("h", &[u], u);
        let x = problem.var(0);
        let a = problem.constant("a");
        let b = problem.constant("b");
        let c = problem.constant("c");
        let d = problem.constant("d");
        let fx = problem.app(f, &[x], u);
        let hx = problem.app(h, &[x], u);
        let body = problem.eq(fx, hx);
        let q = problem.forall(1, body);
        problem.assert(q);
        let fa = problem.app(f, &[a], u);
        let eq = problem.eq(fa, b);
        problem.assert(eq);
        let hc = problem.app(h, &[c], u);
        let eq = problem.eq(hc, d);
        problem.assert(eq);
        let neq = problem.neq(a, c);
        problem.assert(neq);
        problem.report("macro-sat");
    }

    fn mk_quasi_macro_problem(is_sat: bool) -> Problem {
        // ∀x. f(x, a) = g(x), and f(b, a) = c and g(c) = b, or f(b, a) ≠ g(b).
        let mut problem = Problem::new();
        let u = problem.u;
        let f = problem.func("f", &[u, u], u);
        let g = problem.func("g", &[u], u);
        let x = problem.var(0);
        let a = problem.constant("a");
        let b = problem.constant("b");
        let c = if is_sat { problem.constant("c") } else { -1 };
        let fxa = problem.app(f, &[x, a], u);
        let gx = problem.app(g, &[x], u);
        let body = problem.eq(fxa, gx);
        let q = problem.forall(1, body);
        problem.assert(q);
        let fba = problem.app(f, &[b, a], u);
        if is_sat {
            let eq = problem.eq(fba, c);
            problem.assert(eq);
            let gc = problem.app(g, &[c], u);
            let eq = problem.eq(gc, b);
            problem.assert(eq);
        } else {
            let gb = problem.app(g, &[b], u);
            let neq = problem.neq(fba, gb);
            problem.assert(neq);
        }
        problem
    }

    #[test]
    fn interprets_a_function_by_a_quasi_macro() {
        mk_quasi_macro_problem(true).report("quasi-macro");
    }

    #[test]
    fn refutes_a_quasi_macro() {
        mk_quasi_macro_problem(false).report("quasi-macro-unsat");
    }

    #[test]
    fn instantiates_over_several_rounds() {
        // ∀x. ¬p(x) ∨ p(s(x)), p(a), ¬p(s(s(s(a)))).
        let mut problem = Problem::new();
        let u = problem.u;
        let p = problem.func("p", &[u], SORT_BOOL);
        let s = problem.func("s", &[u], u);
        let x = problem.var(0);
        let a = problem.constant("a");
        let px = problem.app(p, &[x], SORT_BOOL);
        let not_px = problem.not(px);
        let sx = problem.app(s, &[x], u);
        let psx = problem.app(p, &[sx], SORT_BOOL);
        let body = problem.or(&[not_px, psx]);
        let q = problem.forall(1, body);
        problem.assert(q);
        let pa = problem.app(p, &[a], SORT_BOOL);
        problem.assert(pa);
        let sa = problem.app(s, &[a], u);
        let ssa = problem.app(s, &[sa], u);
        let sssa = problem.app(s, &[ssa], u);
        let psssa = problem.app(p, &[sssa], SORT_BOOL);
        let not = problem.not(psssa);
        problem.assert(not);
        problem.report("rounds");
    }

    fn mk_two_vars_problem(is_sat: bool) -> Problem {
        // ∀x y. x = y ∨ ¬r(x, y), and r(a, b) and a ≠ b, or r(a, a) and r(b, c) ∨ b = c.
        let mut problem = Problem::new();
        let u = problem.u;
        let r = problem.func("r", &[u, u], SORT_BOOL);
        let x = problem.var(1);
        let y = problem.var(0);
        let a = problem.constant("a");
        let b = problem.constant("b");
        let c = if is_sat { problem.constant("c") } else { -1 };
        let xy = problem.eq(x, y);
        let rxy = problem.app(r, &[x, y], SORT_BOOL);
        let not_rxy = problem.not(rxy);
        let body = problem.or(&[xy, not_rxy]);
        let q = problem.forall(2, body);
        problem.assert(q);
        if is_sat {
            let raa = problem.app(r, &[a, a], SORT_BOOL);
            problem.assert(raa);
            let rbc = problem.app(r, &[b, c], SORT_BOOL);
            let bc = problem.eq(b, c);
            let either = problem.or(&[rbc, bc]);
            problem.assert(either);
        } else {
            let rab = problem.app(r, &[a, b], SORT_BOOL);
            problem.assert(rab);
            let neq = problem.neq(a, b);
            problem.assert(neq);
        }
        problem
    }

    #[test]
    fn refutes_a_relation_between_two_variables() {
        mk_two_vars_problem(false).report("two-vars");
    }

    #[test]
    fn finds_a_model_after_refuted_candidates() {
        mk_two_vars_problem(true).report("two-vars-sat");
    }

    #[test]
    fn refutes_injectivity() {
        // ∀x y. f(x) ≠ f(y) ∨ x = y, f(a) = f(b), a ≠ b.
        let mut problem = Problem::new();
        let u = problem.u;
        let f = problem.func("f", &[u], u);
        let x = problem.var(1);
        let y = problem.var(0);
        let a = problem.constant("a");
        let b = problem.constant("b");
        let fx = problem.app(f, &[x], u);
        let fy = problem.app(f, &[y], u);
        let neq = problem.neq(fx, fy);
        let xy = problem.eq(x, y);
        let body = problem.or(&[neq, xy]);
        let q = problem.forall(2, body);
        problem.assert(q);
        let fa = problem.app(f, &[a], u);
        let fb = problem.app(f, &[b], u);
        let eq = problem.eq(fa, fb);
        problem.assert(eq);
        let neq = problem.neq(a, b);
        problem.assert(neq);
        problem.report("injective");
    }

    #[test]
    fn refutes_chained_macros() {
        // ∀x. f(x) = g(x), ∀x. g(x) = a, f(b) = c, c ≠ a.
        let mut problem = Problem::new();
        let u = problem.u;
        let f = problem.func("f", &[u], u);
        let g = problem.func("g", &[u], u);
        let x = problem.var(0);
        let a = problem.constant("a");
        let b = problem.constant("b");
        let c = problem.constant("c");
        let fx = problem.app(f, &[x], u);
        let gx = problem.app(g, &[x], u);
        let body = problem.eq(fx, gx);
        let q = problem.forall(1, body);
        problem.assert(q);
        let gx = problem.app(g, &[x], u);
        let body = problem.eq(gx, a);
        let q = problem.forall(1, body);
        problem.assert(q);
        let fb = problem.app(f, &[b], u);
        let eq = problem.eq(fb, c);
        problem.assert(eq);
        let neq = problem.neq(c, a);
        problem.assert(neq);
        problem.report("chained-macros");
    }

    #[test]
    fn avoids_the_exceptions_of_a_variable() {
        // ∀x. x = a ∨ f(x) = b, f(a) = c, b ≠ c.
        let mut problem = Problem::new();
        let u = problem.u;
        let f = problem.func("f", &[u], u);
        let x = problem.var(0);
        let a = problem.constant("a");
        let b = problem.constant("b");
        let c = problem.constant("c");
        let xa = problem.eq(x, a);
        let fx = problem.app(f, &[x], u);
        let fxb = problem.eq(fx, b);
        let body = problem.or(&[xa, fxb]);
        let q = problem.forall(1, body);
        problem.assert(q);
        let fa = problem.app(f, &[a], u);
        let eq = problem.eq(fa, c);
        problem.assert(eq);
        let neq = problem.neq(b, c);
        problem.assert(neq);
        problem.report("exceptions-sat");
    }
}

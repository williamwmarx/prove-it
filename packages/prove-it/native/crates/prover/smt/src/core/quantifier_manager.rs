//! Ported from Z3 (src/smt/smt_quantifier.cpp), MIT license, see z3-license.txt, through
//! `quantifier-manager.ts`. Z3's default quantifier plugin: patterns go to an eager matcher, except
//! that a quantifier with only multi-patterns keeps one of them eager and sends the rest to a lazy
//! matcher that runs in the final check. With MBQI, the model finder and the model checker turn
//! candidate models into instances.
//!
//! `DefaultQuantifierManager` keeps `private context: Context`, so (design/smt-core.md, "The
//! context") its state is a struct held by the context as `qmanager`, the methods that touch only
//! its own fields stay on it, and the methods that reach the context are `impl Context` methods
//! named `qmanager_<method>`. Its matchers, queue, finder and checker are its fields, reached the
//! same way (`mam_<method>`, `qi_queue_<method>`, `model_finder_<method>`,
//! `model_checker_<method>`).

use std::collections::HashMap;

use crate::core::ast::{AstManager, Expr};
use crate::core::context::{
    CHECK_MODEL_RESTART, CHECK_MODEL_SAT, CHECK_MODEL_UNKNOWN, Context, FC_CONTINUE, FC_DONE,
    TrailClosure,
};
use crate::core::e_matching::{Mam, MamKind};
use crate::core::enode::EnodeId;
use crate::core::fingerprints::FingerprintSet;
use crate::core::model_checker::ModelChecker;
use crate::core::model_finder::ModelFinder;
use crate::core::proto_model::ProtoModelRef;
use crate::core::qi_queue::QiQueue;
use crate::util::error::SmtError;
use crate::util::ordered_map::OrderedMap;

const QI_MAX_EAGER_MULTIPATTERNS: usize = 0;
const QI_MAX_LAZY_MULTIPATTERN_MATCHING: u32 = 2;

/// Model-based quantifier instantiation: the finder completes candidate models, the checker
/// refutes them with instances. The finder's and the checker's methods that reach the context move
/// it out of `mbqi` while they run (`model_finder.rs`).
pub(crate) struct Mbqi {
    pub(crate) finder: ModelFinder,
    pub(crate) checker: ModelChecker,
}

pub struct DefaultQuantifierManager {
    pub quantifiers: Vec<Expr>,
    generations: HashMap<Expr, u32>,
    pub(crate) qi_queue: QiQueue,
    mam: Mam,
    lazy_mam: Mam,
    fingerprints: FingerprintSet,
    is_active: bool,
    /// What the trail closure of `finalCheckEh` restores (`TrailClosure::LazyMatchingIndex`).
    pub lazy_matching_index: u32,
    pub(crate) mbqi: Option<Box<Mbqi>>,
}

impl DefaultQuantifierManager {
    /// `new DefaultQuantifierManager(context, isMbqi)`: its matchers, queue and fingerprints, and
    /// the model finder and checker with MBQI.
    pub fn new(m: &mut AstManager, is_mbqi: bool) -> Self {
        let qi_queue = QiQueue::new(m);
        let mbqi = if is_mbqi {
            let finder = ModelFinder::new(m);
            Some(Box::new(Mbqi {
                finder,
                checker: ModelChecker::new(m),
            }))
        } else {
            None
        };
        DefaultQuantifierManager {
            quantifiers: Vec::new(),
            generations: HashMap::new(),
            qi_queue,
            mam: Mam::new(),
            lazy_mam: Mam::new(),
            fingerprints: FingerprintSet::new(),
            is_active: false,
            lazy_matching_index: 0,
            mbqi,
        }
    }

    pub fn mam(&self, kind: MamKind) -> &Mam {
        match kind {
            MamKind::Eager => &self.mam,
            MamKind::Lazy => &self.lazy_mam,
        }
    }

    pub fn mam_mut(&mut self, kind: MamKind) -> &mut Mam {
        match kind {
            MamKind::Eager => &mut self.mam,
            MamKind::Lazy => &mut self.lazy_mam,
        }
    }

    pub fn get_num_instances(&self) -> u32 {
        self.qi_queue.num_instances
    }

    pub fn del(&mut self, quantifier: Expr) {
        self.quantifiers.pop();
        self.generations.remove(&quantifier);
    }

    pub fn has_quantifiers(&self) -> bool {
        !self.quantifiers.is_empty()
    }

    pub fn get_generation(&self, quantifier: Expr) -> u32 {
        self.generations.get(&quantifier).copied().unwrap_or(0)
    }

    /// is_shared: a ground term of a pattern, once a quantifier was asserted.
    pub fn is_shared(&self, node: EnodeId) -> bool {
        self.is_active && (self.mam.is_shared(node) || self.lazy_mam.is_shared(node))
    }

    pub fn is_model_based(&self) -> bool {
        self.mbqi.is_some()
    }
}

impl Context {
    pub fn qmanager_add(&mut self, quantifier: Expr, generation: u32) -> Result<(), SmtError> {
        self.qmanager.quantifiers.push(quantifier);
        self.qmanager.generations.insert(quantifier, generation);
        if self.qmanager.mbqi.is_some() {
            self.model_finder_register_quantifier(quantifier)?;
        }
        Ok(())
    }

    pub fn qmanager_assign_eh(&mut self, quantifier: Expr) -> Result<(), SmtError> {
        self.qmanager.is_active = true;
        let patterns: Vec<Vec<Expr>> = self
            .m
            .get_quantifier(quantifier)?
            .patterns
            .iter()
            .map(|pattern| self.m.get_args(*pattern))
            .collect();
        let has_unary_pattern = patterns.iter().any(|pattern| pattern.len() == 1);
        let num_eager_multi_patterns =
            QI_MAX_EAGER_MULTIPATTERNS + if has_unary_pattern { 0 } else { 1 };
        let mut multi_pattern_index = 0;
        for pattern in &patterns {
            let is_unary = pattern.len() == 1;
            if !is_unary && multi_pattern_index >= num_eager_multi_patterns {
                self.mam_add_pattern(MamKind::Lazy, quantifier, pattern)?;
            } else {
                self.mam_add_pattern(MamKind::Eager, quantifier, pattern)?;
            }
            if !is_unary {
                multi_pattern_index += 1;
            }
        }
        Ok(())
    }

    pub fn qmanager_add_eq_eh(&mut self, first: EnodeId, second: EnodeId) -> Result<(), SmtError> {
        if !self.qmanager.quantifiers.is_empty() {
            self.mam_add_eq_eh(MamKind::Eager, first, second);
        }
        Ok(())
    }

    pub fn qmanager_relevant_eh(&mut self, node: EnodeId) -> Result<(), SmtError> {
        if self.qmanager.quantifiers.is_empty() {
            return Ok(());
        }
        self.mam_relevant_eh(MamKind::Eager, node, false);
        self.mam_relevant_eh(MamKind::Lazy, node, true);
        Ok(())
    }

    pub fn qmanager_push(&mut self) -> Result<(), SmtError> {
        let qmanager = &mut self.qmanager;
        qmanager.mam.push_scope();
        qmanager.lazy_mam.push_scope();
        if let Some(mbqi) = qmanager.mbqi.as_mut() {
            mbqi.finder.push_scope();
        }
        qmanager.qi_queue.push();
        qmanager.fingerprints.push();
        Ok(())
    }

    pub fn qmanager_pop(&mut self, num_scopes: u32) -> Result<(), SmtError> {
        self.mam_pop_scope(MamKind::Eager, num_scopes);
        self.mam_pop_scope(MamKind::Lazy, num_scopes);
        if let Some(mbqi) = self.qmanager.mbqi.as_mut() {
            mbqi.finder.pop_scope(&mut self.m, num_scopes)?;
        }
        self.qmanager.qi_queue.pop(&mut self.m, num_scopes)?;
        self.qmanager.fingerprints.pop(num_scopes);
        Ok(())
    }

    pub fn qmanager_can_propagate(&self) -> bool {
        self.qmanager.qi_queue.has_work()
            || (self.qmanager.is_active && self.qmanager.mam.has_work())
    }

    pub fn qmanager_propagate(&mut self) -> Result<(), SmtError> {
        if self.qmanager.is_active {
            self.mam_match(MamKind::Eager)?;
        }
        self.qi_queue_instantiate()
    }

    /// add_instance: the matchers' onMatch.
    pub fn qmanager_add_instance(
        &mut self,
        quantifier: Expr,
        bindings: &[EnodeId],
        max_generation: u32,
    ) -> Result<(), SmtError> {
        let qmanager = &mut self.qmanager;
        let generation = max_generation.max(qmanager.get_generation(quantifier));
        let roots = qmanager
            .fingerprints
            .insert(&self.m, &self.enode_arena, quantifier, bindings);
        if let Some(roots) = roots {
            qmanager
                .qi_queue
                .insert(&self.m, quantifier, roots, generation)?;
        }
        Ok(())
    }

    /// An `FC_*` status.
    pub fn qmanager_final_check_eh(&mut self, is_full: bool) -> Result<u8, SmtError> {
        if !is_full {
            return Ok(FC_DONE);
        }
        let mut result = if self.qi_queue_final_check_eh()? {
            FC_DONE
        } else {
            FC_CONTINUE
        };
        if !self.qmanager.quantifiers.is_empty()
            && self.qmanager.lazy_matching_index < QI_MAX_LAZY_MULTIPATTERN_MATCHING
        {
            self.mam_rematch(MamKind::Lazy)?;
            let saved = self.qmanager.lazy_matching_index;
            self.push_trail(TrailClosure::LazyMatchingIndex { saved });
            self.qmanager.lazy_matching_index += 1;
        }
        if self.can_propagate() {
            result = FC_CONTINUE;
        }
        Ok(result)
    }

    pub fn qmanager_init_search_eh(&mut self) -> Result<(), SmtError> {
        self.qmanager.lazy_matching_index = 0;
        if let Some(mbqi) = self.qmanager.mbqi.as_mut() {
            mbqi.checker.init_search_eh();
        }
        self.qmanager.qi_queue.init_search_eh(&mut self.m)
    }

    pub fn qmanager_restart_eh(&mut self) -> Result<(), SmtError> {
        if self.qmanager.mbqi.is_some() {
            self.model_finder_restart_eh()?;
            self.model_checker_restart_eh()?;
        }
        Ok(())
    }

    /// adjust_model: the finder fixes the model with MBQI.
    pub fn qmanager_adjust_model(&mut self, model: &ProtoModelRef) -> Result<(), SmtError> {
        if self.qmanager.mbqi.is_some() {
            self.model_finder_fix_model(model)?;
        }
        Ok(())
    }

    /// check_model: a `CHECK_MODEL_*` status.
    pub fn qmanager_check_model(
        &mut self,
        model: &ProtoModelRef,
        root2value: &OrderedMap<EnodeId, Expr>,
    ) -> Result<u8, SmtError> {
        if self.qmanager.quantifiers.is_empty() {
            return Ok(CHECK_MODEL_SAT);
        }
        if self.qmanager.mbqi.is_none() {
            return Ok(CHECK_MODEL_UNKNOWN);
        }
        if self.model_checker_check(model, root2value)? {
            return Ok(CHECK_MODEL_SAT);
        }
        let has_new_instances = self
            .qmanager
            .mbqi
            .as_ref()
            .is_some_and(|mbqi| mbqi.checker.has_new_instances());
        Ok(if has_new_instances {
            CHECK_MODEL_RESTART
        } else {
            CHECK_MODEL_UNKNOWN
        })
    }
}

#[cfg(test)]
mod tests {
    //! Quantified EUF problems that E-matching refutes without MBQI, internalized from hand-built
    //! expressions and searched. The expected results, conflicts, steps and instances are those
    //! `scripts/smt-ematching-reference.ts` prints for the TypeScript kernel on the same
    //! expressions, made in the same order, with MBQI off. The TypeScript theory's `init` makes
    //! four numerals and their enodes, which the stubbed theory does not, so the ids here are
    //! those of the TypeScript less four; the counts do not depend on it. The script's `sat`
    //! problem is not ported: a candidate model goes to the model generator, still a stub.

    use prove_decide::Limits;

    use crate::core::ast::{AstManager, Decl, Expr, QuantifierData, SORT_BOOL, SmtSymbol, Sort};
    use crate::core::context::{Context, SmtParams};
    use crate::util::lbool::LBool;
    use crate::util::rlimit::ResourceLimit;

    /// The steps the TypeScript takes in what is still stubbed here, which the script prints for
    /// each problem: the empty arithmetic theory (two in its first propagation, two in each of its
    /// final checks).
    struct Stubbed {
        theory: u64,
    }

    struct Problem {
        context: Context,
        sort: Sort,
    }

    impl Problem {
        fn new() -> Problem {
            let limits = Limits::new(f64::INFINITY, None, None);
            let m = AstManager::new(ResourceLimit::new(&limits));
            let mut context = Context::new(
                m,
                SmtParams {
                    is_mbqi: false,
                    relevancy_level: 2,
                },
            )
            .unwrap();
            context.setup_context().unwrap();
            let sort = context.m.mk_sort("U");
            Problem { context, sort }
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
            let decl = self.func(name, &[], self.sort);
            self.app(decl, &[], self.sort)
        }

        fn var(&mut self, index: i32) -> Expr {
            self.context.m.mk_var(index, self.sort)
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

        fn forall(
            &mut self,
            num_vars: usize,
            body: Expr,
            patterns: &[&[Expr]],
            weight: i32,
        ) -> Expr {
            let patterns = patterns
                .iter()
                .map(|terms| self.context.m.mk_pattern(terms).unwrap())
                .collect();
            self.context
                .m
                .mk_quantifier(QuantifierData {
                    is_forall: true,
                    sorts: vec![self.sort; num_vars],
                    names: (0..num_vars)
                        .map(|index| SmtSymbol::Name(format!("x{index}")))
                        .collect(),
                    body,
                    patterns,
                    weight,
                    qid: String::new(),
                })
                .unwrap()
        }

        fn assert(&mut self, expr: Expr) {
            self.context.internalize_assertion(expr, 0).unwrap();
        }

        /// The result, the conflicts, the steps with those of the stubs added, and the instances.
        fn search(&mut self, stubbed: Stubbed) -> (LBool, u32, u64, u32) {
            let result = self.context.search().unwrap();
            (
                result,
                self.context.get_num_conflicts(),
                self.context.m.limit.count() + stubbed.theory,
                self.context.qmanager.get_num_instances(),
            )
        }
    }

    #[test]
    fn instantiates_an_inverse_on_its_pattern() {
        // ∀x {g(x)}. f(g(x)) = x, g(a) = g(b), a ≠ b.
        let mut problem = Problem::new();
        let u = problem.sort;
        let f = problem.func("f", &[u], u);
        let g = problem.func("g", &[u], u);
        let x = problem.var(0);
        let gx = problem.app(g, &[x], u);
        let fgx = problem.app(f, &[gx], u);
        let body = problem.eq(fgx, x);
        let q = problem.forall(1, body, &[&[gx]], 0);
        let a = problem.constant("a");
        let b = problem.constant("b");
        problem.assert(q);
        let ga = problem.app(g, &[a], u);
        let gb = problem.app(g, &[b], u);
        let eq = problem.eq(ga, gb);
        problem.assert(eq);
        let eq = problem.eq(a, b);
        let not = problem.not(eq);
        problem.assert(not);
        let stubbed = Stubbed { theory: 2 };
        assert_eq!(problem.search(stubbed), (LBool::False, 1, 41, 2));
    }

    #[test]
    fn chains_transitivity_with_a_multi_pattern() {
        // ∀x y z {r(x, y), r(y, z)}. ¬r(x, y) ∨ ¬r(y, z) ∨ r(x, z), r(a, b), r(b, c), r(c, d),
        // ¬r(a, d).
        let mut problem = Problem::new();
        let u = problem.sort;
        let r = problem.func("r", &[u, u], SORT_BOOL);
        let x = problem.var(2);
        let y = problem.var(1);
        let z = problem.var(0);
        let rxy = problem.app(r, &[x, y], SORT_BOOL);
        let ryz = problem.app(r, &[y, z], SORT_BOOL);
        let not_rxy = problem.not(rxy);
        let not_ryz = problem.not(ryz);
        let rxz = problem.app(r, &[x, z], SORT_BOOL);
        let body = problem.or(&[not_rxy, not_ryz, rxz]);
        let q = problem.forall(3, body, &[&[rxy, ryz]], 0);
        let a = problem.constant("a");
        let b = problem.constant("b");
        let c = problem.constant("c");
        let d = problem.constant("d");
        problem.assert(q);
        for (first, second) in [(a, b), (b, c), (c, d)] {
            let atom = problem.app(r, &[first, second], SORT_BOOL);
            problem.assert(atom);
        }
        let rad = problem.app(r, &[a, d], SORT_BOOL);
        let not = problem.not(rad);
        problem.assert(not);
        let stubbed = Stubbed { theory: 2 };
        assert_eq!(problem.search(stubbed), (LBool::False, 1, 91, 3));
    }

    #[test]
    fn matches_a_nested_pattern_modulo_equalities() {
        // ∀x {f(f(g(x)))}. f(f(g(x))) = g(x), b = g(a), c = f(b), f(c) ≠ b.
        let mut problem = Problem::new();
        let u = problem.sort;
        let f = problem.func("f", &[u], u);
        let g = problem.func("g", &[u], u);
        let x = problem.var(0);
        let gx = problem.app(g, &[x], u);
        let fgx = problem.app(f, &[gx], u);
        let pattern = problem.app(f, &[fgx], u);
        let body = problem.eq(pattern, gx);
        let q = problem.forall(1, body, &[&[pattern]], 0);
        let a = problem.constant("a");
        let b = problem.constant("b");
        let c = problem.constant("c");
        problem.assert(q);
        let ga = problem.app(g, &[a], u);
        let eq = problem.eq(b, ga);
        problem.assert(eq);
        let fb = problem.app(f, &[b], u);
        let eq = problem.eq(c, fb);
        problem.assert(eq);
        let fc = problem.app(f, &[c], u);
        let eq = problem.eq(fc, b);
        let not = problem.not(eq);
        problem.assert(not);
        let stubbed = Stubbed { theory: 2 };
        assert_eq!(problem.search(stubbed), (LBool::False, 1, 42, 1));
    }

    #[test]
    fn instantiates_over_several_rounds() {
        // ∀x {p(x)}. ¬p(x) ∨ p(s(x)), p(a), ¬p(s(s(s(a)))).
        let mut problem = Problem::new();
        let u = problem.sort;
        let p = problem.func("p", &[u], SORT_BOOL);
        let s = problem.func("s", &[u], u);
        let x = problem.var(0);
        let px = problem.app(p, &[x], SORT_BOOL);
        let not_px = problem.not(px);
        let sx = problem.app(s, &[x], u);
        let psx = problem.app(p, &[sx], SORT_BOOL);
        let body = problem.or(&[not_px, psx]);
        let q = problem.forall(1, body, &[&[px]], 0);
        let a = problem.constant("a");
        problem.assert(q);
        let pa = problem.app(p, &[a], SORT_BOOL);
        problem.assert(pa);
        let sa = problem.app(s, &[a], u);
        let ssa = problem.app(s, &[sa], u);
        let sssa = problem.app(s, &[ssa], u);
        let psssa = problem.app(p, &[sssa], SORT_BOOL);
        let not = problem.not(psssa);
        problem.assert(not);
        let stubbed = Stubbed { theory: 2 };
        assert_eq!(problem.search(stubbed), (LBool::False, 1, 82, 3));
    }

    #[test]
    fn checks_the_instances_of_a_heavy_quantifier() {
        // ∀x {p(x)} (weight 12). r(x) ∨ ¬p(x), p(a) ∨ p(b), ¬r(a), ¬r(b).
        let mut problem = Problem::new();
        let u = problem.sort;
        let p = problem.func("p", &[u], SORT_BOOL);
        let r = problem.func("r", &[u], SORT_BOOL);
        let x = problem.var(0);
        let px = problem.app(p, &[x], SORT_BOOL);
        let rx = problem.app(r, &[x], SORT_BOOL);
        let not_px = problem.not(px);
        let body = problem.or(&[rx, not_px]);
        let q = problem.forall(1, body, &[&[px]], 12);
        let a = problem.constant("a");
        let b = problem.constant("b");
        problem.assert(q);
        let pa = problem.app(p, &[a], SORT_BOOL);
        let pb = problem.app(p, &[b], SORT_BOOL);
        let either = problem.or(&[pa, pb]);
        problem.assert(either);
        for constant in [a, b] {
            let atom = problem.app(r, &[constant], SORT_BOOL);
            let not = problem.not(atom);
            problem.assert(not);
        }
        let stubbed = Stubbed { theory: 2 };
        assert_eq!(problem.search(stubbed), (LBool::False, 2, 64, 2));
    }

    #[test]
    fn matches_a_lazy_multi_pattern_in_the_final_check() {
        // ∀x y {p(x, y), p(y, x)} {q(x), q(y)}. ¬q(x) ∨ ¬q(y) ∨ x = y, q(a), q(b), a ≠ b.
        let mut problem = Problem::new();
        let u = problem.sort;
        let p = problem.func("p", &[u, u], u);
        let qd = problem.func("q", &[u], SORT_BOOL);
        let x = problem.var(1);
        let y = problem.var(0);
        let qx = problem.app(qd, &[x], SORT_BOOL);
        let qy = problem.app(qd, &[y], SORT_BOOL);
        let not_qx = problem.not(qx);
        let not_qy = problem.not(qy);
        let eq = problem.eq(x, y);
        let body = problem.or(&[not_qx, not_qy, eq]);
        let pxy = problem.app(p, &[x, y], u);
        let pyx = problem.app(p, &[y, x], u);
        let q = problem.forall(2, body, &[&[pxy, pyx], &[qx, qy]], 0);
        let a = problem.constant("a");
        let b = problem.constant("b");
        problem.assert(q);
        let qa = problem.app(qd, &[a], SORT_BOOL);
        problem.assert(qa);
        let qb = problem.app(qd, &[b], SORT_BOOL);
        problem.assert(qb);
        let eq = problem.eq(a, b);
        let not = problem.not(eq);
        problem.assert(not);
        let stubbed = Stubbed { theory: 4 };
        assert_eq!(problem.search(stubbed), (LBool::False, 1, 47, 1));
    }

    #[test]
    fn refutes_without_a_match() {
        // ∀x {h(x)}. h(x) = x, f(a) ≠ f(b), a = b.
        let mut problem = Problem::new();
        let u = problem.sort;
        let h = problem.func("h", &[u], u);
        let f = problem.func("f", &[u], u);
        let x = problem.var(0);
        let hx = problem.app(h, &[x], u);
        let body = problem.eq(hx, x);
        let q = problem.forall(1, body, &[&[hx]], 0);
        let a = problem.constant("a");
        let b = problem.constant("b");
        problem.assert(q);
        let fa = problem.app(f, &[a], u);
        let fb = problem.app(f, &[b], u);
        let eq = problem.eq(fa, fb);
        let not = problem.not(eq);
        problem.assert(not);
        let eq = problem.eq(a, b);
        problem.assert(eq);
        let stubbed = Stubbed { theory: 0 };
        assert_eq!(problem.search(stubbed), (LBool::False, 1, 7, 0));
    }
}

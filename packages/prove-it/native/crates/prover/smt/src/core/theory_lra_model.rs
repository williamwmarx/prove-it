//! Ported from Z3 (src/smt/theory_lra.cpp), MIT license, see z3-license.txt, through
//! `theory-lra-model.ts`. The model of theory_lra: the values of its variables, and the equalities
//! between shared terms with equal values that it assumes.

use std::collections::{HashMap, HashSet};

use prove_num::{Int, Rational};

use crate::core::ast::{
    Expr, FAMILY_ARITH, FAMILY_BASIC, OP_DIV, OP_DIV0, OP_IDIV, OP_IDIV0, OP_ITE, OP_MOD, OP_MOD0,
};
use crate::core::context::{Context, TrailClosure};
use crate::core::enode::EnodeId;
use crate::core::proto_model::ProtoModel;
use crate::core::theory_lra_state::TheoryClosure;
use crate::core::theory_lra_state::get_lra_mut;
use crate::lp::lar_solver::NULL_LPVAR;
use crate::lp::nla_core::Nla;
use crate::lp::nra_solver::NraSolver;
use crate::lp::numeric_pair::Impq;
use crate::lp::random_updater::random_update;
use crate::nlsat::algebraic::{Anum, AnumValue};
use crate::util::error::SmtError;

impl Context {
    pub(crate) fn lra_init_variable_values(&mut self) {
        self.lra_mut().is_model_initialized = false;
        if self.check_canceled() || self.lra().get_num_vars() == 0 {
            return;
        }
        let saved = self.lra().is_model_initialized;
        self.push_trail(TrailClosure::Theory(TheoryClosure::IsModelInitialized {
            saved,
        }));
        let theory = self.lra_mut();
        theory.is_model_initialized = theory.solver.init_model();
    }

    fn lra_is_relevant_and_shared(&self, node: EnodeId) -> bool {
        self.is_relevant(self.node(node).owner) && self.lra_is_shared(node)
    }

    /// The key the TypeScript writes as `${isInt}:${value}`.
    fn lra_value_key(&mut self, th_var: i32) -> (bool, Impq) {
        let column = self.lra_register_var(th_var);
        (
            self.lra_is_int_var(th_var),
            self.lra().solver.get_value(column).clone(),
        )
    }

    /// random_update: moves the values of shared variables that collide with others.
    fn lra_random_update(&mut self) {
        if self
            .lra_with_nla(|nla| nla.has_relevant_monomial())
            .unwrap_or(false)
        {
            return;
        }
        let mut by_value: HashMap<(bool, Impq), i32> = HashMap::new();
        let mut tmp_var_set: HashSet<i32> = HashSet::new();
        let mut columns = Vec::new();
        for th_var in 0..self.lra().get_num_vars() as i32 {
            if !self.lra_is_relevant_and_shared(self.theory_get_enode(th_var)) {
                continue;
            }
            let key = self.lra_value_key(th_var);
            let column = self.lra_register_var(th_var);
            let Some(other) = by_value.get(&key).copied() else {
                by_value.insert(key, th_var);
                continue;
            };
            if self.lra_is_equal(th_var, other) {
                continue;
            }
            let solver = &self.lra().solver;
            if !solver.is_fixed(column) {
                columns.push(column);
            } else if !tmp_var_set.contains(&other) {
                let other_column = solver.external_to_local_column(other as usize);
                if !solver.is_fixed(other_column) {
                    tmp_var_set.insert(other);
                    columns.push(other_column);
                }
            }
        }
        if !columns.is_empty() {
            random_update(&mut self.lra_mut().solver, &columns);
        }
    }

    /// assume_eqs: model-based theory combination.
    pub(crate) fn lra_assume_eqs(&mut self) -> Result<bool, SmtError> {
        if self.lra_delayed_assume_eqs()? {
            return Ok(true);
        }
        self.lra_random_update();
        let num_vars = self.lra().get_num_vars();
        let old_size = self.lra().assume_eq_candidates.len();
        let mut num_candidates = 0;
        let start = self.get_random_value() as usize;
        let mut by_value: HashMap<(bool, Impq), i32> = HashMap::new();
        let mut representatives: Vec<i32> = Vec::new();
        for index in 0..num_vars {
            let th_var = ((index + start) % num_vars) as i32;
            if !self.lra_is_relevant_and_shared(self.theory_get_enode(th_var)) {
                continue;
            }
            // m_model_eqs: with nlsat's model, the values are compared one by one.
            let key = self.lra_value_key(th_var);
            let other = if self.lra_is_using_nra_model() {
                let mut found = None;
                for representative in representatives.iter().copied() {
                    if self.lra_is_int_var(representative) == self.lra_is_int_var(th_var)
                        && self.lra_is_eq(representative, th_var)?
                    {
                        found = Some(representative);
                        break;
                    }
                }
                found
            } else {
                by_value.get(&key).copied()
            };
            let Some(other) = other else {
                by_value.insert(key, th_var);
                representatives.push(th_var);
                continue;
            };
            if self.lra_is_equal(th_var, other) {
                continue;
            }
            self.lra_mut().assume_eq_candidates.push((th_var, other));
            num_candidates += 1;
        }
        if num_candidates > 0 {
            self.push_trail(TrailClosure::Theory(
                TheoryClosure::ShrinkAssumeEqCandidates { size: old_size },
            ));
        }
        self.lra_delayed_assume_eqs()
    }

    fn lra_is_using_nra_model(&self) -> bool {
        self.lra()
            .nla
            .as_ref()
            .is_some_and(|nla| nla.is_using_nra_model)
    }

    fn lra_delayed_assume_eqs(&mut self) -> Result<bool, SmtError> {
        if self.lra().assume_eq_head == self.lra().assume_eq_candidates.len() {
            return Ok(false);
        }
        let saved = self.lra().assume_eq_head;
        self.push_trail(TrailClosure::Theory(TheoryClosure::AssumeEqHead { saved }));
        while self.lra().assume_eq_head < self.lra().assume_eq_candidates.len() {
            let theory = self.lra_mut();
            let candidate = theory.assume_eq_candidates[theory.assume_eq_head];
            theory.assume_eq_head += 1;
            if self.lra_is_eq(candidate.0, candidate.1)?
                && !self.lra_is_equal(candidate.0, candidate.1)
                && self.assume_eq(
                    self.theory_get_enode(candidate.0),
                    self.theory_get_enode(candidate.1),
                )?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// init_model: the model knows the value of every theory variable without δ, so fresh numbers
    /// avoid them. Like get_value(enode*, expr_ref&), it skips an integer with a fractional value.
    pub fn theory_init_model(&mut self, model: &mut ProtoModel) -> Result<(), SmtError> {
        if self.theory.is_none() {
            return Ok(());
        }
        self.lra_init_variable_values();
        if !self.lra().is_model_initialized {
            return Ok(());
        }
        for th_var in 0..self.lra().get_num_vars() as i32 {
            let solver = &self.lra().solver;
            let column = solver.external_to_local_column(th_var as usize);
            let value = if column == NULL_LPVAR {
                None
            } else {
                solver.get_exact_value(column)
            };
            let Some(value) = value else {
                continue;
            };
            if !self.lra_is_int_var(th_var) {
                let numeral = self.m.mk_real_numeral(&value);
                model.register_value(&mut self.m, numeral);
            } else if value.is_int() {
                let numeral = self.m.mk_numeral(value.num());
                model.register_value(&mut self.m, numeral);
            }
        }
        Ok(())
    }

    /// mk_value: the value of the class of a root, rounded down for an integer; none for a node
    /// without a theory variable.
    pub fn theory_mk_value(&mut self, node: EnodeId) -> Result<Option<Expr>, SmtError> {
        let th_var = self.node(node).th_var;
        if th_var < 0 || self.theory.is_none() {
            return Ok(None);
        }
        if !self.lra_is_using_nra_model()
            || self.lra().solver.external_to_local_column(th_var as usize) == NULL_LPVAR
        {
            return Ok(Some(self.lra_get_value_expr(th_var)));
        }
        // nlsat's value, zero for an integer whose value is not one.
        let anum = self.lra_with_nra_model(|nla| get_nl_value(nla, th_var))?;
        let value = anum.value();
        if self.lra_is_int_var(th_var) {
            let numeral = match &*value {
                AnumValue::Rational(value) if value.is_int() => value.num().clone(),
                _ => Int::zero(),
            };
            return Ok(Some(self.m.mk_numeral(&numeral)));
        }
        match &*value {
            AnumValue::Rational(value) => Ok(Some(self.m.mk_real_numeral(value))),
            AnumValue::Cell(_) => Err(SmtError::Unsupported("an irrational model value".into())),
        }
    }

    /// is_eq: whether two variables have the same value, in nlsat's model when nla uses it.
    fn lra_is_eq(&mut self, first: i32, second: i32) -> Result<bool, SmtError> {
        if self.lra_is_using_nra_model() {
            return self.lra_with_nra_model(|nla| {
                let first = get_nl_value(nla, first)?;
                let second = get_nl_value(nla, second)?;
                Ok(nla.core.nra.am().compare(&first, &second)? == 0)
            });
        }
        let first_column = self.lra_register_var(first);
        let second_column = self.lra_register_var(second);
        let solver = &self.lra().solver;
        Ok(solver.get_value(first_column) == solver.get_value(second_column))
    }

    /// nla's view for reading nlsat's model, which `lra_is_using_nra_model` says nla has. Reading
    /// it consults no relevancy, so the view answers none, unlike `lra_with_nla`'s.
    fn lra_with_nra_model<T>(
        &mut self,
        body: impl FnOnce(&mut Nla<'_, 'static>) -> Result<T, SmtError>,
    ) -> Result<T, SmtError> {
        let theory = get_lra_mut(&mut self.theory);
        let Some(core) = theory.nla.as_mut() else {
            unreachable!("nlsat's model is nla's");
        };
        body(&mut Nla {
            core,
            lra: &mut theory.solver,
            limit: &self.m.limit,
            is_relevant: &|_| false,
        })
    }

    fn lra_get_value(&self, th_var: i32) -> Rational {
        let solver = &self.lra().solver;
        let column = solver.external_to_local_column(th_var as usize);
        if column == NULL_LPVAR {
            Rational::zero()
        } else {
            solver.get_model_value(column)
        }
    }

    fn lra_get_value_expr(&mut self, th_var: i32) -> Expr {
        let value = self.lra_get_value(th_var);
        if self.lra_is_int_var(th_var) {
            self.m.mk_numeral(value.floor().num())
        } else {
            self.m.mk_real_numeral(&value)
        }
    }

    fn lra_is_shared(&self, node: EnodeId) -> bool {
        let root = self.root(node);
        if self.m.get_op(self.node(root).owner) == OP_ITE {
            return true;
        }
        if self.node(root).th_var < 0 {
            return false;
        }
        if self.qmanager.is_shared(root) {
            return true;
        }
        for parent in &self.node(root).parents {
            let family = self.m.get_family(self.node(*parent).owner);
            if family != FAMILY_ARITH && family != FAMILY_BASIC {
                return true;
            }
        }
        self.lra_is_shared_with_underspecified(root)
    }

    /// theory_lra::is_shared: whether the class is an argument of a division by a term or by
    /// zero.
    fn lra_is_shared_with_underspecified(&self, root: EnodeId) -> bool {
        let terms = &self.lra().underspecified_terms;
        let count = terms.len();
        if count == 0 {
            return false;
        }
        if self.node(root).parents.len() > 2 * count {
            return terms.iter().any(|term| {
                self.m.some_arg(*term, |arg, _| {
                    self.get_enode(arg)
                        .is_some_and(|node| self.root(node) == root)
                })
            });
        }
        self.node(root)
            .parents
            .iter()
            .any(|parent| self.lra_is_underspecified(self.node(*parent).owner))
    }

    /// arith_util::is_underspecified.
    fn lra_is_underspecified(&self, expr: Expr) -> bool {
        let op = self.m.get_op(expr);
        op == OP_DIV
            || op == OP_IDIV
            || op == OP_MOD
            || op == OP_DIV0
            || op == OP_IDIV0
            || op == OP_MOD0
    }
}

/// nl_value: the value of a variable in nlsat's model, a term's the sum over its columns.
fn get_nl_value(nla: &mut Nla<'_, '_>, th_var: i32) -> Result<Anum, SmtError> {
    let column = nla.lra.external_to_local_column(th_var as usize);
    if !nla.lra.has_term(column) {
        return NraSolver::value(nla, column);
    }
    let mut result = Anum::new(Rational::zero());
    let mut todo = vec![(column, Rational::one())];
    while let Some(pending) = todo.pop() {
        let entries: Vec<(usize, Rational)> = nla
            .lra
            .get_term(pending.0)?
            .iter()
            .map(|entry| (entry.0, entry.1.clone()))
            .collect();
        for entry in entries {
            let coeff = entry.1.mul(&pending.1);
            if nla.lra.has_term(entry.0) {
                todo.push((entry.0, coeff));
                continue;
            }
            let value = NraSolver::value(nla, entry.0)?;
            let am = nla.core.nra.am();
            let product = am.mul(&value, &Anum::new(coeff))?;
            result = am.add(&product, &result)?;
        }
    }
    Ok(result)
}

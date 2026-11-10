// Ported from Z3 (src/math/lp/cross_nested.h), MIT license, see z3-license.txt. Enumerates the
// cross-nested forms of a sum, such as x*(y + z) + w for x*y + x*z + w, and calls back on each
// until the callback returns true or 100 forms are reported. A form is built by rewriting the
// expression in place: the front holds the slots of the subsums still to split.
//
// The occurrence map is a Map in insertion order, where Z3 has an unordered_map. So when several
// variables divide every summand, the extracted common factor may list them in another order.
//
// The TypeScript takes two closures, the callback on a form and var_is_fixed, which both reach
// nla's core; here they are the two methods of one `CrossNestedCallbacks`, so that one value can
// hold the core mutably. The callback reads the form from the creator it is given.
use prove_num::Rational;

use crate::lp::nex::{
    Nex, NexId, NexPow, contains_var, get_powers_from_mul, get_vars_of_expr, is_linear,
};
use crate::lp::nex_creator::{NexCreator, NexFactor, Occ};
use crate::util::random_gen::RandomGen;

pub trait CrossNestedCallbacks {
    // call_on_result: whether to stop at this form.
    fn call_on_result(&mut self, nex_creator: &NexCreator, expr: NexId) -> bool;
    fn var_is_fixed(&self, variable: usize) -> bool;
}

impl<CallOnResult, VarIsFixed> CrossNestedCallbacks for (CallOnResult, VarIsFixed)
where
    CallOnResult: FnMut(&NexCreator, NexId) -> bool,
    VarIsFixed: Fn(usize) -> bool,
{
    fn call_on_result(&mut self, nex_creator: &NexCreator, expr: NexId) -> bool {
        (self.0)(nex_creator, expr)
    }

    fn var_is_fixed(&self, variable: usize) -> bool {
        (self.1)(variable)
    }
}

// A place that holds an expression, where Z3 has a nex**: the root, or a child of a product or of
// a sum.
#[derive(Clone, Copy)]
enum NexSlot {
    Root,
    MulChild(NexId, usize),
    SumChild(NexId, usize),
}

fn is_divisible_by_var(nexes: &[Nex], expr: NexId, variable: usize) -> bool {
    match nexes[expr] {
        Nex::Mul(_) => contains_var(nexes, expr, variable),
        Nex::Var(expr_variable) => expr_variable == variable,
        _ => false,
    }
}

// has_common_factor: whether a variable of the first summand divides the rest. A sum that
// simplified to one term counts as a sum of that term.
fn has_common_factor(nexes: &[Nex], expr: NexId) -> bool {
    let children = match &nexes[expr] {
        Nex::Sum(sum) => sum.children.clone(),
        _ => vec![expr],
    };
    for variable in get_vars_of_expr(nexes, children[0]) {
        if children[1..]
            .iter()
            .all(|child| contains_var(nexes, *child, variable))
        {
            return true;
        }
    }
    false
}

pub struct CrossNested<'a, Callbacks: CrossNestedCallbacks> {
    root: NexId,
    is_done: bool,
    is_limit_exceeded: bool,
    reported: u32,
    is_random_bit: bool,
    callbacks: Callbacks,
    limit: &'a dyn Fn() -> bool,
    random: RandomGen,
    pub nex_creator: &'a mut NexCreator,
}

impl<'a, Callbacks: CrossNestedCallbacks> CrossNested<'a, Callbacks> {
    pub fn new(
        callbacks: Callbacks,
        limit: &'a dyn Fn() -> bool,
        random_seed: u32,
        nex_creator: &'a mut NexCreator,
    ) -> CrossNested<'a, Callbacks> {
        let root = nex_creator.mk_sum(&[]);
        CrossNested {
            root,
            is_done: false,
            is_limit_exceeded: false,
            reported: 0,
            is_random_bit: false,
            callbacks,
            limit,
            random: RandomGen::new(random_seed),
            nex_creator,
        }
    }

    pub fn run(&mut self, expr: NexId) {
        self.root = expr;
        self.explore_expr_on_front_elem(NexSlot::Root, &mut Vec::new());
    }

    pub fn done(&self) -> bool {
        self.is_done
    }

    fn get_slot(&self, slot: NexSlot) -> NexId {
        match slot {
            NexSlot::Root => self.root,
            NexSlot::MulChild(mul, index) => self.nex_creator.get_mul(mul).children[index].expr,
            NexSlot::SumChild(sum, index) => self.nex_creator.get_sum(sum).children[index],
        }
    }

    fn set_slot(&mut self, slot: NexSlot, value: NexId) {
        match slot {
            NexSlot::Root => self.root = value,
            NexSlot::MulChild(mul, index) => {
                let children = &mut self.nex_creator.get_mul_mut(mul).children;
                children[index] = NexPow {
                    expr: value,
                    power: children[index].power,
                };
            }
            NexSlot::SumChild(sum, index) => {
                self.nex_creator.get_sum_mut(sum).children[index] = value;
            }
        }
    }

    fn report(&mut self) {
        self.is_done = self.callbacks.call_on_result(self.nex_creator, self.root) || {
            self.reported += 1;
            self.reported > 100
        };
    }

    fn extract_common_factor(&mut self, sum: NexId) -> Option<NexId> {
        let size = self.nex_creator.get_sum(sum).children.len();
        let entries: Vec<(usize, Occ)> = self
            .nex_creator
            .occurences_map
            .iter()
            .filter(|entry| entry.1.occs == size)
            .copied()
            .collect();
        let factors: Vec<NexPow> = entries
            .into_iter()
            .map(|entry| NexPow {
                expr: self.nex_creator.mk_var(entry.0),
                power: entry.1.power,
            })
            .collect();
        if factors.is_empty() {
            return None;
        }
        Some(
            self.nex_creator
                .mk_mul_with_powers(Rational::one(), factors),
        )
    }

    fn proceed_with_common_factor(
        &mut self,
        slot: NexSlot,
        expr: NexId,
        front: &mut Vec<NexSlot>,
    ) -> bool {
        let Some(factor) = self.extract_common_factor(expr) else {
            return false;
        };
        let division = self.nex_creator.mk_div(expr, factor);
        let quotient = self.nex_creator.simplify(division);
        let product = self
            .nex_creator
            .mk_mul(&[NexFactor::Expr(factor), NexFactor::Expr(quotient)]);
        self.set_slot(slot, product);
        self.explore_expr_on_front_elem(NexSlot::MulChild(product, 1), front);
        true
    }

    fn explore_expr_on_front_elem_vars(
        &mut self,
        slot: NexSlot,
        front: &[NexSlot],
        vars: &[usize],
    ) {
        let copy_of_expr = self.get_slot(slot);
        let copy_of_front: Vec<NexId> = front
            .iter()
            .map(|front_slot| self.get_slot(*front_slot))
            .collect();
        for variable in vars {
            if self.is_done || self.is_limit_exceeded {
                return;
            }
            if self.callbacks.var_is_fixed(*variable) {
                continue;
            }
            self.explore_of_expr_on_sum_and_var(slot, *variable, front.to_vec());
            if self.is_done || self.is_limit_exceeded {
                return;
            }
            self.set_slot(slot, copy_of_expr);
            for (index, front_slot) in front.iter().enumerate() {
                self.set_slot(*front_slot, copy_of_front[index]);
            }
        }
    }

    fn calc_occurences(&mut self, sum: NexId) {
        let creator = &mut *self.nex_creator;
        creator.occurences_map.clear();
        creator.powers.clear();
        let Nex::Sum(sum) = &creator.nexes[sum] else {
            panic!("nex {sum} is not a sum");
        };
        for child in &sum.children {
            match &creator.nexes[*child] {
                Nex::Mul(mul) => {
                    get_powers_from_mul(&creator.nexes, mul, &mut creator.powers);
                    for entry in &creator.powers {
                        match creator
                            .occurences_map
                            .iter_mut()
                            .find(|occurence| occurence.0 == entry.0)
                        {
                            None => creator.occurences_map.push((
                                entry.0,
                                Occ {
                                    occs: 1,
                                    power: entry.1,
                                },
                            )),
                            Some(occurence) => {
                                occurence.1.occs += 1;
                                occurence.1.power = occurence.1.power.min(entry.1);
                            }
                        }
                    }
                }
                Nex::Var(variable) => {
                    match creator
                        .occurences_map
                        .iter_mut()
                        .find(|occurence| occurence.0 == *variable)
                    {
                        None => creator
                            .occurences_map
                            .push((*variable, Occ { occs: 1, power: 1 })),
                        Some(occurence) => {
                            occurence.1.occs += 1;
                            occurence.1.power = 1;
                        }
                    }
                }
                _ => {}
            }
        }
        creator.occurences_map.retain(|entry| entry.1.occs > 1);
    }

    // The variables to factor out, by occurrences, then by power, then by index in the direction
    // of a random bit.
    fn get_vars_from_occurences_map(&mut self) -> Vec<usize> {
        self.is_random_bit = self.random.next() % 2 == 1;
        let mut entries = self.nex_creator.occurences_map.clone();
        let is_random_bit = self.is_random_bit;
        entries.sort_by(|first, second| {
            if first.1.occs != second.1.occs {
                return second.1.occs.cmp(&first.1.occs);
            }
            if first.1.power != second.1.power {
                return second.1.power.cmp(&first.1.power);
            }
            if is_random_bit {
                first.0.cmp(&second.0)
            } else {
                second.0.cmp(&first.0)
            }
        });
        entries.into_iter().map(|entry| entry.0).collect()
    }

    fn explore_expr_on_front_elem(&mut self, slot: NexSlot, front: &mut Vec<NexSlot>) {
        if self.is_done || self.is_limit_exceeded {
            return;
        }
        if !(self.limit)() {
            self.is_limit_exceeded = true;
            return;
        }
        let expr = self.get_slot(slot);
        // A front element is a sum, unlike in Z3, which would misread anything else as one.
        if matches!(self.nex_creator.nexes[expr], Nex::Sum(_)) {
            self.calc_occurences(expr);
            // Z3 passes a copy of the front here.
            if self.proceed_with_common_factor(slot, expr, &mut front.clone()) {
                return;
            }
            let vars = self.get_vars_from_occurences_map();
            if !vars.is_empty() {
                return self.explore_expr_on_front_elem_vars(slot, front, &vars);
            }
        }
        let Some(next) = front.pop() else {
            return self.report();
        };
        self.explore_expr_on_front_elem(next, front);
    }

    fn explore_of_expr_on_sum_and_var(
        &mut self,
        slot: NexSlot,
        variable: usize,
        mut front: Vec<NexSlot>,
    ) {
        if self.is_done || self.is_limit_exceeded {
            return;
        }
        if !(self.limit)() {
            self.is_limit_exceeded = true;
            return;
        }
        if !self.split_with_var(slot, variable, &mut front) {
            return;
        }
        let Some(next) = front.pop() else {
            return self.report();
        };
        self.explore_expr_on_front_elem(next, &mut front);
    }

    // split_with_var: e = j*a + b, where a sums the summands divisible by j, divided by it, and b
    // sums the rest. It is enough to split on the variables where a has no common factor.
    fn split_with_var(&mut self, slot: NexSlot, variable: usize, front: &mut Vec<NexSlot>) -> bool {
        let expr = self.get_slot(slot);
        let Nex::Sum(sum) = &self.nex_creator.nexes[expr] else {
            return false;
        };
        let mut quotients = Vec::new();
        let mut rest = Vec::new();
        for child in sum.children.clone() {
            if is_divisible_by_var(&self.nex_creator.nexes, child, variable) {
                quotients.push(self.nex_creator.mk_div_by_var(child, variable));
            } else {
                rest.push(child);
            }
        }
        let quotients_sum = self.nex_creator.mk_sum(&quotients);
        let quotient = self.nex_creator.simplify_sum(quotients_sum);
        let remainder = if rest.len() == 1 {
            rest[0]
        } else {
            self.nex_creator.mk_sum(&rest)
        };
        if has_common_factor(&self.nex_creator.nexes, quotient) {
            return false;
        }
        let variable_nex = self.nex_creator.mk_var(variable);
        let product = self
            .nex_creator
            .mk_mul(&[NexFactor::Expr(variable_nex), NexFactor::Expr(quotient)]);
        let split = self.nex_creator.mk_sum(&[product, remainder]);
        self.set_slot(slot, split);
        if !is_linear(&self.nex_creator.nexes, quotient) {
            front.push(NexSlot::MulChild(product, 1));
        }
        if matches!(self.nex_creator.nexes[remainder], Nex::Sum(_))
            && !is_linear(&self.nex_creator.nexes, remainder)
        {
            front.push(NexSlot::SumChild(split, 1));
        }
        true
    }
}

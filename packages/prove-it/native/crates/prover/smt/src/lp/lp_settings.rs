// Ported from Z3 (src/math/lp/lp_settings.h, src/math/lp/lp_settings.cpp), MIT license, see
// z3-license.txt. The settings that theory_lra's UFNIA configuration gives the lp solver, its
// random generator and its statistics.
use crate::util::random_gen::RandomGen;

#[derive(Default, Clone, Debug)]
pub struct LpStats {
    pub make_feasible: u64,
    pub pivots: u64,
    pub patches: u64,
    pub patches_success: u64,
    pub gcd_calls: u64,
    pub gcd_conflicts: u64,
    pub branches: u64,
    pub bp_rows_analyzed: u64,
    pub offset_eqs: u64,
    pub fixed_eqs: u64,
    pub dio_calls: u64,
    pub dio_tighten_conflicts: u64,
    pub dio_rewrite_conflicts: u64,
    pub dio_state_resets: u64,
    pub lcube_calls: u64,
    pub lcube_success: u64,
    pub lcube_flip_success: u64,
    pub nla_calls: u64,
    pub nla_add_bounds: u64,
    pub nla_propagate_bounds: u64,
    pub nla_propagate_eq: u64,
    pub nla_lemmas: u64,
    pub nla_bounds_improvements: u64,
    pub nla_throttled_lemmas: u64,
    pub nra_calls: u64,
}

pub struct LpSettings {
    random: RandomGen,
    pub stats: LpStats,
    pub max_row_length_for_bound_propagation: usize,
    pub max_iterations_with_no_improvements: u64,
    pub is_propagating_eqs: bool,
    pub int_find_cube_period: u64,
    // lp.lcube_flips: the most flips that repair a rounded cube center.
    pub lcube_flips: u64,
    pub hnf_cut_period: u64,
    pub limit_on_rows_for_hnf_cutter: usize,
    pub limit_on_columns_for_hnf_cutter: usize,
    pub int_gomory_cut_period: u64,
    // lp.dio_calls_period, which the Diophantine solver's results move, its decrease, and
    // lp.dio_gomory_enable_period.
    pub dio_calls_period: u64,
    pub dio_calls_period_decrease: u64,
    pub dio_gomory_enable_period: u64,
    // m_run_gomory_with_dio: Gomory cuts run once the Diophantine solver keeps failing.
    pub is_running_gomory_with_dio: bool,
    // lp.dio_ignore_big_nums and lp.dio_undo_max_work.
    pub is_dio_ignoring_big_nums: bool,
    pub dio_undo_max_work: u64,
    is_canceled: Box<dyn Fn() -> bool>,
}

impl LpSettings {
    pub fn new(is_canceled: Box<dyn Fn() -> bool>) -> LpSettings {
        LpSettings {
            random: RandomGen::new(0),
            stats: LpStats::default(),
            max_row_length_for_bound_propagation: 300,
            max_iterations_with_no_improvements: 2000000,
            is_propagating_eqs: true,
            int_find_cube_period: 4,
            lcube_flips: 16,
            hnf_cut_period: 4,
            limit_on_rows_for_hnf_cutter: 75,
            limit_on_columns_for_hnf_cutter: 150,
            int_gomory_cut_period: 4,
            dio_calls_period: 1,
            dio_calls_period_decrease: 2,
            dio_gomory_enable_period: 16,
            is_running_gomory_with_dio: false,
            is_dio_ignoring_big_nums: true,
            dio_undo_max_work: 1000000,
            is_canceled,
        }
    }

    // In TypeScript a closure the LarSolver's creator passes; the theory's counts a step of the
    // resource limit, so this is not a pure query.
    pub fn is_canceled(&self) -> bool {
        (self.is_canceled)()
    }

    // random_next: random_gen's next value.
    pub fn get_random_next(&mut self) -> u32 {
        self.random.next()
    }

    // random_next with a bound: that value modulo the bound.
    pub fn get_random_next_below(&mut self, bound: u32) -> u32 {
        self.random.next() % bound
    }
}

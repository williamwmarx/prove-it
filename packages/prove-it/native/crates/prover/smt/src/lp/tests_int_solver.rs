// The integer solver end to end: a depth-first search that branches on the solver's branches and
// adds its cuts as bounded terms. The expected logs, statistics and values come from running the
// same driver over the TypeScript IntSolver.
use std::cell::Cell;

use prove_num::{Int, Rational};

use crate::lp::constraints::{ConstraintKind, KIND_GE, KIND_LE};
use crate::lp::core_solver::LP_INFEASIBLE;
use crate::lp::int_solver::{IntSolver, Lia, LiaMove};
use crate::lp::lar_solver::{LarSolver, NULL_LPVAR};

fn parse(text: &str) -> Rational {
    let (num, den) = text.split_once('/').unwrap_or((text, "1"));
    Rational::of(
        Int::from(num.parse::<i64>().expect("a numerator")),
        Int::from(den.parse::<i64>().expect("a denominator")),
    )
}

fn add_bound(solver: &mut LarSolver<'_>, column: usize, kind: ConstraintKind, rhs: &Rational) {
    let index = solver.mk_var_bound(column, kind, rhs);
    solver.activate(index);
}

// v<external>i|r adds a variable, t<external>:<external>=<coeff>,... a term, and
// b<external><=|>=<value> a bound.
fn apply(solver: &mut LarSolver<'_>, ops: &str) {
    for op in ops.split(' ') {
        if let Some(var) = op.strip_prefix('v') {
            let external = var[..var.len() - 1].parse().expect("an external");
            solver.add_var(external, var.ends_with('i'));
        } else if let Some(term) = op.strip_prefix('t') {
            let (external, entries) = term.split_once(':').expect("a term");
            let coeffs: Vec<(usize, Rational)> = entries
                .split(',')
                .map(|entry| {
                    let (column, coeff) = entry.split_once('=').expect("an entry");
                    let column = column.parse().expect("a column");
                    (solver.external_to_local_column(column), parse(coeff))
                })
                .collect();
            solver.add_term(&coeffs, external.parse().expect("an external"));
        } else {
            let bound = &op[1..];
            let (kind, (column, value)) = match bound.split_once("<=") {
                Some(parts) => (KIND_LE, parts),
                None => (KIND_GE, bound.split_once(">=").expect("a bound")),
            };
            let column = solver.external_to_local_column(column.parse().expect("a column"));
            add_bound(solver, column, kind, &parse(value));
        }
    }
}

fn get_stats(solver: &LarSolver<'_>) -> String {
    let stats = &solver.settings().stats;
    [
        stats.make_feasible,
        stats.pivots,
        stats.patches,
        stats.patches_success,
        stats.gcd_calls,
        stats.gcd_conflicts,
        stats.branches,
        stats.dio_calls,
        stats.dio_tighten_conflicts,
        stats.dio_rewrite_conflicts,
        stats.dio_state_resets,
        stats.lcube_calls,
        stats.lcube_success,
        stats.lcube_flip_success,
    ]
    .map(|count| count.to_string())
    .join(",")
}

fn get_values(solver: &LarSolver<'_>) -> String {
    (0..solver.get_column_count())
        .map(|column| solver.get_value(column).to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

fn get_dio_state(solver: &LarSolver<'_>) -> String {
    let hooks = solver.dio_hooks.as_ref().expect("the hooks");
    let join = |columns: &mut dyn Iterator<Item = &usize>| {
        columns
            .map(|column| column.to_string())
            .collect::<Vec<_>>()
            .join(",")
    };
    format!(
        "active {} added {} rows {}",
        join(&mut hooks.active_terms.iter()),
        join(&mut hooks.added_terms.iter()),
        hooks.e_matrix.get_row_count()
    )
}

fn run(
    lia: &mut IntSolver,
    solver: &mut LarSolver<'_>,
    log: &mut Vec<String>,
    depth: usize,
) -> String {
    for _ in 0..40 {
        if solver.find_feasible_solution() == LP_INFEASIBLE {
            log.push("lp-infeasible".to_string());
            return "unsat".to_string();
        }
        let lia_move = Lia { lia, lra: solver }
            .check()
            .expect("no invariant fails");
        let term = lia
            .term
            .iter()
            .map(|entry| format!("{}*{}", entry.0, entry.1))
            .collect::<Vec<_>>()
            .join("+");
        match &lia_move {
            LiaMove::Sat => log.push("sat".to_string()),
            LiaMove::Undef => log.push("undef".to_string()),
            LiaMove::Continue => log.push("continue".to_string()),
            LiaMove::Conflict => {
                let explanation: Vec<String> = lia
                    .explanation
                    .iter()
                    .map(|index| index.to_string())
                    .collect();
                log.push(format!("conflict [{}]", explanation.join(",")));
            }
            LiaMove::Cut { offset, is_upper } => {
                log.push(format!("cut {offset} {is_upper} {term}"))
            }
            LiaMove::Branch { is_upper, offset } => {
                log.push(format!("branch {offset} {is_upper} {term}"))
            }
        }
        match lia_move {
            LiaMove::Sat => return "sat".to_string(),
            LiaMove::Undef => return "undef".to_string(),
            LiaMove::Conflict => return "unsat".to_string(),
            LiaMove::Continue => {}
            LiaMove::Cut { offset, is_upper } => {
                let coeffs: Vec<(usize, Rational)> = lia
                    .term
                    .iter()
                    .map(|entry| (entry.0, entry.1.clone()))
                    .collect();
                let column = solver.add_term(&coeffs, NULL_LPVAR);
                add_bound(
                    solver,
                    column,
                    if is_upper { KIND_LE } else { KIND_GE },
                    &offset,
                );
            }
            LiaMove::Branch { is_upper, offset } => {
                if depth > 6 {
                    return "deep".to_string();
                }
                let column = lia.term.iter().next().expect("a branch column").0;
                let sides = if is_upper {
                    [
                        (KIND_LE, offset.clone()),
                        (KIND_GE, offset.add(&Rational::one())),
                    ]
                } else {
                    [
                        (KIND_GE, offset.clone()),
                        (KIND_LE, offset.sub(&Rational::one())),
                    ]
                };
                for side in sides {
                    solver.push();
                    add_bound(solver, column, side.0, &side.1);
                    let result = run(lia, solver, log, depth + 1);
                    solver.pop(1);
                    log.push(format!("pop {result}"));
                    if result == "sat" {
                        return result;
                    }
                }
                return "unsat".to_string();
            }
        }
    }
    "steps".to_string()
}

fn check_case(ops: &str, result: &str, log: &[&str], stats: &str, values: &str, cancel_count: u64) {
    // Each check of the closure counts a resource step in production, so their number is compared.
    let cancel_checks = Cell::new(0);
    let mut solver = LarSolver::new(Box::new(|| {
        cancel_checks.set(cancel_checks.get() + 1);
        false
    }));
    let mut lia = IntSolver::new(&mut solver);
    apply(&mut solver, ops);
    let mut actual = Vec::new();
    assert_eq!(run(&mut lia, &mut solver, &mut actual, 0), result);
    assert_eq!(actual, log);
    assert_eq!(get_stats(&solver), stats);
    assert_eq!(get_values(&solver), values);
    assert_eq!(cancel_checks.get(), cancel_count);
}

#[test]
fn branches_on_a_fractional_column() {
    check_case(
        "v0i v1i t2:0=3,1=3/2 b2>=2 b2<=3 b0>=-2 b0<=10 b1>=-3 b1<=4",
        "sat",
        &[
            "branch -2 true 0*1",
            "lp-infeasible",
            "pop unsat",
            "sat",
            "pop sat",
        ],
        "5,7,2,0,2,0,1,1,0,0,0,1,1,0",
        "-1 4 3",
        20,
    );
}

#[test]
fn finds_a_diophantine_conflict() {
    check_case(
        "v0i v1i t2:0=2,1=4 b2>=3 b2<=3 b0>=-5 b1<=7",
        "unsat",
        &["conflict [0,1]"],
        "2,1,1,0,0,0,0,1,0,1,0,0,0,0",
        "-5 13/4 3",
        5,
    );
}

#[test]
fn adds_gomory_cuts() {
    check_case(
        "v0i v1i v2i t3:0=1/2,1=-2,2=-3 b3>=0 b3<=1 t4:0=2,1=-1/2,2=3 b4>=8 b4<=8 t5:0=4,1=-1 \
         b5>=8 b5<=10 b0>=-1 b0<=6 b1>=-2 b1<=5 b2>=-5 b2<=2",
        "unsat",
        &[
            "continue",
            "branch 5 false 7*1",
            "lp-infeasible",
            "pop unsat",
            "lp-infeasible",
            "pop unsat",
        ],
        "5,11,2,0,2,0,1,1,0,0,0,0,0,0",
        "2 -2 1 2 8 10 5 4",
        34,
    );
}

#[test]
fn repairs_the_rounded_center_of_the_largest_cube() {
    check_case(
        "v0i v1i v2i t3:0=4,1=3/2,2=4 b3>=1/2 b3<=2 t4:0=-1,2=2 b4>=9/2 b4<=9 b0>=-4 b0<=2 \
         b1>=2 b1<=11 b2>=-1 b2<=6",
        "sat",
        &["branch 1 true 2*1", "sat", "pop sat"],
        "3,9,2,0,2,0,1,1,0,0,0,1,1,1",
        "-3 6 1 1 5",
        22,
    );
}

// Terms the Diophantine solver holds are popped: one at a time while undoing is cheap, and by a
// reset of its state when it is not.
fn check_push_pop(max_work: u64, inner_state: &str, stats: &str, cancel_count: u64) {
    // Each check of the closure counts a resource step in production, so their number is compared.
    let cancel_checks = Cell::new(0);
    let mut solver = LarSolver::new(Box::new(|| {
        cancel_checks.set(cancel_checks.get() + 1);
        false
    }));
    solver.settings_mut().dio_undo_max_work = max_work;
    let mut lia = IntSolver::new(&mut solver);
    apply(
        &mut solver,
        "v0i v1i v2i t3:0=4,1=6,2=10 b3>=1 b3<=30 b0>=-9 b0<=9 b1>=-9 b1<=9 b2>=-9 b2<=9",
    );
    let mut log = Vec::new();
    let result = run(&mut lia, &mut solver, &mut log, 0);
    log.push(format!("outer {result}"));
    solver.push();
    apply(
        &mut solver,
        "t4:0=3,1=6,2=9 t5:0=1,2=-2 b4>=4 b4<=5 b5>=1 b5<=1",
    );
    let result = run(&mut lia, &mut solver, &mut log, 0);
    log.push(format!("inner {result}"));
    solver.pop(1);
    log.push(get_dio_state(&solver));
    let result = run(&mut lia, &mut solver, &mut log, 0);
    log.push(format!("after {result}"));
    solver.push();
    apply(&mut solver, "t6:0=2,1=2 b6>=3 b6<=3");
    let result = run(&mut lia, &mut solver, &mut log, 0);
    log.push(format!("again {result}"));
    solver.pop(1);
    log.push(get_dio_state(&solver));
    let result = run(&mut lia, &mut solver, &mut log, 0);
    log.push(format!("last {result}"));
    assert_eq!(
        log,
        [
            "sat",
            "outer sat",
            "conflict [8,9]",
            "inner unsat",
            inner_state,
            "branch -8 false 1*1",
            "sat",
            "pop sat",
            "after sat",
            "cut -1 true 0*-2+1*-3+2*-5",
            "cut 1 true 0*1+1*1",
            "lp-infeasible",
            "again unsat",
            "active 3 added  rows 1",
            "branch 2 false 2*1",
            "sat",
            "pop sat",
            "last sat",
        ]
    );
    assert_eq!(get_stats(&solver), stats);
    assert_eq!(get_values(&solver), "9 -9 2 2");
    assert_eq!(cancel_checks.get(), cancel_count);
}

#[test]
fn pops_active_terms_one_by_one() {
    check_push_pop(
        1000000,
        "active 3 added  rows 1",
        "19,21,6,1,0,0,2,2,1,0,0,1,0,0",
        60,
    );
}

#[test]
fn pops_active_terms_by_a_reset() {
    check_push_pop(
        0,
        "active  added 3 rows 0",
        "19,21,6,1,0,0,2,2,1,0,1,1,0,0",
        58,
    );
}
